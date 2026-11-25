/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GenericCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Curve.GenericComparison
public import WeilConjectures.AlgebraicGeometry.Curve.FunctionFieldUnits
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
public import WeilConjectures.AlgebraicGeometry.Sites.SplitSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-!
# Higher cohomology of `𝔾ₘ` on a curve

Let `C` be an integral curve over an algebraically closed field `k`, with generic point
`η : Spec k(C) ⟶ C`. Assume that `Hᵠ(Spec L, 𝔾ₘ) = 0` for `q ≥ 1` and every algebraic
extension `L` of `k(C)` (blueprint `lemma-cohomology-multiplicative-group`). Then `Hᵠ(C_ét, 𝔾ₘ) = 0`
for `q ≥ 2` (blueprint `lemma-cohomology-multiplicative-group--2`).

The argument follows the blueprint at the generic point, without spectral sequences:

* `Hᵠ(C, 𝔾ₘ) ≅ Hᵠ(C, η_* η^* 𝔾ₘ)` for `q ≥ 2`
  (`AlgebraicGeometry.IsCurve.bijective_H_map_unit_fromSpecFunctionField`), and
  `η^* 𝔾ₘ = 𝔾ₘ`;
* an affine étale `k(C)`-scheme `W` is a finite disjoint union of spectra of finite separable
  extensions of `k(C)`, so `Hᵇ(W, 𝔾ₘ) = 0` for `b ≥ 1`
  (`AlgebraicGeometry.Scheme.subsingleton_sheafH_upperStar_gmSheaf_of_isAffine`);
* a sheaf `N` on `Spec k(C)` without higher cohomology on affine étale `k(C)`-schemes has
  `Hᵖ(C, η_* N) = 0` for `p ≥ 1`
  (`AlgebraicGeometry.IsCurve.subsingleton_sheafH_lowerStar_of_forall_isAffine`): dimension
  shifting along an injective envelope `0 → N → I → N' → 0`, which stays exact after `η_*`
  since `H¹` of `N` vanishes on the affine generic fibres of affine étale `C`-schemes.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_gmSheaf_of_forall_field`: the vanishing for
  an integral curve, under the field hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open AlgebraicGeometry.Etale

namespace AlgebraicGeometry

namespace Scheme

/-- A scheme with a single point is affine: an affine open neighbourhood of the point is the
whole scheme. -/
lemma isAffine_of_subsingleton (X : Scheme.{u}) [Subsingleton X] : IsAffine X := by
  cases isEmpty_or_nonempty X with
  | inl _ => infer_instance
  | inr hX =>
  obtain ⟨x⟩ := hX
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU' : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact Subsingleton.elim x y ▸ hxU
  subst hU'
  have : IsAffine (⊤ : X.Opens).toScheme := hU
  exact .of_isIso X.topIso.inv

/-- The global sections of a nonempty reduced scheme with a single point form a field. -/
lemma isField_Γ_of_subsingleton (X : Scheme.{u}) [Subsingleton X] [Nonempty X] [IsReduced X] :
    IsField Γ(X, ⊤) := by
  have := X.isAffine_of_subsingleton
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  rw [← PrimeSpectrum.subsingleton_iff_isField_of_isReduced]
  exact (X.isoSpec.inv.homeomorph.symm.toEquiv).subsingleton_congr.mp inferInstance

/-- **`𝔾ₘ` on an affine étale scheme over a field.** Let `W` be an affine étale scheme over a
field `K`. If `Hᵠ(Spec L, 𝔾ₘ) = 0` for every finite separable field extension `L` of `K`, then
`Hᵠ(W, 𝔾ₘ) = 0`: `W` is the finite disjoint union of its points, each the spectrum of such a
field. -/
theorem subsingleton_sheafH_upperStar_gmSheaf_of_isAffine {K : Type u} [Field K]
    (W : (Spec (.of K)).Etale) [IsAffine W.left] (q : ℕ)
    (h : ∀ (L : Type u) [Field L] [Algebra K L] [Algebra.Etale K L],
      Subsingleton (Sheaf.H (Spec (.of L)).gmSheaf q)) :
    Subsingleton (Sheaf.H ((W.hom)^*[AddCommGrpCat.{u + 1}].obj (Spec (.of K)).gmSheaf) q) := by
  have : AlgebraicGeometry.Etale W.hom := W.prop
  have : Finite W.left := finite_of_compact_of_discrete
  refine Etale.subsingleton_H_of_isClopen (pointOpens W) (fun _ ↦ isClosed_discrete _)
    (fun v w hvw ↦ Set.disjoint_singleton.2 hvw) (fun v ↦ ⟨v, rfl⟩) _ q fun v ↦ ?_
  set U := pointOpens W v
  -- the restriction of `𝔾ₘ` to the open point `U` is `𝔾ₘ`
  let e₁ : (U.ι)^*[AddCommGrpCat.{u + 1}].obj
      ((W.hom)^*[AddCommGrpCat.{u + 1}].obj (Spec (.of K)).gmSheaf) ≅ U.toScheme.gmSheaf :=
    ((U.ι)^*[AddCommGrpCat.{u + 1}]).mapIso (upperStarGmSheafIso W.hom) ≪≫
      upperStarGmSheafIso U.ι
  refine (Sheaf.functorH _ q).mapIso e₁ |>.addCommGroupIsoToAddEquiv.subsingleton_congr.2 ?_
  -- the open point is the spectrum of a finite separable extension of `K`
  have : Subsingleton U.toScheme := inferInstanceAs (Subsingleton ({v} : Set W.left))
  have : Nonempty U.toScheme := ⟨⟨v, rfl⟩⟩
  have : AlgebraicGeometry.Etale (U.ι ≫ W.hom) := inferInstance
  have : IsReduced ((Functor.fromPUnit (Spec (.of K))).obj W.right) :=
    inferInstanceAs (IsReduced (Spec (.of K)))
  have : IsReduced U.toScheme := isReduced_of_etale (U.ι ≫ W.hom)
  have := U.toScheme.isAffine_of_subsingleton
  let := (U.toScheme.isField_Γ_of_subsingleton).toField
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (U.toScheme.isoSpec.inv ≫ U.ι ≫ W.hom)
  have hφe : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale), hφ]
    infer_instance
  algebraize [φ.hom]
  have := h Γ(U.toScheme, ⊤)
  let j : Spec (.of Γ(U.toScheme, ⊤)) ⟶ U.toScheme := U.toScheme.isoSpec.inv
  have hj := Etale.injective_cohomologyMap_of_comp_eq_id j U.toScheme.isoSpec.hom
    U.toScheme.isoSpec.hom_inv_id U.toScheme.gmSheaf q
  have : Subsingleton (Sheaf.H ((j)^*[AddCommGrpCat.{u + 1}].obj U.toScheme.gmSheaf) q) :=
    ((Sheaf.functorH _ q).mapIso
      (upperStarGmSheafIso j)).addCommGroupIsoToAddEquiv.subsingleton_congr.2 this
  exact hj.subsingleton

end Scheme

namespace IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsCurve f] [IsIntegral C]

omit [IsAlgClosed k] in
include f in
/-- **Cohomology of `η_* N`.** Let `C` be an integral curve over an algebraically closed field,
with generic point `η : Spec k(C) ⟶ C`, and let `N` be a sheaf on `Spec k(C)` without higher
cohomology on affine étale `k(C)`-schemes. Then `Hᵖ(C, η_* N) = 0` for `p ≥ 1`: for `p = 1` the
edge map `H¹(C, η_* N) ⟶ H¹(k(C), N) = 0` is injective, and for `p ≥ 2` an injective envelope
`0 → N → I → N' → 0` stays exact after `η_*`
(`AlgebraicGeometry.IsCurve.epi_lowerStar_map_fromSpecFunctionField`), `η_* I` is injective, and
`N'` again has no higher cohomology on affine étale `k(C)`-schemes. -/
theorem subsingleton_sheafH_lowerStar_of_forall_isAffine (p : ℕ) :
    ∀ (N : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ W : (Spec C.functionField).Etale, IsAffine W.left → ∀ b : ℕ,
        Subsingleton (Sheaf.H ((W.hom)^*[AddCommGrpCat.{u + 1}].obj N) (b + 1))) →
      Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N)
        (p + 1)) := by
  induction p with
  | zero =>
    intro N h
    let T : (Spec C.functionField).Etale :=
      MorphismProperty.Over.mk ⊤ (𝟙 _) (inferInstance : AlgebraicGeometry.Etale (𝟙 _))
    have : IsAffine T.left := inferInstanceAs (IsAffine (Spec C.functionField))
    have : Subsingleton (Sheaf.H ((𝟙 (Spec C.functionField))^*[AddCommGrpCat.{u + 1}].obj N)
        1) :=
      h T this 0
    have : Subsingleton (Sheaf.H ((𝟭 _).obj N) 1) :=
      Sheaf.H.subsingleton_of_iso ((Etale.upperStarId AddCommGrpCat.{u + 1} _).app N).symm 1
    exact (Etale.injective_edgeMap_one C.fromSpecFunctionField N).subsingleton
  | succ p ih =>
    intro N h
    let ι := Injective.ι N
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    let P := (C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}]
    have hSP : (S.map P).ShortExact :=
      { exact := hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
        mono_f := inferInstanceAs (Mono (P.map S.f))
        epi_g := epi_lowerStar_map_fromSpecFunctionField f hS fun W hW ↦ h W hW 0 }
    have hN' : ∀ W : (Spec C.functionField).Etale, IsAffine W.left → ∀ b : ℕ,
        Subsingleton (Sheaf.H ((W.hom)^*[AddCommGrpCat.{u + 1}].obj S.X₃) (b + 1)) := by
      intro W hW b
      have : AlgebraicGeometry.Etale W.hom := W.prop
      let Q := (W.hom)^*[AddCommGrpCat.{u + 1}]
      have hSQ := hS.map_of_exact Q
      have : Injective (S.map Q).X₂ :=
        Etale.injective_upperStar_obj_of_etale_addCommGrp W.hom (Injective.under N)
      have : Subsingleton (Sheaf.H (S.map Q).X₂ (b + 1)) :=
        Abelian.Ext.subsingleton_of_injective _ _ b
      have : Subsingleton (Sheaf.H (S.map Q).X₁ (b + 1 + 1)) := h W hW (b + 1)
      exact Sheaf.H.subsingleton_X₃_of_shortExact hSQ (b + 1)
    have : Subsingleton (Sheaf.H (S.map P).X₃ (p + 1)) := ih S.X₃ hN'
    have : Injective (S.map P).X₂ :=
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        C.fromSpecFunctionField).map_injective _ inferInstance
    have : Subsingleton (Sheaf.H (S.map P).X₂ (p + 1 + 1)) :=
      Abelian.Ext.subsingleton_of_injective _ _ (p + 1)
    exact Sheaf.H.subsingleton_X₁_of_shortExact hSP (p + 1)

include f in
/-- **Higher cohomology of `𝔾ₘ` on an integral curve.** Let `C` be an integral curve over an
algebraically closed field `k`. Assume that `Hᵠ(Spec L, 𝔾ₘ) = 0` for `q ≥ 1` and every
algebraic extension `L` of `k(C)` (blueprint `lemma-cohomology-multiplicative-group`). Then
`Hᵠ(C_ét, 𝔾ₘ) = 0` for `q ≥ 2`.

By `AlgebraicGeometry.IsCurve.bijective_H_map_unit_fromSpecFunctionField`,
`Hᵠ(C, 𝔾ₘ) ≅ Hᵠ(C, η_* η^* 𝔾ₘ)` for `q ≥ 2`, and `η^* 𝔾ₘ = 𝔾ₘ`. An affine étale `k(C)`-scheme
is a finite disjoint union of spectra of finite separable extensions of `k(C)`, so `𝔾ₘ` has
no higher cohomology on it, and
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_lowerStar_of_forall_isAffine` applies. -/
theorem subsingleton_sheafH_gmSheaf_of_forall_field
    (hL : ∀ (L : Type u) [Field L] [Algebra C.functionField L]
      [Algebra.IsAlgebraic C.functionField L] (q : ℕ),
        Subsingleton (Sheaf.H (Spec (.of L)).gmSheaf (q + 1)))
    (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H C.gmSheaf q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hq
  have hinj := (bijective_H_map_unit_fromSpecFunctionField f C.gmSheaf n).injective
  have := C.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField
  let e := ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}]).mapIso
    (asIso (Scheme.upperStarGmSheafToGmSheaf C.fromSpecFunctionField))
  have hN (W : (Spec C.functionField).Etale) (hW : IsAffine W.left) (b : ℕ) :
      Subsingleton (Sheaf.H ((W.hom)^*[AddCommGrpCat.{u + 1}].obj
        (Spec C.functionField).gmSheaf) (b + 1)) :=
    Scheme.subsingleton_sheafH_upperStar_gmSheaf_of_isAffine (K := C.functionField) W (b + 1)
      fun L _ _ _ ↦ by
        have : Module.Finite C.functionField L :=
          Algebra.FormallyUnramified.finite_of_free _ _
        exact hL L b
  have := subsingleton_sheafH_lowerStar_of_forall_isAffine f (n + 1) _ hN
  have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField ⋙
      Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj C.gmSheaf) (n + 2)) :=
    ((Sheaf.functorH _ (n + 2)).mapIso e).addCommGroupIsoToAddEquiv.subsingleton_congr.2 this
  exact hinj.subsingleton

include f in
/-- **Higher cohomology of `𝔾ₘ` on an integral curve.** Let `C` be an integral curve over an
algebraically closed field `k`. Then `Hᵠ(C_ét, 𝔾ₘ) = 0` for `q ≥ 2`. This is
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_gmSheaf_of_forall_field` together with the
vanishing for algebraic extensions of `k(C)`
(`AlgebraicGeometry.IsCurve.subsingleton_sheafH_gmSheaf_of_isAlgebraic_functionField`). Neither
smoothness nor properness is needed.
(blueprint: `lemma-cohomology-multiplicative-group--2`, for integral curves) -/
theorem subsingleton_sheafH_gmSheaf_of_isIntegral (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H C.gmSheaf q) :=
  subsingleton_sheafH_gmSheaf_of_forall_field f
    (fun L _ _ _ q ↦ subsingleton_sheafH_gmSheaf_of_isAlgebraic_functionField f L (q + 1)
      (by omega)) q hq

end IsCurve

namespace IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Higher cohomology of `𝔾ₘ` on a smooth curve.** Let `C` be a smooth separated curve of
finite type over an algebraically closed field `k`. Then `Hᵠ(C_ét, 𝔾ₘ) = 0` for `q ≥ 2`.

The finitely many connected components of `C` are clopen, so it suffices to treat each of them
(`AlgebraicGeometry.Etale.subsingleton_H_of_isClopen`); a connected smooth curve is integral,
and `AlgebraicGeometry.IsCurve.subsingleton_sheafH_gmSheaf_of_isIntegral` applies.
(blueprint: `lemma-cohomology-multiplicative-group--2`) -/
theorem subsingleton_sheafH_gmSheaf_of_smooth (f : C ⟶ Spec (.of k)) [IsCurve f] [Smooth f]
    (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H C.gmSheaf q) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  -- the connected components of `C`, indexed by `ConnectedComponents C`
  choose x hx using _root_.ConnectedComponents.surjective_coe (α := C)
  let U (c : _root_.ConnectedComponents C) : C.Opens :=
    ⟨connectedComponent (x c), TopologicalSpace.NoetherianSpace.isOpen_connectedComponent _⟩
  have hU (y : C) : y ∈ U y := by
    change y ∈ connectedComponent (x y)
    rw [_root_.ConnectedComponents.coe_eq_coe.mp (hx y)]
    exact mem_connectedComponent
  refine Etale.subsingleton_H_of_isClopen U (fun c ↦ isClosed_connectedComponent)
    (fun c d hcd ↦ ?_) (fun y ↦ ⟨y, hU y⟩) _ q fun c ↦ ?_
  · refine Set.disjoint_left.mpr fun y (hyc : y ∈ connectedComponent (x c))
      (hyd : y ∈ connectedComponent (x d)) ↦ hcd ?_
    rw [← hx c, ← hx d, _root_.ConnectedComponents.coe_eq_coe,
      connectedComponent_eq hyc, connectedComponent_eq hyd]
  -- each connected component is a smooth connected curve, hence integral
  have : ConnectedSpace (U c) := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : IsCurve ((U c).ι ≫ f) :=
    { krullDim_le_one :=
        (topologicalKrullDim_subspace_le C (U c)).trans (IsCurve.krullDim_le_one f) }
  have : IsLocallyNoetherian (U c) := LocallyOfFiniteType.isLocallyNoetherian ((U c).ι ≫ f)
  have : IsRegular (U c) := IsRegular.of_smooth ((U c).ι ≫ f)
  have : IrreducibleSpace (U c) := IsRegular.irreducibleSpace (U c)
  have : IsReduced (U c) := isReduced_of_isReduced_stalk (U c)
  have : IsIntegral (U c) := isIntegral_of_irreducibleSpace_of_isReduced (U c)
  have := subsingleton_sheafH_gmSheaf_of_isIntegral ((U c).ι ≫ f) q hq
  exact ((Sheaf.functorH _ q).mapIso
    (Scheme.upperStarGmSheafIso (U c).ι)).addCommGroupIsoToAddEquiv.subsingleton_congr.2 this

end IsCurve

end AlgebraicGeometry
