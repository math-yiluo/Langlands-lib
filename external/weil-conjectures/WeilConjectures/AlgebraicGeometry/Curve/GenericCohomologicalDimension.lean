/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.FunctionFieldCohomology
public import WeilConjectures.AlgebraicGeometry.Curve.GenericRestriction
public import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFiniteness
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMap

/-!
# Cohomological dimension of a smooth curve, at the generic point

Let `C` be a smooth integral curve over an algebraically closed field `k`, with generic point
`η : Spec k(C) ⟶ C`. We show that `Hᵠ(C, F) = 0` for every torsion étale sheaf `F` on `C` and
`q ≥ 3` (blueprint `theorem-cohomology-curves--1`), following the blueprint argument at the
generic point, without spectral sequences:

* by the generic replacement `Hᵠ(C, F) ≅ Hᵠ(C, η_* η^* F)` for `q ≥ 2`
  (`AlgebraicGeometry.IsCurve.bijective_H_map_unit_fromSpecFunctionField`, blueprint
  `theorem-cohomology-curves`) it suffices to treat `η_* M`;
* every affine étale `k(C)`-scheme `W` is finite over `k(C)`, so its cohomology is that of
  `Spec k(C)` with coefficients in a pushforward, and vanishes in degrees `≥ 2` for torsion
  coefficients since `k(C)` has cohomological dimension at most one
  (`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_isAlgebraic_functionField`, blueprint
  `theorem-cohomology-curves`); this is the vanishing of `Rᵇη_* M` for `b ≥ 2`;
* dimension shifting along acyclic envelopes `0 → M → J → N → 0` of sheaves killed by `n`
  (`AlgebraicGeometry.Etale.exists_mono_acyclic_of_nsmul_eq_zero`) then replaces the Grothendieck
  spectral sequence: if `H¹(W, M) = 0` on all affine étale `k(C)`-schemes `W` then
  `0 → η_* M → η_* J → η_* N → 0` is exact, and the edge map `H¹(C, η_* M) ⟶ H¹(k(C), M)` is
  injective, which gives `Hᵖ(C, η_* M) = 0` for `p ≥ 1`
  (`AlgebraicGeometry.IsCurve.subsingleton_sheafH_lowerStar_fromSpecFunctionField`);
* for a general `M` killed by `n`, the cokernel `Q` of `η_* M ⟶ η_* J` has generic restriction
  `η^* Q ≅ N` (`AlgebraicGeometry.Scheme.isIso_counit_app_fromSpecFunctionField`), so the generic
  replacement identifies `Hᵖ(C, Q)` with `Hᵖ(C, η_* N)` for `p ≥ 2`, and `N` satisfies the
  hypothesis above.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_etale_functionField`: affine étale
  `k(C)`-schemes have cohomological dimension at most one for sheaves killed by an integer.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le_of_smooth`: `Hᵠ(C, F) = 0` for
  `q ≥ 3`, `C` a smooth integral curve and `F` a torsion sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Etale

namespace IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsCurve f] [IsIntegral C]

/-- The pushforward of a sheaf killed by `n` is killed by `n`. -/
lemma nsmul_id_lowerStar_eq_zero {X Y : Scheme.{u}} (g : X ⟶ Y)
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {n : ℕ} (hG : n • 𝟙 G = 0) :
    n • 𝟙 ((g)_*[AddCommGrpCat.{u + 1}].obj G) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hG, Functor.map_zero]

/-- The pullback of a sheaf killed by `n` is killed by `n`. -/
lemma nsmul_id_upperStar_eq_zero {X Y : Scheme.{u}} (g : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} {n : ℕ} (hG : n • 𝟙 G = 0) :
    n • 𝟙 ((g)^*[AddCommGrpCat.{u + 1}].obj G) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hG, Functor.map_zero]

/-- An affine étale scheme over a field is finite over it. -/
lemma isFinite_of_etale_of_isAffine {K : Type u} [Field K] {W : Scheme.{u}}
    (e : W ⟶ Spec (.of K)) [AlgebraicGeometry.Etale e] [IsAffine W] : IsFinite e := by
  by_cases hW : Nonempty W
  · obtain ⟨O, hO, -, hfin⟩ := e.exists_isFinite_preimage_of_etale
    have hOtop : O = ⊤ := by
      obtain ⟨x, hx⟩ := hO
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact Subsingleton.elim x y ▸ hx
    exact IsZariskiLocalAtTarget.of_iSup_eq_top (fun _ : Unit ↦ O) (by simp [hOtop])
      fun _ ↦ hfin
  · have : IsEmpty W := not_nonempty_iff.mp hW
    refine (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).2 ⟨inferInstance, ?_⟩
    let := (e.appTop).hom.toAlgebra
    exact Module.Finite.of_finite

include f in
/-- **Affine étale schemes over the function field have cohomological dimension at most one.**
Let `C` be an integral curve over an algebraically closed field and `W` an affine étale
`k(C)`-scheme. Then `Hᵠ(W, G) = 0` for `q ≥ 2` and every sheaf `G` on `W` killed by some `n > 0`:
`W` is finite over `k(C)`, so `Hᵠ(W, G) = Hᵠ(k(C), e_* G)`, which vanishes as `k(C)` has
cohomological dimension at most one. (blueprint: `theorem-cohomology-curves`) -/
theorem subsingleton_sheafH_of_etale_functionField {W : Scheme.{u}}
    (e : W ⟶ Spec C.functionField) [AlgebraicGeometry.Etale e] [IsAffine W] {n : ℕ}
    (hn : 0 < n) (G : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : n • 𝟙 G = 0)
    {q : ℕ} (hq : 2 ≤ q) : Subsingleton (Sheaf.H G q) := by
  have : IsFinite e := isFinite_of_etale_of_isAffine (K := C.functionField) e
  have : Subsingleton (Sheaf.H ((e)_*[AddCommGrpCat.{u + 1}].obj G) q) :=
    subsingleton_sheafH_of_isAlgebraic_functionField f C.functionField _
      (Scheme.isTorsion_of_nsmul_id_eq_zero hn (nsmul_id_lowerStar_eq_zero e hG)) hq
  exact (bijective_edgeMap_of_isFinite e G q).surjective.subsingleton

omit [IsAlgClosed k] in
include f in
/-- The generic fibre `V ×_C Spec k(C)` of an affine étale `C`-scheme `V` is affine: the generic
point `Spec k(C) ⟶ C` is an affine morphism, `C` being separated. -/
lemma isAffine_generic_etale_obj (V : C.Etale) [IsAffine V.left] :
    IsAffine ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
      C.fromSpecFunctionField).obj V).left := by
  have : IsAffineHom C.fromSpecFunctionField :=
    MorphismProperty.HasOfPostcompProperty.of_postcomp (W := @IsAffineHom)
      (W' := @IsSeparated) C.fromSpecFunctionField f inferInstance inferInstance
  have : IsAffine ((𝟭 Scheme.{u}).obj V.left) := ‹IsAffine V.left›
  change IsAffine (pullback V.hom C.fromSpecFunctionField)
  infer_instance

omit [IsAlgClosed k] in
include f in
/-- **Vanishing of `R¹η_*`, locally.** Let `0 → M → J → N → 0` be a short exact sequence of
sheaves on `Spec k(C)` such that `H¹(W, M) = 0` for every affine étale `k(C)`-scheme `W`. Then
`η_* J ⟶ η_* N` is an epimorphism: over an affine étale `C`-scheme `V` the generic fibre
`V ×_C Spec k(C)` is affine, so sections of `N` over it lift to `J`. -/
theorem epi_lowerStar_map_fromSpecFunctionField
    {S : ShortComplex (Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact)
    (h : ∀ W : (Spec C.functionField).Etale, IsAffine W.left →
      Subsingleton (Sheaf.H ((W.hom)^*[AddCommGrpCat.{u + 1}].obj S.X₁) 1)) :
    Epi ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].map S.g) := by
  have : Sheaf.IsLocallySurjective
      ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].map S.g) := by
    refine ⟨fun {V} s ↦ (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_⟩
    obtain ⟨A, hA, hxA, -⟩ : ∃ A : V.left.Opens, A ∈ V.left.affineOpens ∧ x ∈ A ∧ A ≤ ⊤ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1
      V.left.isBasis_affineOpens) (TopologicalSpace.Opens.mem_top x)
    have : IsAffine A := hA
    let VA : C.Etale := MorphismProperty.Over.mk ⊤ (A.ι ≫ V.hom)
      (MorphismProperty.comp_mem _ _ _ inferInstance V.prop)
    let g : VA ⟶ V := MorphismProperty.Over.homMk A.ι rfl trivial
    refine ⟨VA, g, ?_, ⟨x, hxA⟩, rfl⟩
    let W := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
      C.fromSpecFunctionField).obj VA
    have : IsAffine VA.left := ‹IsAffine A›
    have := h W (isAffine_generic_etale_obj f VA)
    obtain ⟨t, ht⟩ := Etale.surjective_app_of_subsingleton_H_one hS W
      (((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj S.X₃).obj.map g.op s)
    exact ⟨t, ht⟩
  exact Sheaf.epi_of_isLocallySurjective _

include f in
/-- The cokernel `N` of an acyclic envelope `M ⟶ J` of a sheaf `M` on `Spec k(C)` killed by `n`
satisfies `H¹(W, N) = 0` for every affine étale `k(C)`-scheme `W`, as `H¹(W, N) ≅ H²(W, M)`. -/
lemma subsingleton_sheafH_one_cokernel {n : ℕ} (hn : 0 < n)
    {S : ShortComplex (Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (hM : n • 𝟙 S.X₁ = 0)
    (hJ : ∀ {W : Scheme.{u}} (w : W ⟶ Spec C.functionField) [AlgebraicGeometry.Etale w] q,
      Subsingleton (Sheaf.H ((w)^*[AddCommGrpCat.{u + 1}].obj S.X₂) (q + 1)))
    (W : (Spec C.functionField).Etale) (hW : IsAffine W.left) :
    Subsingleton (Sheaf.H ((W.hom)^*[AddCommGrpCat.{u + 1}].obj S.X₃) 1) := by
  have : AlgebraicGeometry.Etale W.hom := W.prop
  have : IsAffine ((𝟭 Scheme.{u}).obj W.left) := hW
  let P := (W.hom)^*[AddCommGrpCat.{u + 1}]
  have hS' := hS.map_of_exact P
  have : Subsingleton (Sheaf.H (S.map P).X₂ 1) := hJ W.hom 0
  have : Subsingleton (Sheaf.H (S.map P).X₁ 2) :=
    subsingleton_sheafH_of_etale_functionField f W.hom hn _
      (nsmul_id_upperStar_eq_zero W.hom hM) le_rfl
  exact Sheaf.H.subsingleton_X₃_of_shortExact hS' 1

include f in
/-- **Cohomology of `η_* N`.** Let `N` be a sheaf on `Spec k(C)` killed by some `n > 0` with
`H¹(W, N) = 0` for every affine étale `k(C)`-scheme `W`. Then `Hᵖ(C, η_* N) = 0` for `p ≥ 1`:
for `p = 1` the edge map `H¹(C, η_* N) ⟶ H¹(k(C), N) = 0` is injective, and for `p ≥ 2`
an acyclic envelope `0 → N → J → N' → 0` gives a short exact sequence
`0 → η_* N → η_* J → η_* N' → 0`
(`AlgebraicGeometry.IsCurve.epi_lowerStar_map_fromSpecFunctionField`) with `η_* J` acyclic and
`N'` again of this kind. This replaces the Grothendieck spectral sequence of the blueprint. -/
theorem subsingleton_sheafH_lowerStar_fromSpecFunctionField (p : ℕ) :
    ∀ (N : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ),
      0 < n → n • 𝟙 N = 0 →
      (∀ W : (Spec C.functionField).Etale, IsAffine W.left →
        Subsingleton (Sheaf.H ((W.hom)^*[AddCommGrpCat.{u + 1}].obj N) 1)) →
      Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N)
        (p + 1)) := by
  induction p with
  | zero =>
    intro N n hn hN h
    let T : (Spec C.functionField).Etale :=
      MorphismProperty.Over.mk ⊤ (𝟙 _) (inferInstance : AlgebraicGeometry.Etale (𝟙 _))
    have : IsAffine T.left := inferInstanceAs (IsAffine (Spec C.functionField))
    have : Subsingleton (Sheaf.H ((𝟙 (Spec C.functionField))^*[AddCommGrpCat.{u + 1}].obj N) 1) :=
      h T this
    have : Subsingleton (Sheaf.H ((𝟭 _).obj N) 1) :=
      Sheaf.H.subsingleton_of_iso ((Etale.upperStarId AddCommGrpCat.{u + 1} _).app N).symm 1
    exact (injective_edgeMap_one C.fromSpecFunctionField N).subsingleton
  | succ p ih =>
    intro N n hn hN h
    obtain ⟨J, ι, hι, hJn, -, hJ1, hJ2⟩ :=
      Etale.exists_mono_acyclic_of_nsmul_eq_zero _ hn.ne' N hN
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) hι inferInstance
    let P := (C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}]
    have hSP : (S.map P).ShortExact :=
      { exact := hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
        mono_f := inferInstanceAs (Mono (P.map S.f))
        epi_g := epi_lowerStar_map_fromSpecFunctionField f hS h }
    have : Subsingleton (Sheaf.H (S.map P).X₃ (p + 1)) :=
      ih S.X₃ n hn (Etale.nsmul_id_cokernel_eq_zero ι hJn)
        (subsingleton_sheafH_one_cokernel f hn hS hN (fun w _ q ↦ hJ2 w q))
    have : Subsingleton (Sheaf.H (S.map P).X₂ (p + 1 + 1)) := hJ1 C.fromSpecFunctionField _
    exact Sheaf.H.subsingleton_X₁_of_shortExact hSP (p + 1)

include f in
/-- `Hᵠ(C, F) = 0` for `q ≥ 3` and a sheaf `F` killed by some `n > 0` on an integral curve. -/
theorem subsingleton_sheafH_of_three_le_of_nsmul_eq_zero
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) {n : ℕ} (hn : 0 < n)
    (hF : n • 𝟙 F = 0) (q : ℕ) : Subsingleton (Sheaf.H F (q + 3)) := by
  let η := C.fromSpecFunctionField
  let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} η
  let P := (η)_*[AddCommGrpCat.{u + 1}]
  let M := (η)^*[AddCommGrpCat.{u + 1}].obj F
  have hM : n • 𝟙 M = 0 := nsmul_id_upperStar_eq_zero η hF
  -- generic replacement: `Hᵠ(C, F) ≅ Hᵠ(C, η_* M)`
  have : QuasiSeparatedSpace C := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  have := Scheme.isIso_counit_app_fromSpecFunctionField (X := C) M
  suffices hs : Subsingleton (Sheaf.H (P.obj M) (q + 3)) by
    have : Subsingleton (Sheaf.H (((η)^*[AddCommGrpCat.{u + 1}] ⋙ P).obj F) (q + 1 + 2)) := hs
    exact (bijective_H_map_unit_fromSpecFunctionField f F (q + 1)).injective.subsingleton
  -- an acyclic envelope `0 → M → J → N → 0`
  obtain ⟨J, ι, hι, hJn, -, hJ1, hJ2⟩ := Etale.exists_mono_acyclic_of_nsmul_eq_zero _ hn.ne' M hM
  have := Scheme.isIso_counit_app_fromSpecFunctionField (X := C) J
  let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) hι inferInstance
  -- the cokernel `Q` of `η_* M ⟶ η_* J`
  let Sa := ShortComplex.mk (P.map ι) (cokernel.π (P.map ι)) (cokernel.condition _)
  have hSa : Sa.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _)
      (inferInstanceAs (Mono (P.map ι))) inferInstance
  -- its generic restriction is `N`
  have e : (η)^*[AddCommGrpCat.{u + 1}].obj (cokernel (P.map ι)) ≅ S.X₃ :=
    PreservesCokernel.iso _ _ ≪≫ cokernel.mapIso _ ι
      (asIso (adj.counit.app M)) (asIso (adj.counit.app J)) (adj.counit.naturality ι)
  -- `Hᵠ⁺²(C, Q) ≅ Hᵠ⁺²(C, η_* η^* Q) ≅ Hᵠ⁺²(C, η_* N) = 0`
  have hN : Subsingleton (Sheaf.H (P.obj S.X₃) (q + 1 + 1)) :=
    subsingleton_sheafH_lowerStar_fromSpecFunctionField f (q + 1) S.X₃ n hn
      (Etale.nsmul_id_cokernel_eq_zero ι hJn)
      (subsingleton_sheafH_one_cokernel f hn hS hM (fun w _ q ↦ hJ2 w q))
  have : Subsingleton (Sheaf.H Sa.X₃ (q + 2)) := by
    have : Subsingleton (Sheaf.H (P.obj ((η)^*[AddCommGrpCat.{u + 1}].obj
        (cokernel (P.map ι)))) (q + 2)) :=
      Sheaf.H.subsingleton_of_iso (P.mapIso e) _
    have : Subsingleton (Sheaf.H (((η)^*[AddCommGrpCat.{u + 1}] ⋙ P).obj
        (cokernel (P.map ι))) (q + 2)) := this
    exact (bijective_H_map_unit_fromSpecFunctionField f _ q).injective.subsingleton
  have : Subsingleton (Sheaf.H Sa.X₂ (q + 2 + 1)) := hJ1 η _
  exact Sheaf.H.subsingleton_X₁_of_shortExact hSa (q + 2)

include f in
/-- **Cohomological dimension of an integral curve.** Let `C` be an integral curve over an
algebraically closed field `k`. Then `Hᵠ(C, F) = 0` for every torsion étale sheaf `F` on `C` and
`q ≥ 3`. Smoothness is not needed: the argument at the generic point
(`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le_of_nsmul_eq_zero`) only uses the
generic replacement, the vanishing of `Rᵇη_*` for `b ≥ 2` and the cohomological dimension of
`k(C)`; torsion sheaves are filtered unions of sheaves killed by an integer.
(blueprint: `theorem-cohomology-curves--1`) -/
theorem subsingleton_sheafH_of_three_le_of_isIntegral
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 3 ≤ q) : Subsingleton (Sheaf.H F q) := by
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace C := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hq
  exact Etale.subsingleton_H_of_isTorsion hF _ fun G n hn hG ↦
    subsingleton_sheafH_of_three_le_of_nsmul_eq_zero f G hn hG q

end IsCurve

end AlgebraicGeometry
