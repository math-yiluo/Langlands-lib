/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.LinearAlgebra.SemilinearFrobenius

import WeilConjectures.AlgebraicGeometry.ArtinSchreierSequence
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierPullbackRows
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveScalarBaseChange
import WeilConjectures.AlgebraicGeometry.ArtinSchreier
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Compatible coherent Frobenius models for Artin--Schreier exact rows -/

@[expose] public section

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

/-- On a smooth proper connected curve over an algebraically closed field of characteristic `p`,
the Artin--Schreier map `a ↦ a ^ p - a` of the additive sheaf is surjective on global sections. -/
theorem surjective_sheafH_zero_artinSchreier
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [Smooth f] [ConnectedSpace C] [IsProper f]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (wp : G ⟶ G)
    (hwp : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x) :
    Function.Surjective (Sheaf.H.map wp 0) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IsReduced C := isReduced_of_isReduced_stalk C
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper (C ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  let ρ : k →+* Γ(C, ⊤) := Scheme.globalSectionsRingHom k
  have hρ : Function.Surjective ρ :=
    Scheme.GlobalSectionsBijective.bijective_globalSectionsRingHom.surjective
  have hs : Function.Surjective (fun x : Γ(C, ⊤) ↦ x ^ p - x) := by
    intro y
    obtain ⟨c, rfl⟩ := hρ y
    obtain ⟨d, hd⟩ := (IsAlgClosed.artinSchreier_surjective_and_kernel (k := k) p).1 c
    refine ⟨ρ d, ?_⟩
    change ρ d ^ p - ρ d = ρ c
    change d ^ p - d = c at hd
    rw [← map_pow, ← map_sub, hd]
  let U : C.Etaleᵒᵖ := .op (Scheme.Etale.mk (𝟙 C))
  have hw : Function.Surjective (wp.hom.app U) := by
    intro y
    obtain ⟨x, hx⟩ := hs (a U y)
    refine ⟨(a U).symm x, (a U).injective ?_⟩
    rw [hwp, AddEquiv.apply_symm_apply]
    exact hx
  have ht : Limits.IsTerminal (Scheme.Etale.mk (𝟙 C)) :=
    MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale C
  intro y
  obtain ⟨x, hx⟩ := hw (Sheaf.H.equiv₀ G ht y)
  refine ⟨(Sheaf.H.equiv₀ G ht).symm x, (Sheaf.H.equiv₀ G ht).injective ?_⟩
  rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply]
  exact hx

/-- A `k`-module structure on `H¹` of the additive sheaf `G`, induced by multiplication on sections,
turns the map induced by `a ↦ a ^ p` into a `p`-linear endomorphism `F`; the Artin--Schreier map
`wp` then acts on `H¹` as `F - 1`. -/
theorem exists_frobenius_model
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (wp : G ⟶ G)
    (hwp : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x)
    (W : Type (u + 1)) [AddCommGroup W] [Module k W]
    (b : Sheaf.H G 1 ≃+ W)
    (hscalar : ∀ c : k, ∃ μ : G ⟶ G,
      (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
          (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
        a U (μ.hom.app U x) = a U x * ρ c) ∧
      ∀ x : Sheaf.H G 1, b (Sheaf.H.map μ 1 x) = c • b x) :
    ∃ F : W →ₛₗ[frobenius k p] W,
      ∀ x, b (Sheaf.H.map wp 1 x) = F (b x) - b x := by
  let φ : G ⟶ G := wp + 𝟙 G
  have hφ (U : C.Etaleᵒᵖ) (x : G.obj.obj U) :
      a U (φ.hom.app U x) = (a U x) ^ p := by
    change a U (wp.hom.app U x + x) = _
    rw [map_add, hwp, sub_add_cancel]
  let ψ : W →+ W := b.toAddMonoidHom.comp
    ((Sheaf.H.map φ 1).comp b.symm.toAddMonoidHom)
  have hψ (x : Sheaf.H G 1) : ψ (b x) = b (Sheaf.H.map φ 1 x) := by
    simp [ψ]
  have hsemi (c : k) (x : W) : ψ (c • x) = c ^ p • ψ x := by
    obtain ⟨y, rfl⟩ := b.surjective x
    obtain ⟨μ, hμ, hμmap⟩ := hscalar c
    obtain ⟨ν, hν, hνmap⟩ := hscalar (c ^ p)
    have hcomm : μ ≫ φ = φ ≫ ν := by
      apply Sheaf.hom_ext
      ext U z
      apply (a U).injective
      change a U (φ.hom.app U (μ.hom.app U z)) =
        a U (ν.hom.app U (φ.hom.app U z))
      rw [hφ, hμ, hν, hφ]
      let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
      change (a U z * ρ c) ^ p = (a U z) ^ p * ρ (c ^ p)
      rw [mul_pow, map_pow]
    rw [← hμmap, hψ, ← Sheaf.H.map_comp_apply, hcomm, Sheaf.H.map_comp_apply,
      hνmap, hψ]
  let F : W →ₛₗ[frobenius k p] W :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := fun c x ↦ by simpa only [frobenius_def] using hsemi c x }
  refine ⟨F, fun x ↦ ?_⟩
  change b (Sheaf.H.map wp 1 x) = ψ (b x) - b x
  rw [hψ, Sheaf.H.map_add_apply, Sheaf.H.map_id_apply, map_add, add_sub_cancel_right]

/-- Coherent Frobenius models and compatible Artin--Schreier exact rows under base change.
Source: Stacks Project, Tag 0A3P, proof, and Tag 02KH, flat coherent base change.
(blueprint: lem-pbc-artin-schreier-frobenius-exact-rows)

Proof: Take G and G' to be the universe-lifted additive structure sheaves on C and C'.
Use the Artin--Schreier sequence on each scheme, transporting the constant term on C'
through the inverse-image constant-sheaf isomorphism. The maps i and i' send a locally
constant prime-field section to that section times 1; wp and wp' act by x^p-x.
The structure-ring pullback gives q from the inverse image of G to G', and the formula
for constant sections gives the asserted square. The degree-zero maps are onto:
smoothness implies reducedness, and proper connectedness over an algebraically closed
field identifies the global sections with the field; x^p-x is onto that field. The
base-changed curve is again smooth, proper and connected, so the same argument applies.
Take V to be coherent H¹(C,O_C), with its actual scalar action. Proper coherent finiteness
makes it finite-dimensional. The etale/Zariski comparison gives b, while flat coherent
base change and the comparison on C' give b'. The sectionwise p-th power endomorphisms
induce semilinear F and F', since (cx)^p=c^p x^p. Naturality of powers under structure-ring
pullback gives the identity on pure tensors. Additivity of cohomology gives the formulas
for wp and wp'. The canonical flat base-change map sends a cohomology class v to 1 tensor v;
use the same affine-cover Cech comparisons on both schemes to obtain the last identity.
These comparisons commute with sectionwise powers even though Frobenius is not O-linear.
If C has dimension zero, smooth proper connected C is Spec k and coherent H¹ vanishes;
use the zero vector space, with the same degree-zero and exact-row arguments. This
statement supplies no degree-one kernel equivalence and uses no fixed-point invariance. -/
theorem exists_artinSchreier_frobenius_exact_rows
    {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f] [Smooth f] [ConnectedSpace C] [IsProper f]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :
    ∃ (V : ModuleCat.{u + 1} k) (_ : FiniteDimensional k V)
      (F : V →ₛₗ[frobenius k p] V)
      (F' : (k' ⊗[k] V) →ₛₗ[frobenius k' p] (k' ⊗[k] V)),
      (∀ v : V, F' (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] F v) ∧
      ∃ (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
        (G' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1})
        (i : C.constantZMod p ⟶ G)
        (i' : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj (C.constantZMod p) ⟶ G')
        (wp : G ⟶ G) (wp' : G' ⟶ G')
        (z : i ≫ wp = 0) (z' : i' ≫ wp' = 0)
        (q : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj G ⟶ G')
        (b : Sheaf.H G 1 ≃+ V) (b' : Sheaf.H G' 1 ≃+ (k' ⊗[k] V)),
        (ShortComplex.mk i wp z).ShortExact ∧
        (ShortComplex.mk i' wp' z').ShortExact ∧
        Function.Surjective (Sheaf.H.map wp 0) ∧
        Function.Surjective (Sheaf.H.map wp' 0) ∧
        (Etale.upperStar AddCommGrpCat.{u + 1} ι').map i ≫ q = i' ∧
        (∀ x, b (Sheaf.H.map wp 1 x) = F (b x) - b x) ∧
        (∀ x, b' (Sheaf.H.map wp' 1 x) = F' (b' x) - b' x) ∧
        ∀ x, b' (Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x)) =
          1 ⊗ₜ[k] b x := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let bk := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hcurve := (baseChange_curve (k' := k') f).1
  have : IsCurve (Limits.pullback.snd f bk) := hcurve
  have hdim : topologicalKrullDim C' ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso h.isoPullback).isHomeomorph]
    exact IsCurve.krullDim_le_one (f := Limits.pullback.snd f bk)
  have : IsSeparated f' := IsSeparated.isStableUnderBaseChange.of_isPullback h inferInstance
  have : LocallyOfFiniteType f' :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback h inferInstance
  have : QuasiCompact f' := quasiCompact_isStableUnderBaseChange.of_isPullback h inferInstance
  have : IsCurve f' := { krullDim_le_one := hdim }
  obtain ⟨G, -, a, wp, i, z, ha, hwp, hi, hs⟩ := artinSchreier_shortExact f p hp0
  obtain ⟨G', -, a', wp', i0, z0, ha', hwp', hi0, hs0⟩ := artinSchreier_shortExact f' p hp0
  obtain ⟨q, i', z', hs', hiq, hwpq, hq⟩ :=
    exists_artinSchreier_pullback_rows ι' p G G' a a' ha ha' wp wp' hwp hwp'
      i i0 hi hi0 z0 hs0
  obtain ⟨V, hfinite, b, b', hscalar, hscalar', hbc⟩ :=
    exists_additive_scalar_base_change f h G G' a a' ha ha' q hq
  obtain ⟨F, hF⟩ := exists_frobenius_model f p G a wp hwp V b hscalar
  obtain ⟨F', hF'⟩ := exists_frobenius_model f' p G' a' wp' hwp' (k' ⊗[k] V) b' hscalar'
  have hcompat (x : Sheaf.H G 1) :
      Sheaf.H.map wp' 1 (Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x)) =
        Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 (Sheaf.H.map wp 1 x)) := by
    rw [Etale.cohomologyMap_map, ← Sheaf.H.map_comp_apply, ← hwpq,
      Sheaf.H.map_comp_apply]
  have hFF' (v : V) : F' (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] F v := by
    obtain ⟨x, rfl⟩ := b.surjective v
    have he := hF' (Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x))
    rw [hcompat, hbc, hbc, hF, TensorProduct.tmul_sub] at he
    exact (sub_left_inj).mp he.symm
  have : Smooth f' := MorphismProperty.of_isPullback h inferInstance
  have : IsProper f' := MorphismProperty.of_isPullback h inferInstance
  have : GeometricallyConnected f :=
    GeometricallyConnected.of_connectedSpace_of_isSepClosed f
  have : GeometricallyConnected f' := MorphismProperty.of_isPullback h inferInstance
  have : ConnectedSpace C' := GeometricallyConnected.connectedSpace_of_subsingleton f'
  exact ⟨V, hfinite, F, F', hFF', G, G', i, i', wp, wp', z, z', q, b, b',
    hs, hs', surjective_sheafH_zero_artinSchreier f p G a wp hwp,
    surjective_sheafH_zero_artinSchreier f' p G' a' wp' hwp', hiq, hF, hF', hbc⟩

end AlgebraicGeometry.IsCurve
