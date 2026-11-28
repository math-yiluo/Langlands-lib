import Langlands.Cohomology.SylowDetectionProof
import Langlands.GroupScheme.GaloisCocycleScalarExtension
import Langlands.GroupScheme.Torus.InducedWeilDecompositionProof
import Langlands.GroupScheme.Torus.LatticeGaloisScalarExtension
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.GroupScheme.Torus.WeilRestrictionSemilocalCocycle
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Finite Galois torus cocycles with a permutation subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

namespace GaloisCocycle

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

private theorem value_map_nsmul (ξ : Cocycle T.toGrp (cover F E))
    (n : ℕ) (σ : E ≃ₐ[F] E) :
    value (ξ.map (CommGroupScheme.groupHom (n • 𝟙 T))) σ = value ξ σ ^ n := by
  change value ξ σ ≫ ((𝟙 T.toGrp : T.toGrp ⟶ T.toGrp) ^ n).hom.hom = _
  rw [Grp.Hom.hom_pow, Mon.Hom.hom_pow, MonObj.comp_pow]
  rfl

variable [FiniteDimensional F E] [IsGalois F E]

/-- A coboundary on a subgroup of the cover's Galois group kills the original
commutative cocycle by any multiple of the subgroup index. -/
theorem isTrivial_nsmul_of_restricted_coboundary
    (ξ : Cocycle T.toGrp (cover F E)) (H : Subgroup (E ≃ₐ[F] E)) {n : ℕ}
    (hn : H.index ∣ n) (f : GroupScheme.affinePoints T.toGrp (CommAlgCat.of F E))
    (hf : ∀ σ ∈ H, value ξ σ = f * (GaloisPoint.conjugate F E T.toGrp σ f)⁻¹) :
    (ξ.map (CommGroupScheme.groupHom (n • 𝟙 T))).IsTrivial := by
  let A := pointRepresentation (G := T.toGrp) (k := F) (L := E)
  let c := additiveCocycle ξ
  have hres : groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 1
      (groupCohomology.H1π A c) = 0 := by
    rw [groupCohomology.H1π_comp_map_apply, groupCohomology.H1π_eq_zero_iff]
    let inversePoint : GroupScheme.affinePoints T.toGrp (CommAlgCat.of F E) := f⁻¹
    refine ⟨Additive.ofMul inversePoint, ?_⟩
    funext σ
    rw [groupCohomology.d₀₁_hom_apply]
    change Additive.ofMul (GaloisPoint.conjugate F E T.toGrp σ.val (f⁻¹) * (f⁻¹)⁻¹) =
      Additive.ofMul (value ξ σ.val)
    rw [map_inv, inv_inv, mul_comm, hf σ.val σ.property]
  have hz := Langlands.Cohomology.index_nsmul_eq_zero_of_restriction_eq_zero A H 1
    (groupCohomology.H1π A c) hres
  have hmul : n • groupCohomology.H1π A c = 0 := by
    obtain ⟨m, rfl⟩ := hn
    rw [mul_nsmul, hz, nsmul_zero]
  let ζ := ξ.map (CommGroupScheme.groupHom (n • 𝟙 T))
  have hc : additiveCocycle ζ = n • c := by
    apply Subtype.ext
    funext σ
    change Additive.ofMul (value ζ σ) = Additive.ofMul (value ξ σ ^ n)
    exact congrArg Additive.ofMul (value_map_nsmul T ξ n σ)
  have hζ : groupCohomology.H1π A (additiveCocycle ζ) = 0 := by
    rw [hc, map_nsmul]
    exact hmul
  obtain ⟨x, hx⟩ := (groupCohomology.H1π_eq_zero_iff (additiveCocycle ζ)).mp hζ
  let z : GroupScheme.affinePoints T.toGrp (CommAlgCat.of F E) :=
    (x : Additive (GroupScheme.affinePoints T.toGrp (CommAlgCat.of F E))).toMul
  refine (isTrivial_iff ζ).mpr ⟨z⁻¹, fun σ => ?_⟩
  have hs := congrFun hx σ
  rw [groupCohomology.d₀₁_hom_apply] at hs
  have hs' : GaloisPoint.conjugate F E T.toGrp σ z * z⁻¹ = value ζ σ :=
    congrArg (fun y : Additive (GroupScheme.affinePoints T.toGrp (CommAlgCat.of F E)) => y.toMul) hs
  rw [← hs', map_inv, inv_inv, mul_comm]

omit [FiniteDimensional F E] [IsGalois F E] in
private theorem relativeExtend_self (p : GroupScheme.affinePoints T.toGrp (CommAlgCat.of F E)) :
    GaloisPoint.relativeExtend F E E T.toGrp p = p := by
  change coverMap F E E ≫ p = p
  have he : coverMap F E E = 𝟙 _ := by
    unfold coverMap
    rw [show IsScalarTower.toAlgHom F E E = AlgHom.id F E from AlgHom.ext fun _ => rfl]
    exact CategoryTheory.Functor.map_id _ _
  rw [he, Category.id_comp]

end GaloisCocycle

/-- A splitting cover whose character lattice has a basis permuted by a
subgroup gives cocycle annihilation by any multiple of the subgroup index. -/
def FiniteGaloisTorusPermutationIndexStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (T : CommGroupScheme (Spec (CommRingCat.of F))),
    IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap F E)).obj T.toGrp) →
    ∀ (H : Subgroup (E ≃ₐ[F] E)) (I : Type u)
      (B : Module.Basis I ℤ (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T))),
      (∀ σ ∈ H, ∀ i, ∃ j, characterLattice.galoisRepresentation F E T σ (B i) = B j) →
      ∀ (n : ℕ), H.index ∣ n → ∀ ξ : Cocycle T.toGrp (GaloisCocycle.cover F E),
        (ξ.map (CommGroupScheme.groupHom (n • 𝟙 T))).IsTrivial

open GaloisCocycle in
theorem finiteGaloisTorusPermutationIndex : FiniteGaloisTorusPermutationIndexStatement.{u} := by
  classical
  intro F E _ _ _ _ _ T hT H I B hB n hn ξ
  let K := IntermediateField.fixedField H
  let TK := (CommGroupScheme.baseChange (algebraBaseMap F K)).obj T
  have hc : algebraBaseMap K E ≫ algebraBaseMap F K = algebraBaseMap F E := by
    simp only [algebraBaseMap, ← Spec.map_comp]
    congr 1
  have hTK : IsSplitTorus (GaloisPointComparison.baseChanged K E TK.toGrp) :=
    (IsSplitTorus.baseChange_fieldTower_iff F K E T.toGrp).mp hT
  let eH : H ≃* (E ≃ₐ[K] E) := IntermediateField.subgroupEquivAlgEquiv H
  have heH (σ : E ≃ₐ[K] E) : σ.restrictScalars F = (eH.symm σ).val :=
    AlgEquiv.ext fun _ => rfl
  let a := characterLattice.scalarExtensionGaloisEquiv hc T
  have hInd : IsInducedTorus TK := by
    refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
      hTK, I, B.map a.toLinearEquiv, fun σ i => ?_⟩
    obtain ⟨j, hj⟩ := hB (eH.symm σ).val (eH.symm σ).property i
    refine ⟨j, ?_⟩
    simp only [Module.Basis.map_apply]
    change characterLattice.galoisRepresentation K E TK σ (a (B i)) = a (B j)
    have ha : a (characterLattice.galoisRepresentation F E T (σ.restrictScalars F) (B i)) =
        characterLattice.galoisRepresentation K E TK σ (a (B i)) :=
      characterLattice.galoisRepresentation_scalarExtension hc T σ (B i)
    rw [← ha]
    change a (characterLattice.galoisRepresentation F E T (σ.restrictScalars F) (B i)) = _
    rw [heH, hj]
  obtain ⟨m, D, ⟨e⟩⟩ := inducedTorusWeilDecomposition K E TK hTK hInd
  let restricted := scalarExtension (K := K) (M := E) ξ
  let : IsAffineHom (cover K E).hom := inferInstanceAs (IsAffineHom (Spec.algebraMap K E))
  let : Flat (cover K E).hom := (fieldExtension_fpqc K E).2.1
  let : Surjective (cover K E).hom := (fieldExtension_fpqc K E).1
  have htriv : restricted.IsTrivial := Cocycle.isTrivial_of_weilPresentation_of_semilocal
    (A := CommRingCat.of K) (B := CommRingCat.of (∀ j, D j)) restricted (CommGroupScheme.groupIso e)
  obtain ⟨x, hx⟩ := (isTrivial_iff restricted).mp htriv
  let f := scalarExtensionPointsEquiv T.toGrp x
  apply isTrivial_nsmul_of_restricted_coboundary T ξ H hn f
  intro τ hτ
  let σ := eH ⟨τ, hτ⟩
  have hσ : σ.restrictScalars F = τ := AlgEquiv.ext fun _ => rfl
  have hval := value_scalarExtension (K := K) (M := E) ξ σ
  have hself : τ.restrictNormal E = τ := AlgEquiv.ext (τ.restrictNormal_commutes E)
  rw [hσ, hself, relativeExtend_self T] at hval
  rw [← hval, hx σ, map_mul, map_inv, scalarExtensionPointsEquiv_conjugate]
  change f * (GaloisPoint.conjugate F E T.toGrp (σ.restrictScalars F) f)⁻¹ = _
  rw [hσ]

end Langlands.GroupScheme
