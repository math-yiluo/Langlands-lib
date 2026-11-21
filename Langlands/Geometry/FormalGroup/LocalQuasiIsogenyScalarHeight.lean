import Langlands.Geometry.FormalGroup.FieldRationalDegree
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Scalar-kernel heights under actual local quasi-isogenies -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {S : Type v} [CommRing S] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {π : O} {q h : ℕ}

/-- Evaluate the actual structure sections at the residue field of a point of the open. -/
def coefficientResidueMap (V : Opens (PrimeSpectrum R)) (x : V) :
    (coefficientStructurePresheaf R).obj (op V) →ₐ[R] (x : PrimeSpectrum R).asIdeal.ResidueField := by
  let A := (Spec.structureSheaf R).presheaf.stalk (x : PrimeSpectrum R)
  let germ : (coefficientStructurePresheaf R).obj (op V) →ₐ[R] A := {
    __ := ((Spec.structureSheaf R).presheaf.germ V x.val x.property).hom
    commutes' r := StructureSheaf.algebraMap_germ_apply V x.val x.property r }
  let residue : A →ₐ[R] (x : PrimeSpectrum R).asIdeal.ResidueField :=
    IsLocalization.liftAlgHom (M := x.val.asIdeal.primeCompl)
      (f := Algebra.ofId R x.val.asIdeal.ResidueField) (fun y => IsUnit.mk0 _ (by
        change algebraMap R x.val.asIdeal.ResidueField y.val ≠ 0
        exact fun h => y.property (Ideal.algebraMap_residueField_eq_zero.mp h)))
  exact residue.comp germ

private theorem scalarPower_rank_at_image {n : ℕ} (φ : R →ₐ[O] S)
    (K : Hom.FiniteKernelModel (M.scalarHom (π ^ n)))
    (hM : (M.map φ).HasPiHeight π q h) (y : PrimeSpectrum S) :
    K.rank (y.comap φ.toRingHom) = q ^ (n * h) := by
  have hr : ((M.scalarHom (π ^ n)).map φ).HasKernelRank (q ^ (n * h)) := by
    rw [scalarHom_map]
    exact hM.scalarPower_rank n
  rw [← K.rank_baseChange φ y]
  exact (Hom.hasKernelRank_iff _ (K.baseChange φ) _).mp hr y

/-- For a divisible source, coefficient extension surjective on spectra detects
the rank formula for all scalar kernels. -/
theorem IsPiDivisible.hasPiHeight_of_map_surjective (hM : M.IsPiDivisible π)
    (φ : R →ₐ[O] S) (hφ : Function.Surjective (PrimeSpectrum.comap φ.toRingHom))
    (hM' : (M.map φ).HasPiHeight π q h) : M.HasPiHeight π q h := by
  refine ⟨hM, fun n => ?_⟩
  obtain ⟨K⟩ := hM.scalarPower_finiteKernel n
  refine ⟨K, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := hφ x
  exact scalarPower_rank_at_image φ K hM' y

/-- A divisible formal module has constant scalar height if the rank formula holds
at all actual residue fields of the affine base. -/
theorem IsPiDivisible.hasPiHeight_of_residueFields (hM : M.IsPiDivisible π)
    (hf : ∀ x : PrimeSpectrum R,
      let κ := CommAlgCat.of R x.asIdeal.ResidueField
      let : Algebra O κ := coefficientAlgebra κ
      let : IsScalarTower O R κ := coefficientScalarTower κ
      (M.map (IsScalarTower.toAlgHom O R κ)).HasPiHeight π q h) :
    M.HasPiHeight π q h := by
  refine ⟨hM, fun n => ?_⟩
  obtain ⟨K⟩ := hM.scalarPower_finiteKernel n
  refine ⟨K, fun x => ?_⟩
  let κ := CommAlgCat.of R x.asIdeal.ResidueField
  let : Algebra O κ := coefficientAlgebra κ
  let : IsScalarTower O R κ := coefficientScalarTower κ
  let φ := IsScalarTower.toAlgHom O R κ
  let y : PrimeSpectrum κ := ⟨⊥, Ideal.isPrime_bot⟩
  have hx : y.comap φ.toRingHom = x := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R x.asIdeal.ResidueField) ⊥ = x.asIdeal
    exact Ideal.ker_algebraMap_residueField x.asIdeal
  exact hx ▸ scalarPower_rank_at_image φ K (hf x) y

/-- A local quasi-isogeny on all of the affine base transfers the actual finite
scalar height of the source to the target. -/
theorem LocalQuasiIsogeny.target_hasPiHeight
    (z : LocalQuasiIsogeny F π M N (⊤ : Opens (PrimeSpectrum R)))
    (hM : M.HasPiHeight π q h) : N.HasPiHeight π q h := by
  apply z.target_divisible.hasPiHeight_of_residueFields
  intro x
  obtain ⟨V, hx, _, _, f, hf, _⟩ := z.isLocal x (by trivial)
  let A := (coefficientStructurePresheaf R).obj (op V)
  let κ := CommAlgCat.of R x.asIdeal.ResidueField
  let ψ : A ⟶ κ := CommAlgCat.ofHom (coefficientResidueMap V ⟨x, hx⟩)
  let : Algebra O κ := coefficientAlgebra κ
  let : IsScalarTower O R κ := coefficientScalarTower κ
  let φ := IsScalarTower.toAlgHom O R κ
  have hfκ := hf.algebraMapLinear ψ
  have hMκ := hM.map φ
  have hNκ := z.target_divisible.map φ
  refine ⟨hNκ, fun n => ?_⟩
  have hd := @Hom.IsIsogeny.scalarPower_fieldDegree_eq O _ π κ _ (coefficientAlgebra κ) σ τ _ _ _ _ _
    hfκ hMκ.piDivisible hNκ n
  have hr := (hMκ.piDivisible.scalarPower_isIsogeny n).fieldDegree_eq_of_rank (hMκ.scalarPower_rank n)
  rw [← hr, hd]
  exact (hNκ.scalarPower_isIsogeny n).hasKernelRank_fieldDegree

end Langlands.FormalGroup.ModuleLaw
