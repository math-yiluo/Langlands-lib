import Langlands.Geometry.FormalGroup.FiniteKernelBaseChange
import Langlands.Geometry.FormalGroup.PiDivisible

/-! # Base change of affine isogenies and scalar divisibility -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- An R-algebra over an S-test algebra has the induced S-algebra structure. -/
def coefficientLiftAlgebra (φ : R →ₐ[O] S) (A : CommAlgCat.{v} S)
    (B : CommAlgCat.{v} R) (ψ : restrictCoefficientAlgebra φ A ⟶ B) :
    CommAlgCat.{v} S :=
  letI : Algebra S B := (ψ.hom.toRingHom.comp (algebraMap S A)).toAlgebra
  CommAlgCat.of S B

/-- The lift map with its induced S-linearity and unchanged underlying ring map. -/
def coefficientLiftMap (φ : R →ₐ[O] S) (A : CommAlgCat.{v} S)
    (B : CommAlgCat.{v} R) (ψ : restrictCoefficientAlgebra φ A ⟶ B) :
    A ⟶ coefficientLiftAlgebra φ A B ψ :=
  { hom' := {
    __ := ψ.hom.toRingHom
    commutes' := fun _ => rfl } }

namespace Hom

/-- An affine fppf lift over R inherits the S-action through its test algebra. -/
theorem IsFppfLocallySurjective.map {f : Hom M N}
    (hf : f.IsFppfLocallySurjective) (φ : R →ₐ[O] S) :
    (f.map φ).IsFppfLocallySurjective := by
  intro A y
  obtain ⟨B, ψ, hψff, hψfp, x, hx⟩ :=
    hf (restrictCoefficientAlgebra φ A) (N.coefficientPointEquiv φ A y)
  let B' := coefficientLiftAlgebra φ A B ψ
  let ψ' := coefficientLiftMap φ A B ψ
  refine ⟨B', ψ', hψff, hψfp, x, ?_⟩
  have hcomp : (algebraMap S B').comp φ.toRingHom = algebraMap R B := by
    apply RingHom.ext
    intro r
    exact ψ.hom.commutes r
  change SeriesPoint.eval
    ((f.toHom.toCoordinateMap.map φ.toRingHom).map (algebraMap S B')) x =
      SeriesPoint.map ψ.hom.toRingHom y
  rw [CoordinateMap.map_ringHom_comp, hcomp]
  exact hx

/-- Actual finite kernels and affine fppf lifting persist under coefficient extension. -/
theorem IsIsogeny.map {f : Hom M N} (hf : f.IsIsogeny) (φ : R →ₐ[O] S) :
    (f.map φ).IsIsogeny :=
  ⟨hf.1.map φ, hf.2.map φ⟩

/-- The actual constant kernel rank defining an isogeny height is preserved. -/
theorem HasHeight.map {f : Hom M N} {q h : ℕ}
    (hf : f.HasHeight q h) (φ : R →ₐ[O] S) : (f.map φ).HasHeight q h :=
  ⟨hf.1.map φ, hf.2.map φ⟩

end Hom

/-- Coefficient extension commutes with the actual scalar endomorphism. -/
@[simp]
theorem scalarHom_map (M : ModuleLaw O R σ) (a : O) (φ : R →ₐ[O] S) :
    (M.scalarHom a).map φ = (M.map φ).scalarHom a := by
  change Hom.mapLinear φ (a • Hom.id M) = a • Hom.id (M.map φ)
  rw [map_smul]
  change a • (Hom.id M).map φ = _
  rw [Hom.map_id]

/-- The actual O-linear point comparison preserves scalar-power torsion. -/
theorem IsPiPowerTorsion.map {π : O} (hM : M.IsPiPowerTorsion π) (φ : R →ₐ[O] S) :
    (M.map φ).IsPiPowerTorsion π := by
  intro A x
  obtain ⟨n, hn⟩ := hM (restrictCoefficientAlgebra φ A) (M.coefficientPointEquiv φ A x)
  refine ⟨n, (M.coefficientPointEquiv φ A).injective ?_⟩
  rw [map_smul, map_zero]
  exact hn

/-- Nilpotent-base scalar divisibility is stable under arbitrary coefficient extension. -/
theorem IsPiDivisible.map {π : O} (hM : M.IsPiDivisible π) (φ : R →ₐ[O] S) :
    (M.map φ).IsPiDivisible π := by
  refine ⟨?_, hM.torsion.map φ, ?_, ?_⟩
  · rw [← φ.commutes π]
    exact hM.base_nilpotent.map φ.toRingHom
  · simpa only [scalarHom_map] using hM.scalar_locallySurjective.map φ
  · intro n
    simpa only [scalarHom_map] using (hM.scalarPower_finiteKernel n).map φ

/-- Every scalar-power rank, and hence the finite O-height, is preserved. -/
theorem HasPiHeight.map {π : O} {q h : ℕ}
    (hM : M.HasPiHeight π q h) (φ : R →ₐ[O] S) :
    (M.map φ).HasPiHeight π q h := by
  refine ⟨hM.1.map φ, fun n => ?_⟩
  simpa only [scalarHom_map] using (hM.scalarPower_rank n).map φ

end Langlands.FormalGroup.ModuleLaw
