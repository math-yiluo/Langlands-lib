import Langlands.Geometry.Analytic.Spectrum.ResidueField.CharacterTransport
import Langlands.Geometry.Analytic.AffinoidPointwiseEtale
import Mathlib.RingTheory.Unramified.Field

/-! # Algebraic and separable completed residues of finite degree -/

noncomputable section

universe u v w

namespace Langlands.Analytic.BanachSpectrum

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {B : Type v} [NormedCommRing B] [NormedAlgebra K B]

/-- If the completed residue field has finite degree over the complete
base field, the canonical character onto it is surjective. -/
theorem surjective_completedResidueMap_of_finite (y : BanachSpectrum B)
    [Module.Finite K (CompletedResidueField K y)] :
    Function.Surjective (completedResidueMap K y) := by
  let φ := (completedResidueMap K y).toAlgHom
  let S : Subalgebra K (CompletedResidueField K y) := φ.range
  have : Module.Finite K S :=
    Module.Finite.of_injective S.val.toLinearMap Subtype.val_injective
  have htop : S = ⊤ := finite_subalgebra_eq_top_of_residueMap K y S
    (Langlands.Analytic.isClosed_finite_subalgebra S) (fun b => ⟨b, rfl⟩)
  intro z
  have hz : z ∈ S := by rw [htop]; trivial
  exact hz

/-- At finite residue degree, the algebraic kernel quotient already is
the actual completed residue field. -/
def completedResidueQuotientEquivOfFinite (y : BanachSpectrum B)
    [Module.Finite K (CompletedResidueField K y)] :
    (B ⧸ y.kernel) ≃ₐ[K] CompletedResidueField K y := by
  have hk : y.kernel = RingHom.ker (completedResidueMap K y).toAlgHom.toRingHom := by
    apply Ideal.ext
    intro b
    change y b = 0 ↔ completedResidueMap K y b = 0
    rw [← norm_completedResidueMap K y b, norm_eq_zero]
  exact (Ideal.quotientEquivAlgOfEq K hk).trans
    (Ideal.quotientKerAlgEquivOfSurjective (surjective_completedResidueMap_of_finite K y))

variable {A : Type w} [NormedCommRing A] [NormedAlgebra K A]

/-- An unramified bounded map of finite type above a base-field character
has a separable completed source residue, provided that residue has finite
degree over the base field. -/
theorem isSeparable_completedResidue_of_unramified_over_baseFieldCharacter
    (f : BoundedAlgHom K A B) (hft : f.toAlgHom.toRingHom.FiniteType)
    (y : BanachSpectrum B) (hu : f.IsUnramifiedAtPoint y)
    (g : A →ₐ[K] K)
    (hg : ∀ a, ‖g a‖ = (comap f.toBoundedRingHom y) a)
    [Module.Finite K (CompletedResidueField K y)] :
    Algebra.IsSeparable K (CompletedResidueField K y) := by
  let F := CompletedResidueField K y
  let x := comap f.toBoundedRingHom y
  let ρ := completedResidueLift K x g hg
  have he (a : A) : completedResidueMap K x a =
      algebraMap K (CompletedResidueField K x) (g a) :=
    (isometry_completedResidueLift K x g hg).injective
      ((completedResidueLift_map K x g hg a).trans (ρ.toAlgHom.commutes (g a)).symm)
  let φ := (completedResidueMap K y).toAlgHom
  have hcomp (a : A) : φ (f a) = algebraMap K F (g a) :=
    (completedResidueComap_map K f y a).symm.trans
      ((congrArg (completedResidueComap K f y) (he a)).trans
        ((completedResidueComap K f y).toAlgHom.commutes (g a)))
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra A K := g.toRingHom.toAlgebra
  let : Algebra A F := ((algebraMap K F).comp g.toRingHom).toAlgebra
  let : Algebra B F := φ.toRingHom.toAlgebra
  let : IsScalarTower A K F := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B F :=
    IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  have : Algebra.IsUnramifiedAt A y.kernel :=
    (f.isUnramifiedAtPoint_iff_isUnramifiedAt hft y).mp hu
  let φA : B →ₐ[A] F := IsScalarTower.toAlgHom A B F
  have hunit (b : y.kernel.primeCompl) : IsUnit (φA b) := by
    apply isUnit_iff_ne_zero.mpr
    intro hb
    apply b.property
    change y b = 0
    exact (norm_completedResidueMap K y b).symm.trans
      (by change ‖φA b‖ = 0; rw [hb, norm_zero])
  let ψ : Localization.AtPrime y.kernel →ₐ[A] F := IsLocalization.liftAlgHom hunit
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨b, hb⟩ := surjective_completedResidueMap_of_finite K y z
    refine ⟨algebraMap B (Localization.AtPrime y.kernel) b, ?_⟩
    exact (IsLocalization.lift_eq hunit b).trans hb
  have : Algebra.FormallyUnramified A F := .of_surjective ψ hψ
  have : Algebra.FormallyUnramified K F := .of_restrictScalars A K F
  exact Algebra.FormallyUnramified.isSeparable K F

end Langlands.Analytic.BanachSpectrum
