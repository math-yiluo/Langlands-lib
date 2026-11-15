import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Faithfully flat local extensions with prescribed residue field -/

noncomputable section

universe u

namespace Langlands.CommutativeAlgebra

namespace LocalResidueExtension

variable {R K : Type u} [CommRing R] [Field K] (f : R →+* K)

/-- Evaluation with a variable for every element of the desired residue field. -/
def evaluation : MvPolynomial K R →+* K :=
  MvPolynomial.eval₂Hom f id

theorem evaluation_surjective : Function.Surjective (evaluation f) := by
  intro k
  exact ⟨MvPolynomial.X k, by simp [evaluation]⟩

instance : (RingHom.ker (evaluation f)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (evaluation_surjective f)

/-- Localize the polynomial algebra at the kernel of evaluation. -/
abbrev Extension : Type u := Localization.AtPrime (RingHom.ker (evaluation f))

private theorem evaluation_units
    (s : (RingHom.ker (evaluation f)).primeCompl) : IsUnit (evaluation f s) := by
  apply isUnit_iff_ne_zero.mpr
  exact s.property

/-- Evaluation extends over this localization. -/
def toField : Extension f →+* K :=
  IsLocalization.lift (evaluation_units f)

@[simp]
theorem toField_algebraMap (p : MvPolynomial K R) :
    toField f (algebraMap (MvPolynomial K R) (Extension f) p) = evaluation f p :=
  IsLocalization.lift_eq (evaluation_units f) p

theorem toField_surjective : Function.Surjective (toField f) := by
  intro k
  obtain ⟨p, hp⟩ := evaluation_surjective f k
  exact ⟨algebraMap (MvPolynomial K R) (Extension f) p, by simpa using hp⟩

instance : IsLocalHom (toField f) :=
  IsLocalHom.of_surjective _ (toField_surjective f)

/-- The extension has exactly the specified residue field. -/
def residueEquiv : IsLocalRing.ResidueField (Extension f) ≃+* K :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.lift (toField f)) ⟨
    RingHom.injective _,
    fun k => by
      obtain ⟨b, hb⟩ := toField_surjective f k
      exact ⟨IsLocalRing.residue _ b, hb⟩⟩

variable [IsLocalRing R] [IsLocalHom f]

instance : IsLocalHom (algebraMap R (Extension f)) := by
  constructor
  intro r hr
  apply isUnit_of_map_unit f r
  have h := (toField f).isUnit_map hr
  simpa only [IsScalarTower.algebraMap_apply R (MvPolynomial K R) (Extension f),
    toField_algebraMap, evaluation, MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_C] using h

theorem faithfullyFlat : Module.FaithfullyFlat R (Extension f) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

end LocalResidueExtension

/-- Any local map into a field admits a faithfully flat local extension with
that residue field, in the same universe. -/
theorem exists_faithfullyFlat_local_with_residue
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    (f : R →+* K) [IsLocalHom f] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra R B),
      Module.FaithfullyFlat R B ∧ IsLocalHom (algebraMap R B) ∧
        Nonempty (IsLocalRing.ResidueField B ≃+* K) :=
  ⟨LocalResidueExtension.Extension f, inferInstance, inferInstance, inferInstance,
    LocalResidueExtension.faithfullyFlat f, inferInstance,
    ⟨LocalResidueExtension.residueEquiv f⟩⟩

/-- A local ring embeds faithfully flatly and locally into a local ring whose
residue field is algebraically closed. -/
theorem exists_faithfullyFlat_local_algClosed_residue
    (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra R B),
      Module.FaithfullyFlat R B ∧ IsLocalHom (algebraMap R B) ∧
        IsAlgClosed (IsLocalRing.ResidueField B) := by
  let K := AlgebraicClosure (IsLocalRing.ResidueField R)
  let f : R →+* K :=
    (algebraMap (IsLocalRing.ResidueField R) K).comp (IsLocalRing.residue R)
  obtain ⟨B, hB, hlocal, halg, hflat, hmap, ⟨e⟩⟩ :=
    exists_faithfullyFlat_local_with_residue R K f
  exact ⟨B, hB, hlocal, halg, hflat, hmap, IsAlgClosed.of_ringEquiv K _ e.symm⟩

/-- Same-universe faithfully flat local extensions with algebraically closed
residue fields exist over every commutative local ring. -/
def ClosedResidueLocalExtensionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R],
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra R B),
      Module.FaithfullyFlat R B ∧ IsLocalHom (algebraMap R B) ∧
        IsAlgClosed (IsLocalRing.ResidueField B)

theorem closedResidueLocalExtension : ClosedResidueLocalExtensionStatement.{u} :=
  exists_faithfullyFlat_local_algClosed_residue

end Langlands.CommutativeAlgebra
