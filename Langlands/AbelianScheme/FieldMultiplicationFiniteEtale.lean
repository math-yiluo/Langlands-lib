import Langlands.AbelianScheme.AlgClosedPointDivisibility
import Langlands.AbelianScheme.Isogeny
import Langlands.AbelianScheme.TorsionFiniteEtale

/-! # Multiplication by an integer nonzero in a field is a finite étale isogeny -/

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.GroupScheme

variable {K : Type u} [Field K]
  (B : AbelianScheme (Spec (CommRingCat.of K))) (n : ℕ) (hn : (n : K) ≠ 0)

include hn in
/-- Over a field in which `n` is nonzero, multiplication by `n` is finite: it is proper and
étale, hence locally quasi-finite. -/
lemma multiplication_isFinite_of_ne_zero :
    IsFinite (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left := by
  have : Etale (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left :=
    multiplication_etale_of_field B n hn
  have : IsProper (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left := by
    have : IsProper ((GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left ≫ B.X.hom) := by
      rw [Over.w]
      infer_instance
    exact IsProper.of_comp _ B.X.hom
  have : LocallyQuasiFinite (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left :=
    Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

include hn in
/-- Over a field in which `n` is nonzero, multiplication by `n` is an isogeny in the
finite-flat-surjective sense. -/
theorem multiplication_isIsogeny_of_ne_zero :
    GroupScheme.IsIsogeny (GroupScheme.multiplication B.toGrp (n : ℤ)) := by
  have := multiplication_etale_of_field B n hn
  exact ⟨multiplication_isFinite_of_ne_zero B n hn,
    (inferInstance : Flat (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left),
    multiplication_surjective_of_field B n hn⟩

include hn in
/-- The `n`-torsion kernel is finite over the base. -/
lemma multiplicationKernel_isFinite_of_ne_zero :
    IsFinite (GroupScheme.kernel (GroupScheme.multiplication B.toGrp (n : ℤ))).X.hom := by
  have := multiplication_isFinite_of_ne_zero B n hn
  exact MorphismProperty.of_isPullback
    (kernel_isPullback_scheme (GroupScheme.multiplication B.toGrp (n : ℤ))) inferInstance

include hn in
/-- The `n`-torsion kernel is étale over the base. -/
lemma multiplicationKernel_etale_of_ne_zero :
    Etale (GroupScheme.kernel (GroupScheme.multiplication B.toGrp (n : ℤ))).X.hom := by
  have := multiplication_etale_of_field B n hn
  exact MorphismProperty.of_isPullback
    (kernel_isPullback_scheme (GroupScheme.multiplication B.toGrp (n : ℤ))) inferInstance

end Langlands.AbelianScheme
