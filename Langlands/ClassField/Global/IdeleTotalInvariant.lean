import Langlands.ClassField.Global.IdeleFiniteInvariant
import Langlands.ClassField.Global.IdeleArchimedean
import Langlands.ClassField.Global.IdeleCohomologyExactnessProof

/-! # The sum of all local invariants on idele cohomology -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Local

universe u

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
  {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- Sum of the finite and archimedean invariants, for explicit choices of places. -/
def totalIdeleInvariant
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v) :
    relativeIdeleCohomology F E 2 →+ RationalModIntegers :=
  finiteIdeleInvariantSum I hI wf + ∑ v, archimedeanIdeleInvariant F (wi v).1

/-- On principal classes, the total invariant is exactly the reciprocity sum. -/
theorem totalIdeleInvariant_principal
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (x : relativeCohomology F E 2) :
    totalIdeleInvariant I hI wf wi (principalIdeleCohomologyMap F E 2 x) =
      (∑ᶠ v, haveI := (wf v).2; Reciprocity.finiteLocalInvariant v (wf v).1 I x) +
        ∑ v, Reciprocity.archimedeanInvariant (wi v).1 x := by
  simp only [totalIdeleInvariant, AddMonoidHom.add_apply, AddMonoidHom.finsetSum_apply,
    finiteIdeleInvariantSum_principal, archimedeanIdeleInvariant_principalIdeleCohomologyMap]

/-- The reciprocity law for a class makes its principal image have zero total invariant. -/
theorem totalIdeleInvariant_principal_eq_zero
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (x : relativeCohomology F E 2) (hx : Reciprocity.SumOfInvariantsVanishes I x) :
    totalIdeleInvariant I hI wf wi (principalIdeleCohomologyMap F E 2 x) = 0 := by
  rw [totalIdeleInvariant_principal]
  exact (hx wf wi).2

/-- Assuming reciprocity on all field-unit classes, the total invariant vanishes
on the kernel of the map to idele-class cohomology. -/
theorem totalIdeleInvariant_eq_zero_of_ideleQuotient_eq_zero
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (hrec : ∀ x : relativeCohomology F E 2, Reciprocity.SumOfInvariantsVanishes I x)
    (c : relativeIdeleCohomology F E 2)
    (hc : ideleQuotientCohomologyMap F E 2 c = 0) :
    totalIdeleInvariant I hI wf wi c = 0 := by
  obtain ⟨x, rfl⟩ := (ideleQuotientCohomologyMap_eq_zero_iff F E 2 c).1 hc
  exact totalIdeleInvariant_principal_eq_zero I hI wf wi x (hrec x)

end Langlands.ClassField.Global
