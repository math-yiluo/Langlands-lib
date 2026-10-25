import Langlands.ClassField.Global.InvariantClassConditions
import Langlands.ClassField.Global.IdeleTotalInvariant

/-! # Local compatibility from agreement with total idele invariants -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Local

universe u

namespace FundamentalClass

/-- Agreement on every idele quotient image, for every choice of places above
the finite and infinite places of the base number field. -/
def InvariantTotalAgreement
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
    (inv : GlobalInvariantMaps.{u}) : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (E : Type u) [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (a : relativeIdeleCohomology F E 2),
    inv F E (ideleQuotientCohomologyMap F E 2 a) =
      totalIdeleInvariant I hI wf wi a

end FundamentalClass

open FundamentalClass in
/-- Conditional local compatibility of supplied global invariants from their
image law, restriction law, and agreement with every total idele invariant sum. -/
def GlobalInvariantLocalFromTotalStatement : Prop :=
  ∀ (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
    (inv : GlobalInvariantMaps.{u}),
    InvariantImages inv →
    InvariantRestrictionOnClasses inv →
    InvariantTotalAgreement I hI inv →
    InvariantLocalOnClasses I inv

end Langlands.ClassField.Global
