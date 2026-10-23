import Langlands.ClassField.Global.IdeleLocalSupport
import Langlands.ClassField.Global.IdeleCoefficientSequence
import Langlands.ClassField.Global.ReciprocityStatement
import Langlands.ClassFieldTheory.Local.RelativeInvariantEquivalences

/-! # Finite-place invariants of idele cohomology -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory FundamentalClass

universe u

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- The finite local invariant of an actual idele-cohomology class. -/
def finiteIdeleInvariant (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] :
    relativeIdeleCohomology F E 2 →+ RationalModIntegers :=
  haveI : IsGalois (padicField v).Carrier (w.adicCompletion E) :=
    isGalois_adicCompletion v w
  haveI : FiniteDimensional (padicField v).Carrier (w.adicCompletion E) :=
    FiniteExtension.local_finite v w
  ((I (residuePrime v)).relative (padicField v) (w.adicCompletion E)).comp
    (ideleLocalMap v w 2).hom.toAddMonoidHom

/-- On principal classes, the finite idele invariant is the field-unit local invariant. -/
@[simp] theorem finiteIdeleInvariant_principal
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] (x : relativeCohomology F E 2) :
    finiteIdeleInvariant I v w (principalIdeleCohomologyMap F E 2 x) =
      Reciprocity.finiteLocalInvariant v w I x := by
  have := isGalois_adicCompletion v w
  have := FiniteExtension.local_finite v w
  have h := congrArg (fun f => f x)
    (principalIdeleCohomologyMap_comp_ideleLocalMap (F := F) (E := E) v w 2)
  exact congrArg ((I (residuePrime v)).relative (padicField v) (w.adicCompletion E)) h

variable (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)

include hI in
/-- The local image laws supply the finiteness hypotheses for idele local support. -/
theorem finite_ideleLocalSupport (c : relativeIdeleCohomology F E 2) :
    (ideleLocalSupport c).Finite := by
  apply finite_setOf_ideleLocalMap_ne_zero
  · intro v w hw
    have := isGalois_adicCompletion v w
    have := FiniteExtension.local_finite v w
    exact (I (residuePrime v)).relativeH2_finite (hI _) (padicField v) _
  · intro v w hw
    have := isGalois_adicCompletion v w
    have := FiniteExtension.local_finite v w
    exact le_of_eq ((I (residuePrime v)).relativeH2_card (hI _) (padicField v) _)

include hI in
/-- Only finitely many of the chosen finite local invariants are nonzero. -/
theorem finite_support_finiteIdeleInvariant
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (c : relativeIdeleCohomology F E 2) :
    (Function.support fun v =>
      haveI := (wf v).2
      finiteIdeleInvariant I v (wf v).1 c).Finite := by
  refine (finite_ideleLocalSupport I hI c).subset ?_
  intro v hv
  have := (wf v).2
  have := isGalois_adicCompletion v (wf v).1
  have := FiniteExtension.local_finite v (wf v).1
  refine ⟨(wf v).1, (wf v).2, ?_⟩
  intro h
  apply hv
  change (I (residuePrime v)).relative (padicField v) ((wf v).1.adicCompletion E)
    (ideleLocalMap v (wf v).1 2 c) = 0
  rw [h, map_zero]

/-- Sum of the finite local invariants, with the chosen places made explicit. -/
def finiteIdeleInvariantSum
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v) :
    relativeIdeleCohomology F E 2 →+ RationalModIntegers where
  toFun c := ∑ᶠ v, haveI := (wf v).2; finiteIdeleInvariant I v (wf v).1 c
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add]
    exact finsum_add_distrib
      (finite_support_finiteIdeleInvariant I hI wf x)
      (finite_support_finiteIdeleInvariant I hI wf y)

/-- Principal classes have the same finite sum as in the reciprocity statement. -/
theorem finiteIdeleInvariantSum_principal
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (x : relativeCohomology F E 2) :
    finiteIdeleInvariantSum I hI wf (principalIdeleCohomologyMap F E 2 x) =
      ∑ᶠ v, haveI := (wf v).2; Reciprocity.finiteLocalInvariant v (wf v).1 I x := by
  change (∑ᶠ v, haveI := (wf v).2;
    finiteIdeleInvariant I v (wf v).1 (principalIdeleCohomologyMap F E 2 x)) = _
  congr 1
  funext v
  have := (wf v).2
  exact finiteIdeleInvariant_principal I v (wf v).1 x

end Langlands.ClassField.Global
