import Langlands.Algebra.NumberFieldBrauerSplitting
import Langlands.ClassField.Global.IdeleFiniteInvariant

/-! # A central simple algebra is split at almost all finite places -/

noncomputable section

universe u

open CategoryTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.Brauer

open Langlands.BrauerComparison Langlands.CentralSimple
open Langlands.ClassField.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

/-- The finite places where a central simple algebra over a number field is not split. -/
def nonsplitFinitePlaces {F : Type u} [Field F] [NumberField F] (A : CSA.{u, u} F) :
    Set (HeightOneSpectrum (𝓞 F)) :=
  {v | ¬IsSplit (baseChange (v.adicCompletion F) A)}

/-- The nonsplit finite places lie in the support of the principal relative Brauer class. -/
theorem finite_nonsplitFinitePlaces {F : Type u} [Field F] [NumberField F] (A : CSA.{u, u} F) :
    (nonsplitFinitePlaces A).Finite := by
  let E := finiteGaloisSplittingField F A
  let e := finiteGaloisSplittingChart F A
  let : NumberField E := NumberField.of_module_finite F E
  let : Nonempty (Fin (reducedDegree F A)) := Fin.pos_iff_nonempty.mp (reducedDegree_pos F A)
  let c := relativeClass e
  let x := (principalIdeleCohomologyMap F E 2).hom c
  refine (finite_ideleLocalSupport
    (fun p _ => localInvariantFamily unramifiedH2Exhaustion p)
    (fun p _ => localInvariantFamilyRelativeImages unramifiedH2Exhaustion p) x).subset ?_
  intro v hv
  let w := (placeAbove E v).1
  let hw : w.asIdeal.LiesOver v.asIdeal := (placeAbove E v).2
  refine ⟨w, hw, ?_⟩
  intro h
  have he : (unitsLocalMap v w 2).hom c = 0 := by
    rw [← principalIdeleCohomologyMap_comp_ideleLocalMap]
    exact h
  change (unitsLocalMap v w 2).hom (relativeClass e) = 0 at he
  rw [unitsLocalMap_relativeClass] at he
  let : FiniteDimensional (v.adicCompletion F) (w.adicCompletion E) := FiniteExtension.local_finite v w
  let : IsGalois (v.adicCompletion F) (w.adicCompletion E) := isGalois_adicCompletion v w
  exact hv ⟨reducedDegree F A, reducedDegree_pos F A, split_of_relativeClass_eq_zero _ he⟩

end Langlands.Brauer
