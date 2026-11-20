import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Automorphic.CuspidalWhittaker.PlaceWhittaker
import Langlands.Automorphic.PlaceComponentExistence
import Langlands.Global.Factors.ComplexIsobaricConstituent
import Langlands.Representation.Archimedean.ComplexGenericStandardParameterProof

/-!
# The prescribed isobaric constituent at a complex place

The irreducible generic components of the actual cuspidal realizations give
irreducible complex standard modules with the required place actions. The
Langlands quotient of the ordered concatenation is a subquotient of the
standard module in the supplied cuspidal block order.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct Matrix.Norms.Operator

namespace Langlands.Global

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Archimedean Langlands.Automorphic
open LocalFactor.Archimedean (ComplexCharacterData)

universe u

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ}

local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local notation "Standard(" n ", " ds ")" => complexStandardKFinite n ds

/-- The supplied cuspidal family has irreducible standard parameters at `v`.
The ordered concatenation has an irreducible quotient that occurs as a
subquotient of the standard module of the concatenation in the supplied order. -/
def HasComplexIsobaricPlaceQuotient (T : ∀ i, CuspidalOperatorRealization F (m i))
    (v : CP) : Prop :=
  ∃ (ds : Fin k → List ComplexCharacterData) (es : List ComplexCharacterData),
    (∀ i, (T i).realization.HasComplexPlaceParameter v (ds i) ∧
      IsIrreducibleGKModule (complexStandardRep (m i + 1) (ds i))
        (complexStandardLie (m i + 1) (ds i))) ∧
    es.Perm (List.ofFn ds).flatten ∧ es.length = r + 1 ∧ IsComplexLanglandsOrdered es ∧
    ∃ (R : Submodule ℂ Standard(r + 1, es))
      (hR : IsGKSubmodule (complexStandardRep (r + 1) es) (complexStandardLie (r + 1) es) R),
      IsIrreducibleGKModule ((complexStandardRep (r + 1) es).quotient R hR.1)
        (RealLeviDuality.quotLie (complexStandardLie (r + 1) es) R hR.2) ∧
      let xs := (List.ofFn ds).flatten
      ∃ (W : Submodule ℂ Standard(r + 1, xs))
        (hW : IsGKSubmodule (complexStandardRep (r + 1) xs) (complexStandardLie (r + 1) xs) W)
        (q : W →ₗ[ℂ] (Standard(r + 1, es) ⧸ R)),
        IsGKSubquotientMap ((complexStandardRep (r + 1) es).quotient R hR.1)
          (RealLeviDuality.quotLie (complexStandardLie (r + 1) es) R hR.2) hW q

theorem hasComplexIsobaricPlaceQuotient
    (hm : ∑ i, (m i + 1) = r + 1) (T : ∀ i, CuspidalOperatorRealization F (m i))
    (v : CP) : HasComplexIsobaricPlaceQuotient (r := r) T v := by
  have hparam (i : Fin k) : ∃ ds,
      (T i).realization.HasComplexPlaceParameter v ds ∧
        IsIrreducibleGKModule (complexStandardRep (m i + 1) ds)
          (complexStandardLie (m i + 1) ds) := by
    obtain ⟨V, _, _, ρ, π, ι, hι, hρ, hπ, hgk, hirr, hadm, hgen⟩ :=
      (cuspidalArchimedeanGenericComponentBridge cuspidalArchimedeanIrreducibleAdmissibleComponent
        cuspidalArchimedeanWhittakerFunctional F (m i) (T i)).2 v
    obtain ⟨ds, hds⟩ :=
      complexGenericStandardParameter (m i + 1) V ρ π hgk hirr hadm hgen
    have hplace := OperatorRealization.hasComplexPlaceParameter_of_component hι hρ hπ hds
    obtain ⟨hn, A, hAinj, hA⟩ := (hasComplexStandardParameter_iff _ ρ π ds).mp hds
    exact ⟨ds, hplace, isIrreducibleGKModule_of_injective hirr hA hAinj
      (complexStandardNontrivial (m i + 1) ds hn)⟩
  choose ds hds using hparam
  let xs := (List.ofFn ds).flatten
  let es := xs.mergeSort complexLanglandsLE
  have hx : xs.length = r + 1 := by
    change (List.ofFn ds).flatten.length = r + 1
    rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    exact (Finset.sum_congr rfl fun i _ => (hds i).1.1).trans hm
  have hperm : es.Perm xs := List.mergeSort_perm _ _
  exact ⟨ds, es, hds, hperm, hperm.length_eq.trans hx, isComplexLanglandsOrdered_mergeSort xs,
    complexOrderedQuotient_subquotient (r + 1) xs hx⟩

end Langlands.Global
