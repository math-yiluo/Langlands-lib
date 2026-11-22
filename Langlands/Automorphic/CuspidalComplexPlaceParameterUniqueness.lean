import Langlands.Automorphic.ArchimedeanPlaceParameterClasses
import Langlands.Automorphic.OperatorSubquotientPlaceComponentComplex
import Langlands.Automorphic.PlaceComponentExistence
import Langlands.Representation.Archimedean.EmbeddedComplexStandardIrreducibility

/-! # Uniqueness of the complex parameter of a cuspidal class -/

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean

attribute [local instance] localComponentRationalGroup localComponentContinuousGroup
  localComponentSmoothGroup localComponentFormGroup localComponentStableGroup
  localComponentRealizationGroup
attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

set_option backward.isDefEq.respectTransparency false in
/-- Two complex standard-module parameters of one actual cuspidal realization
are permutations of each other. -/
theorem CuspidalOperatorRealization.complexPlaceParameters_perm {r : ℕ}
    (T : CuspidalOperatorRealization F r) (v : CP) {ds es : List ComplexCharacterData}
    (hd : T.realization.HasComplexPlaceParameter v ds)
    (he : T.realization.HasComplexPlaceParameter v es) :
    ds.Perm es := by
  let Q := T.toIrreducibleSubquotient
  let A := T.toIrreducibleSubquotientEquiv.toLinearEquiv
  have hK (k : Matrix.unitaryGroup (Fin (r + 1)) ℂ) (x : T.Space) :
      A (T.realization.complexPlaceCompactRepresentation v k x) =
        Q.subquotient.complexPlaceCompactRepresentation v k (A x) :=
    (Q.subquotient.complexPlaceCompactRepresentation_projection v k x).symm
  have hL (X : ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : T.Space) :
      A (T.realization.complexPlaceLieAction v X x) =
        Q.subquotient.complexPlaceLieAction v X (A x) :=
    (Q.subquotient.complexPlaceLieAction_projection v X x).symm
  obtain ⟨W, hI, hAdm⟩ := T.exists_complexPlaceComponent v
  have hne : W.map A.toLinearMap ≠ ⊥ := Submodule.map_ne_bot_iff.mpr hI.1
  have hI' := PlaceComponent.isIrreducible_map A.toLinearMap hK hL hI hne
  have hAdm' := PlaceComponent.isAdmissible_map A.toLinearMap hK hI.2.1.1
    (fun x _ hx => A.injective (hx.trans A.map_zero.symm)) hAdm
  have hG := PlaceComponent.isComplexGKModule_restrict hI'.2.1
    (Q.subquotient.isComplexGKModule_complexPlace v)
  have hIrr := PlaceComponent.isIrreducibleGKModule_restrict hI'
  have hAdmissible := PlaceComponent.isAdmissibleGKModule_restrict hI'.2.1 hAdm'
  have hIso := Q.subquotient.isComplexPlaceIsotypic_restrict Q.irreducible v hI'
  obtain ⟨hdlen, f, hf, hfK, hfL⟩ := hd
  obtain ⟨helen, g, hg, hgK, hgL⟩ := he
  have hf' : Archimedean.IsComplexStandardIntertwining (r + 1)
      (T.realization.complexPlaceCompactRepresentation v) (T.realization.complexPlaceLieAction v)
      ds f := ⟨hfK, hfL⟩
  have hg' : Archimedean.IsComplexStandardIntertwining (r + 1)
      (T.realization.complexPlaceCompactRepresentation v) (T.realization.complexPlaceLieAction v)
      es g := ⟨hgK, hgL⟩
  exact Archimedean.complexStandard_parameters_perm_of_isotypic_embeddings ds es hdlen helen
    _ _ _ _ hG hIrr hAdmissible hIso _ _
    (hf'.comp A.toLinearMap hK (fun X => hL (1 ⊗ₜ X))) (A.injective.comp hf)
    (hg'.comp A.toLinearMap hK (fun X => hL (1 ⊗ₜ X))) (A.injective.comp hg)

/-- Two complex parameter lists of the same positive-rank cuspidal class
are permutations of each other. -/
theorem PositiveRankCuspidalClass.complexPlaceParameters_perm (c : PositiveRankCuspidalClass F)
    (v : CP) {ds es : List ComplexCharacterData}
    (hd : c.HasComplexPlaceParameter v ds) (he : c.HasComplexPlaceParameter v es) :
    ds.Perm es := by
  rcases c with ⟨r, c⟩
  obtain ⟨T, rfl⟩ := c.exists_representative
  exact T.complexPlaceParameters_perm v hd he

end Langlands.Automorphic
