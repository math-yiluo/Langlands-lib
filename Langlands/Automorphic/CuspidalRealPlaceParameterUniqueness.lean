import Langlands.Automorphic.ArchimedeanPlaceParameterClasses
import Langlands.Automorphic.OperatorSubquotientPlaceComponent
import Langlands.Automorphic.PlaceComponentExistence
import Langlands.Representation.Archimedean.RealStandardIsotypicParameterUniquenessStatement

/-! # Real parameter comparison for cuspidal classes -/

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean Langlands.Archimedean

attribute [local instance] localComponentRationalGroup localComponentContinuousGroup
  localComponentSmoothGroup localComponentFormGroup localComponentStableGroup
  localComponentRealizationGroup
attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}

set_option backward.isDefEq.respectTransparency false in
/-- The local real standard-module comparison identifies the normalized block lists of
two parameters for the same actual cuspidal realization. -/
theorem CuspidalOperatorRealization.realPlaceParameters_perm
    (unique : RealStandardIsotypicParameterUniquenessStatement.{u, u}) {r : ℕ}
    (T : CuspidalOperatorRealization F r) (v : RP) {ds es : List RealBlock}
    (hd : T.realization.HasRealPlaceParameter v ds)
    (he : T.realization.HasRealPlaceParameter v es) :
    (realMoeglinData ds).Perm (realMoeglinData es) := by
  let Q := T.toIrreducibleSubquotient
  let A := T.toIrreducibleSubquotientEquiv.toLinearEquiv
  have hK (k : Matrix.unitaryGroup (Fin (r + 1)) ℝ) (x : T.Space) :
      A (T.realization.realPlaceCompactRepresentation v k x) =
        Q.subquotient.realPlaceCompactRepresentation v k (A x) :=
    (Q.subquotient.realPlaceCompactRepresentation_projection v k x).symm
  have hL (X : ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (x : T.Space) :
      A (T.realization.realPlaceLieAction v X x) =
        Q.subquotient.realPlaceLieAction v X (A x) :=
    (Q.subquotient.realPlaceLieAction_projection v X x).symm
  obtain ⟨W, hI, hAdm⟩ := T.exists_realPlaceComponent v
  have hne : W.map A.toLinearMap ≠ ⊥ := Submodule.map_ne_bot_iff.mpr hI.1
  have hI' := PlaceComponent.isIrreducible_map A.toLinearMap hK hL hI hne
  have hAdm' := PlaceComponent.isAdmissible_map A.toLinearMap hK hI.2.1.1
    (fun x _ hx => A.injective (hx.trans A.map_zero.symm)) hAdm
  have hG := PlaceComponent.isRealGKModule_restrict hI'.2.1
    (Q.subquotient.isRealGKModule_realPlace v)
  have hIrr := PlaceComponent.isIrreducibleGKModule_restrict hI'
  have hAdmissible := PlaceComponent.isAdmissibleGKModule_restrict hI'.2.1 hAdm'
  have hIso := Q.subquotient.isRealPlaceIsotypic_restrict Q.irreducible v hI'
  obtain ⟨hdrank, f, hf, hfK, hfL⟩ := hd
  obtain ⟨herank, g, hg, hgK, hgL⟩ := he
  have hf' : IsRealStandardIntertwiner (r + 1)
      (T.realization.realPlaceCompactRepresentation v) (T.realization.realPlaceLieAction v)
      ds f := ⟨hfK, hfL⟩
  have hg' : IsRealStandardIntertwiner (r + 1)
      (T.realization.realPlaceCompactRepresentation v) (T.realization.realPlaceLieAction v)
      es g := ⟨hgK, hgL⟩
  exact unique (r + 1) _ Q.Space _ _ _ _ ds es (A.toLinearMap.comp f) (A.toLinearMap.comp g)
    hG hIrr hAdmissible hIso hdrank herank
    ⟨fun k x => (congrArg A (hf'.map_realStandardRep k x)).trans (hK k (f x)),
      fun X x => (congrArg A (hf'.map_realStandardLie X x)).trans (hL X (f x))⟩
    (A.injective.comp hf)
    ⟨fun k x => (congrArg A (hg'.map_realStandardRep k x)).trans (hK k (g x)),
      fun X x => (congrArg A (hg'.map_realStandardLie X x)).trans (hL X (g x))⟩
    (A.injective.comp hg)

/-- The normalized real parameter list of a positive-rank cuspidal class is determined
up to permutation by the local comparison of standard modules. -/
theorem PositiveRankCuspidalClass.realPlaceParameters_perm
    (unique : RealStandardIsotypicParameterUniquenessStatement.{u, u})
    (c : PositiveRankCuspidalClass F) (v : RP) {ds es : List RealBlock}
    (hd : c.HasRealPlaceParameter v ds) (he : c.HasRealPlaceParameter v es) :
    (realMoeglinData ds).Perm (realMoeglinData es) := by
  rcases c with ⟨r, c⟩
  obtain ⟨T, rfl⟩ := c.exists_representative
  exact T.realPlaceParameters_perm unique v hd he

end Langlands.Automorphic
