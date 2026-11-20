import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData
import Langlands.Global.Arithmetic.HarrisProposition48MackeyChildCompletion
import Langlands.Global.Arithmetic.HarrisProposition48MackeyCharacterProof
import Langlands.Global.Arithmetic.HarrisProposition48MackeyCMProof

/-! # Assembly of the actual auxiliary Mackey child -/

noncomputable section

universe uF

namespace Langlands.Global.Harris.MackeyChild.CompletedBase

open NumberField AdelicFunctoriality LocalFactor.CommonClosure GeneralPosition
open scoped NumberField

variable {Q : Proposition48Problem.{uF}} {D : IntermediateField Q.E Q.L}
  {T : Extension Q.F} (A : CompletedBase Q D T) (a : Q.L ≃ₐ[Q.E] Q.L)

/-- Assemble the actual child after identifying its auxiliary character and reciprocity
family. The child's infinity-type twist keeps the parent's parity. -/
theorem exists_auxiliaryMackeyChild [IsGalois Q.E Q.L]
    (hUnique : HasUniquePlaceAbove Q.L Q.Ps.v) (hPrime : (Module.finrank Q.E D).Prime)
    {b : ℕ} (hParent : Q.IsAuxiliaryValidAtParity b)
    (e : ReciprocityFamily (T.asPadicField (p := Q.p)))
    (η : FieldCharacter (T.asPadicField (p := Q.p)) (A.localInducing a))
    (he : NormalizedReciprocity (T.asPadicField (p := Q.p)) e)
    (hGeneral : IsInGeneralPosition (T.asPadicField (p := Q.p)) (A.localInducing a)
      (weilCharacter (T.asPadicField (p := Q.p)) e (A.localInducing a) η))
    (hComponent : (A.place a hUnique).HasComponent (Q.mackeyCharacter D a) η) :
    ∃ R : Proposition48Problem.{uF}, Q.IsAuxiliaryMackeyChild D a R ∧
      R.IsAuxiliaryValidAtParity b ∧ Module.finrank R.E R.E' = Q.mackeyRank D a ∧
      R.inductionDegree < Q.inductionDegree := by
  obtain ⟨-, hSplit, -, hNormal, hp, -, -, -, -, hAlg, hReg, hConj, -⟩ := hParent
  let : IsNormalClosure Q.E Q.E' Q.L := hNormal
  let : IsCMField Q.L := CMRealization.isCMField_of_normalClosure Q.E Q.E' Q.L
  let : IsCMField D := CMRealization.isCMField_intermediateField D
  let : IsCMField (Q.mackeyField D a) :=
    CMRealization.isCMField_intermediateField (Q.mackeyField D a)
  let : IsCMField (inducingField Q D a) := this
  let : IsGalois D Q.L := IsGalois.tower_top_of_isGalois Q.E D Q.L
  let : IsCMField (closure Q D a) :=
    CMRealization.isCMField_intermediateField (closure Q D a)
  let R : Proposition48Problem.{uF} :=
    { p := Q.p
      F := T.asPadicField (p := Q.p)
      F' := A.localInducing a
      E := D
      E' := inducingField Q D a
      L := closure Q D a
      compact := compactSpace_adeleQuotient D
      e := e
      χ := η
      χs := η
      K₀ := quadraticField Q D
      P := A.place a hUnique
      Ps := A.place a hUnique
      ξ := Q.mackeyCharacter D a }
  refine ⟨R, ?_, ?_, rfl, degree_lt hPrime⟩
  · refine ⟨RingEquiv.refl D, RingEquiv.refl (Q.mackeyField D a),
      (closure Q D a).val.toRingHom, rfl, fun _ => rfl, fun _ => rfl,
      quadraticField_range Q D, ?_, ?_, ?_⟩
    · change Q.mackeyCharacter D a = (Q.mackeyCharacter D a).comp
        (ContinuousMonoidHom.toContinuousMonoidHom (ideleClassEquiv (RingEquiv.refl _)))
      rw [ideleClassEquiv_refl]
      rfl
    all_goals
      change ((finitePlaceEquiv (RingEquiv.refl D)) (basePlace Q D)).asIdeal.LiesOver Q.Ps.v.asIdeal
      rw [finitePlaceEquiv_refl, Equiv.refl_apply]
      exact basePlace_liesOver Q D
  · obtain ⟨hAlg', hReg', hConj'⟩ := mackeyCharacter_inherits Q D a b hAlg hReg hConj
    exact ⟨he, quadraticField_split Q D hSplit, inferInstance, isNormalClosure,
      prime_mem_basePlace Q D hp, A.place_compatible a hUnique,
      uniqueAbove_basePlace Q D a hUnique, uniqueAbove_conjPlace Q D a hUnique,
      hGeneral, hAlg', hReg', hConj', hComponent⟩

end Langlands.Global.Harris.MackeyChild.CompletedBase
