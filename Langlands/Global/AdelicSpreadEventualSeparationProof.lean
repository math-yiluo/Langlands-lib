import Langlands.Global.AdelicSpreadEventualSeparationStatement
import Langlands.Global.AdelicSIntegersColimitProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum
import Langlands.AlgebraicGeometry.SchemeLimitSeparatedProof
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Eventual separatedness along the actual arithmetic integer diagrams -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.AffineLimit
open Langlands.AlgebraicGeometry.SchemeLimitModel

/-- The relative base change of a structure map is separated exactly when
the structure map of the actual pullback is separated. -/
private theorem isSeparated_structure_baseChange_iff
    {S X T : Scheme.{u}} (a : X ⟶ S) (p : T ⟶ S) :
    IsSeparated (baseChangeMap a (𝟙 S) a (by simp) p) ↔
      IsSeparated (pullback.snd a p) := by
  calc
    IsSeparated (baseChangeMap a (𝟙 S) a (by simp) p) ↔
        IsSeparated (baseChangeMap a (𝟙 S) a (by simp) p ≫
          pullback.fst p (𝟙 S)) := IsSeparated.comp_iff.symm
    _ ↔ IsSeparated (pullback.fst p a) := by rw [baseChangeMap_fst]
    _ ↔ IsSeparated (pullback.snd a p) := by
      rw [← pullbackSymmetry_hom_comp_fst a p]
      exact (MorphismProperty.cancel_left_of_respectsIso
        (P := @IsSeparated) (pullbackSymmetry a p).hom (pullback.fst p a)).symm

/-- Noetherian finite-type models satisfy the generic separation-descent
hypotheses without an extra quasi-separatedness assumption. -/
private theorem finiteTypeModel_separated_iff_stage
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (A : J ⥤ CommAlgCat.{u} R) (c : Cocone A) (hc : IsColimit c)
    (M : Over (Spec (CommRingCat.of R)))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom] :
    IsSeparated (pullback.snd M.hom (spectrumBaseMap R A c)) ↔
      ∃ j : J, IsSeparated
        (pullback.snd M.hom ((spectrumStructure R A).app (op j))) := by
  let : IsLocallyNoetherian M.left := LocallyOfFiniteType.isLocallyNoetherian M.hom
  have h := relativeSeparatednessDescent (spectrumDiagram R A) (spectrumStructure R A)
    M.hom (𝟙 _) M.hom (by simp) (spectrumCone R A c)
    (spectrumConeIsLimit R A c hc) (spectrumBaseMap R A c)
    (spectrumCone_compat R A c)
  have h' : IsSeparated (pullback.snd M.hom (spectrumBaseMap R A c)) ↔
      ∃ j : Jᵒᵖ, IsSeparated
        (pullback.snd M.hom ((spectrumStructure R A).app j)) := by
    simpa only [isSeparated_structure_baseChange_iff] using h
  exact h'.trans ⟨fun ⟨j, hj⟩ => ⟨j.unop, hj⟩, fun ⟨j, hj⟩ => ⟨op j, hj⟩⟩

/-- The original function field is the colimit of the literal integer
inclusions, so separatedness occurs after one finite enlargement. -/
theorem curvePlaceSpreadEventualSeparation :
    CurvePlaceSpreadEventualSeparationStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S M _ _
  let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
    (adelicSIntegersNoetherian.1 k F S).1
  exact finiteTypeModel_separated_iff_stage (curvePlaceSIntegers k F S)
    (curvePlaceSIntegersOverDiagram k F S) (curvePlaceSIntegersOverCocone k F S)
    (curvePlaceSIntegersOverIsColimit k F S) M

/-- The same specialization uses the original number field and the actual
outside-set integer subrings, without changing the supplied model. -/
theorem numberFieldSpreadEventualSeparation :
    NumberFieldSpreadEventualSeparationStatement.{u} := by
  intro K _ _ S M _ _
  let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  exact finiteTypeModel_separated_iff_stage ((S : Set (FinitePlace K)).integer K)
    (numberFieldSIntegersOverDiagram K S) (numberFieldSIntegersOverCocone K S)
    (numberFieldSIntegersOverIsColimit K S) M

/-- Both arithmetic forms of eventual separatedness for supplied spreads. -/
theorem adelicSpreadEventualSeparation : AdelicSpreadEventualSeparationStatement.{u} :=
  ⟨curvePlaceSpreadEventualSeparation, numberFieldSpreadEventualSeparation⟩

end Langlands.Global
