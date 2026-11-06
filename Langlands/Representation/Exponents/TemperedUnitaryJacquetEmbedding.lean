import Langlands.Representation.Exponents.TemperedUnitaryJacquetQuotient
import Langlands.Representation.Exponents.TemperedJacquetRestriction
import Langlands.Representation.Aubert.General.FirstAdjointness

/-!
# Induction embeddings from actual unitary Jacquet quotients

A quotient of the unitary Jacquet summand extends to the full Jacquet module
through the supplied complementary retraction. First adjointness then gives
an actual induction embedding for an irreducible ambient representation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance embeddingAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

variable [IsAffineHom M.X.hom]

local instance embeddingLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  RationalPointFamily.pointTopology

/-- Extend the chosen quotient map to the full normalized Jacquet module
by composing with the actual unitary-part retraction. -/
def unitaryJacquetQuotientFullMap
    (hcompl : IsCompl
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    (leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶ D.quotient :=
  leviUnitaryJacquetRetraction p l r hp hl hr hmul ha π hcompl ≫ D.quotientMap

/-- Restriction of the full map to the actual unitary part recovers
the original chosen quotient map. -/
@[simp] theorem unitaryJacquetModuleι_quotientFullMap
    (hcompl : IsCompl
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π ≫
      unitaryJacquetQuotientFullMap p l r hp hl hr hmul ha π hcompl D =
        D.quotientMap := by
  simp only [unitaryJacquetQuotientFullMap, ← Category.assoc,
    leviUnitaryJacquetModuleι_retraction, Category.id_comp]

/-- The full Jacquet map is surjective because its restriction to the
unitary summand is the given surjective quotient map. -/
theorem unitaryJacquetQuotientFullMap_surjective
    (hcompl : IsCompl
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    Function.Surjective
      (SmoothRep.hom (unitaryJacquetQuotientFullMap p l r hp hl hr hmul ha π hcompl D)) := by
  intro y
  obtain ⟨x, hx⟩ := D.surjective y
  refine ⟨SmoothRep.hom (leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π) x, ?_⟩
  have he := congrArg (fun f => SmoothRep.hom f x)
    (unitaryJacquetModuleι_quotientFullMap p l r hp hl hr hmul ha π hcompl D)
  exact he.trans hx

/-- The same quotient map on the literal Levi image, with its underlying
linear map unchanged by the inverse Levi-point transport. -/
def unitaryJacquetQuotientImageMap
    (hcompl : IsCompl
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    ((jacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
      (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm D.quotient).representation where
  toLinearMap :=
    (SmoothRep.hom (unitaryJacquetQuotientFullMap p l r hp hl hr hmul ha π hcompl D)).toLinearMap
  isIntertwining' m := by
    let e := leviPointsEquiv p l hp hl
    have he := (SmoothRep.hom
      (unitaryJacquetQuotientFullMap p l r hp hl hr hmul ha π hcompl D)).isIntertwining'
        (e.symm m)
    change
      (SmoothRep.hom
        (unitaryJacquetQuotientFullMap p l r hp hl hr hmul ha π hcompl D)).toLinearMap.comp
        (((jacquetFunctor p l r hp hr hl hmul).obj π).representation (e (e.symm m))) =
      (D.quotient.representation (e.symm m)).comp
        (SmoothRep.hom
          (unitaryJacquetQuotientFullMap p l r hp hl hr hmul ha π hcompl D)).toLinearMap at he
    change
      (SmoothRep.hom
        (unitaryJacquetQuotientFullMap p l r hp hl hr hmul ha π hcompl D)).toLinearMap.comp
        (((jacquetFunctor p l r hp hr hl hmul).obj π).representation m) =
      (D.quotient.representation (e.symm m)).comp
        (SmoothRep.hom
          (unitaryJacquetQuotientFullMap p l r hp hl hr hmul ha π hcompl D)).toLinearMap
    simpa only [e.apply_symm_apply] using he

/-- The induction intertwiner adjoint to the actual full Jacquet quotient.
Unimodularity of the literal radical remains an explicit input. -/
def unitaryJacquetQuotientInductionMap
    (hδ : IsUnimodularModulus (pointImage (r ≫ p))
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup))
    (hcompl : IsCompl
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    π.representation.IntertwiningMap
      ((leviInductionFunctor p l r hp hr hl hmul).obj D.quotient).representation :=
  (General.FirstAdjointness.equiv
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    hδ π (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm D.quotient)).symm
      (unitaryJacquetQuotientImageMap p l r hp hl hr hmul ha π hcompl D)

/-- For an irreducible ambient representation, the adjoint of this nonzero
surjective Jacquet map is injective. The field and carrier universes stay independent. -/
theorem unitaryJacquetQuotientInductionMap_injective
    (hδ : IsUnimodularModulus (pointImage (r ≫ p))
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup))
    (hπ : π.IsIrreducible)
    (hcompl : IsCompl
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    Function.Injective
      (unitaryJacquetQuotientInductionMap p l r hp hl hr hmul ha π hδ hcompl D) := by
  have : π.representation.IsIrreducible := hπ
  have : D.quotient.representation.IsIrreducible := D.irreducible
  have : Nontrivial D.quotient :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M)) D.quotient.representation.asModule
  apply (Representation.IsIrreducible.injective_or_eq_zero
    (unitaryJacquetQuotientInductionMap p l r hp hl hr hmul ha π hδ hcompl D)).resolve_right
  intro hz
  have hqzero : unitaryJacquetQuotientImageMap p l r hp hl hr hmul ha π hcompl D = 0 := by
    let E := General.FirstAdjointness.equiv
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      hδ π (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm D.quotient)
    have he : E (E.symm
        (unitaryJacquetQuotientImageMap p l r hp hl hr hmul ha π hcompl D)) = E 0 :=
      congrArg E hz
    exact (E.apply_symm_apply _).symm.trans (he.trans E.map_zero)
  obtain ⟨y, hy⟩ := exists_ne (0 : D.quotient)
  obtain ⟨x, hx⟩ :=
    unitaryJacquetQuotientFullMap_surjective p l r hp hl hr hmul ha π hcompl D y
  apply hy
  rw [← hx]
  exact congrArg (fun f => f x) hqzero

omit [IsAffineHom M.X.hom] in
/-- A nonzero complementary unitary Jacquet part yields an actual embedding
into the normalized induction of an irreducible Levi representation.
The Levi's affine structure is derived from the rational Levi witness. -/
theorem exists_irreducible_induction_embedding_of_unitaryJacquetPart
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (hδ : IsUnimodularModulus (pointImage (r ≫ p))
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup))
    (hπ : π.IsIrreducible)
    (hcompl : IsCompl
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule)
    (hne : Nontrivial
      (SmoothRep.subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π)
        (unitaryJacquetPart p l r hp hl hr hmul ha π))) :
    letI := leviPointTopology l hl
    ∃ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M), σ.IsIrreducible ∧
      ∃ f : π.representation.IntertwiningMap
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation,
        Function.Injective f := by
  let := hl.isConnectedReductive.isAffineHom
  let D := unitaryJacquetIrreducibleQuotient p l r hp hl hr hmul ha π hπ hcompl hne
  exact ⟨D.quotient, D.irreducible,
    unitaryJacquetQuotientInductionMap p l r hp hl hr hmul ha π hδ hcompl D,
    unitaryJacquetQuotientInductionMap_injective p l r hp hl hr hmul ha π hδ hπ hcompl D⟩

end Langlands.Aubert.General.RepresentedParabolic
