import Langlands.Shimura.Coefficients.EtaleCoverComparisonStatement
import Langlands.Shimura.Coefficients.CrossCoverEvaluation
import Langlands.Shimura.Coefficients.TorsorSectionSplittingProof
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Invertibility of the associated-sheaf comparison between finite etale torsors -/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

section General

variable {C : Type w} [Category.{v} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable {R : Type u} [CommRing R]
variable {G H : Type u} [Group G] [Group H]

/-- If both covers split sections along translated graphs and the coefficient map
is invertible, the cross-cover map is invertible after localizing at the target
cover. -/
theorem isIso_overPullback_crossCoverMap {Y : Action C G} {Z : Action C H}
    (φ : H →* G) (a : Z ⟶ (Action.res C φ).obj Y)
    (hY : TorsorSectionSplitting (R := R) J Y) (hZ : TorsorSectionSplitting (R := R) J Z)
    {F : Action (Sheaf J (ModuleCat.{u} R)) G}
    {E : Action (Sheaf J (ModuleCat.{u} R)) H}
    (c : (Action.res (Sheaf J (ModuleCat.{u} R)) φ).obj F ⟶ E) (hc : IsIso c.hom) :
    IsIso ((J.overPullback (ModuleCat.{u} R) Z.V).map (crossCoverMap J φ a c)) := by
  have hEZ : IsIso (associatedEvaluation J Z E) := by
    have (U : (Over Z.V)ᵒᵖ) : IsIso ((associatedEvaluation J Z E).hom.app U) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        (associatedEvaluation_bijective J Z E U.unop (hZ E.V U.unop))
    have := NatIso.isIso_of_isIso_app (associatedEvaluation J Z E).hom
    exact (ObjectProperty.isIso_hom_iff _).1 inferInstance
  have hEY : IsIso (associatedEvaluationAlong J Y a.hom F) :=
    ((associatedTrivializationAlongOfSplitting J Y a.hom hY).app F).isIso_hom
  have hcomp : IsIso (associatedEvaluationAlong J Y a.hom F ≫
      (J.overPullback (ModuleCat.{u} R) Z.V).map c.hom) :=
    IsIso.comp_isIso' hEY
      ((J.overPullback (ModuleCat.{u} R) Z.V).mapIso (@asIso _ _ _ _ c.hom hc)).isIso_hom
  exact IsIso.of_isIso_fac_right (crossCoverMap_evaluation J φ a c)

end General

/-- The identity of `X` is a terminal object of the small etale category. -/
def etaleIdIsTerminal (X : Scheme.{u}) : IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom
    (fun W => MorphismProperty.Over.homMk W.hom (Category.comp_id _))
    (fun W m => MorphismProperty.Over.Hom.ext (by
      have h := MorphismProperty.Over.w m
      change _ ≫ 𝟙 X = _ at h
      exact (Category.comp_id _).symm.trans h))

/-- An etale object with surjective structure morphism covers the final object
of the small etale site. -/
theorem etale_coversTop_of_surjective {X : Scheme.{u}} (V : X.Etale)
    (hV : Function.Surjective V.hom) :
    (Scheme.smallEtaleTopology X).CoversTop (fun _ : Unit => V) := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ (etaleIdIsTerminal X)]
  refine GrothendieckTopology.superset_covering _ ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff
      (fun _ : Unit => (etaleIdIsTerminal X).from V)).2 ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact ⟨i, ⟨𝟙 _⟩⟩
  · have hleft : ((etaleIdIsTerminal X).from V).left = V.hom := by
      have h := MorphismProperty.Over.w ((etaleIdIsTerminal X).from V)
      change _ ≫ 𝟙 X = _ at h
      exact (Category.comp_id _).symm.trans h
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨(), ?_⟩
    show x ∈ Set.range ((etaleIdIsTerminal X).from V).left
    rw [hleft]
    exact hV x

/-- Compatible maps between finite geometric etale torsors induce isomorphisms
of the associated coefficient sheaves of restricted representations. -/
theorem etaleAssociatedCoverComparison : EtaleAssociatedCoverComparisonStatement.{u} := by
  intro X G H _ _ Y Z hY hZ φ a R _ M
  refine Sheaf.isIso_of_coversTop (etale_coversTop_of_surjective Z.V hZ.2.2.1) fun _ => ?_
  have hc : IsIso (((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).mapAction
      H).map (𝟙 ((Action.res (ModuleCat.{u} R) φ).obj M))).hom := by
    rw [CategoryTheory.Functor.map_id, Action.id_hom]
    infer_instance
  exact isIso_overPullback_crossCoverMap (Scheme.smallEtaleTopology X) φ a
    (etaleTorsorSectionSplitting X G Y hY R) (etaleTorsorSectionSplitting X H Z hZ R)
    (F := ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).mapAction G).obj M)
    (((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).mapAction H).map
      (𝟙 ((Action.res (ModuleCat.{u} R) φ).obj M))) hc

end Langlands.Shimura.Coefficients
