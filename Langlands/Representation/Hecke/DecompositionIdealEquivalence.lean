import Langlands.Representation.Hecke.CentralIdealModuleEquivalence
import Langlands.Representation.Category.DecompositionCentralProjectors

/-! # The factors of a smooth category decomposition as central-ideal modules -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MeasureTheory

namespace Langlands.Hecke

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  (hl : IsSmooth (HarmonicAnalysis.GroupAction.leftTests (G := G)))
  {I : Type w} [DecidableEq I]
  {P : I → ObjectProperty (SmoothRep.{0,u,max u v} ℂ G)}
  (hP : Renard.IsCategoryDecomposition P)
  (hiso : ∀ i {V W}, P i V → (V ≅ W) → P i W)

include hiso in
omit [T2Space G] [NonarchimedeanGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] in
/-- A fixed object is isomorphic to the selected component in its actual coproduct. -/
theorem centralProjector_fixed_iff (i : I) (V : SmoothRep.{0,u,max u v} ℂ G) :
    P i V ↔ (SmoothRep.centralProjector hP i).app V = 𝟙 V := by
  constructor
  · exact SmoothRep.centralProjector_app_of_mem hP i V
  · intro h
    let A := (hP.1 V).choose
    let ι := (hP.1 V).choose_spec.choose
    let hc := (hP.1 V).choose_spec.choose_spec.2.some
    let E : A i ≅ V :=
      { hom := ι i
        inv := SmoothRep.cofanProjection hc i
        hom_inv_id := SmoothRep.inj_cofanProjection_self hc i
        inv_hom_id := h }
    exact hiso i ((hP.1 V).choose_spec.choose_spec.1 i) E

/-- The actual decomposition factor and the fixed-object category have the same objects. -/
def centralProjectorFixedEquivalence (i : I) :
    (P i).FullSubcategory ≌ (centralFixedProperty (SmoothRep.centralProjector hP i)).FullSubcategory := by
  let F : (P i).FullSubcategory ⥤
      (centralFixedProperty (SmoothRep.centralProjector hP i)).FullSubcategory :=
    ObjectProperty.ιOfLE (fun V hV => (centralProjector_fixed_iff hP hiso i V).mp hV)
  letI : F.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj :=
        { mem_essImage V :=
            ⟨⟨V.obj, (centralProjector_fixed_iff hP hiso i V.obj).mpr V.property⟩,
              ⟨(centralFixedProperty (SmoothRep.centralProjector hP i)).isoMk
                (Iso.refl V.obj)⟩⟩ } }
  exact F.asEquivalence

/-- Each iso-stable factor is equivalent to nondegenerate modules over its central Hecke ideal. -/
def decompositionIdealEquivalence (i : I) :
    (P i).FullSubcategory ≌
      Algebra.NondegenerateModuleCat.{u,max u v}
        (centralIdeal μ hl (SmoothRep.centralProjector hP i)) :=
  (centralProjectorFixedEquivalence hP hiso i).trans
    (centralIdealModuleEquivalence μ hl (SmoothRep.centralProjector hP i)
      (SmoothRep.centralProjector_idempotent hP i))

/-- The factor equivalence is the original integrated action restricted to the actual ideal. -/
def decompositionIdealEquivalence_comparison (i : I) :
    (decompositionIdealEquivalence μ hl hP hiso i).functor ⋙
        Algebra.nondegenerateInclusion (centralIdeal μ hl (SmoothRep.centralProjector hP i)) ≅
      (P i).ι ⋙ heckeNondegenerateModuleFunctor μ ⋙
        Algebra.nondegenerateInclusion (HeckeAlgebra μ) ⋙
          Algebra.NonUnitalModuleRestrictScalars.functor
            (NonUnitalSubringClass.subtype (centralIdeal μ hl (SmoothRep.centralProjector hP i))) :=
  Iso.refl _

end Langlands.Hecke
