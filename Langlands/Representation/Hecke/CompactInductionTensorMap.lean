import Langlands.Representation.Hecke.CompactInductionComparisonLaws

/-! The natural map from actual Hecke tensor induction to compact induction. -/

noncomputable section

open MeasureTheory CategoryTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open HarmonicAnalysis Langlands.Algebra

universe uG v v'

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μG : Measure G) [μG.IsHaarMeasure]
  (H : Subgroup G) [LocallyCompactSpace H] (hH : IsClosed (H : Set G))
  (μH : Measure H) [μH.IsHaarMeasure]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)

/-- The elementary comparison as an additive pairing on the original carriers. -/
def compactComparisonPairing :
    HeckeAlgebra μG →+ V →+
      Induction.CompactFunctions H
        (Langlands.twist
          (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ) where
  toFun T := (compactComparisonBilinear H hH μH ρ hρ T).toAddMonoidHom
  map_zero' := by
    apply AddMonoidHom.ext
    intro w
    change compactComparisonBilinear H hH μH ρ hρ 0 w = 0
    rw [map_zero, LinearMap.zero_apply]
  map_add' T S := by
    apply AddMonoidHom.ext
    intro w
    exact congrArg (fun f : V →ₗ[ℂ] _ => f w)
      ((compactComparisonBilinear H hH μH ρ hρ).map_add T S)

/-- The pairing is balanced for the retained original Hecke actions. -/
theorem compactComparisonPairing_balanced :
    letI := rightModule μG μH H.subtype continuous_subtype_val
    letI := heckeNonUnitalModule μH ρ hρ
    NonUnitalModuleTensor.IsBalanced (HeckeAlgebra μH)
      (compactComparisonPairing μG H hH μH ρ hρ) := by
  intro a T w
  exact compactComparisonFunction_balanced H hH μH ρ hρ μG T a w

/-- The actual additive lift through the published integer-tensor quotient. -/
def compactComparisonLift :
    letI := rightModule μG μH H.subtype continuous_subtype_val
    letI := heckeNonUnitalModule μH ρ hρ
    NonUnitalModuleTensor.Tensor (HeckeAlgebra μH) (HeckeAlgebra μG) V →+
      Induction.CompactFunctions H
        (Langlands.twist
          (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ) := by
  letI := rightModule μG μH H.subtype continuous_subtype_val
  letI := heckeNonUnitalModule μH ρ hρ
  exact NonUnitalModuleTensor.lift (HeckeAlgebra μH)
    (compactComparisonPairing μG H hH μH ρ hρ)
    (compactComparisonPairing_balanced μG H hH μH ρ hρ)

@[simp] theorem compactComparisonLift_tmul (T : HeckeAlgebra μG) (w : V) :
    letI := rightModule μG μH H.subtype continuous_subtype_val
    letI := heckeNonUnitalModule μH ρ hρ
    compactComparisonLift μG H hH μH ρ hρ
      (NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V T w) =
        compactComparisonFunction H hH μH ρ hρ T w := rfl

/-- A component of the comparison, as a morphism of the exact functors in III.2.6. -/
def compactComparisonHom (W : Langlands.SmoothRep.{0, uG, v} ℂ H) :
    (tensorInductionHeckeFunctor μG H μH).obj W ⟶
      (compactModularHeckeFunctor μG H).obj W := by
  letI := NonUnitalModule.regular (HeckeAlgebra μG)
  letI := rightModule μG μH H.subtype continuous_subtype_val
  letI := heckeNonUnitalModule μH W.representation W.isSmooth
  letI := heckeNonUnitalModule μG
    (Induction.compactInduced H
      (Langlands.twist
        (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom
        W.representation)) (Induction.compactInduced_smooth H _)
  exact ObjectProperty.homMk <|
    NonUnitalBimoduleTensor.leftLift
      (regular_commutes_right μG μH H.subtype continuous_subtype_val)
      (compactComparisonPairing μG H hH μH W.representation W.isSmooth)
      (compactComparisonPairing_balanced μG H hH μH W.representation W.isSmooth)
      (fun a T w => compactComparisonFunction_hecke H hH μH
        W.representation W.isSmooth μG a T w)

@[simp] theorem compactComparisonHom_tmul
    (W : Langlands.SmoothRep.{0, uG, v} ℂ H) (T : HeckeAlgebra μG) (w : W) :
    (compactComparisonHom μG H hH μH W).hom.toAddMonoidHom
      (tensorInductionTmul μG H μH W T w) =
        compactComparisonFunction H hH μH W.representation W.isSmooth T w := rfl

/-- The categorical component retains exactly the additive quotient lift. -/
theorem compactComparisonHom_toAddMonoidHom
    (W : Langlands.SmoothRep.{0, uG, v} ℂ H) :
    (compactComparisonHom μG H hH μH W).hom.toAddMonoidHom =
      compactComparisonLift μG H hH μH W.representation W.isSmooth := rfl

/-- Original subgroup intertwiners commute with elementary comparison values. -/
theorem compactComparisonFunction_map
    {V' : Type v'} [AddCommGroup V'] [Module ℂ V']
    {ρ' : Representation ℂ H V'} (hρ' : IsSmooth ρ')
    (f : ρ.IntertwiningMap ρ') (T : SchwartzBruhat G) (w : V) :
    Induction.compactInducedMap H
      (Langlands.twistIntertwining
        (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom f)
      (compactComparisonFunction H hH μH ρ hρ T w) =
        compactComparisonFunction H hH μH ρ' hρ' T (f w) := by
  ext g
  exact integratedAction_intertwiner μH hρ hρ' f
    (compactSubgroupTest H hH g T) w

/-- The components form a natural transformation of the prescribed functors. -/
def compactComparisonNatTrans :
    tensorInductionHeckeFunctor.{uG, v} μG H μH ⟶
      compactModularHeckeFunctor.{uG, v} μG H where
  app := compactComparisonHom μG H hH μH
  naturality {W W'} f := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro z
    let := rightModule μG μH H.subtype continuous_subtype_val
    let := heckeNonUnitalModule μH W.representation W.isSmooth
    have he := NonUnitalModuleTensor.hom_ext (HeckeAlgebra μH)
      (f := ((compactComparisonHom μG H hH μH W').hom.toAddMonoidHom).comp
        (((tensorInductionHeckeFunctor μG H μH).map f).hom.toAddMonoidHom))
      (g := (((compactModularHeckeFunctor μG H).map f).hom.toAddMonoidHom).comp
        ((compactComparisonHom μG H hH μH W).hom.toAddMonoidHom))
      (fun T w => (compactComparisonFunction_map H hH μH W.representation W.isSmooth
        W'.isSmooth (Langlands.SmoothRep.hom f) T w).symm)
    exact DFunLike.congr_fun he z

end Langlands.Hecke.Homomorphism
