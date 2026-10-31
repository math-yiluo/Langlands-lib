import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartLimits
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRepresentatives
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Coefficient pullback preserves finite limits of actual rational charts -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A B : PresentedAffinoidAlgebra K}

private theorem hom_unique {d e : RationalChart K B} (f g : d ⟶ e) : f = g :=
  @Subsingleton.elim (Restriction d e) inferInstance f g

/-- Multiplicativity identifies the denominator classes of the two chosen
intersection presentations after coefficient change. -/
theorem pullback_inter_denominator_class (φ : BoundedAlgHom K A B)
    (d e : RationalChart K A) :
    presentationMap K B (pullback φ (d.inter e)).denominator =
      presentationMap K B ((pullback φ d).inter (pullback φ e)).denominator := by
  simp [inter, pullback_denominator_class]

private theorem pullback_extended_class (φ : BoundedAlgHom K A B)
    (d : RationalChart K A) (j : Fin (d.arity + 1)) :
    φ (presentationMap K A
      (Fin.cons (n := d.arity) (α := fun _ => GeneralizedTateAlgebra A.polyradius K)
        d.denominator d.numerators j)) =
      presentationMap K B
        (Fin.cons (n := d.arity) (α := fun _ => GeneralizedTateAlgebra B.polyradius K)
          (pullback φ d).denominator (pullback φ d).numerators j) := by
  induction j using Fin.cases with
  | zero => exact (pullback_denominator_class φ d).symm
  | succ j => exact (pullback_numerator_class φ d j).symm

/-- Every product of denominator-extended numerators has the same coefficient
class in direct pullback and intersection after pullback. -/
theorem pullback_inter_numerator_class (φ : BoundedAlgHom K A B)
    (d e : RationalChart K A) (a : Fin ((d.arity + 1) * (e.arity + 1))) :
    presentationMap K B ((pullback φ (d.inter e)).numerators a) =
      presentationMap K B (((pullback φ d).inter (pullback φ e)).numerators a) := by
  rw [pullback_numerator_class φ (d.inter e) a]
  simp only [inter, RationalPresentation.RationalIntersection.numerators, map_mul]
  congr 1
  · exact pullback_extended_class φ d (finProdFinEquiv.symm a).1
  · exact pullback_extended_class φ e (finProdFinEquiv.symm a).2

/-- Actual bounded representative maps compare pullback of the all-products
intersection with the intersection of the two pulled-back charts. -/
def pullbackInterIso (φ : BoundedAlgHom K A B) (d e : RationalChart K A) :
    pullback φ (d.inter e) ≅ (pullback φ d).inter (pullback φ e) where
  hom := {
    restriction := RationalPresentation.representativeMap K B (d.inter e).radii
      ((pullback φ d).inter (pullback φ e)).denominator
      (pullback φ (d.inter e)).denominator
      ((pullback φ d).inter (pullback φ e)).numerators
      (pullback φ (d.inter e)).numerators
      (pullback_inter_denominator_class φ d e).symm
      (fun a => (pullback_inter_numerator_class φ d e a).symm)
    comp_baseMap := BoundedAlgHom.ext
      (RationalPresentation.representativeMap_baseMap K B (d.inter e).radii
        ((pullback φ d).inter (pullback φ e)).denominator
        (pullback φ (d.inter e)).denominator
        ((pullback φ d).inter (pullback φ e)).numerators
        (pullback φ (d.inter e)).numerators
        (pullback_inter_denominator_class φ d e).symm
        (fun a => (pullback_inter_numerator_class φ d e a).symm)) }
  inv := {
    restriction := RationalPresentation.representativeMap K B (d.inter e).radii
      (pullback φ (d.inter e)).denominator
      ((pullback φ d).inter (pullback φ e)).denominator
      (pullback φ (d.inter e)).numerators
      ((pullback φ d).inter (pullback φ e)).numerators
      (pullback_inter_denominator_class φ d e)
      (pullback_inter_numerator_class φ d e)
    comp_baseMap := BoundedAlgHom.ext
      (RationalPresentation.representativeMap_baseMap K B (d.inter e).radii
        (pullback φ (d.inter e)).denominator
        ((pullback φ d).inter (pullback φ e)).denominator
        (pullback φ (d.inter e)).numerators
        ((pullback φ d).inter (pullback φ e)).numerators
        (pullback_inter_denominator_class φ d e)
        (pullback_inter_numerator_class φ d e)) }
  hom_inv_id := hom_unique _ _
  inv_hom_id := hom_unique _ _

/-- Chosen coefficient representatives of one give an actual comparison with
the whole chart over the new coefficient algebra. -/
def pullbackWholeIso (φ : BoundedAlgHom K A B) :
    pullback φ (whole K A) ≅ whole K B where
  hom := {
    restriction := RationalPresentation.representativeMap K B (whole K B).radii
      (whole K B).denominator (pullback φ (whole K A)).denominator
      (whole K B).numerators (pullback φ (whole K A)).numerators
      (by simp [whole]) (fun j => Fin.elim0 j)
    comp_baseMap := BoundedAlgHom.ext
      (RationalPresentation.representativeMap_baseMap K B (whole K B).radii
        (whole K B).denominator (pullback φ (whole K A)).denominator
        (whole K B).numerators (pullback φ (whole K A)).numerators
        (by simp [whole]) (fun j => Fin.elim0 j)) }
  inv := {
    restriction := RationalPresentation.representativeMap K B (whole K B).radii
      (pullback φ (whole K A)).denominator (whole K B).denominator
      (pullback φ (whole K A)).numerators (whole K B).numerators
      (by simp [whole]) (fun j => Fin.elim0 j)
    comp_baseMap := BoundedAlgHom.ext
      (RationalPresentation.representativeMap_baseMap K B (whole K B).radii
        (pullback φ (whole K A)).denominator (whole K B).denominator
        (pullback φ (whole K A)).numerators (whole K B).numerators
        (by simp [whole]) (fun j => Fin.elim0 j)) }
  hom_inv_id := hom_unique _ _
  inv_hom_id := hom_unique _ _

variable [CompleteSpace K]

@[simp]
theorem pullbackInterIso_hom_interLeft (φ : BoundedAlgHom K A B)
    (d e : RationalChart K A) :
    (pullbackInterIso φ d e).hom ≫ interLeft (pullback φ d) (pullback φ e) =
      (pullbackFunctor φ).map (interLeft d e) :=
  hom_unique _ _

@[simp]
theorem pullbackInterIso_hom_interRight (φ : BoundedAlgHom K A B)
    (d e : RationalChart K A) :
    (pullbackInterIso φ d e).hom ≫ interRight (pullback φ d) (pullback φ e) =
      (pullbackFunctor φ).map (interRight d e) :=
  hom_unique _ _

/-- A cone over the image cospan lifts by the constructed intersection lift,
followed by the actual inverse representative comparison. -/
def pullbackInterPullbackConeIsLimit (φ : BoundedAlgHom K A B)
    {d e b : RationalChart K A} (f : d ⟶ b) (g : e ⟶ b) :
    IsLimit ((interPullbackCone f g).map (pullbackFunctor φ)) :=
  PullbackCone.IsLimit.mk _
    (fun S => interLift S.fst S.snd ≫ (pullbackInterIso φ d e).inv)
    (fun _ => hom_unique _ _) (fun _ => hom_unique _ _)
    (fun _ _ _ _ => hom_unique _ _)

instance pullbackFunctor_preservesCospan (φ : BoundedAlgHom K A B)
    {d e b : RationalChart K A} (f : d ⟶ b) (g : e ⟶ b) :
    PreservesLimit (cospan f g) (pullbackFunctor φ) :=
  preservesLimit_of_preserves_limit_cone (interPullbackConeIsLimit f g)
    ((PullbackCone.isLimitMapConeEquiv _ _).symm
      (pullbackInterPullbackConeIsLimit φ f g))

instance pullbackFunctor_preservesPullbacks (φ : BoundedAlgHom K A B) :
    PreservesLimitsOfShape WalkingCospan (pullbackFunctor φ) where
  preservesLimit {J} :=
    preservesLimit_of_iso_diagram (pullbackFunctor φ) (diagramIsoCospan J).symm

/-- The actual representative comparison transports the proved terminal
property of the whole chart over B. -/
def pullbackWholeIsTerminal (φ : BoundedAlgHom K A B) :
    IsTerminal (pullback φ (whole K A)) :=
  (wholeIsTerminal K B).ofIso (pullbackWholeIso φ).symm

instance pullbackFunctor_preservesTerminal (φ : BoundedAlgHom K A B) :
    PreservesLimit (Functor.empty.{0} (RationalChart K A)) (pullbackFunctor φ) :=
  preservesLimit_of_preserves_limit_cone (wholeIsTerminal K A)
    ((isLimitMapConeEmptyConeEquiv _ _).symm (pullbackWholeIsTerminal φ))

instance pullbackFunctor_preservesEmpty (φ : BoundedAlgHom K A B) :
    PreservesLimitsOfShape (Discrete.{0} PEmpty) (pullbackFunctor φ) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal (pullbackFunctor φ)

/-- Preservation of the constructed terminal chart and intersection pullbacks
gives preservation of every finite chart-category limit. -/
instance pullbackFunctor_preservesFiniteLimits (φ : BoundedAlgHom K A B) :
    PreservesFiniteLimits (pullbackFunctor φ) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks (pullbackFunctor φ)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
