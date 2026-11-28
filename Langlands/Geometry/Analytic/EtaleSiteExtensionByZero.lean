import Langlands.Sheaf.Equivariant.AnalyticEtaleInvariantPullback
import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleDerived
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-! # Exact extension by zero along an analytic étale map -/

noncomputable section

universe u v r

namespace Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X} (hp : etale p)

private abbrev coverTest : EtaleSite X := MorphismProperty.Over.mk ⊤ p hp

private def toCoverTest (V : EtaleSite Y) : (postcomposeEtale hp).obj V ⟶ coverTest hp :=
  MorphismProperty.Over.homMk V.hom rfl

private abbrev liftedTest {U : EtaleSite X} (a : U ⟶ coverTest hp) : EtaleSite Y :=
  MorphismProperty.Over.mk ⊤ a.left (etale_left a)

private def toPostcompose {U : EtaleSite X} (a : U ⟶ coverTest hp) :
    U ⟶ (postcomposeEtale hp).obj (liftedTest hp a) :=
  MorphismProperty.Over.homMk (𝟙 U.left)
    ((Category.id_comp _).trans (MorphismProperty.Over.w a))

private def liftArrows (U : EtaleSite X) :
    Discrete (U ⟶ coverTest hp) ⥤ CostructuredArrow (postcomposeEtale hp).op (op U) :=
  Discrete.functor fun a => CostructuredArrow.mk (toPostcompose hp a).op

private def toLift (U : EtaleSite X) (d : CostructuredArrow (postcomposeEtale hp).op (op U)) :
    StructuredArrow d (liftArrows hp U) := by
  let a := d.hom.unop ≫ toCoverTest hp d.left.unop
  let f : liftedTest hp a ⟶ d.left.unop := MorphismProperty.Over.homMk d.hom.unop.left rfl
  refine StructuredArrow.mk (Y := Discrete.mk a) (CostructuredArrow.homMk
    (f := d) (f' := (liftArrows hp U).obj (Discrete.mk a)) f.op ?_)
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  exact Category.id_comp _

private theorem factor_left (U : EtaleSite X)
    (d : CostructuredArrow (postcomposeEtale hp).op (op U))
    (s : StructuredArrow d (liftArrows hp U)) :
    s.hom.left.unop.left = d.hom.unop.left := by
  have h := congrArg (fun φ => φ.unop.left) s.hom.w
  change 𝟙 U.left ≫ s.hom.left.unop.left = d.hom.unop.left at h
  simpa only [Category.id_comp] using h

private theorem label_eq_of_hom (U : EtaleSite X)
    (d : CostructuredArrow (postcomposeEtale hp).op (op U))
    (s : StructuredArrow d (liftArrows hp U)) :
    s.right.as = d.hom.unop ≫ toCoverTest hp d.left.unop := by
  apply MorphismProperty.Over.Hom.ext
  change s.right.as.left = d.hom.unop.left ≫ d.left.unop.hom
  rw [← factor_left hp U d s]
  exact (MorphismProperty.Over.w s.hom.left.unop).symm

private theorem liftArrows_map_left (U : EtaleSite X)
    {a b : Discrete (U ⟶ coverTest hp)} (f : a ⟶ b) :
    ((liftArrows hp U).map f).left.unop.left = 𝟙 U.left := by
  have h : a = b := Discrete.ext (Discrete.eq_of_hom f)
  subst b
  have hf : f = 𝟙 a := Subsingleton.elim _ _
  subst f
  rw [CategoryTheory.Functor.map_id]
  rfl

private instance liftArrows_final (U : EtaleSite X) : (liftArrows hp U).Final where
  out d := by
    have : Nonempty (StructuredArrow d (liftArrows hp U)) := ⟨toLift hp U d⟩
    apply zigzag_isConnected
    intro s t
    apply Zigzag.of_hom
    refine StructuredArrow.homMk
      (eqToHom (Discrete.ext ((label_eq_of_hom hp U d s).trans
        (label_eq_of_hom hp U d t).symm))) ?_
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change ((liftArrows hp U).map _).left.unop.left ≫ s.hom.left.unop.left =
      t.hom.left.unop.left
    rw [liftArrows_map_left]
    erw [Category.id_comp]
    rw [factor_left, factor_left]

variable (R : Type r) [CommRing R]
  [EssentiallySmall.{r} (EtaleSite Y)] [LocallySmall.{r} (EtaleSite X)]

local instance (U : (EtaleSite X)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (postcomposeEtale hp).op U) (ModuleCat.{r} R) :=
  hasColimitsOfShape_of_essentiallySmall.{r}
    (CostructuredArrow (postcomposeEtale hp).op U) (ModuleCat.{r} R)

local instance (F : (EtaleSite Y)ᵒᵖ ⥤ ModuleCat.{r} R) :
    (postcomposeEtale hp).op.HasPointwiseLeftKanExtension F :=
  fun _ => inferInstance

private theorem commaColimits_exact (U : (EtaleSite X)ᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (postcomposeEtale hp).op U) (ModuleCat.{r} R) := by
  let e := (Discrete.equivalence (equivShrink.{r} (U.unop ⟶ coverTest hp))).inverse
  exact hasExactColimitsOfShape_of_final (ModuleCat.{r} R) (e ⋙ liftArrows hp U.unop)

private instance : PreservesFiniteLimits ((postcomposeEtale hp).op.lan :
    ((EtaleSite Y)ᵒᵖ ⥤ ModuleCat.{r} R) ⥤ (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{r} R) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{r}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation _ J
  intro U
  have := commaColimits_exact hp R U
  exact preservesLimitsOfShape_of_natIso
    (Langlands.Sheaf.SiteDirectImage.lanEvaluationIso (postcomposeEtale hp) R U).symm

variable [HasSheafify (etaleTopology X) (ModuleCat.{r} R)]

/-- Extension by zero along an étale map, given by sheafifying the left Kan extension
along postcomposition on analytic étale tests. -/
def extensionByZero :
    Sheaf (etaleTopology Y) (ModuleCat.{r} R) ⥤ Sheaf (etaleTopology X) (ModuleCat.{r} R) :=
  Langlands.Sheaf.SiteDirectImage.inverseImage (postcomposeEtale hp) R
    (etaleTopology Y) (etaleTopology X)

/-- Extension by zero is left adjoint to ordinary étale restriction. -/
def extensionByZeroAdjunction :
    extensionByZero hp R ⊣
      (postcomposeEtale hp).sheafPushforwardContinuous (ModuleCat.{r} R)
        (etaleTopology Y) (etaleTopology X) :=
  Langlands.Sheaf.SiteDirectImage.adjunction (postcomposeEtale hp) R
    (etaleTopology Y) (etaleTopology X)

instance extensionByZero_preservesFiniteLimits : PreservesFiniteLimits (extensionByZero hp R) := by
  dsimp only [extensionByZero, Langlands.Sheaf.SiteDirectImage.inverseImage,
    Functor.sheafPullbackConstruction.sheafPullback]
  infer_instance

instance extensionByZero_preservesColimits : PreservesColimits (extensionByZero hp R) :=
  (extensionByZeroAdjunction hp R).leftAdjoint_preservesColimits

/-- Extension by zero is exact on module sheaves. -/
def extensionByZeroExactFunctor :
    Sheaf (etaleTopology Y) (ModuleCat.{r} R) ⥤ₑ Sheaf (etaleTopology X) (ModuleCat.{r} R) :=
  ExactFunctor.of (extensionByZero hp R)

/-- Ordinary étale restriction preserves injectives because its left adjoint is left exact. -/
instance restriction_preservesInjectiveObjects :
    ((postcomposeEtale hp).sheafPushforwardContinuous (ModuleCat.{r} R)
      (etaleTopology Y) (etaleTopology X)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (extensionByZeroAdjunction hp R)

end Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite
