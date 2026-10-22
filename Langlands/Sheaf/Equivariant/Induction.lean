import Langlands.Sheaf.Equivariant.Abelian
import Langlands.Sheaf.Equivariant.Limits
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Induction of sheaves to equivariant sheaves

Forgetting equivariance has an exact left adjoint, so it sends injective
equivariant module sheaves to injective ordinary sheaves.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace ActionOpens

variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]

/-- The translates of an open, with their labelled arrows, as costructured
arrows for the inclusion of ordinary opens. -/
def translateArrows (U : ActionOpens G X) :
    Discrete G ⥤ CostructuredArrow (inclusion G X).op (op U) :=
  Discrete.functor fun g =>
    CostructuredArrow.mk (Y := op (translate g U).openSet) (translationIso g U).hom.op

/-- A factorization through a translate forces the translating element to be
the label of the arrow. -/
theorem label_eq_of_hom (U : ActionOpens G X) (d : CostructuredArrow (inclusion G X).op (op U))
    (s : StructuredArrow d (translateArrows U)) : s.right.as = d.hom.unop.label := by
  have h := congrArg (fun φ => φ.unop.label) s.hom.w
  simp only [translateArrows, Discrete.functor_obj_eq_as, unop_comp, comp_label] at h
  change 1 * s.right.as = d.hom.unop.label * 1 at h
  simpa using h

/-- Every costructured arrow factors through the translate by its label. -/
def toTranslate (U : ActionOpens G X) (d : CostructuredArrow (inclusion G X).op (op U)) :
    StructuredArrow d (translateArrows U) :=
  have h : (translate d.hom.unop.label U).openSet ≤ d.left.unop := translate_le d.hom.unop
  StructuredArrow.mk (Y := (⟨d.hom.unop.label⟩ : Discrete G))
    (CostructuredArrow.homMk (f := d) (f' := (translateArrows U).obj ⟨d.hom.unop.label⟩)
      (homOfLE h).op (by
      apply Quiver.Hom.unop_inj
      apply Hom.ext
      change (1 : G) * d.hom.unop.label = d.hom.unop.label
      rw [one_mul]))

/-- The translates of an open are final among its costructured arrows. -/
instance translateArrows_final (U : ActionOpens G X) : (translateArrows U).Final where
  out d := by
    have : Nonempty (StructuredArrow d (translateArrows U)) := ⟨toTranslate U d⟩
    apply zigzag_isConnected
    intro s t
    apply Zigzag.of_hom
    refine StructuredArrow.homMk
      (eqToHom (Discrete.ext (by rw [label_eq_of_hom, label_eq_of_hom]))) ?_
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply Subsingleton.elim

end ActionOpens

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] (X : Type u) [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]

/-- Colimits over the costructured arrows of an open are exact, since the
translates of the open form a final discrete family. -/
instance costructuredArrow_hasExactColimitsOfShape (U : (ActionOpens G X)ᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (ActionOpens.inclusion G X).op U)
      (ModuleCat.{u} R) :=
  hasExactColimitsOfShape_of_final (ModuleCat.{u} R) (ActionOpens.translateArrows U.unop)

/-- Left Kan extension of module presheaves along the inclusion of ordinary
opens is exact. -/
instance lan_preservesFiniteLimits :
    PreservesFiniteLimits ((ActionOpens.inclusion G X).op.lan :
      ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation _ J
  intro U
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim _ _ _).symm

/-- Induction to transport sheaves: left Kan extension followed by sheafification. -/
def transportInduction :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤
      Sheaf (transportTopology G X) (ModuleCat.{u} R) :=
  Functor.sheafPullbackConstruction.sheafPullback (ActionOpens.inclusion G X)
    (ModuleCat.{u} R) (Opens.grothendieckTopology X) (transportTopology G X)

instance transportInduction_preservesFiniteLimits :
    PreservesFiniteLimits (transportInduction R G X) := by
  dsimp only [transportInduction, Functor.sheafPullbackConstruction.sheafPullback]
  infer_instance

/-- Induction from ordinary module sheaves to equivariant module sheaves. -/
def induction :
    TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X) ⥤ TopologicalSheaf G X (ModuleCat.{u} R) :=
  transportInduction R G X ⋙ (sheafEquivalence G X (ModuleCat.{u} R)).inverse

instance induction_preservesFiniteLimits : PreservesFiniteLimits (induction R G X) := by
  have := (sheafEquivalence G X (ModuleCat.{u} R)).toAdjunction.rightAdjoint_preservesLimits
  exact comp_preservesFiniteLimits (transportInduction R G X)
    (sheafEquivalence G X (ModuleCat.{u} R)).inverse

/-- Restricting a transport sheaf to ordinary opens is forgetting equivariance. -/
def pushforwardIso :
    (sheafEquivalence G X (ModuleCat.{u} R)).functor ⋙
        (ActionOpens.inclusion G X).sheafPushforwardContinuous (ModuleCat.{u} R)
          (Opens.grothendieckTopology X) (transportTopology G X) ≅
      toSheaf G X (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Induction is left adjoint to forgetting equivariance. -/
def inductionAdjunction : induction R G X ⊣ toSheaf G X (ModuleCat.{u} R) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (ActionOpens.inclusion G X)
    (ModuleCat.{u} R) (Opens.grothendieckTopology X) (transportTopology G X)).comp
      (sheafEquivalence G X (ModuleCat.{u} R)).symm.toAdjunction).ofNatIsoRight
    (pushforwardIso R G X)

/-- Forgetting equivariance sends injective equivariant module sheaves to
injective sheaves. -/
instance toSheaf_preservesInjectiveObjects :
    (toSheaf G X (ModuleCat.{u} R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (inductionAdjunction R G X)

end Langlands.Sheaf.Equivariant
