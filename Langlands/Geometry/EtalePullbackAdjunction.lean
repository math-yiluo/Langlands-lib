/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The proof of lanEvaluationIso adapts Mathlib CategoryTheory/Functor/Flat.lean,
lanEvaluationIsoColim, to the universes of the small etale sites.
-/
import Langlands.Geometry.EtalePullback
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.ModuleCat.AB

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

/-- Lifts of an étale object over X to an object over Y. -/
abbrev Lift (U : X.Etale) := {s : U.left ⟶ Y // s ≫ f = U.hom}

/-- A lift has an étale structure map. -/
def liftObject (U : X.Etale) (s : Lift f U) : Y.Etale :=
  have : Etale (s.val ≫ f) := by rw [s.property]; infer_instance
  MorphismProperty.Over.mk ⊤ s.val (Etale.of_comp s.val f)

/-- A lift gives an arrow with identity underlying scheme map. -/
def liftArrow (U : X.Etale) (s : Lift f U) :
    U ⟶ (siteMap f).obj (liftObject f U s) :=
  MorphismProperty.Over.homMk (𝟙 U.left) (by simpa [liftObject] using s.property)

/-- The discrete family of lifts as costructured arrows. -/
def liftArrows (U : X.Etale) :
    Discrete (Lift f U) ⥤ CostructuredArrow (siteMap f).op (op U) :=
  Discrete.functor fun s => CostructuredArrow.mk (liftArrow f U s).op

/-- The lift determined by an arbitrary costructured arrow. -/
def arrowLift (U : X.Etale) (d : CostructuredArrow (siteMap f).op (op U)) : Lift f U :=
  ⟨d.hom.unop.left ≫ d.left.unop.hom, by
    rw [Category.assoc]
    exact d.hom.unop.w⟩

/-- Every arrow factors through its determined lift. -/
def toLift (U : X.Etale) (d : CostructuredArrow (siteMap f).op (op U)) :
    StructuredArrow d (liftArrows f U) :=
  StructuredArrow.mk (Y := Discrete.mk (arrowLift f U d))
    (CostructuredArrow.homMk
      (MorphismProperty.Over.homMk
        (A := liftObject f U (arrowLift f U d)) (B := d.left.unop)
        d.hom.unop.left (by rfl)).op (by
        apply Quiver.Hom.unop_inj
        apply MorphismProperty.Over.Hom.ext
        exact Category.id_comp _))

/-- A factorization through a lift has the original underlying scheme arrow. -/
theorem factor_left (U : X.Etale) (d : CostructuredArrow (siteMap f).op (op U))
    (s : StructuredArrow d (liftArrows f U)) :
    s.hom.left.unop.left = d.hom.unop.left := by
  have h := congrArg (fun a => a.unop.left) s.hom.w
  change 𝟙 U.left ≫ s.hom.left.unop.left = d.hom.unop.left at h
  simpa using h

/-- The index of a factorization is the determined lift. -/
theorem lift_eq_of_hom (U : X.Etale) (d : CostructuredArrow (siteMap f).op (op U))
    (s : StructuredArrow d (liftArrows f U)) :
    s.right.as = arrowLift f U d := by
  apply Subtype.ext
  have h := s.hom.left.unop.w
  change s.hom.left.unop.left ≫ d.left.unop.hom = s.right.as.val at h
  rw [factor_left f U d s] at h
  exact h.symm

theorem liftArrows_map_left (U : X.Etale) {s t : Discrete (Lift f U)} (h : s ⟶ t) :
    ((liftArrows f U).map h).left.unop.left = 𝟙 U.left := by
  have hst : s = t := Discrete.ext (Discrete.eq_of_hom h)
  subst t
  have hh : h = 𝟙 s := Subsingleton.elim _ _
  subst h
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The discrete lifts form a final family in the costructured-arrow category. -/
instance liftArrows_final (U : X.Etale) : (liftArrows f U).Final where
  out d := by
    have : Nonempty (StructuredArrow d (liftArrows f U)) := ⟨toLift f U d⟩
    apply zigzag_isConnected
    intro s t
    apply Zigzag.of_hom
    refine StructuredArrow.homMk
      (eqToHom (Discrete.ext (by rw [lift_eq_of_hom, lift_eq_of_hom]))) ?_
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change ((liftArrows f U).map _).left.unop.left ≫ s.hom.left.unop.left =
      t.hom.left.unop.left
    rw [liftArrows_map_left]
    erw [Category.id_comp]
    rw [factor_left, factor_left]

variable (R : Type u) [CommRing R]

/-- The large comma category has colimits of module-valued diagrams because
its final family of lifts is small. -/
instance liftComma_hasColimits (U : X.Etaleᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (siteMap f).op U) (ModuleCat.{u} R) :=
  Functor.Final.hasColimitsOfShape_of_final (liftArrows f U.unop)

/-- These colimits are exact, being coproducts of modules. -/
instance liftComma_hasExactColimits (U : X.Etaleᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (siteMap f).op U) (ModuleCat.{u} R) :=
  hasExactColimitsOfShape_of_final (ModuleCat.{u} R) (liftArrows f U.unop)

instance hasPointwiseLeftKanExtension (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} R) :
    (siteMap f).op.HasPointwiseLeftKanExtension F :=
  fun U => (liftComma_hasColimits f R U).has_colimit _

/-- Evaluation of left Kan extension is the corresponding comma colimit,
with universes appropriate for the large small-étale sites. -/
def lanEvaluationIso (U : X.Etaleᵒᵖ) :
    (siteMap f).op.lan ⋙ (evaluation X.Etaleᵒᵖ (ModuleCat.{u} R)).obj U ≅
      (Functor.whiskeringLeft _ _ (ModuleCat.{u} R)).obj
        (CostructuredArrow.proj (siteMap f).op U) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (siteMap f).op G U)
      (colimit.isColimit _)) (fun {G₁ G₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (siteMap f).op G₁ U).hom_ext
    intro T
    have h₁ := fun (G : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} R) =>
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (siteMap f).op G U)
        (colimit.isColimit _) T
    have h₂ := congr_app ((siteMap f).op.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

/-- Left Kan extension along the opposite site map preserves finite limits. -/
instance lan_preservesFiniteLimits :
    PreservesFiniteLimits ((siteMap f).op.lan :
      (Y.Etaleᵒᵖ ⥤ ModuleCat.{u} R) ⥤ X.Etaleᵒᵖ ⥤ ModuleCat.{u} R) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation _ J
  intro U
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIso f R U).symm

/-- The left adjoint of étale restriction: sheafified left Kan extension. -/
def extension :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  Functor.sheafPullbackConstruction.sheafPullback (siteMap f)
    (ModuleCat.{u} R) Y.smallEtaleTopology X.smallEtaleTopology

/-- The extension and restriction adjunction. -/
def extensionAdjunction : extension f R ⊣ restriction f (ModuleCat.{u} R) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (siteMap f)
    (ModuleCat.{u} R) Y.smallEtaleTopology X.smallEtaleTopology

instance extension_preservesFiniteLimits : PreservesFiniteLimits (extension f R) := by
  dsimp only [extension, Functor.sheafPullbackConstruction.sheafPullback]
  infer_instance

instance extension_preservesColimits : PreservesColimits (extension f R) :=
  (extensionAdjunction f R).leftAdjoint_preservesColimits

instance restriction_preservesLimits : PreservesLimits (restriction f (ModuleCat.{u} R)) :=
  (extensionAdjunction f R).rightAdjoint_preservesLimits

/-- Restriction along an étale morphism preserves injective module sheaves. -/
instance restriction_preservesInjectiveObjects :
    (restriction f (ModuleCat.{u} R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (extensionAdjunction f R)

end Langlands.Geometry.EtalePullback
