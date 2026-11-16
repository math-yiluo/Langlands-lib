import Langlands.Sheaf.Equivariant.TwistedGodement
import Mathlib.CategoryTheory.Limits.Final

/-!
# Product coordinates for induction on the twisted site
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates

open CategoryTheory CategoryTheory.Limits Opposite

universe v u uG uA vA

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] (ρ : G →* Aut X)

/-- The inverse relabellings form a discrete family in the right Kan indexing category. -/
def arrows (U : TwistedOver P ρ) :
    Discrete G ⥤ StructuredArrow (op U) (ι P ρ).op :=
  Discrete.functor fun g =>
    StructuredArrow.mk (Y := op ((translate P ρ g).obj U.obj))
      (relabelInv ρ g U.obj).op

/-- An arrow from a coordinate forces its index to be the inverse twist. -/
theorem index_eq (U : TwistedOver P ρ)
    (d : StructuredArrow (op U) (ι P ρ).op) (g : Discrete G)
    (s : (arrows ρ U).obj g ⟶ d) :
    g.as = (Hom.twist d.hom.unop)⁻¹ := by
  have h := congrArg (fun f => Hom.twist f.unop) (StructuredArrow.w s)
  change g.as⁻¹ * 1 = Hom.twist d.hom.unop at h
  simpa only [mul_one, inv_inv] using congrArg Inv.inv h

/-- The ordinary map obtained by cancelling the twist at the target. -/
def factor (U : TwistedOver P ρ) (d : StructuredArrow (op U) (ι P ρ).op) :
    d.right.unop ⟶ (translate P ρ (Hom.twist d.hom.unop)⁻¹).obj U.obj :=
  MorphismProperty.Over.homMk (Hom.left d.hom.unop) (by
    change Hom.left d.hom.unop ≫ (U.hom ≫ (ρ (Hom.twist d.hom.unop)⁻¹).hom) = _
    rw [← Category.assoc, Hom.w, Category.assoc, rho_hom_inv_hom, Category.comp_id]
    rfl)

/-- The factorization recovers the original twisted arrow. -/
theorem factor_comp_relabelInv (U : TwistedOver P ρ)
    (d : StructuredArrow (op U) (ι P ρ).op) :
    (ι P ρ).map (factor ρ U d) ≫
      relabelInv ρ (Hom.twist d.hom.unop)⁻¹ U.obj = d.hom.unop := by
  apply hom_ext
  · change (Hom.twist d.hom.unop)⁻¹⁻¹ * 1 = Hom.twist d.hom.unop
    simp
  · change Hom.left d.hom.unop ≫ 𝟙 _ = Hom.left d.hom.unop
    exact Category.comp_id _

/-- Each indexing arrow is reached from the coordinate with its inverse twist. -/
def fromCoordinate (U : TwistedOver P ρ)
    (d : StructuredArrow (op U) (ι P ρ).op) :
    CostructuredArrow (arrows ρ U) d :=
  CostructuredArrow.mk (Y := (⟨(Hom.twist d.hom.unop)⁻¹⟩ : Discrete G))
    (StructuredArrow.homMk (factor ρ U d).op
      (Quiver.Hom.unop_inj (factor_comp_relabelInv ρ U d)))

/-- The map from a fixed coordinate is unique, since its underlying relabelling is identity. -/
instance hom_subsingleton (U : TwistedOver P ρ)
    (d : StructuredArrow (op U) (ι P ρ).op) (g : Discrete G) :
    Subsingleton ((arrows ρ U).obj g ⟶ d) :=
  ⟨fun a b => by
    apply StructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    have ha := congrArg (fun f => Hom.left f.unop) (StructuredArrow.w a)
    have hb := congrArg (fun f => Hom.left f.unop) (StructuredArrow.w b)
    change a.right.unop.left ≫ 𝟙 _ = Hom.left d.hom.unop at ha
    change b.right.unop.left ≫ 𝟙 _ = Hom.left d.hom.unop at hb
    simpa only [Category.comp_id] using ha.trans hb.symm⟩

/-- The inverse relabellings are initial in the pointwise right Kan indexing category. -/
instance arrows_initial (U : TwistedOver P ρ) : (arrows ρ U).Initial where
  out d := by
    have : Nonempty (CostructuredArrow (arrows ρ U) d) := ⟨fromCoordinate ρ U d⟩
    apply zigzag_isConnected
    intro s t
    apply Zigzag.of_hom
    exact CostructuredArrow.homMk (eqToHom (Discrete.ext
      ((index_eq ρ U d _ s.hom).trans (index_eq ρ U d _ t.hom).symm)))
      (Subsingleton.elim _ _)

section Coordinates

variable {A : Type uA} [Category.{vA} A]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ A, (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The translated coefficient objects at a twisted object. -/
def objects (F : (P.Over ⊤ X)ᵒᵖ ⥤ A) (U : TwistedOver P ρ) (g : G) : A :=
  F.obj (op ((translate P ρ g).obj U.obj))

/-- The coordinate projection of the actual right Kan extension. -/
def projection (F : (P.Over ⊤ X)ᵒᵖ ⥤ A) (U : TwistedOver P ρ) (g : G) :
    ((ι P ρ).op.ran.obj F).obj (op U) ⟶ objects ρ F U g :=
  ((ι P ρ).op.ran.obj F).map (relabelInv ρ g U.obj).op ≫
    ((ι P ρ).op.ranCounit.app F).app (op ((translate P ρ g).obj U.obj))

/-- The actual right Kan extension is the vertex of the translated-coordinate fan. -/
def fan (F : (P.Over ⊤ X)ᵒᵖ ⥤ A) (U : TwistedOver P ρ) :
    Fan (objects ρ F U) :=
  Fan.mk _ (projection ρ F U)

/-- The coordinate fan is limiting by initiality of the inverse relabellings. -/
def fanIsLimit (F : (P.Over ⊤ X)ᵒᵖ ⥤ A) (U : TwistedOver P ρ) :
    IsLimit (fan ρ F U) := by
  let c := (Functor.RightExtension.mk _ ((ι P ρ).op.ranCounit.app F)).coneAt (op U)
  let h := (Functor.Initial.isLimitWhiskerEquiv (arrows ρ U) c).symm
    ((ι P ρ).op.isPointwiseRightKanExtensionRanCounit F (op U))
  let e : arrows ρ U ⋙ StructuredArrow.proj (op U) (ι P ρ).op ⋙ F ≅
      Discrete.functor (objects ρ F U) := Discrete.natIso fun _ => Iso.refl _
  exact IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv e _).symm h)
    (Cone.ext (Iso.refl _) (by
      intro j
      change projection ρ F U j.as ≫ 𝟙 _ = 𝟙 _ ≫ projection ρ F U j.as
      simp))

variable [HasProducts.{uG} A]

/-- Product coordinates for the actual right Kan extension. -/
def productIso (F : (P.Over ⊤ X)ᵒᵖ ⥤ A) (U : TwistedOver P ρ) :
    ((ι P ρ).op.ran.obj F).obj (op U) ≅ ∏ᶜ (objects ρ F U) :=
  (fanIsLimit ρ F U).conePointUniqueUpToIso (productIsProduct (objects ρ F U))

/-- Each product projection is the corresponding inverse relabelling followed by the counit. -/
@[reassoc (attr := simp)]
theorem productIso_hom_π (F : (P.Over ⊤ X)ᵒᵖ ⥤ A) (U : TwistedOver P ρ) (g : G) :
    (productIso ρ F U).hom ≫ Pi.π (objects ρ F U) g = projection ρ F U g :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk g)

/-- The inverse product comparison recovers the coordinate projections. -/
@[reassoc (attr := simp)]
theorem productIso_inv_projection (F : (P.Over ⊤ X)ᵒᵖ ⥤ A)
    (U : TwistedOver P ρ) (g : G) :
    (productIso ρ F U).inv ≫ projection ρ F U g = Pi.π (objects ρ F U) g :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk g)

variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]

/-- The same product comparison for the existing induction of sheaves. -/
def sheafProductIso (F : Sheaf J A) (U : TwistedOver P ρ) :
    ((induction ρ J A).obj F).obj.obj (op U) ≅ ∏ᶜ (objects ρ F.obj U) :=
  productIso ρ F.obj U

end Coordinates

end Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates
