import Langlands.Sheaf.Equivariant.TwistedCompactComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Left induction to sheaves on a twisted site

Restriction of module sheaves from the twisted site of a `G`-object `X` to the site over `X`
has a right adjoint, `induction` (the right Kan extension along the inclusion `ι`), and also a
left adjoint, `leftInduction`: the left Kan extension along `ι` followed by sheafification.
Left induction preserves finite limits when coproducts of modules indexed by `G` exist and are
exact. So restriction sends injective sheaves on the twisted site to injective sheaves over
`X`. The left Kan extension at an object `V` is computed over the costructured arrows of `V`;
the translates `gV`, with their relabelling arrows, are final among them.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u uG

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] (ρ : G →* Aut X)

section Translates

/-- The translates `gV` of an object `V` of the twisted category, with their relabelling
arrows `V ⟶ gV`, as costructured arrows for the opposite of the inclusion `ι`. -/
def translateArrows (V : TwistedOver P ρ) :
    Discrete G ⥤ CostructuredArrow (ι P ρ).op (op V) :=
  Discrete.functor fun g =>
    CostructuredArrow.mk (Y := op ((translate P ρ g).obj V.obj)) (relabel ρ g V.obj).op

variable {ρ}

/-- A morphism from a costructured arrow `d` to the translate by `g` forces `g` to be the
twist of the arrow of `d`. -/
theorem twist_eq_of_hom_translateArrows (V : TwistedOver P ρ) (d : CostructuredArrow (ι P ρ).op (op V))
    (j : Discrete G) (s : d ⟶ (translateArrows ρ V).obj j) :
    j.as = Hom.twist d.hom.unop := by
  have h := congrArg (fun φ => Hom.twist φ.unop) (CostructuredArrow.w s)
  change Hom.twist ((ι P ρ).map s.left.unop) * j.as = Hom.twist d.hom.unop at h
  rw [ι_map_twist, one_mul] at h
  exact h

/-- Morphisms from a costructured arrow to a translate are unique: the relabelling arrow is
invertible and `ι` is faithful. -/
instance translateArrows_hom_subsingleton (V : TwistedOver P ρ) (d : CostructuredArrow (ι P ρ).op (op V))
    (j : Discrete G) : Subsingleton (d ⟶ (translateArrows ρ V).obj j) :=
  ⟨fun a b => by
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply (ι P ρ).map_injective
    have ha : relabel ρ j.as V.obj ≫ (ι P ρ).map a.left.unop = d.hom.unop :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w a)
    have hb : relabel ρ j.as V.obj ≫ (ι P ρ).map b.left.unop = d.hom.unop :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w b)
    exact (cancel_epi (relabel ρ j.as V.obj)).1 (ha.trans hb.symm)⟩

variable (ρ) in
/-- Every costructured arrow factors through the translate by the twist of its arrow. -/
def toTranslate (V : TwistedOver P ρ) (d : CostructuredArrow (ι P ρ).op (op V)) :
    StructuredArrow d (translateArrows ρ V) :=
  StructuredArrow.mk (Y := (⟨Hom.twist d.hom.unop⟩ : Discrete G))
    (CostructuredArrow.homMk (f := d) (f' := (translateArrows ρ V).obj ⟨Hom.twist d.hom.unop⟩)
      (untwist (U := V.obj) (V := d.left.unop) (Hom.twist d.hom.unop) d.hom.unop rfl).op
      (Quiver.Hom.unop_inj
        (relabel_comp_ι_map_untwist (U := V.obj) (V := d.left.unop) _ d.hom.unop rfl)))

/-- The translates of an object are final among its costructured arrows. -/
instance translateArrows_final (V : TwistedOver P ρ) : (translateArrows ρ V).Final where
  out d := by
    have : Nonempty (StructuredArrow d (translateArrows ρ V)) := ⟨toTranslate ρ V d⟩
    apply zigzag_isConnected
    intro s t
    apply Zigzag.of_hom
    exact StructuredArrow.homMk (eqToHom (Discrete.ext ((twist_eq_of_hom_translateArrows V d _ s.hom).trans
      (twist_eq_of_hom_translateArrows V d _ t.hom).symm))) (Subsingleton.elim _ _)

end Translates

section Exact

variable (R : Type w) [CommRing R]

omit [Group G] in
/-- Coproducts of modules indexed by a `w`-small group exist. -/
theorem discrete_hasColimitsOfShape [Small.{w} G] :
    HasColimitsOfShape (Discrete G) (ModuleCat.{w} R) :=
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{w} G)).symm

omit [Group G] in
/-- Coproducts of modules indexed by a `w`-small group are exact. -/
theorem discrete_hasExactColimitsOfShape [Small.{w} G] :
    haveI := discrete_hasColimitsOfShape.{w} (G := G) R
    HasExactColimitsOfShape (Discrete G) (ModuleCat.{w} R) :=
  HasExactColimitsOfShape.of_domain_equivalence _ (Discrete.equivalence (equivShrink.{w} G)).symm

variable [HasColimitsOfShape (Discrete G) (ModuleCat.{w} R)]

/-- Colimits of modules over the costructured arrows of an object exist: the translates are
final, and coproducts indexed by `G` exist. -/
instance costructuredArrow_hasColimitsOfShape (V : (TwistedOver P ρ)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (ι P ρ).op V) (ModuleCat.{w} R) :=
  Functor.Final.hasColimitsOfShape_of_final (translateArrows ρ V.unop)

/-- Every module presheaf over `X` has a pointwise left Kan extension along `ι`. -/
instance hasPointwiseLeftKanExtension (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) :
    (ι P ρ).op.HasPointwiseLeftKanExtension F :=
  fun V => (costructuredArrow_hasColimitsOfShape ρ R V).has_colimit _

/-- Every module presheaf over `X` has a left Kan extension along `ι`. -/
instance hasLeftKanExtension (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) :
    (ι P ρ).op.HasLeftKanExtension F :=
  inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The value of the left Kan extension at `V` is the colimit over the costructured arrows of
`V`. This is Mathlib's `lanEvaluationIsoColim` without its smallness assumptions, with the
same proof. -/
def lanEvaluationIsoColimit (V : (TwistedOver P ρ)ᵒᵖ) :
    ((ι P ρ).op.lan : ((P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (TwistedOver P ρ)ᵒᵖ ⥤
        ModuleCat.{w} R) ⋙ (CategoryTheory.evaluation (TwistedOver P ρ)ᵒᵖ
          (ModuleCat.{w} R)).obj V ≅
      (Functor.whiskeringLeft _ _ (ModuleCat.{w} R)).obj (CostructuredArrow.proj (ι P ρ).op V) ⋙
        colim :=
  NatIso.ofComponents (fun F =>
    IsColimit.coconePointUniqueUpToIso
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (ι P ρ).op F V)
    (colimit.isColimit _)) (fun {F₁ F₂} φ => by
      apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (ι P ρ).op F₁ V).hom_ext
      intro T
      have h₁ := fun (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) =>
        IsColimit.comp_coconePointUniqueUpToIso_hom
          (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (ι P ρ).op F V)
          (colimit.isColimit _) T
      have h₂ := congr_app ((ι P ρ).op.lanUnit.naturality φ) T.left
      dsimp at h₁ h₂ ⊢
      simp only [Category.assoc] at h₁ ⊢
      simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
      rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
        ι_colimMap, Functor.whiskerLeft_app]
      rfl)

variable [HasExactColimitsOfShape (Discrete G) (ModuleCat.{w} R)]

/-- Colimits of modules over the costructured arrows of an object are exact, since the
translates of the object form a final discrete family. -/
instance costructuredArrow_hasExactColimitsOfShape (V : (TwistedOver P ρ)ᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (ι P ρ).op V) (ModuleCat.{w} R) :=
  hasExactColimitsOfShape_of_final (ModuleCat.{w} R) (translateArrows ρ V.unop)

/-- Left Kan extension of module presheaves along the inclusion `ι` preserves finite
limits. -/
instance lan_preservesFiniteLimits :
    PreservesFiniteLimits ((ι P ρ).op.lan : ((P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤
      (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R) := by
  constructor
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation _ K
  intro V
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColimit ρ R V).symm

end Exact

section Sheaves

variable (R : Type w) [CommRing R]
variable [HasColimitsOfShape (Discrete G) (ModuleCat.{w} R)]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]

/-- Left induction from module sheaves over `X` to module sheaves on the twisted site: left
Kan extension along `ι` followed by sheafification for the twisted topology. -/
def leftInduction :
    Sheaf J (ModuleCat.{w} R) ⥤ Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) :=
  Functor.sheafPullbackConstruction.sheafPullback (ι P ρ) (ModuleCat.{w} R) J
    (twistedTopology ρ J)

/-- Left induction is left adjoint to restriction. -/
def leftInductionAdjunction :
    leftInduction ρ R J ⊣ restriction ρ J (ModuleCat.{w} R) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (ι P ρ) (ModuleCat.{w} R) J
    (twistedTopology ρ J)

variable [HasExactColimitsOfShape (Discrete G) (ModuleCat.{w} R)]

/-- Left induction preserves finite limits. -/
instance leftInduction_preservesFiniteLimits :
    PreservesFiniteLimits (leftInduction ρ R J) := by
  have : PreservesFiniteLimits ((ι P ρ).op.lan ⋙
      presheafToSheaf (twistedTopology ρ J) (ModuleCat.{w} R)) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits (sheafToPresheaf J (ModuleCat.{w} R)) _

/-- Restriction from the twisted site sends injective module sheaves to injective module
sheaves over `X`. -/
instance restriction_preservesInjectiveObjects :
    (restriction ρ J (ModuleCat.{w} R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (leftInductionAdjunction ρ R J)

end Sheaves

end Langlands.Sheaf.Equivariant.TwistedOver
