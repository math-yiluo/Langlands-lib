import Langlands.Sheaf.Equivariant.TwistedRepCohomology
import Mathlib.RepresentationTheory.Rep.Res

/-!
# Restriction of twisted sheaves to a subgroup

Let `G` act on an object `X` through `ρ : G →* Aut X` and let `H` be a subgroup of `G`. The
twisted category of the restricted action `ρ.comp H.subtype` has the same objects as the
twisted category of `G`, and its morphisms are the twisted morphisms whose twist lies in `H`.
The resulting inclusion `subgroupInclusion` is continuous and cocontinuous for the twisted
topologies. Precomposition with it restricts sheaves on the twisted site of `G` to sheaves on
the twisted site of `H`. Restriction has a right adjoint, the right Kan extension, and a left
adjoint, the left Kan extension followed by sheafification. The left Kan extension at an
object `V` is a coproduct over the right cosets `H\G`: the translates of `V` by chosen coset
representatives are final among the costructured arrows of `V`. When these coproducts of
modules exist and are exact, restriction to `H` sends injective module sheaves to injective
module sheaves. Then the right derived functors of the global sections representation of the
restriction to `H` are the restrictions to `H` of the right derived functors of the global
sections representation of `G`, and likewise for the compactly supported global sections
representation (`subgroupRestrictionGlobalCohomologyIso`,
`subgroupRestrictionCompactCohomologyIso`).
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Cohomology

universe w v u uG uI

section LanEvaluation

variable {C D E : Type*} [Category C] [Category D] [Category E]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The value at `V` of the left Kan extension along `F` is the colimit over the costructured
arrows of `V`. This is Mathlib's `lanEvaluationIsoColim` without its smallness assumptions,
with the same proof. -/
def lanEvaluationIsoColimitOf (F : C ⥤ D) (V : D)
    [∀ V : D, HasColimitsOfShape (CostructuredArrow F V) E] :
    (F.lan : (C ⥤ E) ⥤ D ⥤ E) ⋙ (CategoryTheory.evaluation D E).obj V ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F V) ⋙ colim :=
  NatIso.ofComponents (fun F' =>
    IsColimit.coconePointUniqueUpToIso
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F F' V)
    (colimit.isColimit _)) (fun {F₁ F₂} φ => by
      apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F F₁ V).hom_ext
      intro T
      have h₁ := fun (F' : C ⥤ E) =>
        IsColimit.comp_coconePointUniqueUpToIso_hom
          (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F F' V)
          (colimit.isColimit _) T
      have h₂ := congr_app (F.lanUnit.naturality φ) T.left
      dsimp at h₁ h₂ ⊢
      simp only [Category.assoc] at h₁ ⊢
      simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
      rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
        ι_colimMap, Functor.whiskerLeft_app]
      rfl)

end LanEvaluation

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} {X : C}
variable {G : Type uG} [Group G] (ρ : G →* Aut X) (H : Subgroup G)

section Inclusion

/-- The inclusion of the twisted category of the restricted action `ρ.comp H.subtype` into the
twisted category of `G`: the same objects, and a twisted morphism with twist `h ∈ H` is the
twisted morphism with twist `(h : G)` and the same underlying arrow. -/
def subgroupInclusion : TwistedOver P (ρ.comp H.subtype) ⥤ TwistedOver P ρ where
  obj U := ⟨U.obj⟩
  map f := homMk ((Hom.twist (ρ := ρ.comp H.subtype) f : H) : G)
    (Hom.left (ρ := ρ.comp H.subtype) f) (Hom.w (ρ := ρ.comp H.subtype) f)
  map_id _ := hom_ext rfl rfl
  map_comp _ _ := hom_ext rfl rfl

variable {ρ H}

@[simp]
theorem subgroupInclusion_obj_obj (U : TwistedOver P (ρ.comp H.subtype)) :
    ((subgroupInclusion ρ H).obj U).obj = U.obj :=
  rfl

@[simp]
theorem subgroupInclusion_map_twist {U V : TwistedOver P (ρ.comp H.subtype)} (f : U ⟶ V) :
    Hom.twist ((subgroupInclusion ρ H).map f) =
      ((Hom.twist (ρ := ρ.comp H.subtype) f : H) : G) :=
  rfl

@[simp]
theorem subgroupInclusion_map_left {U V : TwistedOver P (ρ.comp H.subtype)} (f : U ⟶ V) :
    Hom.left ((subgroupInclusion ρ H).map f) = Hom.left (ρ := ρ.comp H.subtype) f :=
  rfl

instance : (subgroupInclusion (P := P) ρ H).Faithful where
  map_injective {_ _} _ _ h :=
    hom_ext (Subtype.ext (congrArg (fun φ => Hom.twist (ρ := ρ) φ) h))
      (congrArg (fun φ => Hom.left (ρ := ρ) φ) h)

variable (ρ H) in
/-- The inclusion of `P.Over ⊤ X` into the twisted category of `H`, followed by the subgroup
inclusion, is the inclusion of `P.Over ⊤ X` into the twisted category of `G`. -/
theorem ι_comp_subgroupInclusion :
    ι P (ρ.comp H.subtype) ⋙ subgroupInclusion ρ H = ι P ρ :=
  rfl

end Inclusion

section Topology

variable [P.RespectsIso]

/-- Translation by `h ∈ H` for the restricted action is translation by `(h : G)`. -/
theorem translate_comp_subtype (h : H) :
    translate P (ρ.comp H.subtype) h = translate P ρ (h : G) :=
  rfl

variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]

/-- A topology invariant under `G` is invariant under the subgroup `H`. -/
instance isTranslationInvariant_comp_subtype :
    IsTranslationInvariant (ρ := ρ.comp H.subtype) J where
  isCocontinuous h := IsTranslationInvariant.isCocontinuous (ρ := ρ) (J := J) (h : G)

/-- The subgroup inclusion is cocontinuous: a sieve on the twisted site of `G` covers when its
arrows over `X` cover, and these are the arrows over `X` of its pullback to the twisted site
of `H`. -/
instance subgroupInclusion_isCocontinuous :
    (subgroupInclusion (P := P) ρ H).IsCocontinuous (twistedTopology (ρ.comp H.subtype) J)
      (twistedTopology ρ J) where
  cover_lift hS := hS

/-- The subgroup inclusion is continuous: a sheaf on the twisted site of `G` restricts to a
sheaf on `P.Over ⊤ X`, which is the restriction to `P.Over ⊤ X` of its pullback to the twisted
site of `H`. -/
instance subgroupInclusion_isContinuous :
    (subgroupInclusion (P := P) ρ H).IsContinuous (twistedTopology (ρ.comp H.subtype) J)
      (twistedTopology ρ J) where
  op_comp_isSheaf_of_types F :=
    isSheaf_of_isSheaf_comp (ρ := ρ.comp H.subtype) J
      ((ι P ρ).op_comp_isSheaf_of_types J (twistedTopology ρ J) F)

variable (A : Type*) [Category A]

/-- Restriction of sheaves on the twisted site of `G` to the twisted site of the subgroup `H`:
precomposition with the subgroup inclusion. -/
abbrev subgroupRestriction :
    Sheaf (twistedTopology ρ J) A ⥤ Sheaf (twistedTopology (ρ.comp H.subtype) J) A :=
  (subgroupInclusion ρ H).sheafPushforwardContinuous A (twistedTopology (ρ.comp H.subtype) J)
    (twistedTopology ρ J)

/-- Restricting to `H` and then to `P.Over ⊤ X` is restricting to `P.Over ⊤ X`. -/
def subgroupRestrictionCompRestrictionIso :
    subgroupRestriction ρ H J A ⋙ restriction (ρ.comp H.subtype) J A ≅ restriction ρ J A :=
  Iso.refl _

/-- Restriction to `H` is faithful. -/
instance subgroupRestriction_faithful : (subgroupRestriction ρ H J A).Faithful :=
  Functor.Faithful.of_comp_iso (subgroupRestrictionCompRestrictionIso ρ H J A)

variable [∀ F : (TwistedOver P (ρ.comp H.subtype))ᵒᵖ ⥤ A,
  (subgroupInclusion ρ H).op.HasPointwiseRightKanExtension F]

/-- Coinduction of sheaves from the twisted site of `H` to the twisted site of `G`: the right
Kan extension along the subgroup inclusion. -/
abbrev subgroupCoinduction :
    Sheaf (twistedTopology (ρ.comp H.subtype) J) A ⥤ Sheaf (twistedTopology ρ J) A :=
  (subgroupInclusion ρ H).sheafPushforwardCocontinuous A (twistedTopology (ρ.comp H.subtype) J)
    (twistedTopology ρ J)

/-- Restriction to `H` is left adjoint to coinduction. -/
def subgroupRestrictionAdjunction : subgroupRestriction ρ H J A ⊣ subgroupCoinduction ρ H J A :=
  (subgroupInclusion ρ H).sheafAdjunctionCocontinuous A (twistedTopology (ρ.comp H.subtype) J)
    (twistedTopology ρ J)

end Topology

section Modules

variable [P.RespectsIso]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]

omit [P.RespectsIso] in
/-- Module presheaves in a universe containing the objects and morphisms of `C` and the group
have right Kan extensions along the subgroup inclusion. -/
theorem subgroupInclusion_hasPointwiseRightKanExtension_moduleCat (R : Type (max u v uG))
    [CommRing R] (F : (TwistedOver P (ρ.comp H.subtype))ᵒᵖ ⥤ ModuleCat.{max u v uG} R) :
    (subgroupInclusion ρ H).op.HasPointwiseRightKanExtension F :=
  inferInstance

/-- Restriction of module sheaves to `H` is additive. -/
instance subgroupRestriction_additive :
    (subgroupRestriction ρ H J (ModuleCat.{w} R)).Additive where
  map_add := rfl

/-- Restriction of module sheaves to `H` preserves finite limits. -/
instance subgroupRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (subgroupRestriction ρ H J (ModuleCat.{w} R)) := by
  have : PreservesFiniteLimits (subgroupRestriction ρ H J (ModuleCat.{w} R) ⋙
      sheafToPresheaf (twistedTopology (ρ.comp H.subtype) J) (ModuleCat.{w} R)) :=
    preservesFiniteLimits_of_natIso ((subgroupInclusion ρ H).sheafPushforwardContinuousCompSheafToPresheafIso
      (ModuleCat.{w} R) (twistedTopology (ρ.comp H.subtype) J) (twistedTopology ρ J)).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (twistedTopology (ρ.comp H.subtype) J) (ModuleCat.{w} R))

variable [∀ F : (TwistedOver P (ρ.comp H.subtype))ᵒᵖ ⥤ ModuleCat.{w} R,
  (subgroupInclusion ρ H).op.HasPointwiseRightKanExtension F]

/-- Restriction of module sheaves to `H` is a left adjoint, so it preserves finite
colimits. -/
instance subgroupRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (subgroupRestriction ρ H J (ModuleCat.{w} R)) := by
  have := (subgroupRestrictionAdjunction ρ H J (ModuleCat.{w} R)).leftAdjoint_preservesColimits.{0, 0}
  exact PreservesColimitsOfSize.preservesFiniteColimits _

end Modules

section Cosets

variable [P.RespectsIso]
variable {ρ H}

/-- A twisted morphism `f : U ⟶ U'` to an object of the twisted category of `H`, whose twist
lies in the right coset `H g`, is the relabelling by `g` followed by a morphism with twist in
`H` from the translate `gU`. This is that morphism. -/
def subgroupUntwist (g : G) {U : TwistedOver P ρ} {U' : TwistedOver P (ρ.comp H.subtype)}
    (f : U ⟶ (subgroupInclusion ρ H).obj U') (hf : Hom.twist f * g⁻¹ ∈ H) :
    (⟨(translate P ρ g).obj U.obj⟩ : TwistedOver P (ρ.comp H.subtype)) ⟶ U' :=
  homMk ⟨Hom.twist f * g⁻¹, hf⟩ (Hom.left (ρ := ρ) f) (by
    change Hom.left f ≫ U'.hom = (U.hom ≫ (ρ g).hom) ≫ (ρ (Hom.twist f * g⁻¹)).hom
    rw [Category.assoc, ← rho_mul_hom, inv_mul_cancel_right]
    exact Hom.w f)

theorem relabel_comp_subgroupInclusion_map_subgroupUntwist (g : G) {U : TwistedOver P ρ}
    {U' : TwistedOver P (ρ.comp H.subtype)} (f : U ⟶ (subgroupInclusion ρ H).obj U')
    (hf : Hom.twist f * g⁻¹ ∈ H) :
    relabel ρ g U.obj ≫ (subgroupInclusion ρ H).map (subgroupUntwist g f hf) = f :=
  hom_ext (inv_mul_cancel_right (Hom.twist f) g) (Category.id_comp (Hom.left (ρ := ρ) f))

variable (ρ H) in
/-- The translates `gV` of an object `V` of the twisted category of `G` by the chosen
representatives `g` of the right cosets `H\G`, with their relabelling arrows `V ⟶ gV`, as
costructured arrows for the opposite of the subgroup inclusion. -/
def cosetTranslateArrows (V : TwistedOver P ρ) :
    Discrete (Quotient (QuotientGroup.rightRel H)) ⥤
      CostructuredArrow (subgroupInclusion ρ H).op (op V) :=
  Discrete.functor fun q =>
    CostructuredArrow.mk
      (Y := op (⟨(translate P ρ q.out).obj V.obj⟩ : TwistedOver P (ρ.comp H.subtype)))
      (relabel ρ q.out V.obj).op

/-- A morphism from a costructured arrow `d` to the translate by the representative of a
coset forces the coset to be the coset of the twist of the arrow of `d`. -/
theorem coset_eq_of_hom_cosetTranslateArrows (V : TwistedOver P ρ)
    (d : CostructuredArrow (subgroupInclusion ρ H).op (op V))
    (j : Discrete (Quotient (QuotientGroup.rightRel H)))
    (s : d ⟶ (cosetTranslateArrows ρ H V).obj j) :
    j.as = Quotient.mk _ (Hom.twist d.hom.unop) := by
  have h := congrArg (fun φ => Hom.twist φ.unop) (CostructuredArrow.w s)
  change Hom.twist ((subgroupInclusion ρ H).map s.left.unop) * j.as.out =
    Hom.twist d.hom.unop at h
  rw [subgroupInclusion_map_twist] at h
  rw [← Quotient.out_eq j.as]
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.2 ?_
  rw [← h, mul_inv_cancel_right]
  exact (Hom.twist s.left.unop).2

/-- Morphisms from a costructured arrow to a coset translate are unique: the relabelling
arrow is invertible and the subgroup inclusion is faithful. -/
instance cosetTranslateArrows_hom_subsingleton (V : TwistedOver P ρ)
    (d : CostructuredArrow (subgroupInclusion ρ H).op (op V))
    (j : Discrete (Quotient (QuotientGroup.rightRel H))) :
    Subsingleton (d ⟶ (cosetTranslateArrows ρ H V).obj j) :=
  ⟨fun a b => by
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply (subgroupInclusion ρ H).map_injective
    have ha : relabel ρ j.as.out V.obj ≫ (subgroupInclusion ρ H).map a.left.unop =
        d.hom.unop :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w a)
    have hb : relabel ρ j.as.out V.obj ≫ (subgroupInclusion ρ H).map b.left.unop =
        d.hom.unop :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w b)
    exact (cancel_epi (relabel ρ j.as.out V.obj)).1 (ha.trans hb.symm)⟩

/-- The twist of a twisted morphism lies in the right coset of `H` of its chosen
representative. -/
theorem mul_inv_out_mem (g : G) :
    g * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) g))⁻¹ ∈ H :=
  QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)

variable (ρ H) in
/-- Every costructured arrow factors through the translate by the representative of the
coset of the twist of its arrow. -/
def toCosetTranslate (V : TwistedOver P ρ)
    (d : CostructuredArrow (subgroupInclusion ρ H).op (op V)) :
    StructuredArrow d (cosetTranslateArrows ρ H V) :=
  StructuredArrow.mk (Y := (⟨Quotient.mk _ (Hom.twist d.hom.unop)⟩ :
      Discrete (Quotient (QuotientGroup.rightRel H))))
    (CostructuredArrow.homMk (f := d)
      (f' := (cosetTranslateArrows ρ H V).obj ⟨Quotient.mk _ (Hom.twist d.hom.unop)⟩)
      (subgroupUntwist (U := V) (U' := d.left.unop)
        (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) (Hom.twist d.hom.unop)))
        d.hom.unop (mul_inv_out_mem _)).op
      (Quiver.Hom.unop_inj
        (relabel_comp_subgroupInclusion_map_subgroupUntwist (U := V) (U' := d.left.unop) _
          d.hom.unop (mul_inv_out_mem _))))

/-- The coset translates of an object are final among its costructured arrows. -/
instance cosetTranslateArrows_final (V : TwistedOver P ρ) :
    (cosetTranslateArrows ρ H V).Final where
  out d := by
    have : Nonempty (StructuredArrow d (cosetTranslateArrows ρ H V)) :=
      ⟨toCosetTranslate ρ H V d⟩
    apply zigzag_isConnected
    intro s t
    apply Zigzag.of_hom
    exact StructuredArrow.homMk (eqToHom (Discrete.ext
      ((coset_eq_of_hom_cosetTranslateArrows V d _ s.hom).trans
        (coset_eq_of_hom_cosetTranslateArrows V d _ t.hom).symm))) (Subsingleton.elim _ _)

end Cosets

section Exact

variable [P.RespectsIso]
variable (R : Type w) [CommRing R]
variable [HasColimitsOfShape (Discrete (Quotient (QuotientGroup.rightRel H))) (ModuleCat.{w} R)]

/-- Colimits of modules over the costructured arrows of an object for the subgroup inclusion
exist: the coset translates are final, and coproducts indexed by `H\G` exist. -/
instance subgroupCostructuredArrow_hasColimitsOfShape (V : (TwistedOver P ρ)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (subgroupInclusion ρ H).op V) (ModuleCat.{w} R) :=
  Functor.Final.hasColimitsOfShape_of_final (cosetTranslateArrows ρ H V.unop)

/-- Every module presheaf on the twisted category of `H` has a pointwise left Kan extension
along the subgroup inclusion. -/
instance subgroupInclusion_hasPointwiseLeftKanExtension
    (F : (TwistedOver P (ρ.comp H.subtype))ᵒᵖ ⥤ ModuleCat.{w} R) :
    (subgroupInclusion ρ H).op.HasPointwiseLeftKanExtension F :=
  fun V => (subgroupCostructuredArrow_hasColimitsOfShape ρ H R V).has_colimit _

/-- Every module presheaf on the twisted category of `H` has a left Kan extension along the
subgroup inclusion. -/
instance subgroupInclusion_hasLeftKanExtension
    (F : (TwistedOver P (ρ.comp H.subtype))ᵒᵖ ⥤ ModuleCat.{w} R) :
    (subgroupInclusion ρ H).op.HasLeftKanExtension F :=
  inferInstance

variable [HasExactColimitsOfShape (Discrete (Quotient (QuotientGroup.rightRel H)))
  (ModuleCat.{w} R)]

/-- Colimits of modules over the costructured arrows of an object for the subgroup inclusion
are exact, since the coset translates form a final discrete family. -/
instance subgroupCostructuredArrow_hasExactColimitsOfShape (V : (TwistedOver P ρ)ᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (subgroupInclusion ρ H).op V)
      (ModuleCat.{w} R) :=
  hasExactColimitsOfShape_of_final (ModuleCat.{w} R) (cosetTranslateArrows ρ H V.unop)

/-- Left Kan extension of module presheaves along the subgroup inclusion preserves finite
limits. -/
instance subgroupLan_preservesFiniteLimits :
    PreservesFiniteLimits ((subgroupInclusion ρ H).op.lan :
      ((TwistedOver P (ρ.comp H.subtype))ᵒᵖ ⥤ ModuleCat.{w} R) ⥤
        (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R) := by
  constructor
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation _ K
  intro V
  exact preservesLimitsOfShape_of_natIso
    (lanEvaluationIsoColimitOf (E := ModuleCat.{w} R) (subgroupInclusion ρ H).op V).symm

end Exact

section Induction

variable [P.RespectsIso]
variable (R : Type w) [CommRing R]
variable [HasColimitsOfShape (Discrete (Quotient (QuotientGroup.rightRel H))) (ModuleCat.{w} R)]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]

/-- Induction of module sheaves from the twisted site of `H` to the twisted site of `G`: left
Kan extension along the subgroup inclusion, a coproduct over the coset translates, followed
by sheafification for the twisted topology of `G`. -/
def subgroupInduction :
    Sheaf (twistedTopology (ρ.comp H.subtype) J) (ModuleCat.{w} R) ⥤
      Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) :=
  Functor.sheafPullbackConstruction.sheafPullback (subgroupInclusion ρ H) (ModuleCat.{w} R)
    (twistedTopology (ρ.comp H.subtype) J) (twistedTopology ρ J)

/-- Induction is left adjoint to restriction to `H`. -/
def subgroupInductionAdjunction :
    subgroupInduction ρ H R J ⊣ subgroupRestriction ρ H J (ModuleCat.{w} R) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (subgroupInclusion ρ H)
    (ModuleCat.{w} R) (twistedTopology (ρ.comp H.subtype) J) (twistedTopology ρ J)

variable [HasExactColimitsOfShape (Discrete (Quotient (QuotientGroup.rightRel H)))
  (ModuleCat.{w} R)]

/-- Induction from `H` preserves finite limits. -/
instance subgroupInduction_preservesFiniteLimits :
    PreservesFiniteLimits (subgroupInduction ρ H R J) := by
  have : PreservesFiniteLimits ((subgroupInclusion ρ H).op.lan ⋙
      presheafToSheaf (twistedTopology ρ J) (ModuleCat.{w} R)) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits
    (sheafToPresheaf (twistedTopology (ρ.comp H.subtype) J) (ModuleCat.{w} R)) _

/-- Restriction to `H` sends injective module sheaves to injective module sheaves. -/
instance subgroupRestriction_preservesInjectiveObjects :
    (subgroupRestriction ρ H J (ModuleCat.{w} R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (subgroupInductionAdjunction ρ H R J)

end Induction

section GlobalSections

open Langlands.Cohomology.AcyclicResolution

variable [P.RespectsIso] [P.ContainsIdentities]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]

/-- The global sections representation of the restriction to `H` of a module sheaf is the
restriction to `H` of its global sections representation. Both have the module of sections
at the base object, on which `h ∈ H` acts by restriction along the endomorphism `h⁻¹` of the
base object. -/
def subgroupRestrictionGlobalSectionsIso :
    sheafGlobalSectionsRep J R (ρ := ρ) ⋙ Rep.resFunctor H.subtype ≅
      subgroupRestriction ρ H J (ModuleCat.{w} R) ⋙
        sheafGlobalSectionsRep J R (ρ := ρ.comp H.subtype) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by ext; rfl)

variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]
variable [HasSheafify (twistedTopology (ρ.comp H.subtype) J) (ModuleCat.{w} R)]
variable [EnoughInjectives (Sheaf (twistedTopology (ρ.comp H.subtype) J) (ModuleCat.{w} R))]
variable [∀ F : (TwistedOver P (ρ.comp H.subtype))ᵒᵖ ⥤ ModuleCat.{w} R,
  (subgroupInclusion ρ H).op.HasPointwiseRightKanExtension F]

/-- The comparison from the restriction to `H` of the representation
`sheafGlobalRepDerived J R q` of `G` to the representation `sheafGlobalRepDerived J R q` of
`H` of the restriction of the sheaf to `H`: the base change transformation of
`subgroupRestrictionGlobalSectionsIso` along the exact functors `Rep.resFunctor` and
restriction to `H`. -/
def subgroupRestrictionGlobalComparison (q : ℕ) :
    sheafGlobalRepDerived J R (ρ := ρ) q ⋙ Rep.resFunctor H.subtype ⟶
      subgroupRestriction ρ H J (ModuleCat.{w} R) ⋙
        sheafGlobalRepDerived J R (ρ := ρ.comp H.subtype) q :=
  ExactBaseChange.baseChangeNatTrans (subgroupRestrictionGlobalSectionsIso ρ H J R).hom q

variable [HasColimitsOfShape (Discrete (Quotient (QuotientGroup.rightRel H))) (ModuleCat.{w} R)]
variable [HasExactColimitsOfShape (Discrete (Quotient (QuotientGroup.rightRel H)))
  (ModuleCat.{w} R)]

/-- The comparison is an isomorphism: restriction to `H` sends an injective resolution on the
twisted site of `G` to an injective resolution on the twisted site of `H`. -/
theorem isIso_subgroupRestrictionGlobalComparison_app (q : ℕ)
    (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)) :
    IsIso ((subgroupRestrictionGlobalComparison ρ H J R q).app F) := by
  let K := (injectiveResolution F).cocomplex
  have := ExactBaseChange.quasiIso_mapResolutionAugmentation
    (subgroupRestriction ρ H J (ModuleCat.{w} R)) (injectiveResolution F).ι
  have : IsIso ((NatTrans.mapHomologicalComplex
      (subgroupRestrictionGlobalSectionsIso ρ H J R).hom (ComplexShape.up ℕ)).app K) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex
      (subgroupRestrictionGlobalSectionsIso ρ H J R) (ComplexShape.up ℕ)).app K).hom)
  exact ExactBaseChange.isIso_baseChangeNatTrans_app_of_acyclic
    (subgroupRestrictionGlobalSectionsIso ρ H J R).hom (ε := (injectiveResolution F).ι)
    (ε' := mapResolutionAugmentation (subgroupRestriction ρ H J (ModuleCat.{w} R))
      (injectiveResolution F).ι)
    (ψ := 𝟙 _)
    (Φ := (NatTrans.mapHomologicalComplex (subgroupRestrictionGlobalSectionsIso ρ H J R).hom
      (ComplexShape.up ℕ)).app K)
    (Category.comp_id _)
    (fun n => by simp; rfl)
    (fun n r => (sheafGlobalSectionsRep J R (ρ := ρ)).isZero_rightDerived_obj_injective_succ r
      (K.X n))
    (fun n r => (sheafGlobalSectionsRep J R (ρ := ρ.comp H.subtype)).isZero_rightDerived_obj_injective_succ
      r ((subgroupRestriction ρ H J (ModuleCat.{w} R)).obj (K.X n)))
    q

/-- The restriction to `H` of the representation `sheafGlobalRepDerived J R q` of `G` is the
representation `sheafGlobalRepDerived J R q` of `H` of the restriction of the sheaf to `H`. -/
def subgroupRestrictionGlobalCohomologyIso (q : ℕ) :
    sheafGlobalRepDerived J R (ρ := ρ) q ⋙ Rep.resFunctor H.subtype ≅
      subgroupRestriction ρ H J (ModuleCat.{w} R) ⋙
        sheafGlobalRepDerived J R (ρ := ρ.comp H.subtype) q :=
  haveI : ∀ F, IsIso ((subgroupRestrictionGlobalComparison ρ H J R q).app F) :=
    isIso_subgroupRestrictionGlobalComparison_app ρ H J R q
  haveI : IsIso (subgroupRestrictionGlobalComparison ρ H J R q) :=
    NatIso.isIso_of_isIso_app _
  asIso (subgroupRestrictionGlobalComparison ρ H J R q)

end GlobalSections

section CompactSections

open Langlands.Cohomology.AcyclicResolution Langlands.Sheaf.PointSupport

variable [P.RespectsIso] [P.ContainsIdentities]
variable {J : GrothendieckTopology (P.Over ⊤ X)}
variable {I : Type uI} [MulAction G I] {Φ : I → J.Point.{w}}

/-- A subgroup of a group acting on `I` by homeomorphisms acts on `I` by homeomorphisms. -/
instance subgroup_continuousConstSMul [TopologicalSpace I] [ContinuousConstSMul G I] :
    ContinuousConstSMul H I :=
  IsScalarTower.continuousConstSMul H G I

variable {ρ} in
/-- A compatibility of a family of points with the translations by `G` restricts to a
compatibility with the translations by the subgroup `H`: translation by `h ∈ H` for the
restricted action is translation by `(h : G)`. -/
def PointEquivariance.toSubgroup (E : PointEquivariance ρ Φ) :
    PointEquivariance (ρ.comp H.subtype) Φ where
  fiberIso h i := E.fiberIso h i

variable (J) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable [LocallySmall.{w} (P.Over ⊤ X)] [TopologicalSpace I] [ContinuousConstSMul G I]

/-- The compactly supported global sections representation of the restriction to `H` of a
module sheaf is the restriction to `H` of its compactly supported global sections
representation. Both have the module of compactly supported sections at the base object, on
which `h ∈ H` acts by restriction along the endomorphism `h⁻¹` of the base object. -/
def subgroupRestrictionCompactSectionsIso (E : PointEquivariance ρ Φ) :
    sheafCompactSectionsRep J R E ⋙ Rep.resFunctor H.subtype ≅
      subgroupRestriction ρ H J (ModuleCat.{w} R) ⋙
        sheafCompactSectionsRep J R (E.toSubgroup H) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by ext; rfl)

variable [HasSheafify J (ModuleCat.{w} R)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]
variable [HasSheafify (twistedTopology (ρ.comp H.subtype) J) (ModuleCat.{w} R)]
variable [EnoughInjectives (Sheaf (twistedTopology (ρ.comp H.subtype) J) (ModuleCat.{w} R))]
variable [∀ F : (TwistedOver P (ρ.comp H.subtype))ᵒᵖ ⥤ ModuleCat.{w} R,
  (subgroupInclusion ρ H).op.HasPointwiseRightKanExtension F]

/-- The comparison from the restriction to `H` of the representation
`sheafCompactRepDerived J R E q` of `G` to the representation
`sheafCompactRepDerived J R (E.toSubgroup H) q` of `H` of the restriction of the sheaf to
`H`: the base change transformation of `subgroupRestrictionCompactSectionsIso` along the exact
functors `Rep.resFunctor` and restriction to `H`. -/
def subgroupRestrictionCompactComparison (E : PointEquivariance ρ Φ) (q : ℕ) :
    sheafCompactRepDerived J R E q ⋙ Rep.resFunctor H.subtype ⟶
      subgroupRestriction ρ H J (ModuleCat.{w} R) ⋙
        sheafCompactRepDerived J R (E.toSubgroup H) q :=
  ExactBaseChange.baseChangeNatTrans (subgroupRestrictionCompactSectionsIso ρ H J R E).hom q

variable [HasColimitsOfShape (Discrete (Quotient (QuotientGroup.rightRel H))) (ModuleCat.{w} R)]
variable [HasExactColimitsOfShape (Discrete (Quotient (QuotientGroup.rightRel H)))
  (ModuleCat.{w} R)]

/-- The compact comparison is an isomorphism: restriction to `H` sends an injective
resolution on the twisted site of `G` to an injective resolution on the twisted site of
`H`. -/
theorem isIso_subgroupRestrictionCompactComparison_app (E : PointEquivariance ρ Φ) (q : ℕ)
    (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)) :
    IsIso ((subgroupRestrictionCompactComparison ρ H J R E q).app F) := by
  let K := (injectiveResolution F).cocomplex
  have := ExactBaseChange.quasiIso_mapResolutionAugmentation
    (subgroupRestriction ρ H J (ModuleCat.{w} R)) (injectiveResolution F).ι
  have : IsIso ((NatTrans.mapHomologicalComplex
      (subgroupRestrictionCompactSectionsIso ρ H J R E).hom (ComplexShape.up ℕ)).app K) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex
      (subgroupRestrictionCompactSectionsIso ρ H J R E) (ComplexShape.up ℕ)).app K).hom)
  exact ExactBaseChange.isIso_baseChangeNatTrans_app_of_acyclic
    (subgroupRestrictionCompactSectionsIso ρ H J R E).hom (ε := (injectiveResolution F).ι)
    (ε' := mapResolutionAugmentation (subgroupRestriction ρ H J (ModuleCat.{w} R))
      (injectiveResolution F).ι)
    (ψ := 𝟙 _)
    (Φ := (NatTrans.mapHomologicalComplex (subgroupRestrictionCompactSectionsIso ρ H J R E).hom
      (ComplexShape.up ℕ)).app K)
    (Category.comp_id _)
    (fun n => by simp; rfl)
    (fun n r => (sheafCompactSectionsRep J R E).isZero_rightDerived_obj_injective_succ r (K.X n))
    (fun n r => (sheafCompactSectionsRep J R (E.toSubgroup H)).isZero_rightDerived_obj_injective_succ
      r ((subgroupRestriction ρ H J (ModuleCat.{w} R)).obj (K.X n)))
    q

/-- The restriction to `H` of the representation `sheafCompactRepDerived J R E q` of `G` is
the representation `sheafCompactRepDerived J R (E.toSubgroup H) q` of `H` of the restriction
of the sheaf to `H`. -/
def subgroupRestrictionCompactCohomologyIso (E : PointEquivariance ρ Φ) (q : ℕ) :
    sheafCompactRepDerived J R E q ⋙ Rep.resFunctor H.subtype ≅
      subgroupRestriction ρ H J (ModuleCat.{w} R) ⋙
        sheafCompactRepDerived J R (E.toSubgroup H) q :=
  haveI : ∀ F, IsIso ((subgroupRestrictionCompactComparison ρ H J R E q).app F) :=
    isIso_subgroupRestrictionCompactComparison_app ρ H J R E q
  haveI : IsIso (subgroupRestrictionCompactComparison ρ H J R E q) :=
    NatIso.isIso_of_isIso_app _
  asIso (subgroupRestrictionCompactComparison ρ H J R E q)

end CompactSections

end Langlands.Sheaf.Equivariant.TwistedOver
