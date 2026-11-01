import Langlands.Geometry.EtaleTransportAbelian
import Langlands.Geometry.EtaleGodement
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-! # Exact induction and restriction for actual small-etale transport sheaves -/

noncomputable section

universe u w

namespace Langlands.Geometry.EtaleTransport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} {G : Type w} [Group G]
variable (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- The genuine translations, as costructured arrows for ordinary restriction. -/
def translateArrows (U : Object ρ) :
    Discrete G ⥤ CostructuredArrow (inclusion ρ).op (op U) :=
  Discrete.functor fun g =>
    CostructuredArrow.mk (Y := op (Object.translate g U).etale)
      (Object.translationIso g U).hom.op

/-- A factorization through a translation determines the group label. -/
theorem label_eq_of_hom (U : Object ρ)
    (d : CostructuredArrow (inclusion ρ).op (op U))
    (s : StructuredArrow d (translateArrows ρ U)) :
    s.right.as = d.hom.unop.label := by
  have h := congrArg (fun φ => φ.unop.label) s.hom.w
  simp only [translateArrows, Discrete.functor_obj_eq_as, unop_comp,
    Object.comp_label] at h
  simpa using h

/-- The ordinary part gives the canonical factorization through a translation. -/
def toTranslate (U : Object ρ)
    (d : CostructuredArrow (inclusion ρ).op (op U)) :
    StructuredArrow d (translateArrows ρ U) :=
  StructuredArrow.mk (Y := (⟨d.hom.unop.label⟩ : Discrete G))
    (CostructuredArrow.homMk (f := d)
      (f' := (translateArrows ρ U).obj ⟨d.hom.unop.label⟩)
      (Object.ordinaryPart d.hom.unop).op (by
        apply Quiver.Hom.unop_inj
        exact Object.translationIso_hom_comp_ordinaryPart d.hom.unop))

/-- A factorization retains the actual underlying scheme map. -/
theorem factor_left (U : Object ρ)
    (d : CostructuredArrow (inclusion ρ).op (op U))
    (s : StructuredArrow d (translateArrows ρ U)) :
    s.hom.left.unop.left = d.hom.unop.left := by
  have h := congrArg (fun φ => φ.unop.left) s.hom.w
  change 𝟙 U.etale.left ≫ s.hom.left.unop.left = d.hom.unop.left at h
  simpa using h

/-- The map of any arrow between discrete translation labels is an identity on schemes. -/
theorem translateArrows_map_left (U : Object ρ) {s t : Discrete G} (h : s ⟶ t) :
    ((translateArrows ρ U).map h).left.unop.left = 𝟙 U.etale.left := by
  have hst : s = t := Discrete.ext (Discrete.eq_of_hom h)
  subst t
  have hh : h = 𝟙 s := Subsingleton.elim _ _
  subst h
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The translates form a final discrete family of actual labelled arrows. -/
instance translateArrows_final (U : Object ρ) : (translateArrows ρ U).Final where
  out d := by
    have : Nonempty (StructuredArrow d (translateArrows ρ U)) := ⟨toTranslate ρ U d⟩
    apply zigzag_isConnected
    intro s t
    apply Zigzag.of_hom
    refine StructuredArrow.homMk
      (eqToHom (Discrete.ext (by rw [label_eq_of_hom, label_eq_of_hom]))) ?_
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change ((translateArrows ρ U).map _).left.unop.left ≫ s.hom.left.unop.left =
      t.hom.left.unop.left
    rw [translateArrows_map_left]
    erw [Category.id_comp]
    rw [factor_left, factor_left]

variable [Small.{u} G]
variable (R : Type u) [CommRing R]

/-- Shrinking only the labels gives a `u`-small final family for Kan extension. -/
def smallTranslateArrows (U : Object ρ) :
    Discrete (Shrink.{u} G) ⥤ CostructuredArrow (inclusion ρ).op (op U) :=
  (Discrete.equivalence (equivShrink G)).inverse ⋙ translateArrows ρ U

instance smallTranslateArrows_final (U : Object ρ) :
    (smallTranslateArrows ρ U).Final :=
  inferInstanceAs ((Discrete.equivalence (equivShrink G)).inverse ⋙
    translateArrows ρ U).Final

instance costructuredArrow_hasColimitsOfShape (U : (Object ρ)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (inclusion ρ).op U) (ModuleCat.{u} R) :=
  Functor.Final.hasColimitsOfShape_of_final (smallTranslateArrows ρ U.unop)

/-- The actual costructured-arrow colimits are exact, by the small final family. -/
instance costructuredArrow_hasExactColimitsOfShape (U : (Object ρ)ᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (inclusion ρ).op U) (ModuleCat.{u} R) :=
  hasExactColimitsOfShape_of_final (ModuleCat.{u} R) (smallTranslateArrows ρ U.unop)

instance inclusion_hasPointwiseLeftKanExtension (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} R) :
    (inclusion ρ).op.HasPointwiseLeftKanExtension F :=
  fun U => (costructuredArrow_hasColimitsOfShape ρ R U).has_colimit _

/-- The comma-colimit evaluation formula in the actual site and module universes. -/
def inclusionLanEvaluationIso (U : (Object ρ)ᵒᵖ) :
    (inclusion ρ).op.lan ⋙ (CategoryTheory.evaluation (Object ρ)ᵒᵖ (ModuleCat.{u} R)).obj U ≅
      (Functor.whiskeringLeft _ _ (ModuleCat.{u} R)).obj
        (CostructuredArrow.proj (inclusion ρ).op U) ⋙ colim :=
  NatIso.ofComponents (fun F =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (inclusion ρ).op F U)
      (colimit.isColimit _)) (fun {F₁ F₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      (inclusion ρ).op F₁ U).hom_ext
    intro T
    have h₁ := fun (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} R) =>
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (inclusion ρ).op F U)
        (colimit.isColimit _) T
    have h₂ := congr_app ((inclusion ρ).op.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

/-- Left Kan extension of module presheaves along ordinary inclusion is exact. -/
instance inclusion_lan_preservesFiniteLimits :
    PreservesFiniteLimits ((inclusion ρ).op.lan :
      (Y.Etaleᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Object ρ)ᵒᵖ ⥤ ModuleCat.{u} R) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation _ J
  intro U
  exact preservesLimitsOfShape_of_natIso (inclusionLanEvaluationIso ρ R U).symm

/-- Induction is left Kan extension of actual presheaves followed by sheafification. -/
def induction : EtaleDerivedSections.ModuleSheaf Y R ⥤ ModuleSheaf.{u, w, u, u} ρ R :=
  Functor.sheafPullbackConstruction.sheafPullback (inclusion ρ) (ModuleCat.{u} R)
    Y.smallEtaleTopology (transportTopology ρ)

instance induction_preservesFiniteLimits : PreservesFiniteLimits (induction ρ R) := by
  dsimp only [induction, Functor.sheafPullbackConstruction.sheafPullback]
  infer_instance

/-- Actual induction is left adjoint to ordinary restriction. -/
def inductionAdjunction : induction ρ R ⊣ toSheaf ρ (ModuleCat.{u} R) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (inclusion ρ)
    (ModuleCat.{u} R) Y.smallEtaleTopology (transportTopology ρ)

instance induction_preservesColimits : PreservesColimits (induction ρ R) :=
  (inductionAdjunction ρ R).leftAdjoint_preservesColimits

/-- Induction has constructed finite-limit and finite-colimit preservation. -/
def inductionExactFunctor :
    EtaleDerivedSections.ModuleSheaf Y R ⥤ₑ ModuleSheaf.{u, w, u, u} ρ R :=
  ExactFunctor.of (induction ρ R)

instance toSheaf_preservesInjectiveObjects :
    (toSheaf ρ (ModuleCat.{u} R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (inductionAdjunction ρ R)

instance toSheaf_additive : (toSheaf ρ (ModuleCat.{u} R)).Additive where
  map_add := rfl

omit [Small.{u} G] in
/-- A transport-local lift is an ordinary local lift by the covering criterion. -/
theorem isLocallySurjective_restrict {P Q : (Object ρ)ᵒᵖ ⥤ ModuleCat.{u} R}
    (φ : P ⟶ Q) [h : Presheaf.IsLocallySurjective (transportTopology ρ) φ] :
    Presheaf.IsLocallySurjective Y.smallEtaleTopology
      (Functor.whiskerLeft (inclusion ρ).op φ) where
  imageSieve_mem {U} s := h.imageSieve_mem (U := (inclusion ρ).obj U) s

/-- Local bijectivity detects sheafification on the essentially small affine basis. -/
instance affineBasis_wEqualsLocallyBijective :
    (affineBasisTopology ρ).WEqualsLocallyBijective (ModuleCat.{u} R) :=
  .ofEssentiallySmall (affineBasisTopology ρ)

/-- Transport local bijectivity through the actual cover-dense affine comparison. -/
instance transport_wEqualsLocallyBijective :
    (transportTopology ρ).WEqualsLocallyBijective (ModuleCat.{u} R) :=
  .transport _ _ _ (Functor.IsDenseSubsite.coverPreserving
    (affineBasisTopology ρ) (transportTopology ρ) (affineBasisInclusion ρ))

omit [Small.{u} G] in
/-- The corepresentable module forgetful functor preserves the sheaf condition. -/
instance transport_moduleSheafCompose :
    (transportTopology ρ).HasSheafCompose (CategoryTheory.forget (ModuleCat.{u} R)) where
  isSheaf P hP := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_iso _ (Functor.isoWhiskerLeft P
      (EtaleGodement.moduleForgetCorepresentable R).toIso) (hP (ModuleCat.of R R))

instance toSheaf_preservesEpimorphisms :
    (toSheaf ρ (ModuleCat.{u} R)).PreservesEpimorphisms where
  preserves {F H} f hf := by
    have hS : Presheaf.IsLocallySurjective (transportTopology ρ) f.hom :=
      (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'.{u, u, u + 1, max u w, u + 1, u} (J := transportTopology ρ)
        (A := ModuleCat.{u} R) (φ := f)).2 hf
    have hU : CategoryTheory.Sheaf.IsLocallySurjective
        ((toSheaf ρ (ModuleCat.{u} R)).map f) :=
      isLocallySurjective_restrict ρ R f.hom
    exact (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'.{u, u, u + 1, u, u + 1, u}
      (J := Y.smallEtaleTopology) (A := ModuleCat.{u} R) (φ := (toSheaf ρ (ModuleCat.{u} R)).map f)).1 hU

instance toSheaf_preservesHomology : (toSheaf ρ (ModuleCat.{u} R)).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

instance toSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (toSheaf ρ (ModuleCat.{u} R)) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Forgetting the actual transport arrows is an exact functor of abelian categories. -/
def toSheafExactFunctor :
    ModuleSheaf.{u, w, u, u} ρ R ⥤ₑ EtaleDerivedSections.ModuleSheaf Y R :=
  ExactFunctor.of (toSheaf ρ (ModuleCat.{u} R))

end Langlands.Geometry.EtaleTransport
