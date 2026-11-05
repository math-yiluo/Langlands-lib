import Langlands.Sheaf.Renard.SheafBasisRestriction
import Langlands.Sheaf.Renard.AllOpenMathlibSheaf

/-! # The canonical compatible-section extension from a chosen basis -/

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace Langlands.Sheaf.Renard.BasisAllOpen

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- All original basis members contained in an actual open. -/
abbrev Inside (B : OpenBasis X) (V : Opens X) := {U : BasisOpen B // U.obj ≤ V}

/-- Compatible families form an additive subgroup of the product of original groups. -/
def familySubgroup (F : RawPresheaf.{u,max u v} B) (V : Opens X) :
    AddSubgroup (∀ U : Inside B V, Sections F U.val) where
  carrier := {s | ∀ (U W : Inside B V) (h : W.val.obj ≤ U.val.obj),
    restriction F h (s U) = s W}
  zero_mem' := by
    intro U W h
    change restriction F h 0 = 0
    exact map_zero _
  add_mem' := by
    intro s t hs ht U W h
    change restriction F h (s U + t U) = s W + t W
    rw [map_add, hs U W h, ht U W h]
  neg_mem' := by
    intro s hs U W h
    change restriction F h (-s U) = -s W
    rw [map_neg, hs U W h]

/-- Sections of the extension on an arbitrary actual open. -/
abbrev Families (F : RawPresheaf.{u,max u v} B) (V : Opens X) := familySubgroup F V

@[ext] theorem families_ext {F : RawPresheaf.{u,max u v} B} {V : Opens X}
    {s t : Families F V} (h : ∀ U : Inside B V, s.val U = t.val U) : s = t :=
  Subtype.ext (funext h)

/-- Restrict a compatible family by discarding components outside the smaller open. -/
def familyRestriction (F : RawPresheaf.{u,max u v} B) {U V : Opens X} (h : U ≤ V) :
    Families F V →+ Families F U where
  toFun s := ⟨fun W => s.val ⟨W.val, W.property.trans h⟩,
    fun W T hTW => s.property ⟨W.val, W.property.trans h⟩
      ⟨T.val, T.property.trans h⟩ hTW⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem familyRestriction_apply (F : RawPresheaf.{u,max u v} B)
    {U V : Opens X} (h : U ≤ V) (s : Families F V) (W : Inside B U) :
    (familyRestriction F h s).val W = s.val ⟨W.val, W.property.trans h⟩ := rfl

/-- Apply the original natural transformation component by component. -/
def familyMap {F G : RawPresheaf.{u,max u v} B} (φ : F ⟶ G) (V : Opens X) :
    Families F V →+ Families G V where
  toFun s := ⟨fun U => φ.app (op U.val) (s.val U), by
    intro U W h
    rw [← restriction_naturality_apply φ h, s.property U W h]⟩
  map_zero' := by apply families_ext; intro U; exact map_zero _
  map_add' s t := by apply families_ext; intro U; exact map_add _ _ _

@[simp] theorem familyMap_apply {F G : RawPresheaf.{u,max u v} B} (φ : F ⟶ G)
    (V : Opens X) (s : Families F V) (U : Inside B V) :
    (familyMap φ V s).val U = φ.app (op U.val) (s.val U) := rfl

/-- The actual all-open presheaf of compatible families. -/
def extensionRaw (F : RawPresheaf.{u,max u v} B) :
    RawPresheaf.{u,max u v} (allOpenBasis X) where
  obj V := AddCommGrpCat.of (Families F V.unop.obj)
  map f := AddCommGrpCat.ofHom (familyRestriction F f.unop.hom.le)
  map_id _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply families_ext
    intro U
    rfl
  map_comp _ _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply families_ext
    intro U
    rfl

/-- The actual natural transformation on compatible families. -/
def extensionRawMap {F G : RawPresheaf.{u,max u v} B} (φ : F ⟶ G) :
    extensionRaw F ⟶ extensionRaw G where
  app V := AddCommGrpCat.ofHom (familyMap φ V.unop.obj)
  naturality _ _ _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply families_ext
    intro U
    rfl

/-- The raw extension functor. Sheafhood is proved below for sheaf inputs. -/
def rawExtension (B : OpenBasis X) :
    RawPresheaf.{u,max u v} B ⥤ RawPresheaf.{u,max u v} (allOpenBasis X) where
  obj := extensionRaw
  map := extensionRawMap
  map_id _ := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply families_ext
    intro U
    rfl
  map_comp _ _ := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply families_ext
    intro U
    rfl

@[simp] theorem extensionRaw_restriction (F : RawPresheaf.{u,max u v} B)
    {U V : BasisOpen (allOpenBasis X)} (h : U.obj ≤ V.obj) :
    (restriction (extensionRaw F) h).hom = familyRestriction F h := rfl

/-- On an original basis member the family is canonically the original section. -/
def basisSectionIso (F : RawPresheaf.{u,max u v} B) (U : BasisOpen B) :
    Sections F U ≃+ Families F U.obj where
  toFun s := ⟨fun W => restriction F W.property s, by
    intro W T h
    exact restriction_comp_apply F h W.property s⟩
  invFun s := s.val ⟨U, le_rfl⟩
  left_inv s := restriction_self_apply F U s
  right_inv s := by
    apply families_ext
    intro W
    exact s.property ⟨U, le_rfl⟩ W W.property
  map_add' s t := by apply families_ext; intro W; exact map_add _ _ _

@[simp] theorem basisSectionIso_apply (F : RawPresheaf.{u,max u v} B)
    (U : BasisOpen B) (s : Sections F U) (W : Inside B U.obj) :
    (basisSectionIso F U s).val W = restriction F W.property s := rfl

@[simp] theorem basisSectionIso_symm_apply (F : RawPresheaf.{u,max u v} B)
    (U : BasisOpen B) (s : Families F U.obj) :
    (basisSectionIso F U).symm s = s.val ⟨U, le_rfl⟩ := rfl

theorem basisSectionIso_restriction (F : RawPresheaf.{u,max u v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (s : Sections F V) :
    basisSectionIso F U (restriction F h s) =
      familyRestriction F h (basisSectionIso F V s) := by
  apply families_ext
  intro W
  exact restriction_comp_apply F W.property h s

theorem basisSectionIso_naturality {F G : RawPresheaf.{u,max u v} B}
    (φ : F ⟶ G) (U : BasisOpen B) (s : Sections F U) :
    basisSectionIso G U (φ.app (op U) s) = familyMap φ U.obj (basisSectionIso F U s) := by
  apply families_ext
  intro W
  exact (restriction_naturality_apply φ W.property s).symm

/-- Original-section matching against local compatible families. -/
def LocallyMatches (F : RawPresheaf.{u,max u v} B) {ι : Type w}
    (O : ι → Opens X) (s : ∀ i, Families F (O i)) (U : BasisOpen B)
    (t : Sections F U) : Prop :=
  ∀ i (W : BasisOpen B) (hWU : W.obj ≤ U.obj) (hWi : W.obj ≤ O i),
    restriction F hWU t = (s i).val ⟨W, hWi⟩

/-- Glue the original sections on the basis refinement of a local open cover. -/
theorem unique_basis_glue (F : BasisSheaf.{u,max u v} B) {ι : Type w}
    (O : ι → Opens X) (s : ∀ i, Families F.obj.obj (O i))
    (hs : ∀ i j (W : BasisOpen B) (hi : W.obj ≤ O i) (hj : W.obj ≤ O j),
      (s i).val ⟨W, hi⟩ = (s j).val ⟨W, hj⟩)
    (U : BasisOpen B) (hcover : ∀ x ∈ U.obj, ∃ i, x ∈ O i) :
    ∃! t : Sections F.obj.obj U, LocallyMatches F.obj.obj O s U t := by
  let I := Σ i, {W : BasisOpen B // W.obj ≤ U.obj ∧ W.obj ≤ O i}
  let R : I → BasisOpen B := fun z => z.2.val
  have hR : FamilyCovers U R := by
    refine ⟨fun z => z.2.property.1, ?_⟩
    intro x hx
    obtain ⟨i, hxi⟩ := hcover x hx
    obtain ⟨W, hxW, hW⟩ := B.exists_subset (U.obj ⊓ O i) ⟨hx, hxi⟩
    exact ⟨⟨i, ⟨W, le_inf_iff.mp hW⟩⟩, hxW⟩
  let r : ∀ z, Sections F.obj.obj (R z) := fun z =>
    (s z.1).val ⟨z.2.val, z.2.property.2⟩
  have hr : Compatible F.obj.obj R r := by
    intro a b W hWa hWb
    exact ((s a.1).property ⟨a.2.val, a.2.property.2⟩
        ⟨W, hWa.trans a.2.property.2⟩ hWa).trans
      ((hs a.1 b.1 W _ _).trans
        ((s b.1).property ⟨b.2.val, b.2.property.2⟩
          ⟨W, hWb.trans b.2.property.2⟩ hWb).symm)
  obtain ⟨t, ht, huniq⟩ := F.unique_gluing U R hR r hr
  refine ⟨t, ?_, ?_⟩
  · intro i W hWU hWi
    exact ht ⟨i, ⟨W, hWU, hWi⟩⟩
  · intro y hy
    apply huniq y
    intro z
    exact hy z.1 z.2.val z.2.property.1 z.2.property.2

/-- The compatible-family extension has literal source gluing for every index universe. -/
theorem extension_familySheafCondition (F : BasisSheaf.{u,max u v} B) :
    FamilySheafCondition.{u,max u v,w} (extensionRaw F.obj.obj) := by
  classical
  intro ι V O hO s hs
  have hs' : ∀ i j (W : BasisOpen B) (hi : W.obj ≤ (O i).obj)
      (hj : W.obj ≤ (O j).obj), (s i).val ⟨W, hi⟩ = (s j).val ⟨W, hj⟩ := by
    intro i j W hi hj
    exact congrArg (fun a : Families F.obj.obj W.obj => a.val ⟨W, le_rfl⟩)
      (hs i j (allOpen W.obj) hi hj)
  have hlocal : ∀ T : Inside B V.obj, ∃! t : Sections F.obj.obj T.val,
      LocallyMatches F.obj.obj (fun i => (O i).obj) s T.val t := by
    intro T
    exact unique_basis_glue F (fun i => (O i).obj) s hs' T.val
      (fun x hx => hO.2 x (T.property hx))
  let t : Families F.obj.obj V.obj := ⟨fun T => Classical.choose (hlocal T), by
    intro T W hWT
    apply (Classical.choose_spec (hlocal W)).2
    intro i Z hZW hZi
    rw [restriction_comp_apply]
    exact (Classical.choose_spec (hlocal T)).1 i Z (hZW.trans hWT) hZi⟩
  refine ⟨t, ?_, ?_⟩
  · intro i
    apply families_ext
    intro W
    have ht := (Classical.choose_spec
      (hlocal ⟨W.val, W.property.trans (hO.1 i)⟩)).1 i W.val le_rfl W.property
    exact (restriction_self_apply _ _ _).symm.trans ht
  · intro y hy
    apply families_ext
    intro T
    apply (Classical.choose_spec (hlocal T)).2
    intro i W hWT hWi
    exact (y.property T ⟨W, hWT.trans T.property⟩ hWT).trans
      (congrArg (fun a : Families F.obj.obj (O i).obj => a.val ⟨W, hWi⟩) (hy i))

/-- The exact published set-cover predicate follows, retaining its empty cover. -/
theorem extension_sheafCondition (F : BasisSheaf.{u,max u v} B) :
    SheafCondition (extensionRaw F.obj.obj) :=
  FamilySheafCondition.sheafCondition _ (extension_familySheafCondition F)

/-- Empty-open normalization is derived from actual empty-cover gluing. -/
theorem extension_isNormalized (F : BasisSheaf.{u,max u v} B) :
    IsNormalized (extensionRaw F.obj.obj) :=
  SheafCondition.isNormalized _ (extension_sheafCondition F)

/-- Extend the actual chosen-basis sheaf, with its original morphisms. -/
def extension (B : OpenBasis X) :
    BasisSheaf.{u,max u v} B ⥤ BasisSheaf.{u,max u v} (allOpenBasis X) where
  obj F := ⟨⟨extensionRaw F.obj.obj, extension_isNormalized F⟩, extension_sheafCondition F⟩
  map φ := ObjectProperty.homMk (ObjectProperty.homMk (extensionRawMap φ.hom.hom))
  map_id F := by
    apply ObjectProperty.hom_ext _
    apply ObjectProperty.hom_ext _
    exact (rawExtension B).map_id F.obj.obj
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext _
    apply ObjectProperty.hom_ext _
    exact (rawExtension B).map_comp φ.hom.hom ψ.hom.hom

/-- An all-open section gives its family of original chosen-basis restrictions. -/
def allOpenToFamily (B : OpenBasis X) (G : RawPresheaf.{u,max u v} (allOpenBasis X))
    (V : Opens X) : Sections G (allOpen V) →+
      Families ((rawBasisRestriction B).obj G) V where
  toFun s := ⟨fun U => restriction G U.property s, by
    intro U W h
    exact restriction_comp_apply G h U.property s⟩
  map_zero' := by apply families_ext; intro U; exact map_zero _
  map_add' s t := by apply families_ext; intro U; exact map_add _ _ _

@[simp] theorem allOpenToFamily_apply (B : OpenBasis X)
    (G : RawPresheaf.{u,max u v} (allOpenBasis X)) (V : Opens X)
    (s : Sections G (allOpen V)) (U : Inside B V) :
    (allOpenToFamily B G V s).val U = restriction G U.property s := rfl

/-- The original all-open sheaf gluing law makes its restriction-family map bijective. -/
theorem allOpenToFamily_bijective (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) (V : Opens X) :
    Function.Bijective (allOpenToFamily B G.obj.obj V) := by
  constructor
  · intro s t h
    apply allOpen_sections_eq_of_basis_restrictions B G (allOpen V) s t
    intro U hU
    exact congrArg (fun a => a.val ⟨U, hU⟩) h
  · intro s
    let U : Inside B V → BasisOpen B := fun T => T.val
    have hs : Compatible ((rawBasisRestriction B).obj G.obj.obj) U s.val := by
      intro T R W hWT hWR
      exact (s.property T ⟨W, hWT.trans T.property⟩ hWT).trans
        (s.property R ⟨W, hWR.trans R.property⟩ hWR).symm
    obtain ⟨t, ht, _⟩ := G.unique_gluing (allOpen V)
      (fun T : Inside B V => allOpen T.val.obj) (basisRefinement_covers B (allOpen V))
      s.val (basisCompatible_allOpenCompatible B G U s.val hs)
    exact ⟨t, families_ext ht⟩

/-- The counit on actual sections: unique gluing, inverse to original basis restrictions. -/
noncomputable def counitSectionIso (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) (V : Opens X) :
    Families ((rawBasisRestriction B).obj G.obj.obj) V ≃+
      Sections G.obj.obj (allOpen V) :=
  (AddEquiv.ofBijective (allOpenToFamily B G.obj.obj V)
    (allOpenToFamily_bijective B G V)).symm

@[simp] theorem counitSectionIso_symm_apply (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) (V : Opens X)
    (s : Sections G.obj.obj (allOpen V)) :
    (counitSectionIso B G V).symm s = allOpenToFamily B G.obj.obj V s := rfl

/-- Evaluation of gluing on every original chosen-basis member. -/
theorem counitSectionIso_amalgamation (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) (V : Opens X)
    (s : Families ((rawBasisRestriction B).obj G.obj.obj) V)
    (U : BasisOpen B) (hU : U.obj ≤ V) :
    restriction G.obj.obj (U := allOpen U.obj) (V := allOpen V) hU
      (counitSectionIso B G V s) =
      s.val ⟨U, hU⟩ :=
  congrArg (fun a => a.val ⟨U, hU⟩) ((counitSectionIso B G V).symm_apply_apply s)

/-- The displayed gluing is uniquely determined by precisely these original restrictions. -/
theorem counitSectionIso_unique (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) (V : Opens X)
    (s : Families ((rawBasisRestriction B).obj G.obj.obj) V)
    (t : Sections G.obj.obj (allOpen V))
    (ht : ∀ (U : BasisOpen B) (hU : U.obj ≤ V), restriction G.obj.obj (U := allOpen U.obj) (V := allOpen V) hU t = s.val ⟨U, hU⟩) :
    t = counitSectionIso B G V s := by
  apply allOpen_sections_eq_of_basis_restrictions B G (allOpen V)
  intro U hU
  exact (ht U hU).trans (counitSectionIso_amalgamation B G V s U hU).symm

theorem counitSectionIso_restriction (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) {U V : Opens X} (h : U ≤ V)
    (s : Families ((rawBasisRestriction B).obj G.obj.obj) V) :
    counitSectionIso B G U (familyRestriction _ h s) =
      restriction G.obj.obj (U := allOpen U) (V := allOpen V) h
        (counitSectionIso B G V s) := by
  apply allOpen_sections_eq_of_basis_restrictions B G (allOpen U)
  intro T hT
  exact (counitSectionIso_amalgamation B G U (familyRestriction _ h s) T hT).trans
    ((counitSectionIso_amalgamation B G V s T (hT.trans h)).symm.trans
      (restriction_comp_apply G.obj.obj (U := allOpen T.obj)
        (V := allOpen U) (W := allOpen V) hT h (counitSectionIso B G V s)).symm)

theorem counitSectionIso_naturality (B : OpenBasis X)
    {G H : BasisSheaf.{u,max u v} (allOpenBasis X)} (φ : G ⟶ H) (V : Opens X)
    (s : Families ((rawBasisRestriction B).obj G.obj.obj) V) :
    counitSectionIso B H V (familyMap ((rawBasisRestriction B).map φ.hom.hom) V s) =
      φ.hom.hom.app (op (allOpen V)) (counitSectionIso B G V s) := by
  apply allOpen_sections_eq_of_basis_restrictions B H (allOpen V)
  intro T hT
  calc
    restriction H.obj.obj hT
        (counitSectionIso B H V (familyMap ((rawBasisRestriction B).map φ.hom.hom) V s)) =
        φ.hom.hom.app (op (allOpen T.obj)) (s.val ⟨T, hT⟩) :=
      counitSectionIso_amalgamation B H V _ T hT
    _ = φ.hom.hom.app (op (allOpen T.obj))
        (restriction G.obj.obj hT (counitSectionIso B G V s)) :=
      congrArg (φ.hom.hom.app (op (allOpen T.obj)))
        (counitSectionIso_amalgamation B G V s T hT).symm
    _ = restriction H.obj.obj hT
        (φ.hom.hom.app (op (allOpen V)) (counitSectionIso B G V s)) :=
      restriction_naturality_apply φ.hom.hom hT _

/-- Raw unit on the original basis, with restriction families and evaluation as its maps. -/
def unitRawIso (F : RawPresheaf.{u,max u v} B) :
    F ≅ (rawBasisRestriction B).obj (extensionRaw F) :=
  NatIso.ofComponents (fun U => (basisSectionIso F U.unop).toAddCommGrpIso) (by
    intro U V f
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact basisSectionIso_restriction F f.unop.hom.le s)

/-- The unit through the existing two full-subcategory layers. -/
def unitIso (B : OpenBasis X) :
    𝟭 (BasisSheaf.{u,max u v} B) ≅ extension B ⋙ sheafBasisRestriction B :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (unitRawIso F.obj.obj))) (by
      intro F G φ
      apply ObjectProperty.hom_ext _
      apply ObjectProperty.hom_ext _
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact basisSectionIso_naturality φ.hom.hom U.unop s)

/-- Raw counit, built from actual all-open gluing. -/
noncomputable def counitRawIso (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) :
    extensionRaw ((rawBasisRestriction B).obj G.obj.obj) ≅ G.obj.obj :=
  NatIso.ofComponents (fun V => (counitSectionIso B G V.unop.obj).toAddCommGrpIso) (by
    intro U V f
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact counitSectionIso_restriction B G f.unop.hom.le s)

/-- The actual counit natural isomorphism on all-open sheaves. -/
noncomputable def counitIso (B : OpenBasis X) :
    sheafBasisRestriction B ⋙ extension B ≅ 𝟭 (BasisSheaf.{u,max u v} (allOpenBasis X)) :=
  NatIso.ofComponents
    (fun G => ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (counitRawIso B G))) (by
      intro G H φ
      apply ObjectProperty.hom_ext _
      apply ObjectProperty.hom_ext _
      apply NatTrans.ext
      funext V
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact counitSectionIso_naturality B φ V.unop.obj s)

/-- The forward triangle is the original compatibility equation, component by component. -/
theorem extension_unit_counit (F : BasisSheaf.{u,max u v} B) :
    (extension B).map ((unitIso B).hom.app F) ≫
      (counitIso B).hom.app ((extension B).obj F) = 𝟙 ((extension B).obj F) := by
  apply ObjectProperty.hom_ext _
  apply ObjectProperty.hom_ext _
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change Families F.obj.obj V.unop.obj at s
  change counitSectionIso B ((extension B).obj F) V.unop.obj
    (familyMap (unitRawIso F.obj.obj).hom V.unop.obj s) = s
  apply (counitSectionIso B ((extension B).obj F) V.unop.obj).symm.injective
  refine ((counitSectionIso B ((extension B).obj F) V.unop.obj).symm_apply_apply _).trans ?_
  apply families_ext
  intro U
  apply families_ext
  intro T
  exact s.property U ⟨T.val, T.property.trans U.property⟩ T.property

/-- The actual equivalence at the sufficient section universe. -/
noncomputable def equivalence (B : OpenBasis X) :
    BasisSheaf.{u,max u v} B ≌ BasisSheaf.{u,max u v} (allOpenBasis X) where
  functor := extension B
  inverse := sheafBasisRestriction B
  unitIso := unitIso B
  counitIso := counitIso B
  functor_unitIso_comp := extension_unit_counit

@[simp] theorem extension_sections (F : BasisSheaf.{u,max u v} B) (V : Opens X) :
    Sections ((extension B).obj F).obj.obj (allOpen V) =
      AddCommGrpCat.of (Families F.obj.obj V) := rfl

@[simp] theorem extension_restriction (F : BasisSheaf.{u,max u v} B)
    {U V : Opens X} (h : U ≤ V) :
    (restriction ((extension B).obj F).obj.obj
      (U := allOpen U) (V := allOpen V) h).hom = familyRestriction F.obj.obj h := rfl

@[simp] theorem extension_map_app {F G : BasisSheaf.{u,max u v} B}
    (φ : F ⟶ G) (V : Opens X) :
    (((extension B).map φ).hom.hom.app (op (allOpen V))).hom =
      familyMap φ.hom.hom V := rfl

/-- The extension uses exactly the raw compatible-family functor after forgetting. -/
theorem extension_forget (B : OpenBasis X) :
    extension.{u,v} B ⋙ sheafForget (allOpenBasis X) ⋙ presheafInclusion (allOpenBasis X) =
      sheafForget B ⋙ presheafInclusion B ⋙ rawExtension B := rfl

/-- This includes empty spaces and bases that do not contain the empty open. -/
theorem extension_empty_zero (F : BasisSheaf.{u,max u v} B)
    (s : Families F.obj.obj (⊥ : Opens X)) : s = 0 := by
  have : Subsingleton (Families F.obj.obj (⊥ : Opens X)) :=
    extension_isNormalized F (allOpen ⊥) rfl
  exact Subsingleton.elim _ _

@[simp] theorem basisSectionIso_symm_apply_apply (F : RawPresheaf.{u,max u v} B)
    (U : BasisOpen B) (s : Sections F U) :
    (basisSectionIso F U).symm (basisSectionIso F U s) = s :=
  (basisSectionIso F U).symm_apply_apply s

@[simp] theorem basisSectionIso_apply_symm_apply (F : RawPresheaf.{u,max u v} B)
    (U : BasisOpen B) (s : Families F U.obj) :
    basisSectionIso F U ((basisSectionIso F U).symm s) = s :=
  (basisSectionIso F U).apply_symm_apply s

theorem basisSectionIso_symm_restriction (F : RawPresheaf.{u,max u v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (s : Families F V.obj) :
    (basisSectionIso F U).symm (familyRestriction F h s) =
      restriction F h ((basisSectionIso F V).symm s) :=
  (s.property ⟨V, le_rfl⟩ ⟨U, h⟩ h).symm

theorem basisSectionIso_symm_naturality {F G : RawPresheaf.{u,max u v} B}
    (φ : F ⟶ G) (U : BasisOpen B) (s : Families F U.obj) :
    (basisSectionIso G U).symm (familyMap φ U.obj s) =
      φ.app (op U) ((basisSectionIso F U).symm s) := rfl

@[simp] theorem counitSectionIso_symm_apply_apply (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) (V : Opens X)
    (s : Families ((rawBasisRestriction B).obj G.obj.obj) V) :
    (counitSectionIso B G V).symm (counitSectionIso B G V s) = s :=
  (counitSectionIso B G V).symm_apply_apply s

@[simp] theorem counitSectionIso_apply_symm_apply (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) (V : Opens X)
    (s : Sections G.obj.obj (allOpen V)) :
    counitSectionIso B G V ((counitSectionIso B G V).symm s) = s :=
  (counitSectionIso B G V).apply_symm_apply s

theorem counitSectionIso_symm_restriction (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) {U V : Opens X} (h : U ≤ V)
    (s : Sections G.obj.obj (allOpen V)) :
    (counitSectionIso B G U).symm
        (restriction G.obj.obj (U := allOpen U) (V := allOpen V) h s) =
      familyRestriction _ h ((counitSectionIso B G V).symm s) := by
  apply families_ext
  intro T
  exact restriction_comp_apply G.obj.obj (U := allOpen T.val.obj)
    (V := allOpen U) (W := allOpen V) T.property h s

theorem counitSectionIso_symm_naturality (B : OpenBasis X)
    {G H : BasisSheaf.{u,max u v} (allOpenBasis X)} (φ : G ⟶ H) (V : Opens X)
    (s : Sections G.obj.obj (allOpen V)) :
    (counitSectionIso B H V).symm (φ.hom.hom.app (op (allOpen V)) s) =
      familyMap ((rawBasisRestriction B).map φ.hom.hom) V
        ((counitSectionIso B G V).symm s) := by
  apply families_ext
  intro T
  exact (restriction_naturality_apply φ.hom.hom
    (U := allOpen T.val.obj) (V := allOpen V) T.property s).symm

@[simp] theorem unit_hom_app (F : BasisSheaf.{u,max u v} B) (U : BasisOpen B) :
    ((unitIso B).hom.app F).hom.hom.app (op U) =
      (basisSectionIso F.obj.obj U).toAddCommGrpIso.hom := rfl

@[simp] theorem unit_inv_app (F : BasisSheaf.{u,max u v} B) (U : BasisOpen B) :
    ((unitIso B).inv.app F).hom.hom.app (op U) =
      (basisSectionIso F.obj.obj U).toAddCommGrpIso.inv := rfl

@[simp] theorem unit_hom_apply (F : BasisSheaf.{u,max u v} B) (U : BasisOpen B)
    (s : Sections F.obj.obj U) :
    ((unitIso B).hom.app F).hom.hom.app (op U) s = basisSectionIso F.obj.obj U s := rfl

@[simp] theorem unit_inv_apply (F : BasisSheaf.{u,max u v} B) (U : BasisOpen B)
    (s : Families F.obj.obj U.obj) :
    ((unitIso B).inv.app F).hom.hom.app (op U) s = s.val ⟨U, le_rfl⟩ := rfl

@[simp] theorem counit_hom_app (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) (V : Opens X) :
    ((counitIso B).hom.app G).hom.hom.app (op (allOpen V)) =
      (counitSectionIso B G V).toAddCommGrpIso.hom := rfl

@[simp] theorem counit_inv_app (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) (V : Opens X) :
    ((counitIso B).inv.app G).hom.hom.app (op (allOpen V)) =
      (counitSectionIso B G V).toAddCommGrpIso.inv := rfl

@[simp] theorem counit_hom_apply (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) (V : Opens X)
    (s : Families ((rawBasisRestriction B).obj G.obj.obj) V) :
    ((counitIso B).hom.app G).hom.hom.app (op (allOpen V)) s =
      counitSectionIso B G V s := rfl

@[simp] theorem counit_inv_apply (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) (V : Opens X)
    (s : Sections G.obj.obj (allOpen V)) :
    ((counitIso B).inv.app G).hom.hom.app (op (allOpen V)) s =
      allOpenToFamily B G.obj.obj V s := rfl

@[simp] theorem unit_hom_inv_id (F : BasisSheaf.{u,max u v} B) :
    (unitIso B).hom.app F ≫ (unitIso B).inv.app F = 𝟙 F :=
  ((unitIso B).app F).hom_inv_id

@[simp] theorem unit_inv_hom_id (F : BasisSheaf.{u,max u v} B) :
    (unitIso B).inv.app F ≫ (unitIso B).hom.app F =
      𝟙 ((sheafBasisRestriction B).obj ((extension B).obj F)) :=
  ((unitIso B).app F).inv_hom_id

@[simp] theorem counit_hom_inv_id (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) :
    (counitIso B).hom.app G ≫ (counitIso B).inv.app G =
      𝟙 ((extension B).obj ((sheafBasisRestriction B).obj G)) :=
  ((counitIso B).app G).hom_inv_id

@[simp] theorem counit_inv_hom_id (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) :
    (counitIso B).inv.app G ≫ (counitIso B).hom.app G = 𝟙 G :=
  ((counitIso B).app G).inv_hom_id

@[simp] theorem inverse_triangle (B : OpenBasis X)
    (G : BasisSheaf.{u,max u v} (allOpenBasis X)) :
    (unitIso B).hom.app ((sheafBasisRestriction B).obj G) ≫
      (sheafBasisRestriction B).map ((counitIso B).hom.app G) =
      𝟙 ((sheafBasisRestriction B).obj G) :=
  (equivalence B).unit_inverse_comp G

end Langlands.Sheaf.Renard.BasisAllOpen
