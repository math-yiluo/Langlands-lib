import Langlands.Sheaf.Renard.BasisStalkComparison

/-!
# Germ sections before and after restricting an all-open presheaf to a chosen basis

The stalk comparison transports families of germs pointwise. Local representation is
preserved in both directions on whole contained neighborhoods, so the transport restricts
to the actual germ-section groups and packages into a natural isomorphism of the all-open
germ-sheaf functors.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X]

/-- Pointwise transport of an arbitrary germ family by the stalk comparison. -/
noncomputable def germFamilyRestrictionEquiv (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X) :
    GermFamily ((rawBasisRestriction B).obj F) U ≃+ GermFamily F U :=
  AddEquiv.piCongrRight fun x : U => rawStalkRestrictionEquiv B F x.val

@[simp]
theorem germFamilyRestrictionEquiv_apply (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X)
    (s : GermFamily ((rawBasisRestriction B).obj F) U) (x : U) :
    germFamilyRestrictionEquiv B F U s x = rawStalkRestrictionEquiv B F x.val (s x) := rfl

@[simp]
theorem germFamilyRestrictionEquiv_symm_apply (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X) (s : GermFamily F U) (x : U) :
    (germFamilyRestrictionEquiv B F U).symm s x =
      (rawStalkRestrictionEquiv B F x.val).symm (s x) := rfl

/-- A restricted representative on a basis open is an original representative on the same
actual open. -/
theorem LocallyRepresented.restrictionTransport (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X)
    {s : GermFamily ((rawBasisRestriction B).obj F) U}
    (hs : LocallyRepresented ((rawBasisRestriction B).obj F) U s) :
    LocallyRepresented F U (germFamilyRestrictionEquiv B F U s) := by
  intro x
  obtain ⟨V, hxV, hVU, t, ht⟩ := hs x
  refine ⟨allOpen V.obj, hxV, hVU, t, ?_⟩
  intro y hy
  rw [germFamilyRestrictionEquiv_apply, ← ht y hy]
  exact (rawStalkRestrictionEquiv_germ B F V y hy t).symm

/-- In the inverse direction, refine an actual representing neighborhood to a chosen basis
neighborhood and restrict the original representing section. -/
theorem LocallyRepresented.restrictionTransportSymm (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X) {s : GermFamily F U}
    (hs : LocallyRepresented F U s) :
    LocallyRepresented ((rawBasisRestriction B).obj F) U
      ((germFamilyRestrictionEquiv B F U).symm s) := by
  intro x
  obtain ⟨W, hxW, hWU, t, ht⟩ := hs x
  obtain ⟨V, hxV, hVW⟩ := B.exists_subset W.obj hxW
  refine ⟨V, hxV, hVW.trans hWU, restriction F (U := allOpen V.obj) hVW t, ?_⟩
  intro y hy
  rw [germFamilyRestrictionEquiv_symm_apply, ← ht y (hVW hy),
    rawStalkRestrictionEquiv_symm_germ_of_le]

/-- Local representation is unchanged by the pointwise stalk comparison. -/
theorem locallyRepresented_restriction_iff (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X)
    (s : GermFamily ((rawBasisRestriction B).obj F) U) :
    LocallyRepresented ((rawBasisRestriction B).obj F) U s ↔
      LocallyRepresented F U (germFamilyRestrictionEquiv B F U s) := by
  refine ⟨LocallyRepresented.restrictionTransport B F U, fun h => ?_⟩
  have h' := LocallyRepresented.restrictionTransportSymm B F U h
  rwa [AddEquiv.symm_apply_apply] at h'

/-- Local representation is unchanged by the inverse pointwise comparison. -/
theorem locallyRepresented_restriction_symm_iff (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X) (s : GermFamily F U) :
    LocallyRepresented F U s ↔
      LocallyRepresented ((rawBasisRestriction B).obj F) U
        ((germFamilyRestrictionEquiv B F U).symm s) := by
  rw [locallyRepresented_restriction_iff, AddEquiv.apply_symm_apply]

/-- The stalk comparison restricted to the actual locally represented families. -/
noncomputable def germSectionsRestrictionEquiv (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X) :
    GermSections ((rawBasisRestriction B).obj F) U ≃+ GermSections F U where
  toFun s := ⟨germFamilyRestrictionEquiv B F U s.val,
    LocallyRepresented.restrictionTransport B F U s.property⟩
  invFun s := ⟨(germFamilyRestrictionEquiv B F U).symm s.val,
    LocallyRepresented.restrictionTransportSymm B F U s.property⟩
  left_inv s := Subtype.ext ((germFamilyRestrictionEquiv B F U).symm_apply_apply s.val)
  right_inv s := Subtype.ext ((germFamilyRestrictionEquiv B F U).apply_symm_apply s.val)
  map_add' s t := Subtype.ext (map_add (germFamilyRestrictionEquiv B F U) s.val t.val)

@[simp]
theorem germSectionsRestrictionEquiv_apply (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X)
    (s : GermSections ((rawBasisRestriction B).obj F) U) (x : U) :
    (germSectionsRestrictionEquiv B F U s).val x =
      rawStalkRestrictionEquiv B F x.val (s.val x) := rfl

@[simp]
theorem germSectionsRestrictionEquiv_symm_apply (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X) (s : GermSections F U) (x : U) :
    ((germSectionsRestrictionEquiv B F U).symm s).val x =
      (rawStalkRestrictionEquiv B F x.val).symm (s.val x) := rfl

/-- A restricted representative is sent to the germs of the same original section. -/
theorem germSectionsRestrictionEquiv_representative (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) {U : Opens X}
    (s : GermSections ((rawBasisRestriction B).obj F) U) (V : BasisOpen B)
    (hVU : V.obj ≤ U) (t : Sections F (allOpen V.obj))
    (ht : ∀ (y : X) (hy : y ∈ V.obj),
      rawGerm ((rawBasisRestriction B).obj F) V y hy t = s.val ⟨y, hVU hy⟩)
    (y : X) (hy : y ∈ V.obj) :
    (germSectionsRestrictionEquiv B F U s).val ⟨y, hVU hy⟩ =
      rawGerm F (allOpen V.obj) y hy t := by
  rw [germSectionsRestrictionEquiv_apply, ← ht y hy, rawStalkRestrictionEquiv_germ]

/-- An original representative on a chosen basis open is sent to the restricted germs of the
same original section. -/
theorem germSectionsRestrictionEquiv_symm_representative (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) {U : Opens X} (s : GermSections F U)
    (V : BasisOpen B) (hVU : V.obj ≤ U) (t : Sections F (allOpen V.obj))
    (ht : ∀ (y : X) (hy : y ∈ V.obj), rawGerm F (allOpen V.obj) y hy t = s.val ⟨y, hVU hy⟩)
    (y : X) (hy : y ∈ V.obj) :
    ((germSectionsRestrictionEquiv B F U).symm s).val ⟨y, hVU hy⟩ =
      rawGerm ((rawBasisRestriction B).obj F) V y hy t := by
  rw [germSectionsRestrictionEquiv_symm_apply, ← ht y hy, rawStalkRestrictionEquiv_symm_germ]

/-- An original representative on an arbitrary actual open is sent, on any smaller chosen
basis open, to the restricted germs of its original restriction. -/
theorem germSectionsRestrictionEquiv_symm_representative_of_le (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) {U : Opens X} (s : GermSections F U)
    (W : BasisOpen (allOpenBasis X)) (hWU : W.obj ≤ U) (t : Sections F W)
    (ht : ∀ (y : X) (hy : y ∈ W.obj), rawGerm F W y hy t = s.val ⟨y, hWU hy⟩)
    (V : BasisOpen B) (hVW : V.obj ≤ W.obj) (y : X) (hy : y ∈ V.obj) :
    ((germSectionsRestrictionEquiv B F U).symm s).val ⟨y, hWU (hVW hy)⟩ =
      rawGerm ((rawBasisRestriction B).obj F) V y hy
        (restriction F (U := allOpen V.obj) hVW t) := by
  rw [germSectionsRestrictionEquiv_symm_apply, ← ht y (hVW hy),
    rawStalkRestrictionEquiv_symm_germ_of_le]

/-- Compatibility with the published germ restriction along an actual-open inclusion. -/
theorem germSectionsRestrictionEquiv_restriction (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) {U V : Opens X} (h : U ≤ V)
    (s : GermSections ((rawBasisRestriction B).obj F) V) :
    germSectionsRestrictionEquiv B F U (germRestriction ((rawBasisRestriction B).obj F) h s) =
      germRestriction F h (germSectionsRestrictionEquiv B F V s) := rfl

theorem germSectionsRestrictionEquiv_symm_restriction (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) {U V : Opens X} (h : U ≤ V)
    (s : GermSections F V) :
    (germSectionsRestrictionEquiv B F U).symm (germRestriction F h s) =
      germRestriction ((rawBasisRestriction B).obj F) h
        ((germSectionsRestrictionEquiv B F V).symm s) := rfl

/-- Naturality for an original natural transformation and its actual restriction. -/
theorem germSectionsRestrictionEquiv_naturality (B : OpenBasis X)
    {F G : RawPresheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (U : Opens X)
    (s : GermSections ((rawBasisRestriction B).obj F) U) :
    germSectionsRestrictionEquiv B G U (germSectionsMap ((rawBasisRestriction B).map φ) U s) =
      germSectionsMap φ U (germSectionsRestrictionEquiv B F U s) :=
  GermSections.ext fun x => rawStalkRestrictionEquiv_naturality B φ x.val (s.val x)

theorem germSectionsRestrictionEquiv_symm_naturality (B : OpenBasis X)
    {F G : RawPresheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (U : Opens X)
    (s : GermSections F U) :
    (germSectionsRestrictionEquiv B G U).symm (germSectionsMap φ U s) =
      germSectionsMap ((rawBasisRestriction B).map φ) U
        ((germSectionsRestrictionEquiv B F U).symm s) :=
  GermSections.ext fun x => rawStalkRestrictionEquiv_symm_naturality B φ x.val (s.val x)

/-- The section isomorphisms as an isomorphism of the all-open germ presheaves. -/
noncomputable def germPresheafRestrictionIso (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) :
    germPresheafOn (allOpenBasis X) ((rawBasisRestriction B).obj F) ≅
      germPresheafOn (allOpenBasis X) F :=
  NatIso.ofComponents
    (fun U => (germSectionsRestrictionEquiv B F U.unop.obj).toAddCommGrpIso)
    (fun _ => rfl)

/-- The same isomorphism of the actual all-open germ sheaves. -/
noncomputable def germSheafRestrictionIso (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) :
    germSheafOn (allOpenBasis X) ((rawBasisRestriction B).obj F) ≅
      germSheafOn (allOpenBasis X) F :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (germPresheafRestrictionIso B F))

/-- Germ extension after basis restriction is the original all-open germ extension. -/
noncomputable def rawRestrictedGermSheafIso (B : OpenBasis X) :
    rawBasisRestriction.{u,v} B ⋙ rawAllOpenGermSheafFunctor B ≅
      rawAllOpenGermSheafFunctor (allOpenBasis X) :=
  NatIso.ofComponents (fun F => germSheafRestrictionIso B F) (fun φ => by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro s
    exact germSectionsRestrictionEquiv_naturality B φ U.unop.obj s)

@[simp]
theorem rawRestrictedGermSheafIso_hom_app (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X) :
    (((rawRestrictedGermSheafIso B).hom.app F).hom.hom.app (op (allOpen U))).hom =
      (germSectionsRestrictionEquiv B F U).toAddMonoidHom := rfl

@[simp]
theorem rawRestrictedGermSheafIso_inv_app (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X) :
    (((rawRestrictedGermSheafIso B).inv.app F).hom.hom.app (op (allOpen U))).hom =
      (germSectionsRestrictionEquiv B F U).symm.toAddMonoidHom := rfl

theorem rawRestrictedGermSheafIso_hom_apply (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X)
    (s : GermSections ((rawBasisRestriction B).obj F) U) :
    (((rawRestrictedGermSheafIso B).hom.app F).hom.hom.app (op (allOpen U))) s =
      germSectionsRestrictionEquiv B F U s := rfl

theorem rawRestrictedGermSheafIso_inv_apply (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : Opens X) (s : GermSections F U) :
    (((rawRestrictedGermSheafIso B).inv.app F).hom.hom.app (op (allOpen U))) s =
      (germSectionsRestrictionEquiv B F U).symm s := rfl

/-- The hom components commute with the published germ restrictions. -/
theorem rawRestrictedGermSheafIso_hom_restriction (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) {U V : Opens X} (h : U ≤ V)
    (s : GermSections ((rawBasisRestriction B).obj F) V) :
    (((rawRestrictedGermSheafIso B).hom.app F).hom.hom.app (op (allOpen U)))
        (germRestriction ((rawBasisRestriction B).obj F) h s) =
      germRestriction F h
        ((((rawRestrictedGermSheafIso B).hom.app F).hom.hom.app (op (allOpen V))) s) := rfl

theorem rawRestrictedGermSheafIso_inv_restriction (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) {U V : Opens X} (h : U ≤ V)
    (s : GermSections F V) :
    (((rawRestrictedGermSheafIso B).inv.app F).hom.hom.app (op (allOpen U)))
        (germRestriction F h s) =
      germRestriction ((rawBasisRestriction B).obj F) h
        ((((rawRestrictedGermSheafIso B).inv.app F).hom.hom.app (op (allOpen V))) s) := rfl

/-- The hom components commute with the published germ-section maps. -/
theorem rawRestrictedGermSheafIso_hom_naturality (B : OpenBasis X)
    {F G : RawPresheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (U : Opens X)
    (s : GermSections ((rawBasisRestriction B).obj F) U) :
    (((rawRestrictedGermSheafIso B).hom.app G).hom.hom.app (op (allOpen U)))
        (germSectionsMap ((rawBasisRestriction B).map φ) U s) =
      germSectionsMap φ U
        ((((rawRestrictedGermSheafIso B).hom.app F).hom.hom.app (op (allOpen U))) s) :=
  germSectionsRestrictionEquiv_naturality B φ U s

theorem rawRestrictedGermSheafIso_inv_naturality (B : OpenBasis X)
    {F G : RawPresheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (U : Opens X)
    (s : GermSections F U) :
    (((rawRestrictedGermSheafIso B).inv.app G).hom.hom.app (op (allOpen U)))
        (germSectionsMap φ U s) =
      germSectionsMap ((rawBasisRestriction B).map φ) U
        ((((rawRestrictedGermSheafIso B).inv.app F).hom.hom.app (op (allOpen U))) s) :=
  germSectionsRestrictionEquiv_symm_naturality B φ U s

/-- The source-normalized specialization, by precomposing with the existing inclusion. -/
noncomputable def restrictedGermSheafIso (B : OpenBasis X) :
    basisRestriction.{u,v} B ⋙ allOpenGermSheafFunctor B ≅
      allOpenGermSheafFunctor (allOpenBasis X) :=
  Functor.isoWhiskerLeft (presheafInclusion (allOpenBasis X)) (rawRestrictedGermSheafIso B)

@[simp]
theorem restrictedGermSheafIso_app (B : OpenBasis X)
    (F : Presheaf.{u,v} (allOpenBasis X)) :
    (restrictedGermSheafIso B).app F = germSheafRestrictionIso B F.obj := rfl

theorem restrictedGermSheafIso_hom_apply (B : OpenBasis X)
    (F : Presheaf.{u,v} (allOpenBasis X)) (U : Opens X)
    (s : GermSections ((rawBasisRestriction B).obj F.obj) U) :
    (((restrictedGermSheafIso B).hom.app F).hom.hom.app (op (allOpen U))) s =
      germSectionsRestrictionEquiv B F.obj U s := rfl

theorem restrictedGermSheafIso_inv_apply (B : OpenBasis X)
    (F : Presheaf.{u,v} (allOpenBasis X)) (U : Opens X) (s : GermSections F.obj U) :
    (((restrictedGermSheafIso B).inv.app F).hom.hom.app (op (allOpen U))) s =
      (germSectionsRestrictionEquiv B F.obj U).symm s := rfl

end Langlands.Sheaf.Renard
