import Langlands.Sheaf.Renard.GermUnit
import Langlands.Sheaf.Renard.SheafGermSeparation

/-!
# Corrected descent of locally represented germ families

Glue images of actual original representatives in the actual target sheaf.
Only the target sheaf is separated; compatibility uses smaller basis opens.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- A contained local representative at every point, with no nonempty-domain premise. -/
structure GermDescentCover (F : RawPresheaf.{u,v} B) (U : BasisOpen B)
    (s : GermSections F U.obj) where
  opens : U.obj → BasisOpen B
  le : ∀ i, (opens i).obj ≤ U.obj
  point_mem : ∀ i, i.val ∈ (opens i).obj
  sections : ∀ i, Sections F (opens i)
  represents : ∀ i (x : X) (hx : x ∈ (opens i).obj),
    rawGerm F (opens i) x hx (sections i) = s.val ⟨x, le i hx⟩

/-- Choose contained original representatives; on an empty open this is empty data. -/
noncomputable def germDescentCover (F : RawPresheaf.{u,v} B) (U : BasisOpen B)
    (s : GermSections F U.obj) : GermDescentCover F U s := by
  classical
  choose V hx hVU t ht using s.property
  exact ⟨V, hVU, hx, t, ht⟩

/-- The chosen representatives form a literal cover of the original basis open. -/
theorem GermDescentCover.covers {F : RawPresheaf.{u,v} B} {U : BasisOpen B}
    {s : GermSections F U.obj} (C : GermDescentCover F U s) : FamilyCovers U C.opens :=
  ⟨C.le, fun x hx => ⟨⟨x, hx⟩, C.point_mem ⟨x, hx⟩⟩⟩

/-- Equal source germs imply compatible target images, without separating the source. -/
theorem GermDescentCover.compatible {F : RawPresheaf.{u,v} B}
    {G : BasisSheaf.{u,v} B} (ψ : F ⟶ G.obj.obj) {U : BasisOpen B}
    {s : GermSections F U.obj} (C : GermDescentCover F U s) :
    Compatible G.obj.obj C.opens (fun i => ψ.app (op (C.opens i)) (C.sections i)) := by
  apply rawTargetGermCompatibility F G.obj.obj ψ G.property
  intro i j x hxi hxj
  exact (C.represents i x hxi).trans (C.represents j x hxj).symm

/-- Glue the actual target images in the original target section group. -/
noncomputable def rawGermDescValue {F : RawPresheaf.{u,v} B}
    {G : BasisSheaf.{u,v} B} (ψ : F ⟶ G.obj.obj) (U : BasisOpen B)
    (s : GermSections F U.obj) : Sections G.obj.obj U :=
  let C := germDescentCover F U s
  Classical.choose (G.unique_gluing U C.opens C.covers
    (fun i => ψ.app (op (C.opens i)) (C.sections i)) (C.compatible ψ))

/-- Evaluation on the cover actually used in the construction. -/
theorem rawGermDescValue_chosen {F : RawPresheaf.{u,v} B}
    {G : BasisSheaf.{u,v} B} (ψ : F ⟶ G.obj.obj) (U : BasisOpen B)
    (s : GermSections F U.obj) (i : U.obj) :
    let C := germDescentCover F U s
    restriction G.obj.obj (C.le i) (rawGermDescValue ψ U s) =
      ψ.app (op (C.opens i)) (C.sections i) := by
  exact (Classical.choose_spec (G.unique_gluing U _ (germDescentCover F U s).covers
    _ ((germDescentCover F U s).compatible ψ))).1 i

/-- The glued original section has precisely the pointwise images of the input germs. -/
theorem rawGermDescValue_germ {F : RawPresheaf.{u,v} B}
    {G : BasisSheaf.{u,v} B} (ψ : F ⟶ G.obj.obj) (U : BasisOpen B)
    (s : GermSections F U.obj) (x : X) (hx : x ∈ U.obj) :
    rawGerm G.obj.obj U x hx (rawGermDescValue ψ U s) =
      rawStalkMap ψ x (s.val ⟨x, hx⟩) := by
  let C := germDescentCover F U s
  let i : U.obj := ⟨x, hx⟩
  calc
    rawGerm G.obj.obj U x hx (rawGermDescValue ψ U s) =
        rawGerm G.obj.obj (C.opens i) x (C.point_mem i)
          (restriction G.obj.obj (C.le i) (rawGermDescValue ψ U s)) :=
      (rawGerm_restriction G.obj.obj (C.le i) x (C.point_mem i) _).symm
    _ = rawGerm G.obj.obj (C.opens i) x (C.point_mem i)
          (ψ.app (op (C.opens i)) (C.sections i)) := by
      rw [rawGermDescValue_chosen]
    _ = rawStalkMap ψ x (s.val ⟨x, hx⟩) := by
      rw [← rawStalkMap_germ, C.represents]

/-- The component is an actual additive homomorphism into original target sections. -/
noncomputable def rawGermDesc {F : RawPresheaf.{u,v} B}
    {G : BasisSheaf.{u,v} B} (ψ : F ⟶ G.obj.obj) (U : BasisOpen B) :
    GermSections F U.obj →+ Sections G.obj.obj U where
  toFun := rawGermDescValue ψ U
  map_zero' := by
    apply rawSheafGermEquality G.obj.obj G.property U
    intro x hx
    rw [rawGermDescValue_germ]
    simp
  map_add' s t := by
    apply rawSheafGermEquality G.obj.obj G.property U
    intro x hx
    rw [rawGermDescValue_germ, map_add, rawGermDescValue_germ, rawGermDescValue_germ]
    exact map_add _ _ _

@[simp]
theorem rawGermDesc_apply {F : RawPresheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj.obj) (U : BasisOpen B) (s : GermSections F U.obj) :
    rawGermDesc ψ U s = rawGermDescValue ψ U s := rfl

/-- Intrinsic germ characterization of the component, independent of representatives. -/
theorem rawGermDesc_germ {F : RawPresheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj.obj) (U : BasisOpen B) (s : GermSections F U.obj)
    (x : X) (hx : x ∈ U.obj) :
    rawGerm G.obj.obj U x hx (rawGermDesc ψ U s) = rawStalkMap ψ x (s.val ⟨x, hx⟩) :=
  rawGermDescValue_germ ψ U s x hx

/-- Every contained original representative gives the same descended local image. -/
theorem rawGermDesc_representative {F : RawPresheaf.{u,v} B}
    {G : BasisSheaf.{u,v} B} (ψ : F ⟶ G.obj.obj) (U : BasisOpen B)
    (s : GermSections F U.obj) (V : BasisOpen B) (hVU : V.obj ≤ U.obj)
    (t : Sections F V)
    (ht : ∀ (x : X) (hx : x ∈ V.obj), rawGerm F V x hx t = s.val ⟨x, hVU hx⟩) :
    restriction G.obj.obj hVU (rawGermDesc ψ U s) = ψ.app (op V) t := by
  apply rawSheafGermEquality G.obj.obj G.property V
  intro x hx
  rw [rawGerm_restriction, rawGermDesc_germ, ← ht x hx, rawStalkMap_germ]

/-- The output is the unique gluing for every contained representative cover. -/
theorem rawGermDesc_amalgamation {F : RawPresheaf.{u,v} B}
    {G : BasisSheaf.{u,v} B} (ψ : F ⟶ G.obj.obj) {ι : Type w}
    (U : BasisOpen B) (s : GermSections F U.obj) (V : ι → BasisOpen B)
    (hV : FamilyCovers U V) (t : ∀ i, Sections F (V i))
    (ht : ∀ i (x : X) (hx : x ∈ (V i).obj),
      rawGerm F (V i) x hx (t i) = s.val ⟨x, hV.1 i hx⟩) :
    IsAmalgamation G.obj.obj hV (fun i => ψ.app (op (V i)) (t i))
      (rawGermDesc ψ U s) :=
  fun i => rawGermDesc_representative ψ U s (V i) (hV.1 i) (t i) (ht i)

@[simp]
theorem rawGermDesc_zero {F : RawPresheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj.obj) (U : BasisOpen B) : rawGermDesc ψ U 0 = 0 := map_zero _

@[simp]
theorem rawGermDesc_add {F : RawPresheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj.obj) (U : BasisOpen B) (s t : GermSections F U.obj) :
    rawGermDesc ψ U (s + t) = rawGermDesc ψ U s + rawGermDesc ψ U t := map_add _ _ _

@[simp]
theorem rawGermDesc_neg {F : RawPresheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj.obj) (U : BasisOpen B) (s : GermSections F U.obj) :
    rawGermDesc ψ U (-s) = -rawGermDesc ψ U s := map_neg _ _

/-- Empty-domain descent returns the unique original target section, namely zero. -/
theorem rawGermDesc_empty {F : RawPresheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj.obj) (U : BasisOpen B) (hU : U.obj = ⊥)
    (s : GermSections F U.obj) : rawGermDesc ψ U s = 0 :=
  empty_section_eq_zero G.obj U hU _

/-- Original-target descent commutes with every basis restriction. -/
theorem rawGermDesc_restriction {F : RawPresheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj.obj) {U V : BasisOpen B} (h : U.obj ≤ V.obj)
    (s : GermSections F V.obj) :
    rawGermDesc ψ U (germRestriction F h s) = restriction G.obj.obj h (rawGermDesc ψ V s) := by
  apply rawSheafGermEquality G.obj.obj G.property U
  intro x hx
  rw [rawGerm_restriction, rawGermDesc_germ, rawGermDesc_germ]
  rfl

/-- The canonical germ family descends to the original image section. -/
@[simp]
theorem rawGermDesc_sectionGerms {F : RawPresheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj.obj) (U : BasisOpen B) (t : Sections F U) :
    rawGermDesc ψ U (sectionGerms F U t) = ψ.app (op U) t := by
  simpa using rawGermDesc_representative ψ U (sectionGerms F U t) U le_rfl t
    (fun _ _ => rfl)

/-- Precomposition acts on the source germ family by the published stalk-family map. -/
theorem rawGermDesc_precomp {E F : RawPresheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (φ : E ⟶ F) (ψ : F ⟶ G.obj.obj) (U : BasisOpen B) (s : GermSections E U.obj) :
    rawGermDesc (φ ≫ ψ) U s = rawGermDesc ψ U (germSectionsMap φ U.obj s) := by
  apply rawSheafGermEquality G.obj.obj G.property U
  intro x hx
  rw [rawGermDesc_germ, rawGermDesc_germ]
  exact ConcreteCategory.congr_hom (rawStalkMap_comp φ ψ x) (s.val ⟨x, hx⟩)

/-- Postcomposition applies the original target morphism to the descended section. -/
theorem rawGermDesc_postcomp {F : RawPresheaf.{u,v} B}
    {G H : BasisSheaf.{u,v} B} (ψ : F ⟶ G.obj.obj) (χ : G ⟶ H)
    (U : BasisOpen B) (s : GermSections F U.obj) :
    rawGermDesc (ψ ≫ χ.hom.hom) U s = χ.hom.hom.app (op U) (rawGermDesc ψ U s) := by
  apply rawSheafGermEquality H.obj.obj H.property U
  intro x hx
  rw [rawGermDesc_germ, ← rawStalkMap_germ, rawGermDesc_germ]
  exact ConcreteCategory.congr_hom (rawStalkMap_comp ψ χ.hom.hom x) (s.val ⟨x, hx⟩)


/-- Any gluing from any contained representative cover agrees with the component. -/
theorem rawGermDesc_eq_of_amalgamation {F : RawPresheaf.{u,v} B}
    {G : BasisSheaf.{u,v} B} (ψ : F ⟶ G.obj.obj) {ι : Type w}
    (U : BasisOpen B) (s : GermSections F U.obj) (V : ι → BasisOpen B)
    (hV : FamilyCovers U V) (t : ∀ i, Sections F (V i))
    (ht : ∀ i (x : X) (hx : x ∈ (V i).obj),
      rawGerm F (V i) x hx (t i) = s.val ⟨x, hV.1 i hx⟩)
    (a : Sections G.obj.obj U)
    (ha : IsAmalgamation G.obj.obj hV (fun i => ψ.app (op (V i)) (t i)) a) :
    rawGermDesc ψ U s = a := by
  apply rawSheafGermEquality G.obj.obj G.property U
  intro x hx
  obtain ⟨i, hxi⟩ := hV.2 x hx
  calc
    rawGerm G.obj.obj U x hx (rawGermDesc ψ U s) = rawStalkMap ψ x (s.val ⟨x, hx⟩) :=
      rawGermDesc_germ ψ U s x hx
    _ = rawGerm G.obj.obj (V i) x hxi (ψ.app (op (V i)) (t i)) := by
      rw [← rawStalkMap_germ, ht]
    _ = rawGerm G.obj.obj (V i) x hxi (restriction G.obj.obj (hV.1 i) a) := by
      rw [ha i]
    _ = rawGerm G.obj.obj U x hx a := rawGerm_restriction G.obj.obj (hV.1 i) x hxi a

/-- Descent at arbitrary original value universe, targeting the actual joint-universe lift. -/
noncomputable def liftedGermDesc {F : Presheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj) :
    (germSheafFunctor.{u,v} B).obj F ⟶ (sheafLiftJoint.{u,v} B).obj G :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        (AddEquiv.ulift.symm.toAddMonoidHom.comp (rawGermDesc ψ.hom U.unop))
      naturality U V f := by
        apply AddCommGrpCat.ext
        intro s
        exact congrArg ULift.up (rawGermDesc_restriction ψ.hom f.unop.hom.le s) })

/-- Its component is literally the lift of the original-target descent. -/
@[simp]
theorem liftedGermDesc_app {F : Presheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj) (U : BasisOpen B) (s : GermSections F.obj U.obj) :
    (liftedGermDesc ψ).hom.hom.app (op U) s = ULift.up (rawGermDesc ψ.hom U s) := rfl

/-- Explicit restriction naturality in the actual lifted target. -/
theorem liftedGermDesc_restriction {F : Presheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj) {U V : BasisOpen B} (h : U.obj ≤ V.obj)
    (s : GermSections F.obj V.obj) :
    (liftedGermDesc ψ).hom.hom.app (op U) (germRestriction F.obj h s) =
      restriction ((sheafLiftJoint B).obj G).obj.obj h
        ((liftedGermDesc ψ).hom.hom.app (op V) s) :=
  congrArg ULift.up (rawGermDesc_restriction ψ.hom h s)

/-- The local representative formula, now in the actual lifted target sheaf. -/
theorem liftedGermDesc_representative {F : Presheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj) (U : BasisOpen B) (s : GermSections F.obj U.obj)
    (V : BasisOpen B) (hVU : V.obj ≤ U.obj) (t : Sections F.obj V)
    (ht : ∀ (x : X) (hx : x ∈ V.obj),
      rawGerm F.obj V x hx t = s.val ⟨x, hVU hx⟩) :
    restriction ((sheafLiftJoint B).obj G).obj.obj hVU
        ((liftedGermDesc ψ).hom.hom.app (op U) s) = ULift.up (ψ.hom.app (op V) t) :=
  congrArg ULift.up (rawGermDesc_representative ψ.hom U s V hVU t ht)

/-- Evaluation on the canonical family recovers the lifted original component. -/
@[simp]
theorem liftedGermDesc_sectionGerms {F : Presheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj) (U : BasisOpen B) (t : Sections F.obj U) :
    (liftedGermDesc ψ).hom.hom.app (op U) (sectionGerms F.obj U t) =
      ULift.up (ψ.hom.app (op U) t) :=
  congrArg ULift.up (rawGermDesc_sectionGerms ψ.hom U t)

/-- Intrinsic factorization through the published lifted canonical unit. -/
theorem liftedGermDesc_factorization {F : Presheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj) :
    (germSheafLiftUnit.{u,v} B).app F ≫ (sheafForget B).map (liftedGermDesc ψ) =
      (presheafLiftJoint.{u,v} B).map ψ := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro t
  exact liftedGermDesc_sectionGerms ψ U.unop t.down

/-- Naturality under precomposition by an arbitrary normalized source morphism. -/
theorem liftedGermDesc_precomp {E F : Presheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (φ : E ⟶ F) (ψ : F ⟶ G.obj) :
    liftedGermDesc (φ ≫ ψ) = (germSheafFunctor B).map φ ≫ liftedGermDesc ψ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  exact congrArg ULift.up (rawGermDesc_precomp φ.hom ψ.hom U.unop s)

/-- Naturality under postcomposition by an actual basis-sheaf morphism. -/
theorem liftedGermDesc_postcomp {F : Presheaf.{u,v} B} {G H : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj) (χ : G ⟶ H) :
    liftedGermDesc (ψ ≫ χ.hom) = liftedGermDesc ψ ≫ (sheafLiftJoint B).map χ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  exact congrArg ULift.up (rawGermDesc_postcomp ψ.hom χ U.unop s)

/-- Direct same-category descent when original values are already in `max u v`. -/
noncomputable def germDesc {F : Presheaf.{u,max u v} B}
    {G : BasisSheaf.{u,max u v} B} (ψ : F ⟶ G.obj) :
    (germSheafFunctor.{u,max u v} B).obj F ⟶ G :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (rawGermDesc ψ.hom U.unop)
      naturality U V f := by
        apply AddCommGrpCat.ext
        intro s
        exact rawGermDesc_restriction ψ.hom f.unop.hom.le s })

/-- Direct component evaluation has an original target value, with no extra lift. -/
@[simp]
theorem germDesc_app {F : Presheaf.{u,max u v} B} {G : BasisSheaf.{u,max u v} B}
    (ψ : F ⟶ G.obj) (U : BasisOpen B) (s : GermSections F.obj U.obj) :
    (germDesc.{u,v} ψ).hom.hom.app (op U) s = rawGermDesc ψ.hom U s := rfl

/-- Explicit restriction naturality for direct descent. -/
theorem germDesc_restriction {F : Presheaf.{u,max u v} B} {G : BasisSheaf.{u,max u v} B}
    (ψ : F ⟶ G.obj) {U V : BasisOpen B} (h : U.obj ≤ V.obj)
    (s : GermSections F.obj V.obj) :
    (germDesc.{u,v} ψ).hom.hom.app (op U) (germRestriction F.obj h s) =
      restriction G.obj.obj h ((germDesc.{u,v} ψ).hom.hom.app (op V) s) :=
  rawGermDesc_restriction ψ.hom h s

/-- Every original local representative evaluates directly to its original target image. -/
theorem germDesc_representative {F : Presheaf.{u,max u v} B}
    {G : BasisSheaf.{u,max u v} B} (ψ : F ⟶ G.obj) (U : BasisOpen B)
    (s : GermSections F.obj U.obj) (V : BasisOpen B) (hVU : V.obj ≤ U.obj)
    (t : Sections F.obj V)
    (ht : ∀ (x : X) (hx : x ∈ V.obj),
      rawGerm F.obj V x hx t = s.val ⟨x, hVU hx⟩) :
    restriction G.obj.obj hVU ((germDesc.{u,v} ψ).hom.hom.app (op U) s) =
      ψ.hom.app (op V) t :=
  rawGermDesc_representative ψ.hom U s V hVU t ht

/-- Direct evaluation on the canonical germ family. -/
@[simp]
theorem germDesc_sectionGerms {F : Presheaf.{u,max u v} B}
    {G : BasisSheaf.{u,max u v} B} (ψ : F ⟶ G.obj) (U : BasisOpen B)
    (t : Sections F.obj U) :
    (germDesc.{u,v} ψ).hom.hom.app (op U) (sectionGerms F.obj U t) =
      ψ.hom.app (op U) t := rawGermDesc_sectionGerms ψ.hom U t

/-- Intrinsic factorization through the published direct canonical unit. -/
theorem germDesc_factorization {F : Presheaf.{u,max u v} B}
    {G : BasisSheaf.{u,max u v} B} (ψ : F ⟶ G.obj) :
    (germSheafUnit.{u,v} B).app F ≫ (sheafForget B).map (germDesc.{u,v} ψ) = ψ := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro t
  exact rawGermDesc_sectionGerms ψ.hom U.unop t

/-- Direct descent is natural under source precomposition. -/
theorem germDesc_precomp {E F : Presheaf.{u,max u v} B}
    {G : BasisSheaf.{u,max u v} B} (φ : E ⟶ F) (ψ : F ⟶ G.obj) :
    germDesc.{u,v} (φ ≫ ψ) = (germSheafFunctor B).map φ ≫ germDesc.{u,v} ψ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  exact rawGermDesc_precomp φ.hom ψ.hom U.unop s

/-- Direct descent is natural under target postcomposition. -/
theorem germDesc_postcomp {F : Presheaf.{u,max u v} B}
    {G H : BasisSheaf.{u,max u v} B} (ψ : F ⟶ G.obj) (χ : G ⟶ H) :
    germDesc.{u,v} (ψ ≫ χ.hom) = germDesc.{u,v} ψ ≫ χ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  exact rawGermDesc_postcomp ψ.hom χ U.unop s

/-- Lowering the lifted-target map by the actual relift isomorphism gives direct descent. -/
theorem liftedGermDesc_eq_relift {F : Presheaf.{u,max u v} B}
    {G : BasisSheaf.{u,max u v} B} (ψ : F ⟶ G.obj) :
    liftedGermDesc.{u,max u v} ψ ≫ (sheafReliftJoint.{u,v} B).hom.app G =
      germDesc.{u,v} ψ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  rfl

/-- The actual inverse relift lifts direct descent back to the lifted-target map. -/
theorem germDesc_eq_relift_inv {F : Presheaf.{u,max u v} B}
    {G : BasisSheaf.{u,max u v} B} (ψ : F ⟶ G.obj) :
    germDesc.{u,v} ψ ≫ (sheafReliftJoint.{u,v} B).inv.app G =
      liftedGermDesc.{u,max u v} ψ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  rfl

end Langlands.Sheaf.Renard
