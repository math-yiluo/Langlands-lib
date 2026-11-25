/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Localized sheaves over a sheafified representable

Source: Stacks Project, Sites, Tag 00Y1, lemma-essential-image-j-shriek, and
lemma-describe-j-shriek in Section 00XZ
(blueprint: lem-weil-pbc-localized-sheaves-over-representable).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

private theorem sigma_ext {C : Type u} [SmallCategory C] {U X : C}
    (H : (Over U)ᵒᵖ ⥤ Type u) {a b : X ⟶ U}
    {s : H.obj (op (Over.mk a))} {t : H.obj (op (Over.mk b))}
    (h : a = b) (hs : H.map (eqToHom (by rw [h])).op t = s) :
    (⟨a, s⟩ : Σ a : X ⟶ U, H.obj (op (Over.mk a))) = ⟨b, t⟩ := by
  subst b
  simpa using congrArg
    (fun t : H.obj (op (Over.mk a)) ↦
      (⟨a, t⟩ : Σ a : X ⟶ U, H.obj (op (Over.mk a)))) hs.symm

private def sigmaRestriction {C : Type u} [SmallCategory C] {U X Y : C}
    (H : (Over U)ᵒᵖ ⥤ Type u) (b : Y ⟶ X)
    (z : Σ a : X ⟶ U, H.obj (op (Over.mk a))) :
    Σ a : Y ⟶ U, H.obj (op (Over.mk a)) :=
  ⟨b ≫ z.1, H.map (Over.homMk b rfl).op z.2⟩

private def sigmaPresheaf {C : Type u} [SmallCategory C] {U : C}
    (H : (Over U)ᵒᵖ ⥤ Type u) : Cᵒᵖ ⥤ Type u where
  obj X := Σ a : X.unop ⟶ U, H.obj (op (Over.mk a))
  map b := ↾(sigmaRestriction H b.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨a, s⟩
    dsimp [sigmaRestriction]
    apply sigma_ext H (Category.id_comp _)
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp

  map_comp b c := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨a, s⟩
    dsimp [sigmaRestriction]
    apply sigma_ext H (Category.assoc _ _ _)
    simp only [← Functor.map_comp_apply]
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp

private def sigmaProjection {C : Type u} [SmallCategory C] {U : C}
    (H : (Over U)ᵒᵖ ⥤ Type u) : sigmaPresheaf H ⟶ yoneda.obj U where
  app _ := ↾fun z ↦ z.1
  naturality _ _ _ := rfl

private def sigmaMap {C : Type u} [SmallCategory C] {U : C}
    {H H' : (Over U)ᵒᵖ ⥤ Type u} (f : H ⟶ H') : sigmaPresheaf H ⟶ sigmaPresheaf H' where
  app _ := ↾fun z ↦ ⟨z.1, f.app _ z.2⟩
  naturality X Y b := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, s⟩
    dsimp [sigmaPresheaf, sigmaRestriction]
    congr 1
    exact f.naturality_apply
      (Over.homMk b.unop rfl : Over.mk (b.unop ≫ a) ⟶ Over.mk a).op s

private def sigmaFunctor {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) (U : C) :
    Sheaf (K.over U) (Type u) ⥤ Over (yoneda.obj U) where
  obj H := Over.mk (sigmaProjection H.obj)
  map f := Over.homMk (sigmaMap f.hom) (by rfl)
  map_id H := by
    apply Over.OverMorphism.ext
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    rfl

private def fibreSubfunctor {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (F : Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) :
    Subfunctor (F.left.over U).obj where
  obj X := {s | F.hom.hom.app (op X.unop.left) s =
    (toSheafify K (yoneda.obj U)).app (op X.unop.left) X.unop.hom}
  map {X Y} b s hs := by
    change F.hom.hom.app _ (F.left.obj.map b.unop.left.op s) = _
    rw [NatTrans.naturality_apply, hs, ← NatTrans.naturality_apply]
    congr 1
    exact Over.w b.unop

private theorem fibre_isSheaf {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (F : Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) :
    Presheaf.IsSheaf (K.over U) (fibreSubfunctor K U F).toFunctor := by
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  apply (Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).mp (F.left.over U).property)).mpr
  intro X s hs
  change F.hom.hom.app _ s = _
  let G := ((presheafToSheaf K (Type u)).obj (yoneda.obj U)).over U
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSeparated _ hs).ext
  intro Y b hb
  change (sheafify K (yoneda.obj U)).map b.left.op (F.hom.hom.app _ s) =
    (sheafify K (yoneda.obj U)).map b.left.op _
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  change F.hom.hom.app _ (F.left.obj.map b.left.op s) =
    (toSheafify K (yoneda.obj U)).app _ (b.left ≫ X.unop.hom)
  rw [Over.w]
  exact hb

private noncomputable def fibreFunctor {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C) :
    Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U)) ⥤ Sheaf (K.over U) (Type u) where
  obj F := ⟨(fibreSubfunctor K U F).toFunctor, fibre_isSheaf K U F⟩
  map {F G} f := ⟨{
    app X := ↾fun s ↦ ⟨f.left.hom.app _ s.val, by
      have h := congrArg (fun t ↦ t.hom.app (op X.unop.left) s.val) (Over.w f)
      exact h.trans s.property⟩
    naturality X Y b := by
      apply ConcreteCategory.hom_ext
      intro s
      apply Subtype.ext
      exact f.left.hom.naturality_apply b.unop.left.op s.val }⟩

private noncomputable abbrev extensionFunctor {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C) :=
  sigmaFunctor K U ⋙ Over.post (presheafToSheaf K (Type u))

private def pairSection {C : Type u} [SmallCategory C] {U : C}
    (H : (Over U)ᵒᵖ ⥤ Type u) (X : Over U) (s : H.obj (op X)) :
    (sigmaPresheaf H).obj (op X.left) :=
  ⟨X.hom, H.map (Over.homMk (𝟙 X.left) (by simp) : Over.mk X.hom ⟶ X).op s⟩

private theorem pairSection_naturality {C : Type u} [SmallCategory C] {U : C}
    (H : (Over U)ᵒᵖ ⥤ Type u) {X Y : Over U} (b : X ⟶ Y) (s : H.obj (op Y)) :
    (sigmaPresheaf H).map b.left.op (pairSection H Y s) =
      pairSection H X (H.map b.op s) := by
  dsimp [sigmaPresheaf, sigmaRestriction, pairSection]
  apply sigma_ext H (Over.w b)
  simp only [← Functor.map_comp_apply]
  congr 2
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  simp

private noncomputable def unitComparison {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (H : Sheaf (K.over U) (Type u)) :
    H ⟶ (fibreFunctor K U).obj ((extensionFunctor K U).obj H) := ⟨{
  app X := ↾fun s ↦ ⟨(toSheafify K (sigmaPresheaf H.obj)).app (op X.unop.left)
    (pairSection H.obj X.unop s), by
      have h := congrArg (fun t ↦ t.app (op X.unop.left)
        (pairSection H.obj X.unop s)) (toSheafify_naturality K (sigmaProjection H.obj))
      exact h.symm⟩
  naturality X Y b := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    symm
    change (sheafify K (sigmaPresheaf H.obj)).map b.unop.left.op
      ((toSheafify K (sigmaPresheaf H.obj)).app _ (pairSection H.obj X.unop s)) = _
    rw [← NatTrans.naturality_apply, pairSection_naturality]
    rfl }⟩

private def forgetPairs {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (F : Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) :
    sigmaPresheaf ((fibreFunctor K U).obj F).obj ⟶ F.left.obj where
  app _ := ↾fun z ↦ z.2.val
  naturality _ _ _ := rfl

private noncomputable def counitComparison {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (F : Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) :
    (extensionFunctor K U).obj ((fibreFunctor K U).obj F) ⟶ F :=
  Over.homMk ⟨sheafifyLift K (forgetPairs K U F) F.left.property⟩ (by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext K _ _
      ((presheafToSheaf K (Type u)).obj (yoneda.obj U)).property
    change toSheafify K _ ≫
      (sheafifyLift K (forgetPairs K U F) F.left.property ≫ F.hom.hom) =
        toSheafify K _ ≫ sheafifyMap K (sigmaProjection ((fibreFunctor K U).obj F).obj)
    rw [← Category.assoc, toSheafify_sheafifyLift, ← toSheafify_naturality]
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    rintro ⟨a, s⟩
    exact s.property)

private theorem forgetPairs_locallyInjective {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (F : Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) :
    Presheaf.IsLocallyInjective K (forgetPairs K U F) := by
  constructor
  rintro X ⟨a, s⟩ ⟨b, t⟩ h
  change s.val = t.val at h
  have hab : (toSheafify K (yoneda.obj U)).app X a =
      (toSheafify K (yoneda.obj U)).app X b := by
    exact s.property.symm.trans ((congrArg (F.hom.hom.app X) h).trans t.property)
  apply K.superset_covering ?_
    (Presheaf.equalizerSieve_mem K (toSheafify K (yoneda.obj U)) a b hab)
  intro Y f hf
  change f ≫ a = f ≫ b at hf
  change (⟨f ≫ a, _⟩ : Σ a : Y ⟶ U,
    ((fibreFunctor K U).obj F).obj.obj (op (Over.mk a))) = ⟨f ≫ b, _⟩
  apply sigma_ext _ hf
  apply Subtype.ext
  change F.left.obj.map
    (eqToHom (by rw [hf]) : Over.mk (f ≫ a) ⟶ Over.mk (f ≫ b)).left.op
      (F.left.obj.map f.op t.val) =
    F.left.obj.map f.op s.val
  simp only [Over.eqToHom_left]
  simp [h]

private theorem forgetPairs_locallySurjective {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (F : Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) :
    Presheaf.IsLocallySurjective K (forgetPairs K U F) := by
  constructor
  intro X s
  apply K.superset_covering ?_
    (Presheaf.imageSieve_mem K (toSheafify K (yoneda.obj U)) (F.hom.hom.app _ s))
  rintro Y b ⟨a, ha⟩
  refine ⟨⟨a, ⟨F.left.obj.map b.op s, ?_⟩⟩, rfl⟩
  change F.hom.hom.app _ (F.left.obj.map b.op s) =
    (toSheafify K (yoneda.obj U)).app _ a
  rw [NatTrans.naturality_apply]
  exact ha.symm

private theorem counitComparison_isIso {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (F : Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) :
    IsIso (counitComparison K U F) := by
  have ht : toSheafify K _ ≫ (counitComparison K U F).left.hom =
      forgetPairs K U F := toSheafify_sheafifyLift _ _ _
  have := forgetPairs_locallyInjective K U F
  have := forgetPairs_locallySurjective K U F
  have : Sheaf.IsLocallyInjective (counitComparison K U F).left :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac K _ ht
  have : Sheaf.IsLocallySurjective (counitComparison K U F).left :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac K ht
  have := (Sheaf.isLocallyBijective_iff_isIso (counitComparison K U F).left).mp
    ⟨inferInstance, inferInstance⟩
  have : IsIso ((Over.forget _).map (counitComparison K U F)) := by
    change IsIso (counitComparison K U F).left
    infer_instance
  exact isIso_of_reflects_iso (counitComparison K U F) (Over.forget _)

private theorem pairSection_injective {C : Type u} [SmallCategory C] {U : C}
    (H : (Over U)ᵒᵖ ⥤ Type u) (X : Over U) :
    Function.Injective (pairSection H X) := by
  intro s t h
  have hn : IsIso (Over.homMk (𝟙 X.left) (by simp) : Over.mk X.hom ⟶ X) :=
    ⟨Over.homMk (𝟙 X.left) (by simp), by ext; simp, by ext; simp⟩
  apply (asIso (H.map
    (Over.homMk (𝟙 X.left) (by simp) : Over.mk X.hom ⟶ X).op)).toEquiv.injective
  exact eq_of_heq (Sigma.mk.inj h).2

private theorem unitComparison_injective {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (H : Sheaf (K.over U) (Type u)) (X : (Over U)ᵒᵖ) :
    Function.Injective ((unitComparison K U H).hom.app X) := by
  intro s t h
  have ht : (toSheafify K (sigmaPresheaf H.obj)).app _ (pairSection H.obj X.unop s) =
      (toSheafify K (sigmaPresheaf H.obj)).app _ (pairSection H.obj X.unop t) :=
    congrArg Subtype.val h
  have hS := Presheaf.equalizerSieve_mem K (toSheafify K (sigmaPresheaf H.obj))
    (pairSection H.obj X.unop s) (pairSection H.obj X.unop t) ht
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp H.property).isSeparated _
    (K.overEquiv_symm_mem_over X.unop _ hS)).ext
  intro Y b hb
  apply pairSection_injective H.obj Y
  change (sigmaPresheaf H.obj).map b.left.op (pairSection H.obj X.unop s) =
    (sigmaPresheaf H.obj).map b.left.op (pairSection H.obj X.unop t) at hb
  simpa only [pairSection_naturality] using hb

private theorem unitComparison_locallySurjective {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (H : Sheaf (K.over U) (Type u)) :
    Sheaf.IsLocallySurjective (unitComparison K U H) := by
  constructor
  intro X z
  let Q := sigmaPresheaf H.obj
  let θ := toSheafify K Q
  let η := toSheafify K (yoneda.obj U)
  let S := Presheaf.imageSieve θ z.val
  have hS : S ∈ K X.left := Presheaf.imageSieve_mem K θ z.val
  apply (K.over U).transitive (K.overEquiv_symm_mem_over X S hS) _
  intro Y b hb
  change ∃ p : Q.obj (op Y.left),
    θ.app (op Y.left) p = (sheafify K Q).map b.left.op z.val at hb
  obtain ⟨⟨a, s⟩, hs⟩ := hb
  have ha : η.app (op Y.left) a = η.app (op Y.left) Y.hom := by
    have hp := congrArg (fun t ↦ t.app (op Y.left) ⟨a, s⟩)
      (toSheafify_naturality K (sigmaProjection H.obj))
    change η.app (op Y.left) a = _ at hp
    rw [hp]
    change (sheafifyMap K (sigmaProjection H.obj)).app _
      (θ.app (op Y.left) ⟨a, s⟩) = _
    rw [hs]
    rw [NatTrans.naturality_apply]
    change (sheafify K (yoneda.obj U)).map b.left.op
      (((extensionFunctor K U).obj H).hom.hom.app _ z.val) = _
    rw [z.property, ← NatTrans.naturality_apply]
    congr 1
    exact Over.w b
  have hT := Presheaf.equalizerSieve_mem K η a Y.hom ha
  apply (K.over U).superset_covering ?_ (K.overEquiv_symm_mem_over Y _ hT)
  intro Z c hc
  change c.left ≫ a = c.left ≫ Y.hom at hc
  have hc' : c.left ≫ a = Z.hom := hc.trans (Over.w c)
  let d : Z ⟶ Over.mk a := Over.homMk c.left hc'
  refine ⟨H.obj.map d.op s, ?_⟩
  apply Subtype.ext
  change θ.app (op Z.left) (pairSection H.obj Z (H.obj.map d.op s)) =
    (sheafify K Q).map (c ≫ b).left.op z.val
  have he : pairSection H.obj Z (H.obj.map d.op s) = Q.map c.left.op ⟨a, s⟩ := by
    dsimp [pairSection, Q, sigmaPresheaf, sigmaRestriction]
    apply sigma_ext H.obj hc'.symm
    simp only [← Functor.map_comp_apply]
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp [d]
  rw [he, NatTrans.naturality_apply, hs]
  simp only [Over.comp_left, op_comp, Functor.map_comp_apply]

private theorem unitComparison_isIso {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (H : Sheaf (K.over U) (Type u)) : IsIso (unitComparison K U H) := by
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  refine ⟨?_, unitComparison_locallySurjective K U H⟩
  exact Presheaf.isLocallyInjective_of_injective _ _ (unitComparison_injective K U H)

private theorem pairSection_map {C : Type u} [SmallCategory C] {U : C}
    {H H' : (Over U)ᵒᵖ ⥤ Type u} (f : H ⟶ H') (X : Over U) (s : H.obj (op X)) :
    (sigmaMap f).app (op X.left) (pairSection H X s) =
      pairSection H' X (f.app (op X) s) := by
  dsimp [sigmaMap, pairSection]
  congr 1
  exact f.naturality_apply
    (Over.homMk (𝟙 X.left) (by simp) : Over.mk X.hom ⟶ X).op s

private noncomputable def unitTransformation {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C) :
    𝟭 (Sheaf (K.over U) (Type u)) ⟶ extensionFunctor K U ⋙ fibreFunctor K U where
  app H := unitComparison K U H
  naturality H H' f := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (toSheafify K (sigmaPresheaf H'.obj)).app _
      (pairSection H'.obj X.unop (f.hom.app X s)) =
        (sheafifyMap K (sigmaMap f.hom)).app _
          ((toSheafify K (sigmaPresheaf H.obj)).app _ (pairSection H.obj X.unop s))
    have h := congrArg (fun t ↦ t.app (op X.unop.left) (pairSection H.obj X.unop s))
      (toSheafify_naturality K (sigmaMap f.hom))
    exact (congrArg ((toSheafify K (sigmaPresheaf H'.obj)).app _)
      (pairSection_map f.hom X.unop s)).symm.trans h

private noncomputable def counitTransformation {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C) :
    fibreFunctor K U ⋙ extensionFunctor K U ⟶
      𝟭 (Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) where
  app F := counitComparison K U F
  naturality F G f := by
    apply Over.OverMorphism.ext
    apply Sheaf.hom_ext
    change sheafifyMap K (sigmaMap ((fibreFunctor K U).map f).hom) ≫
      sheafifyLift K (forgetPairs K U G) G.left.property =
        sheafifyLift K (forgetPairs K U F) F.left.property ≫ f.left.hom
    rw [sheafifyMap_sheafifyLift,
      ← sheafifyLift_comp K (forgetPairs K U F) F.left.property f.left.hom G.left.property]
    congr 1

/-- The fibre/extension equivalence for an arbitrary Grothendieck topology.
Source: Stacks Project, Sites, Tag 00Y1, lemma-essential-image-j-shriek.
(blueprint: lem-weil-pbc-localized-sheaves-over-representable).

Proof: use the same disjoint-union presheaf, sheafification, and fibre constructions
as in the precoverage interface. The unit is locally bijective by local representation
of sheafification sections and local equality of representable arrows; the counit is
locally bijective by forgetting those arrows. Their already proved formulas supply
the equivalence and all the displayed section and restriction identifications.
None of these constructions needs a precoverage presentation of the topology. -/
theorem exists_localizedSheavesOverRepresentable_general
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type u)] (U : C) :
    ∃ (P : Sheaf (J.over U) (Type u) ⥤ Over (yoneda.obj U))
      (e : ∀ (H : Sheaf (J.over U) (Type u)) (X : C),
        (P.obj H).left.obj (op X) ≃ Σ a : X ⟶ U, H.obj.obj (op (Over.mk a))),
      (∀ (H : Sheaf (J.over U) (Type u)) (X : C)
        (z : (P.obj H).left.obj (op X)),
        (P.obj H).hom.app (op X) z = (e H X z).1) ∧
      (∀ (H : Sheaf (J.over U) (Type u)) (X Y : C)
        (b : Y ⟶ X) (a : X ⟶ U) (s : H.obj.obj (op (Over.mk a))),
        e H Y ((P.obj H).left.map b.op ((e H X).symm ⟨a, s⟩)) =
          ⟨b ≫ a, H.obj.map (Over.homMk b rfl).op s⟩) ∧
      (∀ (H H' : Sheaf (J.over U) (Type u)) (f : H ⟶ H')
        (X : C) (a : X ⟶ U) (s : H.obj.obj (op (Over.mk a))),
        e H' X ((P.map f).left.app (op X) ((e H X).symm ⟨a, s⟩)) =
          ⟨a, f.hom.app (op (Over.mk a)) s⟩) ∧
      ∃ E : Sheaf (J.over U) (Type u) ≌
          Over ((presheafToSheaf J (Type u)).obj (yoneda.obj U)),
        Nonempty (E.functor ≅ P ⋙ Over.post (presheafToSheaf J (Type u))) ∧
        ∃ r : ∀ (F : Over
            ((presheafToSheaf J (Type u)).obj (yoneda.obj U))) (X : Over U),
            (E.inverse.obj F).obj.obj (op X) ≃
              {s : F.left.obj.obj (op X.left) |
                F.hom.hom.app (op X.left) s =
                  (toSheafify J (yoneda.obj U)).app (op X.left) X.hom},
          (∀ (F : Over
              ((presheafToSheaf J (Type u)).obj (yoneda.obj U)))
            (X Y : Over U) (b : X ⟶ Y) (s : (E.inverse.obj F).obj.obj (op Y)),
            (r F X ((E.inverse.obj F).obj.map b.op s)).val =
              F.left.obj.map b.left.op (r F Y s).val) ∧
          (∀ (F G : Over
              ((presheafToSheaf J (Type u)).obj (yoneda.obj U)))
            (f : F ⟶ G) (X : Over U) (s : (E.inverse.obj F).obj.obj (op X)),
            (r G X ((E.inverse.map f).hom.app (op X) s)).val =
              f.left.hom.app (op X.left) (r F X s).val) := by
  classical
  let K := J
  let P := sigmaFunctor K U
  let Efun := extensionFunctor K U
  let R := fibreFunctor K U
  have : IsIso (unitTransformation K U) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact unitComparison_isIso K U
  have : IsIso (counitTransformation K U) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact counitComparison_isIso K U
  let E : Sheaf (K.over U) (Type u) ≌
      Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U)) :=
    Equivalence.mk Efun R (asIso (unitTransformation K U))
      (asIso (counitTransformation K U))
  refine ⟨P, fun H X ↦ Equiv.refl _, ?_, ?_, ?_, E, ⟨Iso.refl _⟩,
    fun F X ↦ Equiv.refl _, ?_, ?_⟩
  all_goals intros; rfl

end CategoryTheory
