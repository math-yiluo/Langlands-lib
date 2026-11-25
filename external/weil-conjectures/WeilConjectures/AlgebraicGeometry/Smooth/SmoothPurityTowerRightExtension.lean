/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
/-!
# Normalized right adjoints of coefficient-tower evaluation

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-levels,
`sk-lem-sp-tower-levels-adjoint.proof.md`
(blueprint: lem-sp-tower-normalized-right-adjoints).

Index n represents the positive coefficient exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 2048

-- Elaborate with the existing transport to the full coefficient universe.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped ZeroObject

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

section GenericExtension

universe a av w

variable {C : Type a} [Category.{av} C] {S : GrothendieckTopology C}
  [S.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify S AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf S CommRingCat.{w})

private abbrev coeffMap {m r : ℕ} (h : m ≤ r) :=
  (sheafCompose S
    (forget₂ CommRingCat.{w} RingCat.{w})).map
      (B.map (homOfLE h).op)

omit [S.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify S AddCommGrpCat.{w}] in
private theorem coeffMap_comp {n m r : ℕ} (h : n ≤ m) (k : m ≤ r)
    (U : Cᵒᵖ) :
    ((coeffMap B (h.trans k)).hom.app U).hom =
      ((coeffMap B h).hom.app U).hom.comp
        ((coeffMap B k).hom.app U).hom := by
  let Q := B ⋙
    sheafCompose S
      (forget₂ CommRingCat.{w} RingCat.{w})
  have hq : Q.map (homOfLE (h.trans k)).op =
      Q.map (homOfLE k).op ≫ Q.map (homOfLE h).op := by
    rw [← Q.map_comp]
    rfl
  exact congrArg (fun f ↦ (f.hom.app U).hom) hq

private def restrictionStep {n m r : ℕ} (h : n ≤ m) (k : m ≤ r)
    (J : systemLevel.{a, av, w} B n) :
    (systemRestriction B (h.trans k)).obj J ⟶
      (systemRestriction B k).obj
        ((systemRestriction B h).obj J) where
  val :=
    { app := fun U ↦
        (ModuleCat.restrictScalarsComp'App
          ((coeffMap B k).hom.app U).hom
          ((coeffMap B h).hom.app U).hom
          ((coeffMap B (h.trans k)).hom.app U).hom
          (coeffMap_comp B h k U) (J.val.obj U)).hom
      naturality := fun f ↦ by ext x; rfl }

private def extensionLevel (n : ℕ)
    (J : systemLevel.{a, av, w} B n)
    (r : ℕ) : systemLevel.{a, av, w} B r :=
  if h : n ≤ r then (systemRestriction B h).obj J else 0

private def extensionTransition (n : ℕ)
    (J : systemLevel.{a, av, w} B n)
    {m r : ℕ} (h : m ≤ r) :
    extensionLevel B n J r ⟶
      (systemRestriction B h).obj
        (extensionLevel B n J m) := by
  classical
  by_cases hm : n ≤ m
  · simpa only [extensionLevel, dite_eq_left hm, dite_eq_left (hm.trans h)] using
      restrictionStep B hm h J
  · exact 0

private theorem extensionLevel_above (n r : ℕ) (h : n ≤ r)
    (J : systemLevel.{a, av, w} B n) :
    extensionLevel B n J r = (systemRestriction B h).obj J := by
  exact dite_eq_left h

omit [S.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify S AddCommGrpCat.{w}] in
private theorem module_fun_heq
    {R : Sheaf S RingCat.{w}} {M N M' N' : SheafOfModules.{w} R}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N') (h : HEq f g)
    (U : Cᵒᵖ) :
    HEq (fun x ↦ f.val.app U x) (fun x ↦ g.val.app U x) := by
  subst M'
  subst N'
  cases h
  rfl

private theorem extensionTransition_above (n : ℕ)
    (J : systemLevel.{a, av, w} B n) {m r : ℕ}
    (h : m ≤ r) (hm : n ≤ m) (U : Cᵒᵖ) :
    HEq (fun x ↦ (extensionTransition B n J h).val.app U x)
      (fun x : J.val.obj U ↦ x) := by
  have he : HEq (extensionTransition B n J h) (restrictionStep B hm h J) := by
    unfold extensionTransition
    simp only [dite_eq_left hm]
    exact cast_heq _ _
  have ht := module_fun_heq (extensionLevel_above B n r (hm.trans h) J)
    (congrArg ((systemRestriction B h).obj) (extensionLevel_above B n m hm J))
    _ _ he U
  exact ht

private theorem carrier_above (n r : ℕ) (h : n ≤ r)
    (J : systemLevel.{a, av, w} B n) (U : Cᵒᵖ) :
    ((extensionLevel B n J r).val.obj U : Type w) = (J.val.obj U : Type w) :=
  congrArg (fun M ↦ (M.val.obj U : Type w)) (extensionLevel_above B n r h J)

private theorem id_fun_heq {X Y : Type w} (h : X = Y) :
    HEq (fun x : X ↦ x) (fun y : Y ↦ y) := by
  subst Y
  rfl

private theorem composition_of_heq_identity {X Y Z W : Type w}
    (hX : X = W) (hY : Y = W) (hZ : Z = W)
    (f : X → Y) (g : Y → Z) (k : X → Z)
    (hf : HEq f (fun x : W ↦ x)) (hg : HEq g (fun x : W ↦ x))
    (hk : HEq k (fun x : W ↦ x)) (x : X) : k x = g (f x) := by
  subst W
  subst Y
  subst Z
  rw [eq_of_heq hf, eq_of_heq hg, eq_of_heq hk]

private def extensionObject (n : ℕ)
    (J : systemLevel.{a, av, w} B n) : StrictRingSystem.{a, av, w} B where
  level := extensionLevel B n J
  transition := extensionTransition B n J
  identity := by
    intro r U x
    by_cases h : n ≤ r
    · have ht := extensionTransition_above B n J (Nat.le_refl r) h U
      have hi := id_fun_heq (carrier_above B n r h J U)
      exact congrFun (eq_of_heq (ht.trans hi.symm)) x
    · have hz : IsZero (extensionLevel B n J r) := by
        simpa only [extensionLevel, dite_eq_right h] using
          (isZero_zero (systemLevel.{a, av, w} B r))
      have hz' := (systemRestriction B (Nat.le_refl r)).map_isZero hz
      exact (ModuleCat.subsingleton_of_isZero
        ((SheafOfModules.evaluation _ U).map_isZero hz')).elim _ _
  compose := by
    intro a m r h k U x
    by_cases ha : n ≤ a
    · exact composition_of_heq_identity
        (carrier_above B n r ((ha.trans h).trans k) J U)
        (carrier_above B n m (ha.trans h) J U)
        (carrier_above B n a ha J U)
        _ _ _ (extensionTransition_above B n J k (ha.trans h) U)
        (extensionTransition_above B n J h ha U)
        (extensionTransition_above B n J (h.trans k) ha U) x
    · have hz : IsZero (extensionLevel B n J a) := by
        simpa only [extensionLevel, dite_eq_right ha] using
          (isZero_zero (systemLevel.{a, av, w} B a))
      have hz' := (systemRestriction B (h.trans k)).map_isZero hz
      exact (ModuleCat.subsingleton_of_isZero
        ((SheafOfModules.evaluation _ U).map_isZero hz')).elim _ _

private theorem extensionLevel_below (n r : ℕ) (h : ¬ n ≤ r)
    (J : systemLevel.{a, av, w} B n) :
    IsZero (extensionLevel B n J r) := by
  simpa only [extensionLevel, dite_eq_right h] using
    (isZero_zero (systemLevel.{a, av, w}
      B r))

omit [S.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify S AddCommGrpCat.{w}] in
private theorem hom_comp_heq {R : Sheaf S RingCat.{w}}
    {X Y Z X' Y' Z' : SheafOfModules.{w} R}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst X'
  subst Y'
  subst Z'
  cases hf
  cases hg
  rfl

omit [S.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify S AddCommGrpCat.{w}] in
private theorem hom_map_heq {R R' : Sheaf S RingCat.{w}}
    (F : SheafOfModules.{w} R ⥤ SheafOfModules.{w} R')
    {X Y X' Y' : SheafOfModules.{w} R} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst X'
  subst Y'
  cases h
  rfl

private def extensionMapLevel (n : ℕ)
    {J K : systemLevel.{a, av, w} B n} (f : J ⟶ K) (r : ℕ) :
    extensionLevel B n J r ⟶ extensionLevel B n K r := by
  by_cases h : n ≤ r
  · simpa only [extensionLevel, dite_eq_left h] using (systemRestriction B h).map f
  · exact 0

private theorem extensionMapLevel_above (n r : ℕ) (h : n ≤ r)
    {J K : systemLevel.{a, av, w} B n} (f : J ⟶ K) :
    HEq (extensionMapLevel B n f r) ((systemRestriction B h).map f) := by
  unfold extensionMapLevel
  simp only [dite_eq_left h]
  exact cast_heq _ _

private theorem extensionTransition_heq (n : ℕ)
    (J : systemLevel.{a, av, w} B n) {m r : ℕ} (h : m ≤ r) (hm : n ≤ m) :
    HEq (extensionTransition B n J h) (restrictionStep B hm h J) := by
  unfold extensionTransition
  simp only [dite_eq_left hm]
  exact cast_heq _ _

private def extensionMap (n : ℕ)
    {J K : systemLevel.{a, av, w} B n}
    (f : J ⟶ K) : extensionObject B n J ⟶ extensionObject B n K where
  app := extensionMapLevel B n f
  comm := by
    intro m r h
    by_cases hm : n ≤ m
    · have hr := hm.trans h
      have hJr := extensionLevel_above B n r hr J
      have hKr := extensionLevel_above B n r hr K
      have hJm := extensionLevel_above B n m hm J
      have hKm := extensionLevel_above B n m hm K
      have hl := hom_comp_heq hJr hKr (congrArg ((systemRestriction B h).obj) hKm)
        _ _ _ _ (extensionMapLevel_above B n r hr f)
        (extensionTransition_heq B n K h hm)
      have hh := hom_map_heq (systemRestriction B h) hJm hKm
        _ _ (extensionMapLevel_above B n m hm f)
      have hr' := hom_comp_heq hJr (congrArg ((systemRestriction B h).obj) hJm)
        (congrArg ((systemRestriction B h).obj) hKm)
        _ _ _ _ (extensionTransition_heq B n J h hm) hh
      have he : (systemRestriction B hr).map f ≫ restrictionStep B hm h K =
          restrictionStep B hm h J ≫ (systemRestriction B h).map
            ((systemRestriction B hm).map f) := by ext U x; rfl
      exact eq_of_heq (hl.trans ((heq_of_eq he).trans hr'.symm))
    · apply ((systemRestriction B h).map_isZero
        (extensionLevel_below B n m hm K)).eq_of_tgt

private theorem extension_hom_ext
    {M N : StrictRingSystem.{a, av, w}
      B} (f g : M ⟶ N)
    (h : ∀ r : ℕ, f.app r = g.app r) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have he : f = g := funext h
      subst g
      rfl

omit [S.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify S AddCommGrpCat.{w}] in
private theorem hom_id_heq {R : Sheaf S RingCat.{w}}
    {X Y : SheafOfModules.{w} R} (h : X = Y) : HEq (𝟙 X) (𝟙 Y) := by
  subst Y
  rfl

omit [S.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify S AddCommGrpCat.{w}] in
private theorem isIso_of_hom_heq {R : Sheaf S RingCat.{w}}
    {X Y X' Y' : SheafOfModules.{w} R} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) [IsIso g] : IsIso f := by
  subst X'
  subst Y'
  cases h
  infer_instance

private def restrictionStepIso {n m r : ℕ} (h : n ≤ m) (k : m ≤ r)
    (J : systemLevel.{a, av, w} B n) :
    (systemRestriction B (h.trans k)).obj J ≅
      (systemRestriction B k).obj ((systemRestriction B h).obj J) where
  hom := restrictionStep B h k J
  inv := { val :=
    { app := fun U ↦
        (ModuleCat.restrictScalarsComp'App
          ((coeffMap B k).hom.app U).hom
          ((coeffMap B h).hom.app U).hom
          ((coeffMap B (h.trans k)).hom.app U).hom
          (coeffMap_comp B h k U) (J.val.obj U)).inv
      naturality := fun f ↦ by ext x; rfl } }
  hom_inv_id := by ext U x; rfl
  inv_hom_id := by ext U x; rfl

private theorem extensionTransition_isIso (n : ℕ)
    (J : systemLevel.{a, av, w} B n) {m r : ℕ} (h : m ≤ r) (hm : n ≤ m) :
    IsIso (extensionTransition B n J h) := by
  let : IsIso (restrictionStep B hm h J) := (restrictionStepIso B hm h J).isIso_hom
  exact isIso_of_hom_heq (extensionLevel_above B n r (hm.trans h) J)
    (congrArg ((systemRestriction B h).obj) (extensionLevel_above B n m hm J))
    _ _ (extensionTransition_heq B n J h hm)

private def extensionFunctor (n : ℕ) :
    systemLevel.{a, av, w} B n ⥤
      StrictRingSystem.{a, av, w} B where
  obj := extensionObject B n
  map := extensionMap B n
  map_id J := by
    apply extension_hom_ext B
    intro r
    by_cases h : n ≤ r
    · have hJ := extensionLevel_above B n r h J
      have he := hom_id_heq hJ
      exact eq_of_heq ((extensionMapLevel_above B n r h (𝟙 J)).trans
        ((heq_of_eq ((systemRestriction B h).map_id J)).trans he.symm))
    · exact (extensionLevel_below B n r h J).eq_of_src _ _
  map_comp {J K L} f g := by
    apply extension_hom_ext B
    intro r
    by_cases h : n ≤ r
    · have he := hom_comp_heq (extensionLevel_above B n r h J)
        (extensionLevel_above B n r h K) (extensionLevel_above B n r h L)
        _ _ _ _ (extensionMapLevel_above B n r h f)
        (extensionMapLevel_above B n r h g)
      exact eq_of_heq ((extensionMapLevel_above B n r h (f ≫ g)).trans
        ((heq_of_eq ((systemRestriction B h).map_comp f g)).trans he.symm))
    · exact (extensionLevel_below B n r h J).eq_of_src _ _

omit [S.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify S AddCommGrpCat.{w}] in
private theorem coeffMap_id (n : ℕ) (U : Cᵒᵖ) :
    ((coeffMap B (Nat.le_refl n)).hom.app U).hom = RingHom.id _ := by
  let Q := B ⋙
    sheafCompose S
      (forget₂ CommRingCat.{w} RingCat.{w})
  have hq : Q.map (homOfLE (Nat.le_refl n)).op = 𝟙 _ := Q.map_id _
  exact congrArg (fun f ↦ (f.hom.app U).hom) hq

private def restrictionIdentity (n : ℕ)
    (J : systemLevel.{a, av, w} B n) :
    (systemRestriction B (Nat.le_refl n)).obj J ≅ J where
  hom := { val :=
    { app := fun U ↦ (ModuleCat.restrictScalarsId'App _
        (coeffMap_id B n U) (J.val.obj U)).hom
      naturality := fun f ↦ by ext x; rfl } }
  inv := { val :=
    { app := fun U ↦ (ModuleCat.restrictScalarsId'App _
        (coeffMap_id B n U) (J.val.obj U)).inv
      naturality := fun f ↦ by ext x; rfl } }
  hom_inv_id := by ext U x; rfl
  inv_hom_id := by ext U x; rfl

private def extensionCounit (n : ℕ) (J : systemLevel.{a, av, w} B n) :
    (extensionObject B n J).level n ⟶ J := by
  simpa only [extensionObject, extensionLevel, dite_eq_left (Nat.le_refl n)] using
    (restrictionIdentity B n J).hom

private theorem extensionCounit_heq (n : ℕ) (J : systemLevel.{a, av, w} B n) :
    HEq (extensionCounit B n J) (restrictionIdentity B n J).hom := by
  unfold extensionCounit
  exact cast_heq _ _

private theorem extensionCounit_isIso (n : ℕ) (J : systemLevel.{a, av, w} B n) :
    IsIso (extensionCounit B n J) :=
  isIso_of_hom_heq (extensionLevel_above B n n (Nat.le_refl n) J) rfl
    _ _ (extensionCounit_heq B n J)

private def transposeLevel (n : ℕ)
    (M : StrictRingSystem.{a, av, w} B) (J : systemLevel.{a, av, w} B n)
    (f : M.level n ⟶ J) (r : ℕ) : M.level r ⟶ extensionLevel B n J r := by
  by_cases h : n ≤ r
  · simpa only [extensionLevel, dite_eq_left h] using
      M.transition h ≫ (systemRestriction B h).map f
  · exact 0

private theorem transposeLevel_above (n : ℕ)
    (M : StrictRingSystem.{a, av, w} B) (J : systemLevel.{a, av, w} B n)
    (f : M.level n ⟶ J) (r : ℕ) (h : n ≤ r) :
    HEq (transposeLevel B n M J f r)
      (M.transition h ≫ (systemRestriction B h).map f) := by
  unfold transposeLevel
  simp only [dite_eq_left h]
  exact cast_heq _ _

private def extensionTranspose (n : ℕ)
    (M : StrictRingSystem.{a, av, w} B) (J : systemLevel.{a, av, w} B n)
    (f : M.level n ⟶ J) : M ⟶ extensionObject B n J where
  app := transposeLevel B n M J f
  comm := by
    intro m r h
    by_cases hm : n ≤ m
    · have hr := hm.trans h
      have hJr := extensionLevel_above B n r hr J
      have hJm := extensionLevel_above B n m hm J
      have hl := hom_comp_heq rfl hJr (congrArg ((systemRestriction B h).obj) hJm)
        _ _ _ _ (transposeLevel_above B n M J f r hr)
        (extensionTransition_heq B n J h hm)
      have hh := hom_map_heq (systemRestriction B h) rfl hJm
        _ _ (transposeLevel_above B n M J f m hm)
      have hr' := hom_comp_heq rfl rfl (congrArg ((systemRestriction B h).obj) hJm)
        (M.transition h) _ (M.transition h) _ HEq.rfl hh
      have he : (M.transition hr ≫ (systemRestriction B hr).map f) ≫
          restrictionStep B hm h J = M.transition h ≫ (systemRestriction B h).map
            (M.transition hm ≫ (systemRestriction B hm).map f) := by
        ext U x
        exact congrArg (fun y ↦ f.val.app U y) (M.compose hm h U x)
      exact eq_of_heq (hl.trans ((heq_of_eq he).trans hr'.symm))
    · apply ((systemRestriction B h).map_isZero
        (extensionLevel_below B n m hm J)).eq_of_tgt

private theorem extensionTranspose_counit (n : ℕ)
    (M : StrictRingSystem.{a, av, w} B) (J : systemLevel.{a, av, w} B n)
    (f : M.level n ⟶ J) :
    (extensionTranspose B n M J f).app n ≫ extensionCounit B n J = f := by
  have ht := hom_comp_heq rfl (extensionLevel_above B n n (Nat.le_refl n) J) rfl
    _ _ _ _ (transposeLevel_above B n M J f n (Nat.le_refl n))
    (extensionCounit_heq B n J)
  change transposeLevel B n M J f n ≫ extensionCounit B n J = f
  rw [eq_of_heq ht]
  ext U x
  change f.val.app U ((M.transition (Nat.le_refl n)).val.app U x) = f.val.app U x
  rw [M.identity]

private def extensionHomEquiv (n : ℕ)
    (M : StrictRingSystem.{a, av, w} B) (J : systemLevel.{a, av, w} B n) :
    (M.level n ⟶ J) ≃ (M ⟶ (extensionFunctor B n).obj J) where
  toFun := extensionTranspose B n M J
  invFun g := g.app n ≫ extensionCounit B n J
  left_inv := extensionTranspose_counit B n M J
  right_inv g := by
    let f := g.app n ≫ extensionCounit B n J
    have hn : (extensionTranspose B n M J f).app n = g.app n := by
      let := extensionCounit_isIso B n J
      apply (cancel_mono (extensionCounit B n J)).mp
      exact extensionTranspose_counit B n M J f
    apply extension_hom_ext B
    intro r
    by_cases h : n ≤ r
    · let := extensionTransition_isIso B n J h (Nat.le_refl n)
      apply (cancel_mono (extensionTransition B n J h)).mp
      change (extensionTranspose B n M J f).app r ≫
          (extensionObject B n J).transition h =
        g.app r ≫ (extensionObject B n J).transition h
      exact ((extensionTranspose B n M J f).comm h).trans
        ((congrArg (fun k ↦ M.transition h ≫ (systemRestriction B h).map k) hn).trans
          (g.comm h).symm)
    · exact (extensionLevel_below B n r h J).eq_of_tgt _ _

private def extensionAdjunction (n : ℕ) :
    systemEvaluation B n ⊣ extensionFunctor B n :=
  Adjunction.mkOfHomEquiv
    { homEquiv := extensionHomEquiv B n
      homEquiv_naturality_left_symm := by
        intro C D J f g
        ext U x
        rfl
      homEquiv_naturality_right := by
        intro M J K f g
        apply (extensionHomEquiv B n M K).symm.injective
        change (extensionTranspose B n M K (f ≫ g)).app n ≫ extensionCounit B n K =
          ((extensionTranspose B n M J f).app n ≫ extensionMapLevel B n g n) ≫
            extensionCounit B n K
        rw [extensionTranspose_counit]
        have he : extensionMapLevel B n g n ≫ extensionCounit B n K =
            extensionCounit B n J ≫ g := by
          have hJ := extensionLevel_above B n n (Nat.le_refl n) J
          have hK := extensionLevel_above B n n (Nat.le_refl n) K
          have hl := hom_comp_heq hJ hK rfl _ _ _ _
            (extensionMapLevel_above B n n (Nat.le_refl n) g)
            (extensionCounit_heq B n K)
          have hr := hom_comp_heq hJ rfl rfl
            (extensionCounit B n J) g (restrictionIdentity B n J).hom g
            (extensionCounit_heq B n J) HEq.rfl
          have hh : (systemRestriction B (Nat.le_refl n)).map g ≫
              (restrictionIdentity B n K).hom = (restrictionIdentity B n J).hom ≫ g := by
            ext U x
            rfl
          exact eq_of_heq (hl.trans ((heq_of_eq hh).trans hr.symm))
        rw [Category.assoc, he, ← Category.assoc, extensionTranspose_counit] }

end GenericExtension

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
