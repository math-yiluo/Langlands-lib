import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionLimits

/-! # Isomorphisms after base change descend along affine limits -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

open EtaleEquivalenceRelation.Action.TargetLimit

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S)
  (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)

/-- The morphism induced on two base changes by a map over their common base. -/
noncomputable def baseChangeMap {T : Scheme.{u}} (p : T ⟶ S) :
    pullback p a ⟶ pullback p b :=
  pullback.lift (pullback.fst p a) (pullback.snd p a ≫ f)
    (by rw [Category.assoc, w, pullback.condition])

@[reassoc (attr := simp)]
lemma baseChangeMap_fst {T : Scheme.{u}} (p : T ⟶ S) :
    baseChangeMap a b f w p ≫ pullback.fst p b = pullback.fst p a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeMap_snd {T : Scheme.{u}} (p : T ⟶ S) :
    baseChangeMap a b f w p ≫ pullback.snd p b = pullback.snd p a ≫ f :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma cone_π_fst (c : Cone D) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p) (i : I) :
    (cone D t a c p hp).π.app i ≫ pullback.fst (t.app i) a =
      pullback.fst p a ≫ c.π.app i := by
  dsimp [cone, diagram, Over.pullback, Over.liftCone, Functor.mapCone]
  simp

@[reassoc (attr := simp)]
lemma cone_π_snd (c : Cone D) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p) (i : I) :
    (cone D t a c p hp).π.app i ≫ pullback.snd (t.app i) a =
      pullback.snd p a := by
  dsimp [cone, diagram, Over.pullback, Over.liftCone, Functor.mapCone]
  simp

@[reassoc (attr := simp)]
lemma diagram_map_fst {i j : I} (r : i ⟶ j) :
    (diagram D t a).map r ≫ pullback.fst (t.app j) a =
      pullback.fst (t.app i) a ≫ D.map r := by
  dsimp [diagram, Over.pullback, Over.lift]
  simp

@[reassoc (attr := simp)]
lemma diagram_map_snd {i j : I} (r : i ⟶ j) :
    (diagram D t a).map r ≫ pullback.snd (t.app j) a =
      pullback.snd (t.app i) a := by
  dsimp [diagram, Over.pullback, Over.lift]
  simp

lemma baseChangeMap_naturality {i j : I} (r : i ⟶ j) :
    (diagram D t a).map r ≫ baseChangeMap a b f w (t.app j) =
      baseChangeMap a b f w (t.app i) ≫ (diagram D t b).map r := by
  apply pullback.hom_ext <;> simp

lemma cone_baseChangeMap (c : Cone D) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p) (i : I) :
    (cone D t a c p hp).π.app i ≫ baseChangeMap a b f w (t.app i) =
      baseChangeMap a b f w p ≫ (cone D t b c p hp).π.app i := by
  apply pullback.hom_ext <;> simp

variable [IsCofiltered I] [IsAffine S] [IsAffine X] [IsAffine Y]
  [∀ i, IsAffine (D.obj i)]
  (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)
  [LocallyOfFinitePresentation a] [LocallyOfFinitePresentation b]

include hc hp in
omit [IsAffine X] [LocallyOfFinitePresentation b] in
/-- An inverse to the limit base-change map factors through one level,
retaining its equation over the common base. -/
lemma exists_inverse_factor [IsIso (baseChangeMap a b f w p)] :
    ∃ (i : I) (g : (diagram D t b).obj i ⟶ X),
      (cone D t b c p hp).π.app i ≫ g =
        inv (baseChangeMap a b f w p) ≫ pullback.snd p a ∧
      g ≫ a = pullback.snd (t.app i) b ≫ b := by
  let v := baseChangeMap a b f w p
  have hfst : inv v ≫ pullback.fst p a = pullback.fst p b := by
    rw [← baseChangeMap_fst a b f w p, IsIso.inv_hom_id_assoc]
  have hbase : (inv v ≫ pullback.snd p a) ≫ a = pullback.snd p b ≫ b := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hfst,
      pullback.condition]
  apply Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (diagram D t b) (comparison D t b ≫ (Functor.const I).map b)
    a (cone D t b c p hp) (isLimitCone D t b c p hp hc)
    (inv v ≫ pullback.snd p a)
  ext i
  simp only [NatTrans.comp_app, Functor.const_map_app, comparison,
    cone_π_snd_assoc]
  exact hbase.symm

include hc hp in
/-- If a map between two finitely presented affine schemes over an affine
base becomes an isomorphism at a cofiltered affine limit, it is already an
isomorphism after base change to one level. -/
lemma exists_isIso_baseChangeMap [IsIso (baseChangeMap a b f w p)] :
    ∃ i : I, IsIso (baseChangeMap a b f w (t.app i)) := by
  let v := baseChangeMap a b f w p
  obtain ⟨i, g, hg, hga⟩ := exists_inverse_factor D t a b f w c hc p hp
  have hgf : (cone D t b c p hp).π.app i ≫ (g ≫ f) =
      (cone D t b c p hp).π.app i ≫ pullback.snd (t.app i) b := by
    rw [← Category.assoc, hg, Category.assoc, ← baseChangeMap_snd a b f w p,
      IsIso.inv_hom_id_assoc, cone_π_snd]
  let tb := comparison D t b ≫ (Functor.const I).map b
  obtain ⟨j, r, hr⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (diagram D t b) tb b (cone D t b c p hp) (isLimitCone D t b c p hp hc)
    (g ≫ f) (pullback.snd (t.app i) b)
    (by dsimp [tb, comparison]; rw [Category.assoc, w, hga])
    rfl hgf
  have hfg : (cone D t a c p hp).π.app i ≫
      (baseChangeMap a b f w (t.app i) ≫ g) =
        (cone D t a c p hp).π.app i ≫ pullback.snd (t.app i) a := by
    rw [← Category.assoc, cone_baseChangeMap, Category.assoc, hg,
      IsIso.hom_inv_id_assoc, cone_π_snd]
  let ta := comparison D t a ≫ (Functor.const I).map a
  obtain ⟨k, s, hs⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (diagram D t a) ta a (cone D t a c p hp) (isLimitCone D t a c p hp hc)
    (baseChangeMap a b f w (t.app i) ≫ g) (pullback.snd (t.app i) a)
    (by
      dsimp [ta, comparison]
      rw [Category.assoc, hga, baseChangeMap_snd_assoc, w])
    rfl hfg
  obtain ⟨l, rl, sl, heq⟩ := IsCofiltered.cospan r s
  let z : l ⟶ i := rl ≫ r
  let gl : (diagram D t b).obj l ⟶ X := (diagram D t b).map z ≫ g
  have hgl : gl ≫ a = pullback.snd (t.app l) b ≫ b := by
    dsimp [gl]
    rw [Category.assoc, hga, diagram_map_snd_assoc]
  let n : pullback (t.app l) b ⟶ pullback (t.app l) a :=
    pullback.lift (pullback.fst (t.app l) b) gl
      (by rw [hgl, pullback.condition])
  have hn_fst : n ≫ pullback.fst (t.app l) a = pullback.fst (t.app l) b :=
    pullback.lift_fst _ _ _
  have hn_snd : n ≫ pullback.snd (t.app l) a = gl :=
    pullback.lift_snd _ _ _
  have hright : gl ≫ f = pullback.snd (t.app l) b := by
    dsimp [gl, z]
    simp only [Functor.map_comp, Category.assoc]
    rw [hr]
    simp
  have hleft : baseChangeMap a b f w (t.app l) ≫ gl =
      pullback.snd (t.app l) a := by
    dsimp [gl]
    rw [← Category.assoc, ← baseChangeMap_naturality, Category.assoc]
    dsimp [z]
    rw [heq]
    simp only [Functor.map_comp, Category.assoc]
    rw [hs]
    simp
  refine ⟨l, ⟨n, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · simp [hn_fst]
    · simpa only [Category.assoc, hn_snd, Category.id_comp] using hleft
  · apply pullback.hom_ext
    · simp [hn_fst]
    · simpa only [Category.assoc, baseChangeMap_snd, Category.id_comp,
        ← Category.assoc n, hn_snd] using hright

/-- A chosen level where the base-changed morphism is an isomorphism. -/
noncomputable def isomorphismLevel [IsIso (baseChangeMap a b f w p)] : I :=
  Classical.choose (exists_isIso_baseChangeMap D t a b f w c hc p hp)

lemma isIso_isomorphismLevel [IsIso (baseChangeMap a b f w p)] :
    IsIso (baseChangeMap a b f w
      (t.app (isomorphismLevel D t a b f w c hc p hp))) :=
  Classical.choose_spec (exists_isIso_baseChangeMap D t a b f w c hc p hp)

end Langlands.AlgebraicGeometry.AffineLimit
