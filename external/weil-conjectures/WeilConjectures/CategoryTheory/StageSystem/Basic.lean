/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Order.Directed

/-!
# The pair category of a directed system of categories

Let `I` be a directed preorder (in the application, the finite subextensions `E ⊆ ℚ̄_ℓ` of
`ℚ_ℓ`, ordered by inclusion) and let `C i` (`i : I`) be categories with transition functors
`T h : C i ⥤ C j` for `h : i ≤ j` and associators `T h ⋙ T h' ≅ T (h.trans h')` satisfying the
cocycle condition (`CategoryTheory.StageSystem`). In the application `C E = D^b_c(T, E)` and
`T_{F/E} = F ⊗ᴸ_E -` is the derived extension of scalars.

The *pair category* `S.PairCategory` has
as objects the pairs `(i, x)` with `x : C i`, and as morphisms `(i, x) ⟶ (j, y)` the filtered
colimit
```
  colim_{n ≥ i, j} Hom_{C n}(T x, T y)
```
of the Hom sets at the common stages, the transition maps being the transports
`u ↦ u_p = a⁻¹ ≫ T u ≫ a` (`CategoryTheory.StageSystem.tr`). A morphism is represented by a
triple `(n, u)` (`CategoryTheory.StageSystem.Rep`), two representatives being identified when
their transports to some common stage agree; composition is computed after transporting the
representatives to a common stage. It is the filtered 2-colimit of the categories `C i`
(in the ordinary-category sense). No unit isomorphisms `T (le_refl i) ≅ 𝟭` are needed for
this construction: only the cocycle condition of the associators is used.

## Main definitions

- `CategoryTheory.StageSystem`: a directed system of categories with associators.
- `CategoryTheory.StageSystem.PairCategory`: its pair category, with
  `CategoryTheory.StageSystem.PairCategory.mkHom n hX hY u` the morphism represented by `u` at
  the stage `n`.
- `CategoryTheory.StageSystem.ι i : C i ⥤ S.PairCategory`: the inclusion `j_i` of the stage `i`,
  and `CategoryTheory.StageSystem.transIso h : S.T h ⋙ S.ι j ≅ S.ι i`.

## Main statements

- `CategoryTheory.StageSystem.PairCategory.mkHom_eq_mkHom_iff`: two morphisms represented at a
  stage `n` are equal if and only if they become equal at some further stage.
- `CategoryTheory.StageSystem.PairCategory.exists_mkHom_eq`: every morphism is represented at
  every sufficiently large stage.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category

variable {I : Type w} [Preorder I] (C : I → Type u) [∀ i, Category.{v} (C i)]

/-- A *stage system* on a family of categories `C i` indexed by a preorder: transition functors
`T h : C i ⥤ C j` for `h : i ≤ j` together with associators `T h ⋙ T h' ≅ T (h.trans h')` which
satisfy the cocycle condition (the associativity constraint of a pseudofunctor). In the
application these are the derived extensions of scalars `T_{F/E} = F ⊗ᴸ_E -` between the
finite coefficient stages, with their associators. -/
structure StageSystem where
  /-- The transition functors. -/
  T : ∀ {i j : I}, i ≤ j → (C i ⥤ C j)
  /-- The associators. -/
  assoc : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), T hij ⋙ T hjk ≅ T (hij.trans hjk)
  /-- The cocycle condition of the associators. -/
  cocycle : ∀ {i j k m : I} (hij : i ≤ j) (hjk : j ≤ k) (hkm : k ≤ m) (X : C i),
    (T hkm).map ((assoc hij hjk).hom.app X) ≫ (assoc (hij.trans hjk) hkm).hom.app X =
      (assoc hjk hkm).hom.app ((T hij).obj X) ≫ (assoc hij (hjk.trans hkm)).hom.app X

namespace StageSystem

variable {C} (S : StageSystem C)

@[reassoc]
lemma cocycle_inv {i j k m : I} (hij : i ≤ j) (hjk : j ≤ k) (hkm : k ≤ m) (X : C i) :
    (S.assoc (hij.trans hjk) hkm).inv.app X ≫ (S.T hkm).map ((S.assoc hij hjk).inv.app X) =
      (S.assoc hij (hjk.trans hkm)).inv.app X ≫ (S.assoc hjk hkm).inv.app ((S.T hij).obj X) := by
  rw [← cancel_epi ((S.T hkm).map ((S.assoc hij hjk).hom.app X) ≫
    (S.assoc (hij.trans hjk) hkm).hom.app X)]
  conv_rhs => rw [S.cocycle]
  simp [← Functor.map_comp]

/-- The transport `u ↦ u_p = a⁻¹ ≫ T u ≫ a` of a morphism at the stage `n` to a stage `p ≥ n`. -/
def tr {i j n p : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) {x : C i} {y : C j}
    (f : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    (S.T (hi.trans h)).obj x ⟶ (S.T (hj.trans h)).obj y :=
  (S.assoc hi h).inv.app x ≫ (S.T h).map f ≫ (S.assoc hj h).hom.app y

variable {S}

@[simp]
lemma tr_id {i n p : I} {hi : i ≤ n} (h : n ≤ p) (x : C i) :
    S.tr (hi := hi) (hj := hi) h (𝟙 ((S.T hi).obj x)) = 𝟙 _ := by
  simp [tr]

@[reassoc (attr := simp)]
lemma tr_comp {i j k n p : I} {hi : i ≤ n} {hj : j ≤ n} {hk : k ≤ n} (h : n ≤ p) {x : C i}
    {y : C j} {z : C k} (f : (S.T hi).obj x ⟶ (S.T hj).obj y)
    (g : (S.T hj).obj y ⟶ (S.T hk).obj z) :
    S.tr h (f ≫ g) = S.tr h f ≫ S.tr h g := by
  simp [tr]

/-- Transport along `n ≤ p ≤ q` is the transport along `n ≤ q`: this is where the cocycle
condition is used (`(u_N)_P = u_P`). -/
@[simp]
lemma tr_tr {i j n p q : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) (h' : p ≤ q) {x : C i}
    {y : C j} (f : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    S.tr h' (S.tr h f) = S.tr (h.trans h') f := by
  simp only [tr, Functor.map_comp, Category.assoc]
  rw [S.cocycle hj h h', S.cocycle_inv_assoc hi h h']
  have := (S.assoc h h').hom.naturality f
  simp only [Functor.comp_map] at this
  rw [reassoc_of% this]
  simp

/-- The composite of two transition functors on a morphism, through the associator. -/
lemma map_map_eq {i j k : I} (h : i ≤ j) (h' : j ≤ k) {x y : C i} (f : x ⟶ y) :
    (S.T h').map ((S.T h).map f) =
      (S.assoc h h').hom.app x ≫ (S.T (h.trans h')).map f ≫ (S.assoc h h').inv.app y := by
  simp

/-- Transport of the image of a morphism of the stage `i`. -/
lemma tr_map {i n p : I} {hi : i ≤ n} (h : n ≤ p) {x y : C i} (f : x ⟶ y) :
    S.tr (hi := hi) (hj := hi) h ((S.T hi).map f) = (S.T (hi.trans h)).map f := by
  have := (S.assoc hi h).hom.naturality f
  simp only [Functor.comp_map] at this
  simp [tr, this]

lemma tr_injective {i j n p : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) {x : C i} {y : C j}
    {f g : (S.T hi).obj x ⟶ (S.T hj).obj y} :
    S.tr h f = S.tr h g ↔ (S.T h).map f = (S.T h).map g := by
  constructor
  · intro e
    simpa [tr] using (S.assoc hi h).hom.app x ≫= e =≫ (S.assoc hj h).inv.app y
  · intro e
    simp [tr, e]

variable (S)

/-- The *pair category* of a stage system:
an object is a pair `(i, x)` of a stage `i` and an object `x : C i`. -/
@[ext, nolint unusedArguments]
structure PairCategory (S : StageSystem C) where
  /-- The stage of the object. -/
  stage : I
  /-- The object at that stage. -/
  obj : C stage

namespace PairCategory

variable {S}

/-- The object `T x` at a stage `n ≥ i` of an object `(i, x)` of the pair category. -/
abbrev toStage (X : S.PairCategory) {n : I} (h : X.stage ≤ n) : C n := (S.T h).obj X.obj

/-- A representative `(n, u)` of a morphism `(i, x) ⟶ (j, y)` of the pair category: a stage
`n ≥ i, j` and a morphism `u : T x ⟶ T y` at that stage. -/
structure Rep (X Y : S.PairCategory) where
  /-- The stage of the representative. -/
  k : I
  hX : X.stage ≤ k
  hY : Y.stage ≤ k
  /-- The morphism at the stage `k`. -/
  u : X.toStage hX ⟶ Y.toStage hY

namespace Rep

variable {X Y : S.PairCategory}

/-- Two representatives are equivalent if their transports to some common stage agree. -/
def Rel (r s : Rep X Y) : Prop :=
  ∃ (p : I) (hr : r.k ≤ p) (hs : s.k ≤ p), S.tr hr r.u = S.tr hs s.u

lemma rel_of_eq {r s : Rep X Y} {p : I} (hr : r.k ≤ p) (hs : s.k ≤ p)
    (e : S.tr hr r.u = S.tr hs s.u) {q : I} (h : p ≤ q) :
    S.tr (hr.trans h) r.u = S.tr (hs.trans h) s.u := by
  rw [← tr_tr hr h, ← tr_tr hs h, e]

variable [IsDirectedOrder I]

lemma rel_equivalence : _root_.Equivalence (Rel (X := X) (Y := Y)) where
  refl r := ⟨r.k, le_rfl, le_rfl, rfl⟩
  symm := fun ⟨p, hr, hs, e⟩ ↦ ⟨p, hs, hr, e.symm⟩
  trans := by
    rintro r s t ⟨p, hr, hs, e⟩ ⟨q, hs', ht, e'⟩
    obtain ⟨m, hpm, hqm⟩ := exists_ge_ge p q
    exact ⟨m, hr.trans hpm, ht.trans hqm,
      (rel_of_eq hr hs e hpm).trans (rel_of_eq hs' ht e' hqm)⟩

/-- The setoid of representatives of morphisms of the pair category. -/
instance setoid (X Y : S.PairCategory) : Setoid (Rep X Y) :=
  ⟨Rel, rel_equivalence⟩

end Rep

variable [IsDirectedOrder I]

/-- A common stage of two stages, chosen once and for all. -/
noncomputable def commonStage (n n' : I) : I := (exists_ge_ge n n').choose

lemma le_commonStage_left (n n' : I) : n ≤ commonStage n n' := (exists_ge_ge n n').choose_spec.1

lemma le_commonStage_right (n n' : I) : n' ≤ commonStage n n' :=
  (exists_ge_ge n n').choose_spec.2

/-- The composite of two representatives, computed after transport to a common stage. -/
noncomputable def Rep.comp {X Y Z : S.PairCategory} (r : Rep X Y) (s : Rep Y Z) : Rep X Z :=
  ⟨commonStage r.k s.k, r.hX.trans (le_commonStage_left _ _),
    s.hY.trans (le_commonStage_right _ _),
    S.tr (le_commonStage_left _ _) r.u ≫ S.tr (le_commonStage_right _ _) s.u⟩

lemma Rep.comp_rel {X Y Z : S.PairCategory} {r r' : Rep X Y} {s s' : Rep Y Z}
    (hr : Rep.Rel r r') (hs : Rep.Rel s s') : Rep.Rel (r.comp s) (r'.comp s') := by
  obtain ⟨p, h₁, h₂, e⟩ := hr
  obtain ⟨q, h₃, h₄, e'⟩ := hs
  obtain ⟨a, ha₁, ha₂⟩ := exists_ge_ge p q
  obtain ⟨b, hb₁, hb₂⟩ := exists_ge_ge (commonStage r.k s.k) (commonStage r'.k s'.k)
  obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge a b
  refine ⟨m, hb₁.trans hm₂, hb₂.trans hm₂, ?_⟩
  change S.tr _ (S.tr _ r.u ≫ S.tr _ s.u) = S.tr _ (S.tr _ r'.u ≫ S.tr _ s'.u)
  rw [tr_comp, tr_comp, tr_tr, tr_tr, tr_tr, tr_tr]
  have E := rel_of_eq h₁ h₂ e (ha₁.trans hm₁)
  have E' := rel_of_eq h₃ h₄ e' (ha₂.trans hm₁)
  exact congr_arg₂ (· ≫ ·) E E'

variable (S) in
/-- The morphisms, identities and composition of the pair category: morphisms are classes of
representatives, composition is computed at a common stage. -/
noncomputable instance categoryStruct : CategoryStruct.{max w v} S.PairCategory where
  Hom X Y := Quotient (Rep.setoid X Y)
  id X := Quotient.mk _ ⟨X.stage, le_rfl, le_rfl, 𝟙 _⟩
  comp f g := Quotient.map₂ Rep.comp (fun _ _ hr _ _ hs ↦ Rep.comp_rel hr hs) f g

/-- The morphism of the pair category represented by `u` at the stage `n`. -/
def mkHom {X Y : S.PairCategory} (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
    (u : X.toStage hX ⟶ Y.toStage hY) : X ⟶ Y :=
  Quotient.mk _ ⟨n, hX, hY, u⟩

/-- Induction principle for morphisms of the pair category: every morphism is represented at
some stage. -/
@[elab_as_elim]
lemma hom_induction {X Y : S.PairCategory} {motive : (X ⟶ Y) → Prop}
    (h : ∀ (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n) (u : X.toStage hX ⟶ Y.toStage hY),
      motive (mkHom n hX hY u)) (f : X ⟶ Y) : motive f :=
  Quotient.ind (fun r ↦ h r.k r.hX r.hY r.u) f

lemma mkHom_eq_mkHom_iff' {X Y : S.PairCategory} {n n' : I} {hX : X.stage ≤ n}
    {hY : Y.stage ≤ n} {hX' : X.stage ≤ n'} {hY' : Y.stage ≤ n'}
    (u : X.toStage hX ⟶ Y.toStage hY) (u' : X.toStage hX' ⟶ Y.toStage hY') :
    mkHom n hX hY u = mkHom n' hX' hY' u' ↔
      ∃ (p : I) (h : n ≤ p) (h' : n' ≤ p), S.tr h u = S.tr h' u' :=
  Quotient.eq (r := Rep.setoid X Y)

/-- A morphism represented at the stage `n` is also represented by its transport to any stage
`p ≥ n`. -/
lemma mkHom_tr {X Y : S.PairCategory} {n p : I} {hX : X.stage ≤ n} {hY : Y.stage ≤ n}
    (h : n ≤ p) (u : X.toStage hX ⟶ Y.toStage hY) :
    mkHom p (hX.trans h) (hY.trans h) (S.tr h u) = mkHom n hX hY u :=
  (mkHom_eq_mkHom_iff' _ _).2 ⟨p, le_rfl, h, by simp⟩

/-- Two morphisms represented at the same stage `n` are equal if and only if they become equal
at some stage `p ≥ n`. -/
lemma mkHom_eq_mkHom_iff {X Y : S.PairCategory} {n : I} {hX : X.stage ≤ n} {hY : Y.stage ≤ n}
    (u u' : X.toStage hX ⟶ Y.toStage hY) :
    mkHom n hX hY u = mkHom n hX hY u' ↔
      ∃ (p : I) (h : n ≤ p), (S.T h).map u = (S.T h).map u' := by
  rw [mkHom_eq_mkHom_iff']
  constructor
  · rintro ⟨p, h, h', e⟩
    exact ⟨p, h, tr_injective h |>.1 e⟩
  · rintro ⟨p, h, e⟩
    exact ⟨p, h, h, tr_injective h |>.2 e⟩

/-- Every morphism is represented at every sufficiently large stage. -/
lemma exists_mkHom_eq {X Y : S.PairCategory} (f : X ⟶ Y) :
    ∃ (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n),
      ∀ (p : I) (h : n ≤ p), ∃ u : X.toStage (hX.trans h) ⟶ Y.toStage (hY.trans h),
        f = mkHom p _ _ u := by
  induction f using hom_induction with
  | h n hX hY u => exact ⟨n, hX, hY, fun p h ↦ ⟨S.tr h u, (mkHom_tr h u).symm⟩⟩

/-- Every morphism is represented at some stage above any given stage. -/
lemma exists_le_mkHom_eq {X Y : S.PairCategory} (f : X ⟶ Y) (m : I) :
    ∃ (n : I) (_ : m ≤ n) (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
      (u : X.toStage hX ⟶ Y.toStage hY), f = mkHom n hX hY u := by
  obtain ⟨n, hX, hY, H⟩ := exists_mkHom_eq f
  obtain ⟨p, hnp, hmp⟩ := exists_ge_ge n m
  obtain ⟨u, rfl⟩ := H p hnp
  exact ⟨p, hmp, _, _, u, rfl⟩

lemma mkHom_comp_mkHom {X Y Z : S.PairCategory} {n : I} {hX : X.stage ≤ n} {hY : Y.stage ≤ n}
    {hZ : Z.stage ≤ n} (u : X.toStage hX ⟶ Y.toStage hY) (v : Y.toStage hY ⟶ Z.toStage hZ) :
    mkHom n hX hY u ≫ mkHom n hY hZ v = mkHom n hX hZ (u ≫ v) := by
  change mkHom _ _ _ _ = _
  rw [mkHom_eq_mkHom_iff']
  refine ⟨commonStage n n, le_rfl, le_commonStage_left _ _, ?_⟩
  simp only [tr_comp, tr_tr]

lemma mkHom_comp_mkHom' {X Y Z : S.PairCategory} {n n' : I} {hX : X.stage ≤ n}
    {hY : Y.stage ≤ n} {hY' : Y.stage ≤ n'} {hZ : Z.stage ≤ n'}
    (u : X.toStage hX ⟶ Y.toStage hY) (v : Y.toStage hY' ⟶ Z.toStage hZ)
    {p : I} (h : n ≤ p) (h' : n' ≤ p) :
    mkHom n hX hY u ≫ mkHom n' hY' hZ v = mkHom p _ _ (S.tr h u ≫ S.tr h' v) := by
  rw [← mkHom_tr h u, ← mkHom_tr h' v, mkHom_comp_mkHom]

lemma id_eq_mkHom (X : S.PairCategory) {n : I} (hX : X.stage ≤ n) :
    𝟙 X = mkHom n hX hX (𝟙 _) := by
  change mkHom _ _ _ _ = _
  rw [← mkHom_tr hX (𝟙 _)]
  simp

end PairCategory

open PairCategory

variable [IsDirectedOrder I]

/-- The pair category is a category. -/
noncomputable instance : Category.{max w v} S.PairCategory where
  toCategoryStruct := categoryStruct S
  id_comp f := by
    induction f using hom_induction with
    | h n hX hY u =>
      rw [id_eq_mkHom _ hX, mkHom_comp_mkHom, id_comp]
  comp_id f := by
    induction f using hom_induction with
    | h n hX hY u =>
      rw [id_eq_mkHom _ hY, mkHom_comp_mkHom, comp_id]
  assoc f g h := by
    induction f using hom_induction with
    | h n hX hY u =>
    induction g using hom_induction with
    | h n' hY' hZ v =>
    induction h using hom_induction with
    | h n'' hZ' hW w =>
      obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
      obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
      rw [← mkHom_tr (ha.trans hp) u, ← mkHom_tr (ha'.trans hp) v, ← mkHom_tr hp' w,
        mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom,
        Category.assoc]

namespace PairCategory

variable {S}

@[reassoc]
lemma mkHom_comp_mkHom_assoc' {X Y Z W : S.PairCategory} {n : I} {hX : X.stage ≤ n}
    {hY : Y.stage ≤ n} {hZ : Z.stage ≤ n} (u : X.toStage hX ⟶ Y.toStage hY)
    (v : Y.toStage hY ⟶ Z.toStage hZ) (g : Z ⟶ W) :
    mkHom n hX hY u ≫ mkHom n hY hZ v ≫ g = mkHom n hX hZ (u ≫ v) ≫ g := by
  rw [← Category.assoc, mkHom_comp_mkHom]


/-- Equality of morphisms of the pair category, tested at a common stage. -/
lemma hom_ext_iff {X Y : S.PairCategory} {n : I} {hX : X.stage ≤ n} {hY : Y.stage ≤ n}
    (u u' : X.toStage hX ⟶ Y.toStage hY) :
    (mkHom n hX hY u : X ⟶ Y) = mkHom n hX hY u' ↔
      ∃ (p : I) (h : n ≤ p), (S.T h).map u = (S.T h).map u' :=
  mkHom_eq_mkHom_iff u u'

/-- Two morphisms of the pair category can be represented at a common stage above any given
stage. -/
lemma exists_common_stage {X Y X' Y' : S.PairCategory} (f : X ⟶ Y) (g : X' ⟶ Y') (m : I) :
    ∃ (n : I) (_ : m ≤ n) (hX : X.stage ≤ n) (hY : Y.stage ≤ n) (hX' : X'.stage ≤ n)
      (hY' : Y'.stage ≤ n) (u : X.toStage hX ⟶ Y.toStage hY)
      (u' : X'.toStage hX' ⟶ Y'.toStage hY'), f = mkHom n hX hY u ∧ g = mkHom n hX' hY' u' := by
  obtain ⟨n, hmn, hX, hY, u, rfl⟩ := exists_le_mkHom_eq f m
  obtain ⟨n', hnn', hX', hY', u', rfl⟩ := exists_le_mkHom_eq g n
  exact ⟨n', hmn.trans hnn', hX.trans hnn', hY.trans hnn', hX', hY', S.tr hnn' u, u',
    (mkHom_tr hnn' u).symm, rfl⟩

end PairCategory

open PairCategory

/-- The inclusion `j_i : C i ⥤ S.PairCategory` of the stage `i`, `x ↦ (i, x)`. -/
noncomputable def ι (i : I) : C i ⥤ S.PairCategory where
  obj x := ⟨i, x⟩
  map f := mkHom i le_rfl le_rfl ((S.T le_rfl).map f)
  map_id x := by
    rw [id_eq_mkHom _ le_rfl]
    simp
  map_comp f g := by
    rw [mkHom_comp_mkHom]
    simp

variable {S}

lemma ι_map_eq {i n : I} (h : i ≤ n) {x y : C i} (f : x ⟶ y) :
    (S.ι i).map f = mkHom (X := ⟨i, x⟩) (Y := ⟨i, y⟩) n h h ((S.T h).map f) := by
  change mkHom _ _ _ _ = _
  rw [← mkHom_tr h, tr_map]

lemma ι_obj (i : I) (x : C i) : (S.ι i).obj x = ⟨i, x⟩ := rfl

/-- The stage inclusions are faithful up to passing to a further stage. -/
lemma ι_map_eq_ι_map_iff {i : I} {x y : C i} (f g : x ⟶ y) :
    (S.ι i).map f = (S.ι i).map g ↔ ∃ (p : I) (h : i ≤ p), (S.T h).map f = (S.T h).map g := by
  rw [ι_map_eq le_rfl, ι_map_eq le_rfl, mkHom_eq_mkHom_iff]
  refine exists_congr fun p ↦ exists_congr fun h ↦ ?_
  rw [map_map_eq, map_map_eq, cancel_epi, cancel_mono]

variable (S) in
/-- The isomorphism `(i, x) ≅ (n, T x)` in the pair category, for a stage `n ≥ i`. -/
noncomputable def isoToStage (X : S.PairCategory) {n : I} (h : X.stage ≤ n) :
    X ≅ (S.ι n).obj (X.toStage h) where
  hom := mkHom (Y := ⟨n, _⟩) n h le_rfl ((S.assoc h le_rfl).inv.app X.obj)
  inv := mkHom (X := ⟨n, _⟩) n le_rfl h ((S.assoc h le_rfl).hom.app X.obj)
  hom_inv_id := by rw [mkHom_comp_mkHom, id_eq_mkHom _ h]; simp
  inv_hom_id := by rw [mkHom_comp_mkHom, id_eq_mkHom _ le_rfl]; simp; rfl

/-- A morphism represented at the stage `n` is, up to the isomorphisms `isoToStage`, the image of
its representative under the stage inclusion `j_n`. -/
lemma mkHom_eq_isoToStage {X Y : S.PairCategory} {n : I} (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
    (u : X.toStage hX ⟶ Y.toStage hY) :
    mkHom n hX hY u = (S.isoToStage X hX).hom ≫ (S.ι n).map u ≫ (S.isoToStage Y hY).inv := by
  simp only [isoToStage, ι_map_eq le_rfl, mkHom_comp_mkHom]
  rw [← mkHom_tr (le_rfl : n ≤ n) u]
  rfl

lemma ι_map_eq_isoToStage {X Y : S.PairCategory} {n : I} (hX : X.stage ≤ n)
    (hY : Y.stage ≤ n) (u : X.toStage hX ⟶ Y.toStage hY) :
    (S.ι n).map u = (S.isoToStage X hX).inv ≫ mkHom n hX hY u ≫ (S.isoToStage Y hY).hom := by
  simp [mkHom_eq_isoToStage hX hY u]

variable (S) in
/-- The identification `j_j ∘ T_{j/i} ≅ j_i` (the isomorphisms `(E, K) ≅ (F, T_{F/E} K)`). -/
noncomputable def transIso {i j : I} (h : i ≤ j) : S.T h ⋙ S.ι j ≅ S.ι i :=
  NatIso.ofComponents (fun x ↦ (S.isoToStage ⟨i, x⟩ h).symm) (fun {x y} f ↦ by
    dsimp [isoToStage]
    rw [ι_map_eq le_rfl, ι_map_eq h, mkHom_comp_mkHom, mkHom_comp_mkHom]
    congr 1
    exact (S.assoc h le_rfl).hom.naturality f)

lemma transIso_hom_app {i j : I} (h : i ≤ j) (x : C i) :
    (S.transIso h).hom.app x = (S.isoToStage ⟨i, x⟩ h).inv := rfl

lemma transIso_inv_app {i j : I} (h : i ≤ j) (x : C i) :
    (S.transIso h).inv.app x = (S.isoToStage ⟨i, x⟩ h).hom := rfl

lemma transIso_hom_app_eq {i j : I} (h : i ≤ j) (x : C i) :
    (S.transIso h).hom.app x =
      mkHom (X := ⟨j, (S.T h).obj x⟩) (Y := ⟨i, x⟩) j le_rfl h ((S.assoc h le_rfl).hom.app x) :=
  rfl

lemma eqToHom_mk {i : I} {x y : C i} (h : (⟨i, x⟩ : S.PairCategory) = ⟨i, y⟩) :
    eqToHom h = (S.ι i).map (eqToHom (eq_of_heq (PairCategory.mk.inj h).2)) := by
  obtain rfl := eq_of_heq (PairCategory.mk.inj h).2
  simp only [eqToHom_refl, Functor.map_id]; rfl

/-- A morphism `j_n x ⟶ j_n y` represented at a stage `p ≥ n`, transported along the
identifications `j_n ≅ j_p ∘ T`, is the image of its representative. -/
lemma transIso_hom_app_mkHom_transIso_inv_app {n p : I} (h : n ≤ p) {x y : C n}
    (hX : ((S.ι n).obj x).stage ≤ p) (hY : ((S.ι n).obj y).stage ≤ p)
    (u : (S.T h).obj x ⟶ (S.T h).obj y) :
    (S.transIso h).hom.app x ≫ mkHom (X := (S.ι n).obj x) (Y := (S.ι n).obj y) p hX hY u ≫
      (S.transIso h).inv.app y = (S.ι p).map u := by
  rw [mkHom_eq_isoToStage, transIso_hom_app, transIso_inv_app]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  exact Category.comp_id _

variable (S) in
/-- The stage `ℚ̄_ℓ`: in the filtered 2-colimit of a stage
system (in the application, `Dᵇc(X, ℚ̄_ℓ)` as the colimit of the categories `Dᵇc(X, E)` over the
finite extensions `E/ℚ_ℓ`) every object and every morphism is represented at a finite stage, and
two representatives at a stage define the same morphism if and only if they agree after a further
extension. -/
theorem exists_stage_representation :
    (∀ X : S.PairCategory, ∃ (i : I) (x : C i), (S.ι i).obj x = X) ∧
    (∀ {i j : I} (x : C i) (y : C j) (f : (S.ι i).obj x ⟶ (S.ι j).obj y),
      ∃ (n : I) (hi : i ≤ n) (hj : j ≤ n) (u : (S.T hi).obj x ⟶ (S.T hj).obj y),
        f = (S.transIso hi).inv.app x ≫ (S.ι n).map u ≫ (S.transIso hj).hom.app y) ∧
    ∀ {i : I} {x y : C i} (u u' : x ⟶ y),
      (S.ι i).map u = (S.ι i).map u' ↔ ∃ (p : I) (h : i ≤ p), (S.T h).map u = (S.T h).map u' := by
  refine ⟨fun X ↦ ⟨X.stage, X.obj, rfl⟩, fun {i j} x y f ↦ ?_, fun u u' ↦ ι_map_eq_ι_map_iff u u'⟩
  obtain ⟨n, -, hi, hj, u, rfl⟩ := PairCategory.exists_le_mkHom_eq f i
  exact ⟨n, hi, hj, u, mkHom_eq_isoToStage hi hj u⟩

end StageSystem

end CategoryTheory
