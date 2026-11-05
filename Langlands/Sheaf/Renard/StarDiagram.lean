import Langlands.Sheaf.Renard.GermSectionSheaf
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.Tactic

/-!
# An internal star-space diagram in Renard's basis-sheaf category

The topology is named, with only a local instance. The space universe and
the section-carrier universe are independent.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace Langlands.Sheaf.Renard.StarDiagram

/-- Opens are the empty set and the sets containing the distinguished point. -/
@[instance_reducible]
def topology (I : Type u) : TopologicalSpace (Option I) where
  IsOpen S := S = ∅ ∨ none ∈ S
  isOpen_univ := Or.inr (Set.mem_univ _)
  isOpen_inter := by
    intro S T hS hT
    rcases hS with rfl | hS
    · exact Or.inl (Set.empty_inter T)
    rcases hT with rfl | hT
    · exact Or.inl (Set.inter_empty S)
    exact Or.inr ⟨hS, hT⟩
  isOpen_sUnion := by
    intro S hS
    rcases Set.eq_empty_or_nonempty (⋃₀ S) with h | ⟨x, hx⟩
    · exact Or.inl h
    obtain ⟨U, hU, hxU⟩ := hx
    rcases hS U hU with h | h
    · rw [h] at hxU
      exact False.elim hxU
    · exact Or.inr ⟨U, hU, h⟩

variable (I : Type u)

local instance : TopologicalSpace (Option I) := topology I

theorem isOpen_iff (S : Set (Option I)) : IsOpen S ↔ S = ∅ ∨ none ∈ S := Iff.rfl

/-- All actual opens of the named star topology, in the published basis category. -/
abbrev StarOpen := BasisOpen (allOpenBasis (Option I))

def empty : StarOpen I := allOpen ⊥
def whole : StarOpen I := allOpen ⊤
def E : StarOpen I := allOpen ⟨{none}, Or.inr (by simp)⟩
def U (i : I) : StarOpen I := allOpen ⟨{none, some i}, Or.inr (by simp)⟩

variable {I}

@[simp] theorem mem_empty (x : Option I) : x ∉ (empty I).obj := by simp [empty, allOpen]
@[simp] theorem mem_whole (x : Option I) : x ∈ (whole I).obj := by simp [whole, allOpen]
@[simp] theorem mem_E (x : Option I) : x ∈ (E I).obj ↔ x = none := Iff.rfl
@[simp] theorem mem_U (i : I) (x : Option I) :
    x ∈ (U I i).obj ↔ x = none ∨ x = some i := by
  change x ∈ ({none, some i} : Set (Option I)) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

/-- The nonempty-open test, expressed by the distinguished point. -/
def Live (V : StarOpen I) : Prop := none ∈ V.obj

/-- An open contains a point other than the distinguished point. -/
def Leaf (V : StarOpen I) : Prop := ∃ i, some i ∈ V.obj

theorem live_of_mem {V : StarOpen I} {x : Option I} (hx : x ∈ V.obj) : Live V := by
  rcases V.obj.isOpen with h | h
  · change x ∈ (V.obj : Set (Option I)) at hx
    rw [h] at hx
    exact False.elim hx
  · exact h

theorem live_mono {V W : StarOpen I} (h : V.obj ≤ W.obj) (hV : Live V) : Live W :=
  h hV

theorem leaf_mono {V W : StarOpen I} (h : V.obj ≤ W.obj) : Leaf V → Leaf W := by
  rintro ⟨i, hi⟩
  exact ⟨i, h hi⟩

theorem live_of_leaf {V : StarOpen I} (hV : Leaf V) : Live V := by
  obtain ⟨i, hi⟩ := hV
  exact live_of_mem hi

theorem E_le {V : StarOpen I} (hV : Live V) : (E I).obj ≤ V.obj := by
  intro x hx
  have hx' : x = none := (mem_E x).mp hx
  subst x
  exact hV

theorem U_le {V : StarOpen I} {i : I} (hi : some i ∈ V.obj) :
    (U I i).obj ≤ V.obj := by
  intro x hx
  rcases (mem_U i x).mp hx with rfl | rfl
  · exact live_of_mem hi
  · exact hi

theorem not_live_eq_bot {V : StarOpen I} (hV : ¬ Live V) : V.obj = ⊥ := by
  apply bot_unique
  intro x hx
  exact False.elim (hV (live_of_mem hx))

theorem live_iff_nonempty (V : StarOpen I) : Live V ↔ (V.obj : Set (Option I)).Nonempty :=
  ⟨fun h => ⟨none, h⟩, fun ⟨_, h⟩ => live_of_mem h⟩

theorem eq_E_of_live_not_leaf {V : StarOpen I} (hV : Live V) (hL : ¬ Leaf V) :
    V = E I := by
  apply ObjectProperty.FullSubcategory.ext
  apply le_antisymm
  · intro x hx
    cases x with
    | none => exact (mem_E _).mpr rfl
    | some i => exact False.elim (hL ⟨i, hx⟩)
  · exact E_le hV

@[simp] theorem live_E : Live (E I) := rfl
@[simp] theorem not_leaf_E : ¬ Leaf (E I) := by
  rintro ⟨i, hi⟩
  change some i = none at hi
  cases hi
@[simp] theorem leaf_U (i : I) : Leaf (U I i) := ⟨i, (mem_U i _).mpr (Or.inr rfl)⟩
@[simp] theorem live_U (i : I) : Live (U I i) := live_of_leaf (leaf_U i)
@[simp] theorem not_live_empty : ¬ Live (empty I) := by simp [Live]

/-- Including E as the none-indexed member also handles an empty I. -/
def starCover (i : Option I) : StarOpen I :=
  match i with
  | none => E I
  | some j => U I j

theorem starCover_covers : FamilyCovers (whole I) (starCover (I := I)) := by
  refine ⟨fun _ => le_top, ?_⟩
  intro x _
  cases x with
  | none => exact ⟨none, live_E⟩
  | some i => exact ⟨some i, (mem_U i _).mpr (Or.inr rfl)⟩

theorem U_inter_U {i j : I} (hij : i ≠ j) :
    (U I i).obj ⊓ (U I j).obj = (E I).obj := by
  ext x
  change (x = none ∨ x = some i) ∧ (x = none ∨ x = some j) ↔ x = none
  constructor
  · rintro ⟨hxi, hxj⟩
    rcases hxi with h | h
    · exact h
    rcases hxj with h' | h'
    · exact h'
    exact False.elim (hij (Option.some.inj (h.symm.trans h')))
  · intro h
    exact ⟨Or.inl h, Or.inl h⟩

/-- An ambient group with the constraint that an absent support has only zero sections. -/
def supported (A : Type v) [AddCommGroup A] (p : Prop) : AddSubgroup A where
  carrier := {a | ¬ p → a = 0}
  zero_mem' := fun _ => rfl
  add_mem' := by
    intro a b ha hb h
    simp [ha h, hb h]
  neg_mem' := by
    intro a ha h
    simp [ha h]

theorem supported_ext {A : Type v} [AddCommGroup A] {p : Prop}
    {a b : supported A p} (h : (a : A) = (b : A)) : a = b := Subtype.ext h

theorem supported_eq_zero {A : Type v} [AddCommGroup A] {p : Prop}
    (hp : ¬ p) (a : supported A p) : a = 0 := Subtype.ext (a.property hp)

/-- At a present support the section group is the actual ambient coefficient group. -/
def supportedEquiv (A : Type v) [AddCommGroup A] {p : Prop} (hp : p) :
    supported A p ≃+ A where
  toFun a := a.val
  invFun a := ⟨a, fun h => False.elim (h hp)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

abbrev Integers := ULift.{v} ℤ
abbrev ModTwo := ULift.{v} (ZMod 2)
abbrev IntSections (V : StarOpen I) := supported Integers.{v} (Live V)

/-- The transition multiplier: d only when moving from a leaf-containing open to E. -/
noncomputable def factor (d : ℤ) (V W : StarOpen I) : ℤ :=
  @ite ℤ (Leaf W ∧ ¬ Leaf V) (Classical.propDecidable _) d 1

theorem factor_self (d : ℤ) (V : StarOpen I) : factor d V V = 1 := by
  simp [factor]

theorem factor_comp (d : ℤ) {V W Z : StarOpen I}
    (hVW : V.obj ≤ W.obj) (hWZ : W.obj ≤ Z.obj) :
    factor d V Z = factor d V W * factor d W Z := by
  classical
  have h₁ := leaf_mono hVW
  have h₂ := leaf_mono hWZ
  by_cases hV : Leaf V <;> by_cases hW : Leaf W <;> by_cases hZ : Leaf Z <;>
    simp_all [factor]

/-- Actual additive restriction map, with unique zero restriction to an empty open. -/
noncomputable def intRestriction (d : ℤ) {V W : StarOpen I} (_h : V.obj ≤ W.obj) :
    IntSections.{u,v} W →+ IntSections.{u,v} V := by
  classical
  exact
    { toFun := fun s => if hV : Live V then
        ⟨⟨factor d V W * s.val.down⟩, fun h => False.elim (h hV)⟩ else 0
      map_zero' := by
        by_cases hV : Live V <;> apply Subtype.ext <;> apply ULift.ext <;> simp [hV]
      map_add' := by
        intro a b
        by_cases hV : Live V <;> apply Subtype.ext <;> apply ULift.ext <;> simp [hV, mul_add] }

theorem intRestriction_val (d : ℤ) {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (hV : Live V) (s : IntSections.{u,v} W) :
    (intRestriction d h s).val.down = factor d V W * s.val.down := by
  simp [intRestriction, hV]

theorem intRestriction_self (d : ℤ) (V : StarOpen I) (s : IntSections.{u,v} V) :
    intRestriction d le_rfl s = s := by
  classical
  by_cases hV : Live V
  · apply Subtype.ext
    apply ULift.ext
    simp [intRestriction_val, hV, factor_self]
  · exact (supported_eq_zero hV _).trans (supported_eq_zero hV s).symm

theorem intRestriction_comp (d : ℤ) {V W Z : StarOpen I}
    (hVW : V.obj ≤ W.obj) (hWZ : W.obj ≤ Z.obj) (s : IntSections.{u,v} Z) :
    intRestriction d hVW (intRestriction d hWZ s) =
      intRestriction d (hVW.trans hWZ) s := by
  classical
  by_cases hV : Live V
  · apply Subtype.ext
    apply ULift.ext
    rw [intRestriction_val d hVW hV, intRestriction_val d hWZ (live_mono hVW hV),
      intRestriction_val d (hVW.trans hWZ) hV, factor_comp d hVW hWZ]
    exact (mul_assoc _ _ _).symm
  · exact (supported_eq_zero hV _).trans (supported_eq_zero hV _).symm

/-- Integer-valued normalized functor with the specified transition multiplier. -/
noncomputable def integerPresheaf (d : ℤ) : RawPresheaf.{u,v} (allOpenBasis (Option I)) where
  obj V := AddCommGrpCat.of (IntSections.{u,v} V.unop)
  map h := AddCommGrpCat.ofHom (intRestriction d h.unop.hom.le)
  map_id V := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact intRestriction_self d V.unop s
  map_comp h k := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact (intRestriction_comp d k.unop.hom.le h.unop.hom.le s).symm

theorem integer_restriction (d : ℤ) {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (s : IntSections.{u,v} W) :
    restriction (integerPresheaf d) h s = intRestriction d h s := rfl

theorem integer_normalized (d : ℤ) : IsNormalized (integerPresheaf (I := I) d) := by
  intro V hV
  have hn : ¬ Live V := by simp [Live, hV]
  exact ⟨fun a b => (supported_eq_zero hn a).trans (supported_eq_zero hn b).symm⟩

/-- All nonempty-target restrictions are injective for a nonzero transition. -/
theorem intRestriction_injective (d : ℤ) (hd : d ≠ 0) {V W : StarOpen I}
    (h : V.obj ≤ W.obj) (hV : Live V) :
    Function.Injective (intRestriction.{u,v} d h) := by
  classical
  intro a b hab
  apply Subtype.ext
  apply ULift.ext
  have he := congrArg (fun s : IntSections.{u,v} V => s.val.down) hab
  rw [intRestriction_val d h hV, intRestriction_val d h hV] at he
  have hf : factor d V W ≠ 0 := by
    unfold factor
    split <;> simp_all
  exact mul_left_cancel₀ hf he

/-- A nonempty covered open has a member with the same leaf-containment status. -/
theorem cover_anchor {ι : Type w} {V : StarOpen I} {A : ι → StarOpen I}
    (hA : FamilyCovers V A) (hV : Live V) :
    ∃ j, Live (A j) ∧ (Leaf (A j) ↔ Leaf V) := by
  classical
  by_cases hL : Leaf V
  · obtain ⟨i, hi⟩ := hL
    obtain ⟨j, hj⟩ := hA.2 (some i) hi
    exact ⟨j, live_of_mem hj, ⟨fun _ => ⟨i, hi⟩, fun _ => ⟨i, hj⟩⟩⟩
  · obtain ⟨j, hj⟩ := hA.2 none hV
    exact ⟨j, hj, ⟨leaf_mono (hA.1 j), fun h => False.elim (hL h)⟩⟩

/-- Literal unique gluing, for a family in any index universe. -/
theorem integer_familySheaf (d : ℤ) (hd : d ≠ 0) :
    FamilySheafCondition.{u,v,w} (integerPresheaf (I := I) d) := by
  classical
  intro ι V A hA s hs
  by_cases hV : Live V
  · obtain ⟨j, hj, hjL⟩ := cover_anchor hA hV
    let t : IntSections.{u,v} V :=
      ⟨(s j).val, fun hn => False.elim (hn hV)⟩
    have htj : intRestriction d (hA.1 j) t = s j := by
      apply Subtype.ext
      apply ULift.ext
      rw [intRestriction_val d (hA.1 j) hj]
      have hf : factor d (A j) V = 1 := by
        simp only [factor]
        exact ite_eq_right (fun h => h.2 (hjL.mpr h.1))
      simp [hf, t]
    have ht : IsAmalgamation (integerPresheaf d) hA s t := by
      intro k
      by_cases hk : Live (A k)
      · apply intRestriction_injective d hd (E_le hk) live_E
        change intRestriction d (E_le hk) (intRestriction d (hA.1 k) t) =
          intRestriction d (E_le hk) (s k)
        calc
          intRestriction d (E_le hk) (intRestriction d (hA.1 k) t) =
              intRestriction d (E_le hj) (intRestriction d (hA.1 j) t) := by
            rw [intRestriction_comp, intRestriction_comp]
          _ = intRestriction d (E_le hj) (s j) := congrArg _ htj
          _ = intRestriction d (E_le hk) (s k) :=
            hs j k (E I) (E_le hj) (E_le hk)
      · exact (supported_eq_zero hk _).trans (supported_eq_zero hk _).symm
    refine ⟨t, ht, ?_⟩
    intro y hy
    apply intRestriction_injective d hd (hA.1 j) hj
    exact (hy j).trans htj.symm
  · refine ⟨0, ?_, ?_⟩
    · intro k
      have hk : ¬ Live (A k) := fun hk => hV (live_mono (hA.1 k) hk)
      exact (supported_eq_zero hk _).trans (supported_eq_zero hk _).symm
    · intro y _
      exact supported_eq_zero hV y

theorem integer_sheafCondition (d : ℤ) (hd : d ≠ 0) :
    SheafCondition (integerPresheaf (I := I) d) :=
  FamilySheafCondition.sheafCondition _ (integer_familySheaf d hd)

/-- The actual source-category sheaf, with no size relation on u and v. -/
noncomputable def integerSheaf (d : ℤ) (hd : d ≠ 0) :
    BasisSheaf.{u,v} (allOpenBasis (Option I)) :=
  ⟨⟨integerPresheaf d, integer_normalized d⟩, integer_sheafCondition d hd⟩

/-- Integer sections, with identity restrictions on nonempty opens. -/
noncomputable def G : BasisSheaf.{u,v} (allOpenBasis (Option I)) :=
  integerSheaf 1 (by decide)

/-- Integer sections, with doubling precisely from a leaf-containing open to E. -/
noncomputable def F : BasisSheaf.{u,v} (allOpenBasis (Option I)) :=
  integerSheaf 2 (by decide)

abbrev PointSections (i : I) (V : StarOpen I) :=
  supported ModTwo.{v} (some i ∈ V.obj)

/-- Skyscraper restriction, identity when the distinguished support point remains present. -/
noncomputable def pointRestriction (i : I) {V W : StarOpen I} (_h : V.obj ≤ W.obj) :
    PointSections.{u,v} i W →+ PointSections.{u,v} i V := by
  classical
  exact
    { toFun := fun s => if hi : some i ∈ V.obj then
        ⟨s.val, fun hn => False.elim (hn hi)⟩ else 0
      map_zero' := by
        by_cases hi : some i ∈ V.obj <;> apply Subtype.ext <;> simp [hi]
      map_add' := by
        intro a b
        by_cases hi : some i ∈ V.obj <;> apply Subtype.ext <;> simp [hi] }

theorem pointRestriction_val (i : I) {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (hi : some i ∈ V.obj) (s : PointSections.{u,v} i W) :
    (pointRestriction i h s).val = s.val := by simp [pointRestriction, hi]

theorem pointRestriction_self (i : I) (V : StarOpen I) (s : PointSections.{u,v} i V) :
    pointRestriction i le_rfl s = s := by
  classical
  by_cases hi : some i ∈ V.obj
  · exact Subtype.ext (pointRestriction_val i le_rfl hi s)
  · exact (supported_eq_zero hi _).trans (supported_eq_zero hi _).symm

theorem pointRestriction_comp (i : I) {V W Z : StarOpen I}
    (hVW : V.obj ≤ W.obj) (hWZ : W.obj ≤ Z.obj) (s : PointSections.{u,v} i Z) :
    pointRestriction i hVW (pointRestriction i hWZ s) =
      pointRestriction i (hVW.trans hWZ) s := by
  classical
  by_cases hi : some i ∈ V.obj
  · apply Subtype.ext
    rw [pointRestriction_val i hVW hi, pointRestriction_val i hWZ (hVW hi),
      pointRestriction_val i (hVW.trans hWZ) hi]
  · exact (supported_eq_zero hi _).trans (supported_eq_zero hi _).symm

theorem pointRestriction_injective (i : I) {V W : StarOpen I}
    (h : V.obj ≤ W.obj) (hi : some i ∈ V.obj) :
    Function.Injective (pointRestriction.{u,v} i h) := by
  intro a b hab
  apply Subtype.ext
  have he := congrArg (fun s : PointSections.{u,v} i V => s.val) hab
  simpa only [pointRestriction_val i h hi] using he

/-- The actual ZMod 2 skyscraper functor on the published all-open basis. -/
noncomputable def pointPresheaf (i : I) :
    RawPresheaf.{u,v} (allOpenBasis (Option I)) where
  obj V := AddCommGrpCat.of (PointSections.{u,v} i V.unop)
  map h := AddCommGrpCat.ofHom (pointRestriction i h.unop.hom.le)
  map_id V := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact pointRestriction_self i V.unop s
  map_comp h k := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact (pointRestriction_comp i k.unop.hom.le h.unop.hom.le s).symm

theorem point_normalized (i : I) : IsNormalized (pointPresheaf.{u,v} i) := by
  intro V hV
  have hn : some i ∉ V.obj := by simp [hV]
  exact ⟨fun a b => (supported_eq_zero hn a).trans (supported_eq_zero hn b).symm⟩

theorem point_familySheaf (i : I) :
    FamilySheafCondition.{u,v,w} (pointPresheaf i) := by
  classical
  intro ι V A hA s hs
  by_cases hi : some i ∈ V.obj
  · obtain ⟨j, hj⟩ := hA.2 (some i) hi
    let t : PointSections.{u,v} i V :=
      ⟨(s j).val, fun hn => False.elim (hn hi)⟩
    have htj : pointRestriction i (hA.1 j) t = s j :=
      Subtype.ext (pointRestriction_val i (hA.1 j) hj t)
    have ht : IsAmalgamation (pointPresheaf i) hA s t := by
      intro k
      by_cases hk : some i ∈ (A k).obj
      · apply pointRestriction_injective i (U_le hk)
          ((mem_U i _).mpr (Or.inr rfl))
        change pointRestriction i (U_le hk) (pointRestriction i (hA.1 k) t) =
          pointRestriction i (U_le hk) (s k)
        calc
          pointRestriction i (U_le hk) (pointRestriction i (hA.1 k) t) =
              pointRestriction i (U_le hj) (pointRestriction i (hA.1 j) t) := by
            rw [pointRestriction_comp, pointRestriction_comp]
          _ = pointRestriction i (U_le hj) (s j) := congrArg _ htj
          _ = pointRestriction i (U_le hk) (s k) :=
            hs j k (U I i) (U_le hj) (U_le hk)
      · exact (supported_eq_zero hk _).trans (supported_eq_zero hk _).symm
    refine ⟨t, ht, ?_⟩
    intro y hy
    apply pointRestriction_injective i (hA.1 j) hj
    exact (hy j).trans htj.symm
  · refine ⟨0, ?_, ?_⟩
    · intro k
      have hk : some i ∉ (A k).obj := fun hk => hi (hA.1 k hk)
      exact (supported_eq_zero hk _).trans (supported_eq_zero hk _).symm
    · intro y _
      exact supported_eq_zero hi y

theorem point_sheafCondition (i : I) : SheafCondition (pointPresheaf.{u,v} i) :=
  FamilySheafCondition.sheafCondition _ (point_familySheaf i)

/-- The actual source-category skyscraper sheaf at some i. -/
noncomputable def Ti (i : I) : BasisSheaf.{u,v} (allOpenBasis (Option I)) :=
  ⟨⟨pointPresheaf i, point_normalized i⟩, point_sheafCondition i⟩

/-- Multiplication on a supported integer group, preserving its zero constraint. -/
def intMultiply (n : ℤ) (V : StarOpen I) : IntSections.{u,v} V →+ IntSections.{u,v} V where
  toFun s := ⟨⟨n * s.val.down⟩, by
    intro hV
    apply ULift.ext
    have hs := congrArg ULift.down (s.property hV)
    change n * s.val.down = 0
    simp_all⟩
  map_zero' := by
    apply Subtype.ext
    apply ULift.ext
    exact mul_zero n
  map_add' a b := by
    apply Subtype.ext
    apply ULift.ext
    exact mul_add n a.val.down b.val.down

theorem intMultiply_val (n : ℤ) (V : StarOpen I) (s : IntSections.{u,v} V) :
    (intMultiply n V s).val.down = n * s.val.down := rfl

noncomputable def weight (V : StarOpen I) : ℤ :=
  @ite ℤ (Leaf V) (Classical.propDecidable _) 2 1

theorem weight_factor {V W : StarOpen I} (h : V.obj ≤ W.obj) :
    weight V * factor 2 V W = weight W := by
  classical
  have hL := leaf_mono h
  by_cases hV : Leaf V <;> by_cases hW : Leaf W <;>
    simp_all [weight, factor]

noncomputable def fComponent (V : StarOpen I) :
    IntSections.{u,v} V →+ IntSections.{u,v} V := intMultiply (weight V) V

theorem fComponent_natural {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (s : IntSections.{u,v} W) :
    fComponent V (intRestriction 2 h s) = intRestriction 1 h (fComponent W s) := by
  classical
  by_cases hV : Live V
  · apply Subtype.ext
    apply ULift.ext
    change weight V * (intRestriction 2 h s).val.down =
      (intRestriction 1 h (fComponent W s)).val.down
    rw [intRestriction_val 2 h hV, intRestriction_val 1 h hV]
    change weight V * (factor 2 V W * s.val.down) =
      factor 1 V W * (weight W * s.val.down)
    rw [← mul_assoc, weight_factor h]
    simp [factor]
  · exact (supported_eq_zero hV _).trans (supported_eq_zero hV _).symm

/-- Identity on E and doubling on every leaf-containing open, as an actual transformation. -/
noncomputable def fNat :
    (F (I := I)).obj.obj ⟶ (G (I := I)).obj.obj where
  app V := AddCommGrpCat.ofHom (fComponent V.unop)
  naturality := by
    intro V W h
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact fComponent_natural h.unop.hom.le s

/-- The morphism in the actual published source sheaf category. -/
noncomputable def f : F (I := I) ⟶ G (I := I) :=
  (sheafHomEquiv _ _).symm fNat

/-- Integer reduction modulo two where some i is present, and the unique zero map elsewhere. -/
noncomputable def gComponent (i : I) (V : StarOpen I) :
    IntSections.{u,v} V →+ PointSections.{u,v} i V := by
  classical
  exact
    { toFun := fun s => if hi : some i ∈ V.obj then
        ⟨⟨(s.val.down : ZMod 2)⟩, fun hn => False.elim (hn hi)⟩ else 0
      map_zero' := by
        by_cases hi : some i ∈ V.obj <;> apply Subtype.ext <;>
          apply ULift.ext <;> simp [hi]
      map_add' := by
        intro a b
        by_cases hi : some i ∈ V.obj <;> apply Subtype.ext <;>
          apply ULift.ext <;> simp [hi, Int.cast_add] }

theorem gComponent_val (i : I) (V : StarOpen I) (hi : some i ∈ V.obj)
    (s : IntSections.{u,v} V) :
    (gComponent i V s).val.down = (s.val.down : ZMod 2) := by
  simp [gComponent, hi]

theorem gComponent_natural (i : I) {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (s : IntSections.{u,v} W) :
    gComponent i V (intRestriction 1 h s) = pointRestriction i h (gComponent i W s) := by
  classical
  by_cases hi : some i ∈ V.obj
  · apply Subtype.ext
    apply ULift.ext
    rw [gComponent_val i V hi, pointRestriction_val i h hi,
      gComponent_val i W (h hi), intRestriction_val 1 h (live_of_mem hi)]
    simp [factor]
  · exact (supported_eq_zero hi _).trans (supported_eq_zero hi _).symm

noncomputable def gNat (i : I) :
    (G (I := I)).obj.obj ⟶ (Ti i).obj.obj where
  app V := AddCommGrpCat.ofHom (gComponent i V.unop)
  naturality := by
    intro V W h
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact gComponent_natural i h.unop.hom.le s

/-- The actual source-category morphism to the skyscraper at some i. -/
noncomputable def gi (i : I) : G (I := I) ⟶ Ti i :=
  (sheafHomEquiv _ _).symm (gNat i)

theorem f_component_injective (V : StarOpen I) :
    Function.Injective ((sheafHomEquiv _ _ (f.{u,v} (I := I))).app (op V)) := by
  classical
  intro a b hab
  apply Subtype.ext
  apply ULift.ext
  have he := congrArg (fun s : IntSections.{u,v} V => s.val.down) hab
  change weight V * a.val.down = weight V * b.val.down at he
  have hw : weight V ≠ 0 := by
    unfold weight
    split <;> norm_num
  exact mul_left_cancel₀ hw he

/-- Every actual component of f followed by gi is the zero additive homomorphism. -/
theorem f_gi_component_zero (i : I) (V : StarOpen I) :
    (sheafHomEquiv _ _ (f ≫ gi i)).app (op V) =
      AddCommGrpCat.ofHom (0 : IntSections.{u,v} V →+ PointSections.{u,v} i V) := by
  classical
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change gComponent i V (fComponent V s) = 0
  by_cases hi : some i ∈ V.obj
  · apply Subtype.ext
    apply ULift.ext
    rw [gComponent_val i V hi]
    change ((weight V * s.val.down : ℤ) : ZMod 2) = 0
    have hL : Leaf V := ⟨i, hi⟩
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    simp [weight, hL, Int.cast_mul, htwo]
  · exact supported_eq_zero hi _

theorem empty_le (V : StarOpen I) : (empty I).obj ≤ V.obj := bot_le
theorem le_whole (V : StarOpen I) : V.obj ≤ (whole I).obj := le_top
theorem E_le_U (i : I) : (E I).obj ≤ (U I i).obj := E_le (live_U i)

/-- Concrete integer sections on any nonempty open, valid for both F and G. -/
def intSection (V : StarOpen I) (hV : Live V) (n : ℤ) : IntSections.{u,v} V :=
  (supportedEquiv Integers hV).symm ⟨n⟩

/-- Concrete mod-two sections on neighborhoods of some i. -/
def modSection (i : I) (V : StarOpen I) (hi : some i ∈ V.obj) (a : ZMod 2) :
    PointSections.{u,v} i V := (supportedEquiv ModTwo hi).symm ⟨a⟩

def FSectionsEquiv (V : StarOpen I) (hV : Live V) :
    Sections (F (I := I)).obj.obj V ≃+ Integers.{v} :=
  supportedEquiv _ hV

def GSectionsEquiv (V : StarOpen I) (hV : Live V) :
    Sections (G (I := I)).obj.obj V ≃+ Integers.{v} :=
  supportedEquiv _ hV

def TiSectionsEquiv (i : I) (V : StarOpen I) (hi : some i ∈ V.obj) :
    Sections (Ti i).obj.obj V ≃+ ModTwo.{v} :=
  supportedEquiv _ hi

@[simp] theorem intSection_val (V : StarOpen I) (hV : Live V) (n : ℤ) :
    (intSection.{u,v} V hV n).val.down = n := rfl

@[simp] theorem modSection_val (i : I) (V : StarOpen I) (hi : some i ∈ V.obj)
    (a : ZMod 2) : (modSection.{u,v} i V hi a).val.down = a := rfl

theorem intSection_injective (V : StarOpen I) (hV : Live V) :
    Function.Injective (intSection.{u,v} V hV) := by
  intro a b hab
  exact congrArg (fun s : IntSections.{u,v} V => s.val.down) hab

/-- Evaluated restriction under the concrete section identification. -/
theorem integer_restrict_section (d : ℤ) {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (hV : Live V) (hW : Live W) (n : ℤ) :
    restriction (integerPresheaf.{u,v} d) h (intSection W hW n) =
      intSection V hV (factor d V W * n) := by
  apply Subtype.ext
  apply ULift.ext
  exact intRestriction_val d h hV _

theorem G_restrict_section {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (hV : Live V) (hW : Live W) (n : ℤ) :
    restriction (G (I := I)).obj.obj h (intSection.{u,v} W hW n) =
      intSection V hV n := by
  change intRestriction 1 h (intSection W hW n) = intSection V hV n
  apply Subtype.ext
  apply ULift.ext
  rw [intRestriction_val 1 h hV]
  simp [factor]

theorem F_restrict_section {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (hV : Live V) (hW : Live W) (n : ℤ) :
    restriction (F (I := I)).obj.obj h (intSection.{u,v} W hW n) =
      intSection V hV (factor 2 V W * n) :=
  integer_restrict_section 2 h hV hW n

theorem F_restrict_to_E {W : StarOpen I} (hW : Leaf W) (n : ℤ) :
    restriction (F (I := I)).obj.obj (E_le (live_of_leaf hW))
        (intSection.{u,v} W (live_of_leaf hW) n) =
      intSection (E I) live_E (2 * n) := by
  have hf : factor 2 (E I) W = 2 := by simp [factor, hW]
  simpa only [hf] using
    F_restrict_section (E_le (live_of_leaf hW)) live_E (live_of_leaf hW) n

theorem F_restrict_without_jump {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (hV : Live V) (hW : Live W) (hn : ¬ (Leaf W ∧ ¬ Leaf V)) (n : ℤ) :
    restriction (F (I := I)).obj.obj h (intSection.{u,v} W hW n) =
      intSection V hV n := by
  have hf : factor 2 V W = 1 := by simp [factor, hn]
  simpa only [hf, one_mul] using F_restrict_section h hV hW n

theorem integer_restrict_empty (d : ℤ) {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (hV : ¬ Live V) (s : Sections (integerPresheaf.{u,v} d) W) :
    restriction (integerPresheaf d) h s = 0 := supported_eq_zero hV _

theorem Ti_restrict_section (i : I) {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (hiV : some i ∈ V.obj) (hiW : some i ∈ W.obj) (a : ZMod 2) :
    restriction (Ti i).obj.obj h (modSection.{u,v} i W hiW a) =
      modSection i V hiV a :=
  Subtype.ext (pointRestriction_val i h hiV _)

theorem Ti_restrict_absent (i : I) {V W : StarOpen I} (h : V.obj ≤ W.obj)
    (hi : some i ∉ V.obj) (s : Sections (Ti.{u,v} i).obj.obj W) :
    restriction (Ti i).obj.obj h s = 0 := supported_eq_zero hi _

@[simp] theorem f_app (V : StarOpen I) :
    (sheafHomEquiv _ _ (f.{u,v} (I := I))).app (op V) =
      AddCommGrpCat.ofHom (fComponent V) := rfl

@[simp] theorem gi_app (i : I) (V : StarOpen I) :
    (sheafHomEquiv _ _ (gi.{u,v} i)).app (op V) =
      AddCommGrpCat.ofHom (gComponent i V) := rfl

theorem f_app_val (V : StarOpen I) (s : Sections (F.{u,v} (I := I)).obj.obj V) :
    ((sheafHomEquiv _ _ f).app (op V) s).val.down = weight V * s.val.down := rfl

theorem gi_app_val (i : I) (V : StarOpen I) (hi : some i ∈ V.obj)
    (s : Sections (G.{u,v} (I := I)).obj.obj V) :
    ((sheafHomEquiv _ _ (gi i)).app (op V) s).val.down = (s.val.down : ZMod 2) :=
  gComponent_val i V hi s

theorem f_apply_E (n : ℤ) :
    (sheafHomEquiv _ _ (f.{u,v} (I := I))).app (op (E I))
        (intSection (E I) live_E n) = intSection (E I) live_E n := by
  apply Subtype.ext
  apply ULift.ext
  change weight (E I) * n = n
  simp [weight]

theorem f_apply_leaf (V : StarOpen I) (hV : Leaf V) (n : ℤ) :
    (sheafHomEquiv _ _ (f.{u,v} (I := I))).app (op V)
        (intSection V (live_of_leaf hV) n) =
      intSection V (live_of_leaf hV) (2 * n) := by
  apply Subtype.ext
  apply ULift.ext
  change weight V * n = 2 * n
  simp [weight, hV]

theorem gi_apply_section (i : I) (V : StarOpen I) (hi : some i ∈ V.obj) (n : ℤ) :
    (sheafHomEquiv _ _ (gi.{u,v} i)).app (op V)
        (intSection V (live_of_mem hi) n) = modSection i V hi (n : ZMod 2) := by
  apply Subtype.ext
  apply ULift.ext
  exact gComponent_val i V hi _

theorem gi_apply_absent (i : I) (V : StarOpen I) (hi : some i ∉ V.obj)
    (s : Sections (G.{u,v} (I := I)).obj.obj V) :
    (sheafHomEquiv _ _ (gi i)).app (op V) s = 0 := supported_eq_zero hi _

/-- The later detection argument can use the actual integer-one section. -/
theorem gi_U_one (i : I) :
    (sheafHomEquiv _ _ (gi.{u,v} i)).app (op (U I i))
        (intSection (U I i) (live_U i) 1) =
      modSection i (U I i) ((mem_U i _).mpr (Or.inr rfl)) 1 := by
  exact gi_apply_section i (U I i) ((mem_U i _).mpr (Or.inr rfl)) 1

theorem gi_U_one_ne_zero (i : I) :
    (sheafHomEquiv _ _ (gi.{u,v} i)).app (op (U I i))
        (intSection (U I i) (live_U i) 1) ≠ 0 := by
  intro h
  have he := congrArg (fun s : PointSections.{u,v} i (U I i) => s.val.down) h
  rw [gi_U_one] at he
  change (1 : ZMod 2) = 0 at he
  exact one_ne_zero he

end Langlands.Sheaf.Renard.StarDiagram
