import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Module.PUnit
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Hom

/-!
# The equivariant apartment quotient

For a group `H`, a subgroup `N ≤ H` acting on a type `A`, and a family of
subgroups `P x ≤ H` (`x : A`) with `n P_x n⁻¹ ≤ P_(n • x)` for `n ∈ N`, the
relation

  `(g, x) ∼ (h, y) ↔ ∃ n ∈ N, n • x = y ∧ g⁻¹ * h * n ∈ P x`

on `H × A` is an equivalence relation (relation (4.4.2) of Kaletha–Prasad,
Proposition 4.4.4, with an abstract subgroup family). Its quotient carries the
`H`-action by left multiplication on the first factor and the `N`-equivariant
canonical map `x ↦ [(1, x)]`. The stabilizer of `[(1, x)]` is `P x ⊔ N_x`,
not `P x` in general. An `N`-equivariant `f : A₁ → A₂` with `P₁ x ≤ P₂ (f x)`
for every `x` induces an `H`-equivariant map of quotients.

No building, reductive group, parahoric subgroup or topology is involved.
-/

namespace Langlands.Geometry.Building

universe uH uA uB uC

variable {H : Type uH} [Group H]

section Relation

variable (N : Subgroup H) {A : Type uA} [MulAction N A]

/-- The relation (4.4.2) on `H × A` for a subgroup family `P`:
`(g, x) ∼ (h, y)` iff some `n ∈ N` has `n • x = y` and `g⁻¹ * h * n ∈ P x`. -/
def apartmentRel (P : A → Subgroup H) (a b : H × A) : Prop :=
  ∃ n : N, n • a.2 = b.2 ∧ a.1⁻¹ * b.1 * (n : H) ∈ P a.2

theorem apartmentRel_iff (P : A → Subgroup H) (g h : H) (x y : A) :
    apartmentRel N P (g, x) (h, y) ↔ ∃ n : N, n • x = y ∧ g⁻¹ * h * (n : H) ∈ P x :=
  Iff.rfl

/-- `N`-conjugation covariance of a subgroup family: `n P_x n⁻¹ ≤ P_(n • x)` for `n ∈ N`. -/
def IsConjCovariant (P : A → Subgroup H) : Prop :=
  ∀ (n : N) (x : A) (p : H), p ∈ P x → (n : H) * p * (n : H)⁻¹ ∈ P (n • x)

variable {N}

/-- Covariance applied to `n⁻¹`: `n⁻¹ P_(n • x) n ≤ P_x`. -/
theorem IsConjCovariant.inv_conj_mem {P : A → Subgroup H} (hP : IsConjCovariant N P)
    (n : N) (x : A) {p : H} (hp : p ∈ P (n • x)) : (n : H)⁻¹ * p * (n : H) ∈ P x := by
  simpa using hP n⁻¹ (n • x) p hp

/-- Covariance is an equality: `n p n⁻¹ ∈ P_(n • x) ↔ p ∈ P_x`. -/
theorem IsConjCovariant.conj_mem_iff {P : A → Subgroup H} (hP : IsConjCovariant N P)
    (n : N) (x : A) (p : H) : (n : H) * p * (n : H)⁻¹ ∈ P (n • x) ↔ p ∈ P x := by
  refine ⟨fun h => ?_, hP n x p⟩
  simpa [mul_assoc] using hP.inv_conj_mem n x h

/-- Under covariance, the relation (4.4.2) is an equivalence relation. -/
theorem IsConjCovariant.apartmentRel_equivalence {P : A → Subgroup H}
    (hP : IsConjCovariant N P) : Equivalence (apartmentRel N P) where
  refl a := ⟨1, one_smul _ _, by simp⟩
  symm {a b} := by
    rintro ⟨n, hn, hmem⟩
    refine ⟨n⁻¹, by rw [← hn, inv_smul_smul], ?_⟩
    have h := hP n a.2 _ (inv_mem hmem)
    rw [hn] at h
    simpa [mul_assoc] using h
  trans {a b c} := by
    rintro ⟨n, hn, hmem⟩ ⟨m, hm, hmem'⟩
    refine ⟨m * n, by rw [mul_smul, hn, hm], ?_⟩
    rw [← hn] at hmem'
    have h := mul_mem hmem (hP.inv_conj_mem n a.2 hmem')
    simpa [mul_assoc] using h

variable (N) in
/-- Elements of `N ∩ P x` fix `x`: the condition for the canonical apartment map to be
injective. -/
def IsStabilizerCompatible (P : A → Subgroup H) : Prop :=
  ∀ (n : N) (x : A), (n : H) ∈ P x → n • x = x

end Relation

/-- An `N`-conjugation covariant family of subgroups of `H` indexed by an `N`-set `A`. -/
structure CovariantSubgroupFamily (N : Subgroup H) (A : Type uA) [MulAction N A] where
  /-- The subgroup `P x` attached to `x : A`. -/
  toFun : A → Subgroup H
  /-- `n P_x n⁻¹ ≤ P_(n • x)` for `n ∈ N`. -/
  isConjCovariant : IsConjCovariant N toFun

namespace CovariantSubgroupFamily

variable {N : Subgroup H} {A : Type uA} [MulAction N A]

attribute [coe] CovariantSubgroupFamily.toFun

instance : CoeFun (CovariantSubgroupFamily N A) (fun _ => A → Subgroup H) :=
  ⟨CovariantSubgroupFamily.toFun⟩

/-- The setoid of the relation (4.4.2). -/
def setoid (P : CovariantSubgroupFamily N A) : Setoid (H × A) :=
  ⟨apartmentRel N P, P.isConjCovariant.apartmentRel_equivalence⟩

end CovariantSubgroupFamily

/-- The quotient of `H × A` by the relation (4.4.2). -/
def ApartmentQuotient {N : Subgroup H} {A : Type uA} [MulAction N A]
    (P : CovariantSubgroupFamily N A) : Type (max uH uA) :=
  Quotient P.setoid

namespace ApartmentQuotient

variable {N : Subgroup H} {A : Type uA} [MulAction N A] (P : CovariantSubgroupFamily N A)

/-- The class of `(g, x)`. -/
def mk (a : H × A) : ApartmentQuotient P :=
  Quotient.mk P.setoid a

/-- The fibres of `mk` are the classes of the relation (4.4.2). -/
theorem mk_eq_mk_iff (g h : H) (x y : A) :
    mk P (g, x) = mk P (h, y) ↔ ∃ n : N, n • x = y ∧ g⁻¹ * h * (n : H) ∈ P x :=
  Quotient.eq

variable {P} in
@[elab_as_elim]
theorem ind {motive : ApartmentQuotient P → Prop} (h : ∀ g x, motive (mk P (g, x)))
    (q : ApartmentQuotient P) : motive q :=
  Quotient.ind (fun a => h a.1 a.2) q

instance : SMul H (ApartmentQuotient P) where
  smul h := Quotient.map' (fun a : H × A => (h * a.1, a.2)) (by
    rintro ⟨g, x⟩ ⟨g', y⟩ ⟨n, hn, hmem⟩
    exact ⟨n, hn, by simpa [mul_assoc] using hmem⟩)

theorem smul_mk (h g : H) (x : A) : h • mk P (g, x) = mk P (h * g, x) :=
  rfl

/-- Left multiplication on the first factor is an action of `H` on the quotient. -/
instance : MulAction H (ApartmentQuotient P) where
  one_smul q := by
    induction q using ind with
    | h g x => rw [smul_mk, one_mul]
  mul_smul h h' q := by
    induction q using ind with
    | h g x => rw [smul_mk, smul_mk, smul_mk, mul_assoc]

/-- The canonical apartment map `x ↦ [(1, x)]`. -/
def apartment (x : A) : ApartmentQuotient P :=
  mk P (1, x)

/-- Every class is `g` applied to a canonical apartment point. -/
theorem mk_eq_smul_apartment (g : H) (x : A) : mk P (g, x) = g • apartment P x := by
  rw [apartment, smul_mk, mul_one]

theorem exists_smul_apartment (q : ApartmentQuotient P) :
    ∃ (g : H) (x : A), g • apartment P x = q := by
  induction q using ind with
  | h g x => exact ⟨g, x, (mk_eq_smul_apartment P g x).symm⟩

/-- The canonical apartment map is `N`-equivariant. -/
theorem apartment_smul (n : N) (x : A) :
    apartment P (n • x) = (n : H) • apartment P x := by
  rw [apartment, apartment, smul_mk, mul_one, eq_comm, mk_eq_mk_iff]
  exact ⟨n, rfl, by simp⟩

/-- The canonical apartment map as an `N`-equivariant map, `N` acting on the quotient
through `H`. -/
def apartmentHom : A →[N] ApartmentQuotient P where
  toFun := apartment P
  map_smul' n x := apartment_smul P n x

@[simp] theorem apartmentHom_apply (x : A) : apartmentHom P x = apartment P x :=
  rfl

theorem apartment_eq_apartment_iff (x y : A) :
    apartment P x = apartment P y ↔ ∃ n : N, n • x = y ∧ (n : H) ∈ P x := by
  rw [apartment, apartment, mk_eq_mk_iff]
  simp

/-- The canonical apartment map is injective exactly when elements of `N ∩ P x` fix `x`. -/
theorem apartment_injective_iff :
    Function.Injective (apartment P) ↔ IsStabilizerCompatible N P := by
  constructor
  · intro hinj n x hn
    exact hinj ((apartment_eq_apartment_iff P x (n • x)).2 ⟨n, rfl, hn⟩).symm
  · intro hcomp x y hxy
    obtain ⟨n, hn, hmem⟩ := (apartment_eq_apartment_iff P x y).1 hxy
    rw [← hn, hcomp n x hmem]

theorem apartment_injective (hP : IsStabilizerCompatible N P) :
    Function.Injective (apartment P) :=
  (apartment_injective_iff P).2 hP

/-- Exact stabilizer of a canonical apartment point: `h` fixes `[(1, x)]` iff
`h = p * n` with `p ∈ P x` and `n ∈ N` fixing `x`. -/
theorem mem_stabilizer_apartment_iff (x : A) (h : H) :
    h ∈ MulAction.stabilizer H (apartment P x) ↔
      ∃ n : N, n • x = x ∧ ∃ p ∈ P x, h = p * (n : H) := by
  rw [MulAction.mem_stabilizer_iff, apartment, smul_mk, mul_one, eq_comm, mk_eq_mk_iff]
  constructor
  · rintro ⟨n, hn, hmem⟩
    refine ⟨n⁻¹, by rw [inv_smul_eq_iff, hn], 1⁻¹ * h * (n : H), hmem, by simp⟩
  · rintro ⟨n, hn, p, hp, rfl⟩
    refine ⟨n⁻¹, by rw [inv_smul_eq_iff, hn], by simpa using hp⟩

theorem le_stabilizer_apartment (x : A) : P x ≤ MulAction.stabilizer H (apartment P x) :=
  fun p hp => (mem_stabilizer_apartment_iff P x p).2 ⟨1, one_smul _ _, p, hp, by simp⟩

theorem map_stabilizer_le_stabilizer_apartment (x : A) :
    (MulAction.stabilizer N x).map N.subtype ≤ MulAction.stabilizer H (apartment P x) := by
  rintro _ ⟨n, hn, rfl⟩
  exact (mem_stabilizer_apartment_iff P x n).2
    ⟨n, MulAction.mem_stabilizer_iff.1 hn, 1, one_mem _, by simp⟩

/-- The stabilizer of `[(1, x)]` is generated by `P x` and the `N`-stabilizer of `x`. -/
theorem stabilizer_apartment_eq_sup (x : A) :
    MulAction.stabilizer H (apartment P x) =
      P x ⊔ (MulAction.stabilizer N x).map N.subtype := by
  refine le_antisymm ?_ (sup_le (le_stabilizer_apartment P x)
    (map_stabilizer_le_stabilizer_apartment P x))
  intro h hh
  obtain ⟨n, hn, p, hp, rfl⟩ := (mem_stabilizer_apartment_iff P x h).1 hh
  exact mul_mem (Subgroup.mem_sup_left hp)
    (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem N.subtype
      (MulAction.mem_stabilizer_iff.2 hn)))

/-- The stabilizer of `[(1, x)]` equals `P x` exactly when the `N`-stabilizer of `x`
lies in `P x`. -/
theorem stabilizer_apartment_eq_iff (x : A) :
    MulAction.stabilizer H (apartment P x) = P x ↔ ∀ n : N, n • x = x → (n : H) ∈ P x := by
  constructor
  · intro h n hn
    rw [← h]
    exact map_stabilizer_le_stabilizer_apartment P x
      (Subgroup.mem_map_of_mem N.subtype (MulAction.mem_stabilizer_iff.2 hn))
  · intro h
    refine le_antisymm (fun g hg => ?_) (le_stabilizer_apartment P x)
    obtain ⟨n, hn, p, hp, rfl⟩ := (mem_stabilizer_apartment_iff P x g).1 hg
    exact mul_mem hp (h n hn)

section Map

variable {A₁ : Type uA} {A₂ : Type uB} {A₃ : Type uC}
  [MulAction N A₁] [MulAction N A₂] [MulAction N A₃]
  (P₁ : CovariantSubgroupFamily N A₁) (P₂ : CovariantSubgroupFamily N A₂)
  (P₃ : CovariantSubgroupFamily N A₃)

/-- Representative independence: `(g, x) ∼ (h, y)` implies `(g, f x) ∼ (h, f y)`. -/
theorem apartmentRel_map (f : A₁ →[N] A₂) (hf : ∀ x, P₁ x ≤ P₂ (f x)) {a b : H × A₁}
    (hab : apartmentRel N P₁ a b) : apartmentRel N P₂ (a.1, f a.2) (b.1, f b.2) := by
  obtain ⟨n, hn, hmem⟩ := hab
  exact ⟨n, by rw [← hn, map_smul], hf a.2 hmem⟩

/-- The `H`-equivariant map `[(g, x)] ↦ [(g, f x)]` induced by an `N`-equivariant
`f : A₁ → A₂` with `P₁ x ≤ P₂ (f x)` for every `x`. -/
def map (f : A₁ →[N] A₂) (hf : ∀ x, P₁ x ≤ P₂ (f x)) :
    ApartmentQuotient P₁ →[H] ApartmentQuotient P₂ where
  toFun := Quotient.map' (fun a : H × A₁ => (a.1, f a.2))
    (fun _ _ hab => apartmentRel_map P₁ P₂ f hf hab)
  map_smul' h q := by
    induction q using ind with
    | h g x => rfl

variable {P₁ P₂ P₃}

theorem map_mk (f : A₁ →[N] A₂) (hf : ∀ x, P₁ x ≤ P₂ (f x)) (g : H) (x : A₁) :
    map P₁ P₂ f hf (mk P₁ (g, x)) = mk P₂ (g, f x) :=
  rfl

theorem map_apartment (f : A₁ →[N] A₂) (hf : ∀ x, P₁ x ≤ P₂ (f x)) (x : A₁) :
    map P₁ P₂ f hf (apartment P₁ x) = apartment P₂ (f x) :=
  rfl

theorem map_smul_eq (f : A₁ →[N] A₂) (hf : ∀ x, P₁ x ≤ P₂ (f x)) (h : H)
    (q : ApartmentQuotient P₁) : map P₁ P₂ f hf (h • q) = h • map P₁ P₂ f hf q :=
  (map P₁ P₂ f hf).map_smul h q

theorem map_id : map P₁ P₁ (MulActionHom.id N) (fun _ => le_rfl) = MulActionHom.id H := by
  ext q
  induction q using ind with
  | h g x => rfl

theorem map_comp (f : A₁ →[N] A₂) (hf : ∀ x, P₁ x ≤ P₂ (f x)) (f' : A₂ →[N] A₃)
    (hf' : ∀ y, P₂ y ≤ P₃ (f' y)) :
    map P₁ P₃ (f'.comp f) (fun x => (hf x).trans (hf' (f x))) =
      (map P₂ P₃ f' hf').comp (map P₁ P₂ f hf) := by
  ext q
  induction q using ind with
  | h g x => rfl

theorem map_surjective (f : A₁ →[N] A₂) (hf : ∀ x, P₁ x ≤ P₂ (f x))
    (hsurj : Function.Surjective f) : Function.Surjective (map P₁ P₂ f hf) := by
  intro q
  induction q using ind with
  | h g y =>
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨mk P₁ (g, x), rfl⟩

end Map

section Comparison

variable {P P' : CovariantSubgroupFamily N A}

/-- Same apartment, larger subgroup family: the comparison map is injective exactly when
`P' x` fixes `[(1, x)]` in the quotient for `P`, for every `x`. -/
theorem map_id_injective_iff (hPP' : ∀ x, P x ≤ P' x) :
    Function.Injective (map P P' (MulActionHom.id N) hPP') ↔
      ∀ x, P' x ≤ MulAction.stabilizer H (apartment P x) := by
  constructor
  · intro hinj x p hp
    rw [MulAction.mem_stabilizer_iff]
    apply hinj
    rw [map_smul_eq]
    exact MulAction.mem_stabilizer_iff.1 (le_stabilizer_apartment P' x hp)
  · intro hstab q q'
    induction q using ind with
    | h g x =>
      induction q' using ind with
      | h g' y =>
        intro hq
        obtain ⟨n, hn, hmem⟩ := (mk_eq_mk_iff P' g g' x y).1 hq
        have hfix := hstab x hmem
        rw [MulAction.mem_stabilizer_iff] at hfix
        have hmul : g' * (n : H) = g * (g⁻¹ * g' * (n : H)) := by simp [mul_assoc]
        rw [mk_eq_smul_apartment, mk_eq_smul_apartment, ← hn, apartment_smul, smul_smul, hmul,
          mul_smul, hfix]

theorem map_id_bijective_iff (hPP' : ∀ x, P x ≤ P' x) :
    Function.Bijective (map P P' (MulActionHom.id N) hPP') ↔
      ∀ x, P' x ≤ MulAction.stabilizer H (apartment P x) :=
  ⟨fun h => (map_id_injective_iff hPP').1 h.1,
    fun h => ⟨(map_id_injective_iff hPP').2 h,
      map_surjective _ hPP' Function.surjective_id⟩⟩

/-- Replacing `P` by a pointwise larger family `P'` gives an isomorphic quotient exactly when
`P' x ≤ P x ⊔ N_x` for every `x`. -/
theorem map_id_bijective_iff_le_sup (hPP' : ∀ x, P x ≤ P' x) :
    Function.Bijective (map P P' (MulActionHom.id N) hPP') ↔
      ∀ x, P' x ≤ P x ⊔ (MulAction.stabilizer N x).map N.subtype := by
  rw [map_id_bijective_iff]
  simp_rw [stabilizer_apartment_eq_sup]

end Comparison

end ApartmentQuotient

namespace ApartmentQuotient.Example

variable (H)

/-- The trivial subgroup family over a one-point apartment. -/
def botFamily (N : Subgroup H) : CovariantSubgroupFamily N Unit where
  toFun _ := ⊥
  isConjCovariant n x p hp := by
    simp only [Subgroup.mem_bot] at hp ⊢
    simp [hp]

/-- The full subgroup family over a one-point apartment. -/
def topFamily (N : Subgroup H) : CovariantSubgroupFamily N Unit where
  toFun _ := ⊤
  isConjCovariant _ _ _ _ := Subgroup.mem_top _

theorem botFamily_isStabilizerCompatible (N : Subgroup H) :
    IsStabilizerCompatible N (botFamily H N) :=
  fun _ _ _ => rfl

/-- With `N = H` acting trivially on a point and `P = ⊥`, the canonical point has
stabilizer `⊤`, although `P () = ⊥`. -/
theorem stabilizer_botFamily_top :
    MulAction.stabilizer H (apartment (botFamily H ⊤) ()) = ⊤ := by
  rw [eq_top_iff]
  intro h _
  rw [mem_stabilizer_apartment_iff]
  exact ⟨⟨h, Subgroup.mem_top h⟩, rfl, 1, one_mem _, by simp⟩

/-- For nontrivial `H`, the subgroup `P ()` is properly smaller than the stabilizer of the
canonical point, while the canonical apartment map is injective. -/
theorem botFamily_lt_stabilizer [Nontrivial H] :
    botFamily H ⊤ () < MulAction.stabilizer H (apartment (botFamily H ⊤) ()) := by
  rw [stabilizer_botFamily_top]
  exact bot_lt_top

/-- With `N = ⊥`, the comparison map from the `⊥` family to the `⊤` family over a point
covers the identity of the apartment but is not injective for nontrivial `H`. -/
theorem not_injective_map_botFamily_topFamily [Nontrivial H] :
    ¬ Function.Injective (map (botFamily H ⊥) (topFamily H ⊥) (MulActionHom.id (⊥ : Subgroup H))
      (fun _ => le_top)) := by
  intro hinj
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  have heq : mk (botFamily H ⊥) (h, ()) = mk (botFamily H ⊥) (1, ()) := by
    apply hinj
    exact (mk_eq_mk_iff (topFamily H ⊥) h 1 () ()).2 ⟨1, rfl, Subgroup.mem_top _⟩
  obtain ⟨n, -, hmem⟩ := (mk_eq_mk_iff _ h 1 () ()).1 heq
  have hn : (n : H) = 1 := Subgroup.mem_bot.1 n.2
  rw [hn] at hmem
  exact hh (by simpa using Subgroup.mem_bot.1 hmem)

/-- A concrete instance: for `H = Multiplicative (ZMod 2)`, `N = H` and `P = ⊥` over a point,
`P () = ⊥` is properly smaller than the stabilizer `⊤` of the canonical point. -/
theorem zmodTwo_botFamily_lt_stabilizer :
    botFamily (Multiplicative (ZMod 2)) ⊤ () <
      MulAction.stabilizer (Multiplicative (ZMod 2))
        (apartment (botFamily (Multiplicative (ZMod 2)) ⊤) ()) := by
  have : Nontrivial (ZMod 2) := ⟨⟨0, 1, by decide⟩⟩
  exact botFamily_lt_stabilizer _

end ApartmentQuotient.Example

end Langlands.Geometry.Building
