import Langlands.Cohomology.Tate.ZeroDefinitions
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-!
# Herbrand quotients of representations of finite cyclic groups

For a representation `A` of a finite cyclic group, `HasHerbrandQuotient A q` says that the
ordinary group cohomology groups `H¹(G, A)` and `H²(G, A)` are finite and
`|H²(G, A)| = q * |H¹(G, A)|`.

The proofs use the explicit subquotients `ker φ ⧸ range ψ` of a module with two
endomorphisms `φ, ψ` with `φ ∘ ψ = ψ ∘ φ = 0`, applied to `φ = ρ(g) - 1` and the norm `ψ = N`.
For a short exact sequence they form an exact hexagon, constructed by hand below.
-/

namespace Langlands.Cohomology.Herbrand

open CategoryTheory

universe u v w w'

section Subquotient

variable {R : Type u} [Ring R]
variable {X : Type v} [AddCommGroup X] [Module R X]
variable {Y : Type w} [AddCommGroup Y] [Module R Y]

/-- The subquotient `ker φ ⧸ (range ψ ∩ ker φ)` of a module with two endomorphisms. -/
abbrev Subquotient (φ ψ : X →ₗ[R] X) : Type v :=
  LinearMap.ker φ ⧸ (LinearMap.range ψ).submoduleOf (LinearMap.ker φ)

theorem mem_submoduleOf_iff {p q : Submodule R X} (x : q) :
    x ∈ p.submoduleOf q ↔ (x : X) ∈ p := Iff.rfl

/-- The class of an element of `ker φ` in the subquotient. -/
abbrev Subquotient.mk {φ ψ : X →ₗ[R] X} (x : X) (hx : φ x = 0) : Subquotient φ ψ :=
  Submodule.Quotient.mk ⟨x, hx⟩

theorem Subquotient.mk_eq_zero_iff {φ ψ : X →ₗ[R] X} (x : X) (hx : φ x = 0) :
    Subquotient.mk (ψ := ψ) x hx = 0 ↔ x ∈ LinearMap.range ψ :=
  Submodule.Quotient.mk_eq_zero _

theorem Subquotient.mk_eq_mk_iff {φ ψ : X →ₗ[R] X} (x y : X) (hx : φ x = 0) (hy : φ y = 0) :
    Subquotient.mk (ψ := ψ) x hx = Subquotient.mk y hy ↔ x - y ∈ LinearMap.range ψ :=
  Submodule.Quotient.eq _

theorem Subquotient.mk_surjective {φ ψ : X →ₗ[R] X} (z : Subquotient φ ψ) :
    ∃ (x : X) (hx : φ x = 0), Subquotient.mk x hx = z := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨x, hx, rfl⟩

/-- The map on subquotients induced by a linear map commuting with both endomorphisms. -/
def subquotientMap {φX ψX : X →ₗ[R] X} {φY ψY : Y →ₗ[R] Y} (f : X →ₗ[R] Y)
    (hφ : ∀ x, f (φX x) = φY (f x)) (hψ : ∀ x, f (ψX x) = ψY (f x)) :
    Subquotient φX ψX →ₗ[R] Subquotient φY ψY :=
  Submodule.mapQ _ _ (f.restrict fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← hφ, hx, map_zero])
    (by
      rintro x ⟨y, hy⟩
      exact ⟨f y, by rw [← hψ, hy]; rfl⟩)

@[simp]
theorem subquotientMap_mk {φX ψX : X →ₗ[R] X} {φY ψY : Y →ₗ[R] Y} (f : X →ₗ[R] Y)
    (hφ : ∀ x, f (φX x) = φY (f x)) (hψ : ∀ x, f (ψX x) = ψY (f x)) (x : X) (hx : φX x = 0) :
    subquotientMap f hφ hψ (Subquotient.mk (ψ := ψX) x hx) =
      Subquotient.mk (f x) (by rw [← hφ, hx, map_zero]) :=
  rfl

end Subquotient

section Exact

variable {R : Type u} [Ring R]

/-- The order of the source of a linear map is the product of the orders of its kernel and its
image (both sides are `0` when the source is infinite). -/
theorem card_eq_card_ker_mul_card_range {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Nat.card M = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f),
    Nat.card_congr f.quotKerEquivRange.toEquiv]

/-- The middle term of an exact sequence of modules with finite outer terms is finite. -/
theorem finite_of_exact {M N P : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : LinearMap.ker g = LinearMap.range f)
    [Finite M] [Finite P] : Finite N := by
  apply Nat.finite_of_card_ne_zero
  rw [card_eq_card_ker_mul_card_range g, h]
  have : Finite (LinearMap.range f) := Set.finite_range f |>.to_subtype
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

/-- For an exact hexagon of modules, the products of the orders of alternate terms agree. -/
theorem card_hexagon {X₀ X₁ X₂ X₃ X₄ X₅ : Type*}
    [AddCommGroup X₀] [Module R X₀] [AddCommGroup X₁] [Module R X₁]
    [AddCommGroup X₂] [Module R X₂] [AddCommGroup X₃] [Module R X₃]
    [AddCommGroup X₄] [Module R X₄] [AddCommGroup X₅] [Module R X₅]
    (f₀ : X₀ →ₗ[R] X₁) (f₁ : X₁ →ₗ[R] X₂) (f₂ : X₂ →ₗ[R] X₃) (f₃ : X₃ →ₗ[R] X₄)
    (f₄ : X₄ →ₗ[R] X₅) (f₅ : X₅ →ₗ[R] X₀)
    (h₀ : LinearMap.ker f₀ = LinearMap.range f₅) (h₁ : LinearMap.ker f₁ = LinearMap.range f₀)
    (h₂ : LinearMap.ker f₂ = LinearMap.range f₁) (h₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (h₄ : LinearMap.ker f₄ = LinearMap.range f₃) (h₅ : LinearMap.ker f₅ = LinearMap.range f₄) :
    Nat.card X₀ * Nat.card X₂ * Nat.card X₄ = Nat.card X₁ * Nat.card X₃ * Nat.card X₅ := by
  rw [card_eq_card_ker_mul_card_range f₀, card_eq_card_ker_mul_card_range f₁,
    card_eq_card_ker_mul_card_range f₂, card_eq_card_ker_mul_card_range f₃,
    card_eq_card_ker_mul_card_range f₄, card_eq_card_ker_mul_card_range f₅,
    h₀, h₁, h₂, h₃, h₄, h₅]
  ring

end Exact

section Connecting

variable {R : Type u} [Ring R]
variable {X : Type v} [AddCommGroup X] [Module R X]
variable {Y : Type w} [AddCommGroup Y] [Module R Y]
variable {Z : Type w'} [AddCommGroup Z] [Module R Z]

/-- A short exact sequence `0 → X → Y → Z → 0` of modules, each carrying two endomorphisms
`φ, ψ` with `φ ∘ ψ = ψ ∘ φ = 0`, such that both maps commute with `φ` and `ψ`. -/
structure CompatibleExact (φX ψX : X →ₗ[R] X) (φY ψY : Y →ₗ[R] Y) (φZ ψZ : Z →ₗ[R] Z)
    (i : X →ₗ[R] Y) (p : Y →ₗ[R] Z) : Prop where
  injective : Function.Injective i
  surjective : Function.Surjective p
  exact : LinearMap.ker p = LinearMap.range i
  iφ : ∀ x, i (φX x) = φY (i x)
  iψ : ∀ x, i (ψX x) = ψY (i x)
  pφ : ∀ y, p (φY y) = φZ (p y)
  pψ : ∀ y, p (ψY y) = ψZ (p y)
  φψX : ∀ x, φX (ψX x) = 0
  ψφX : ∀ x, ψX (φX x) = 0
  φψY : ∀ y, φY (ψY y) = 0
  ψφY : ∀ y, ψY (φY y) = 0
  φψZ : ∀ z, φZ (ψZ z) = 0
  ψφZ : ∀ z, ψZ (φZ z) = 0

variable {φX ψX : X →ₗ[R] X} {φY ψY : Y →ₗ[R] Y} {φZ ψZ : Z →ₗ[R] Z}
  {i : X →ₗ[R] Y} {p : Y →ₗ[R] Z}

namespace CompatibleExact

/-- The same data with the roles of `φ` and `ψ` exchanged. -/
theorem swap (S : CompatibleExact φX ψX φY ψY φZ ψZ i p) :
    CompatibleExact ψX φX ψY φY ψZ φZ i p :=
  ⟨S.injective, S.surjective, S.exact, S.iψ, S.iφ, S.pψ, S.pφ, S.ψφX, S.φψX, S.ψφY, S.φψY,
    S.ψφZ, S.φψZ⟩

variable (S : CompatibleExact φX ψX φY ψY φZ ψZ i p)
include S

theorem mem_range_i_iff (y : Y) : y ∈ LinearMap.range i ↔ p y = 0 := by
  rw [← S.exact, LinearMap.mem_ker]

/-- The chosen preimage, under `i`, of `φ` applied to a chosen lift of `z ∈ ker φ`. -/
noncomputable def connectingLift (z : Z) (hz : φZ z = 0) : X :=
  Classical.choose ((S.mem_range_i_iff (φY (Function.surjInv S.surjective z))).2
    (by rw [S.pφ, Function.surjInv_eq S.surjective, hz]))

theorem i_connectingLift (z : Z) (hz : φZ z = 0) :
    i (S.connectingLift z hz) = φY (Function.surjInv S.surjective z) :=
  Classical.choose_spec ((S.mem_range_i_iff (φY (Function.surjInv S.surjective z))).2
    (by rw [S.pφ, Function.surjInv_eq S.surjective, hz]))

theorem ψ_connectingLift (z : Z) (hz : φZ z = 0) : ψX (S.connectingLift z hz) = 0 :=
  S.injective (by rw [S.iψ, i_connectingLift, S.ψφY, map_zero])

/-- Any other choice of lift changes the connecting element by an element of `range φ`. -/
theorem connectingLift_sub_mem (z : Z) (hz : φZ z = 0) (y : Y) (x : X) (hy : p y = z)
    (hx : i x = φY y) : S.connectingLift z hz - x ∈ LinearMap.range φX := by
  obtain ⟨x', hx'⟩ := (S.mem_range_i_iff (Function.surjInv S.surjective z - y)).2
    (by rw [map_sub, Function.surjInv_eq S.surjective, hy, sub_self])
  refine ⟨x', S.injective ?_⟩
  rw [S.iφ, hx', map_sub, map_sub, i_connectingLift, hx]

/-- The connecting map `ker φ_Z → ker ψ_X ⧸ range φ_X`. -/
noncomputable def connectingKer : LinearMap.ker φZ →ₗ[R] Subquotient ψX φX where
  toFun z := Subquotient.mk (S.connectingLift z z.2) (S.ψ_connectingLift z z.2)
  map_add' z z' := by
    rw [← Submodule.Quotient.mk_add]
    refine (Submodule.Quotient.eq _).2 ?_
    show S.connectingLift (↑(z + z')) (z + z').2 -
      (S.connectingLift z z.2 + S.connectingLift z' z'.2) ∈ LinearMap.range φX
    apply S.connectingLift_sub_mem _ _ (Function.surjInv S.surjective z +
      Function.surjInv S.surjective z')
    · rw [map_add, Function.surjInv_eq S.surjective, Function.surjInv_eq S.surjective]; rfl
    · rw [map_add, map_add]
      exact congrArg₂ (· + ·) (S.i_connectingLift _ _) (S.i_connectingLift _ _)
  map_smul' r z := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.eq _).2 ?_
    show S.connectingLift (↑(r • z)) (r • z).2 - r • S.connectingLift z z.2 ∈
      LinearMap.range φX
    apply S.connectingLift_sub_mem _ _ (r • Function.surjInv S.surjective z)
    · rw [map_smul, Function.surjInv_eq S.surjective]; rfl
    · rw [map_smul, map_smul]
      exact congrArg (r • ·) (S.i_connectingLift _ _)

theorem connectingKer_apply_eq (z : Z) (hz : φZ z = 0) (y : Y) (x : X) (hy : p y = z)
    (hx : i x = φY y) (hψx : ψX x = 0) :
    S.connectingKer ⟨z, hz⟩ = Subquotient.mk x hψx :=
  (Subquotient.mk_eq_mk_iff _ _ _ _).2 (S.connectingLift_sub_mem z hz y x hy hx)

/-- The connecting map `ker φ_Z ⧸ range ψ_Z → ker ψ_X ⧸ range φ_X` of the hexagon. -/
noncomputable def connecting : Subquotient φZ ψZ →ₗ[R] Subquotient ψX φX :=
  Submodule.liftQ _ S.connectingKer (by
    rintro ⟨z, hz⟩ ⟨z', rfl⟩
    obtain ⟨y', rfl⟩ := S.surjective z'
    rw [LinearMap.mem_ker, S.connectingKer_apply_eq _ hz (ψY y') 0 (S.pψ y')
      (by rw [map_zero, S.φψY]) (map_zero _)]
    rfl)

theorem connecting_mk_eq (z : Z) (hz : φZ z = 0) (y : Y) (x : X) (hy : p y = z)
    (hx : i x = φY y) (hψx : ψX x = 0) :
    S.connecting (Subquotient.mk z hz) = Subquotient.mk x hψx :=
  S.connectingKer_apply_eq z hz y x hy hx hψx

/-- Exactness at the middle term of `X → Y → Z` on subquotients. -/
theorem ker_map_p_eq_range_map_i :
    LinearMap.ker (subquotientMap (φX := φY) (ψX := ψY) p S.pφ S.pψ) =
      LinearMap.range (subquotientMap (φY := φY) (ψY := ψY) i S.iφ S.iψ) := by
  apply le_antisymm
  · intro t ht
    obtain ⟨y, hy, rfl⟩ := Subquotient.mk_surjective t
    rw [LinearMap.mem_ker, subquotientMap_mk, Subquotient.mk_eq_zero_iff] at ht
    obtain ⟨z', hz'⟩ := ht
    obtain ⟨y', rfl⟩ := S.surjective z'
    obtain ⟨x, hx⟩ := (S.mem_range_i_iff (y - ψY y')).2 (by rw [map_sub, S.pψ, hz', sub_self])
    have hφx : φX x = 0 := S.injective (by rw [S.iφ, hx, map_sub, hy, S.φψY, sub_self, map_zero])
    refine ⟨Subquotient.mk x hφx, ?_⟩
    rw [subquotientMap_mk, Subquotient.mk_eq_mk_iff]
    exact ⟨-y', by rw [hx, map_neg, sub_sub_cancel_left]⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Subquotient.mk_surjective t
    rw [LinearMap.mem_ker, subquotientMap_mk, subquotientMap_mk, Subquotient.mk_eq_zero_iff]
    exact ⟨0, by rw [map_zero, eq_comm, ← LinearMap.mem_ker, S.exact]; exact ⟨x, rfl⟩⟩

/-- Exactness at `Z` (on the `φ`-subquotient) of the hexagon. -/
theorem ker_connecting_eq_range_map_p :
    LinearMap.ker S.connecting =
      LinearMap.range (subquotientMap (φX := φY) (ψX := ψY) p S.pφ S.pψ) := by
  apply le_antisymm
  · intro t ht
    obtain ⟨z, hz, rfl⟩ := Subquotient.mk_surjective t
    obtain ⟨y, rfl⟩ := S.surjective z
    obtain ⟨x, hx⟩ := (S.mem_range_i_iff (φY y)).2 (by rw [S.pφ, hz])
    have hψx : ψX x = 0 := S.injective (by rw [S.iψ, hx, S.ψφY, map_zero])
    rw [LinearMap.mem_ker, S.connecting_mk_eq _ hz y x rfl hx hψx,
      Subquotient.mk_eq_zero_iff] at ht
    obtain ⟨x', rfl⟩ := ht
    have hφ : φY (y - i x') = 0 := by rw [map_sub, ← S.iφ, hx, sub_self]
    refine ⟨Subquotient.mk (y - i x') hφ, ?_⟩
    rw [subquotientMap_mk, Subquotient.mk_eq_mk_iff]
    have hpi : p (i x') = 0 := by rw [← LinearMap.mem_ker, S.exact]; exact ⟨x', rfl⟩
    exact ⟨0, by rw [map_zero, map_sub, hpi, sub_zero, sub_self]⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Subquotient.mk_surjective t
    rw [LinearMap.mem_ker, subquotientMap_mk, S.connecting_mk_eq _ _ y 0 rfl
      (by rw [map_zero, hy]) (map_zero _)]
    rfl

/-- Exactness at `X` (on the `ψ`-subquotient) of the hexagon. -/
theorem ker_map_i_eq_range_connecting :
    LinearMap.ker (subquotientMap (φY := ψY) (ψY := φY) i S.iψ S.iφ) =
      LinearMap.range S.connecting := by
  apply le_antisymm
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Subquotient.mk_surjective t
    rw [LinearMap.mem_ker, subquotientMap_mk, Subquotient.mk_eq_zero_iff] at ht
    obtain ⟨y, hy⟩ := ht
    have hz : φZ (p y) = 0 := by
      rw [← S.pφ, hy, ← LinearMap.mem_ker, S.exact]; exact ⟨x, rfl⟩
    exact ⟨Subquotient.mk (p y) hz, S.connecting_mk_eq _ hz y x rfl hy.symm hx⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Subquotient.mk_surjective t
    obtain ⟨y, rfl⟩ := S.surjective z
    obtain ⟨x, hx⟩ := (S.mem_range_i_iff (φY y)).2 (by rw [S.pφ, hz])
    have hψx : ψX x = 0 := S.injective (by rw [S.iψ, hx, S.ψφY, map_zero])
    rw [S.connecting_mk_eq _ hz y x rfl hx hψx, LinearMap.mem_ker, subquotientMap_mk,
      Subquotient.mk_eq_zero_iff]
    exact ⟨y, hx.symm⟩

/-- The exact hexagon relation between the orders of the six subquotients. -/
theorem card_subquotients :
    Nat.card (Subquotient φX ψX) * Nat.card (Subquotient φZ ψZ) * Nat.card (Subquotient ψY φY) =
      Nat.card (Subquotient φY ψY) * Nat.card (Subquotient ψX φX) *
        Nat.card (Subquotient ψZ φZ) :=
  card_hexagon (subquotientMap i S.iφ S.iψ) (subquotientMap p S.pφ S.pψ) S.connecting
    (subquotientMap i S.iψ S.iφ) (subquotientMap p S.pψ S.pφ) S.swap.connecting
    S.swap.ker_map_i_eq_range_connecting S.ker_map_p_eq_range_map_i
    S.ker_connecting_eq_range_map_p S.ker_map_i_eq_range_connecting
    S.swap.ker_map_p_eq_range_map_i S.swap.ker_connecting_eq_range_map_p

end CompatibleExact

end Connecting

section Ratio

variable {R : Type u} [Ring R]
variable {X : Type v} [AddCommGroup X] [Module R X]
variable {Y : Type w} [AddCommGroup Y] [Module R Y]
variable {Z : Type w'} [AddCommGroup Z] [Module R Z]

/-- The subquotients `ker φ ⧸ range ψ` and `ker ψ ⧸ range φ` are finite and the order of the
first is `q` times the order of the second. -/
def HasSubquotientRatio (φ ψ : X →ₗ[R] X) (q : ℚ) : Prop :=
  Finite (Subquotient φ ψ) ∧ Finite (Subquotient ψ φ) ∧
    (Nat.card (Subquotient φ ψ) : ℚ) = q * Nat.card (Subquotient ψ φ)

/-- A module isomorphic to the cokernel of `range ψ → ker φ` has the order of the subquotient. -/
theorem nonempty_linearEquiv_subquotient {φ ψ : X →ₗ[R] X} {M : Type*} [AddCommGroup M]
    [Module R M] (π : LinearMap.ker φ →ₗ[R] M) (hπ : Function.Surjective π)
    (h : ∀ x, π x = 0 ↔ (x : X) ∈ LinearMap.range ψ) :
    Nonempty (M ≃ₗ[R] Subquotient φ ψ) := by
  refine ⟨(π.quotKerEquivOfSurjective hπ).symm.trans (Submodule.quotEquivOfEq _ _ ?_)⟩
  ext x
  rw [LinearMap.mem_ker, h]
  rfl

theorem card_subquotient_pos {φ ψ : X →ₗ[R] X} [Finite (Subquotient φ ψ)] :
    (0 : ℚ) < Nat.card (Subquotient φ ψ) :=
  Nat.cast_pos.2 Nat.card_pos

theorem HasSubquotientRatio.pos {φ ψ : X →ₗ[R] X} {q : ℚ} (h : HasSubquotientRatio φ ψ q) :
    0 < q := by
  obtain ⟨h₁, h₂, h⟩ := h
  have hpos := card_subquotient_pos (φ := φ) (ψ := ψ)
  have hpos' := card_subquotient_pos (φ := ψ) (ψ := φ)
  rw [h] at hpos
  exact pos_of_mul_pos_left hpos hpos'.le

theorem HasSubquotientRatio.eq {φ ψ : X →ₗ[R] X} {q q' : ℚ} (h : HasSubquotientRatio φ ψ q)
    (h' : HasSubquotientRatio φ ψ q') : q = q' := by
  have := h.2.1
  exact mul_right_cancel₀ card_subquotient_pos.ne' (h.2.2.symm.trans h'.2.2)

/-- If `φ ∘ ψ = 0`, the order of `ker φ` is the order of the subquotient times that of
`range ψ`. -/
theorem card_subquotient_mul_card_range {φ ψ : X →ₗ[R] X} (hφψ : ∀ x, φ (ψ x) = 0) :
    Nat.card (Subquotient φ ψ) * Nat.card (LinearMap.range ψ) =
      Nat.card (LinearMap.ker φ) := by
  have hle : LinearMap.range ψ ≤ LinearMap.ker φ := by
    rintro _ ⟨x, rfl⟩
    exact hφψ x
  rw [Submodule.card_eq_card_quotient_mul_card ((LinearMap.range ψ).submoduleOf (LinearMap.ker φ)),
    Nat.card_congr (Submodule.submoduleOfEquivOfLe hle).toEquiv, mul_comm]

/-- On a finite module the two subquotients have the same order. -/
theorem card_subquotient_eq_of_finite [Finite X] {φ ψ : X →ₗ[R] X} (hφψ : ∀ x, φ (ψ x) = 0)
    (hψφ : ∀ x, ψ (φ x) = 0) :
    Nat.card (Subquotient φ ψ) = Nat.card (Subquotient ψ φ) := by
  have h₁ := card_subquotient_mul_card_range hφψ
  have h₂ := card_subquotient_mul_card_range hψφ
  have h₃ := card_eq_card_ker_mul_card_range φ
  have h₄ := card_eq_card_ker_mul_card_range ψ
  have hφ : 0 < Nat.card (LinearMap.range φ) := Nat.card_pos
  have hψ : 0 < Nat.card (LinearMap.range ψ) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hφ hψ)
  calc Nat.card (Subquotient φ ψ) * (Nat.card (LinearMap.range φ) * Nat.card (LinearMap.range ψ))
      = Nat.card (Subquotient φ ψ) * Nat.card (LinearMap.range ψ) *
          Nat.card (LinearMap.range φ) := by ring
    _ = Nat.card X := by rw [h₁, h₃]
    _ = Nat.card (Subquotient ψ φ) * Nat.card (LinearMap.range φ) *
          Nat.card (LinearMap.range ψ) := by rw [h₂, h₄]
    _ = Nat.card (Subquotient ψ φ) *
          (Nat.card (LinearMap.range φ) * Nat.card (LinearMap.range ψ)) := by ring

/-- A finite module has subquotient ratio `1`. -/
theorem hasSubquotientRatio_of_finite [Finite X] {φ ψ : X →ₗ[R] X} (hφψ : ∀ x, φ (ψ x) = 0)
    (hψφ : ∀ x, ψ (φ x) = 0) : HasSubquotientRatio φ ψ 1 :=
  ⟨Finite.of_surjective _ (Submodule.mkQ_surjective _),
    Finite.of_surjective _ (Submodule.mkQ_surjective _),
    by rw [one_mul, card_subquotient_eq_of_finite hφψ hψφ]⟩

namespace CompatibleExact

variable {φX ψX : X →ₗ[R] X} {φY ψY : Y →ₗ[R] Y} {φZ ψZ : Z →ₗ[R] Z}
  {i : X →ₗ[R] Y} {p : Y →ₗ[R] Z}
variable (S : CompatibleExact φX ψX φY ψY φZ ψZ i p)
include S

/-- The hexagon relation, cast to `ℚ`. -/
theorem card_subquotients_rat :
    (Nat.card (Subquotient φX ψX) : ℚ) * Nat.card (Subquotient φZ ψZ) *
        Nat.card (Subquotient ψY φY) =
      Nat.card (Subquotient φY ψY) * Nat.card (Subquotient ψX φX) *
        Nat.card (Subquotient ψZ φZ) := by
  exact_mod_cast S.card_subquotients

/-- Multiplicativity: the ratio of the middle term is the product of the outer ratios. -/
theorem hasSubquotientRatio_mid {qX qZ : ℚ} (hX : HasSubquotientRatio φX ψX qX)
    (hZ : HasSubquotientRatio φZ ψZ qZ) : HasSubquotientRatio φY ψY (qX * qZ) := by
  obtain ⟨hX₁, hX₂, hX⟩ := hX
  obtain ⟨hZ₁, hZ₂, hZ⟩ := hZ
  have hY₁ : Finite (Subquotient φY ψY) :=
    finite_of_exact _ _ S.ker_map_p_eq_range_map_i
  have hY₂ : Finite (Subquotient ψY φY) :=
    finite_of_exact _ _ S.swap.ker_map_p_eq_range_map_i
  refine ⟨hY₁, hY₂, ?_⟩
  have key := S.card_subquotients_rat
  rw [hX, hZ] at key
  apply mul_right_cancel₀ (mul_ne_zero (card_subquotient_pos (φ := ψX) (ψ := φX)).ne'
    (card_subquotient_pos (φ := ψZ) (ψ := φZ)).ne')
  linear_combination -key

/-- Two out of three: the ratio of the left term. -/
theorem hasSubquotientRatio_left {qY qZ : ℚ} (hY : HasSubquotientRatio φY ψY qY)
    (hZ : HasSubquotientRatio φZ ψZ qZ) : HasSubquotientRatio φX ψX (qY / qZ) := by
  have hqZ := hZ.pos.ne'
  obtain ⟨hY₁, hY₂, hY⟩ := hY
  obtain ⟨hZ₁, hZ₂, hZ⟩ := hZ
  have hX₁ : Finite (Subquotient φX ψX) :=
    finite_of_exact _ _ S.swap.ker_map_i_eq_range_connecting
  have hX₂ : Finite (Subquotient ψX φX) :=
    finite_of_exact _ _ S.ker_map_i_eq_range_connecting
  refine ⟨hX₁, hX₂, ?_⟩
  have key := S.card_subquotients_rat
  rw [hY, hZ] at key
  rw [div_mul_eq_mul_div, eq_div_iff hqZ]
  apply mul_right_cancel₀ (mul_ne_zero (card_subquotient_pos (φ := ψZ) (ψ := φZ)).ne'
    (card_subquotient_pos (φ := ψY) (ψ := φY)).ne')
  linear_combination key

/-- Two out of three: the ratio of the right term. -/
theorem hasSubquotientRatio_right {qX qY : ℚ} (hX : HasSubquotientRatio φX ψX qX)
    (hY : HasSubquotientRatio φY ψY qY) : HasSubquotientRatio φZ ψZ (qY / qX) := by
  have hqX := hX.pos.ne'
  obtain ⟨hX₁, hX₂, hX⟩ := hX
  obtain ⟨hY₁, hY₂, hY⟩ := hY
  have hZ₁ : Finite (Subquotient φZ ψZ) :=
    finite_of_exact _ _ S.ker_connecting_eq_range_map_p
  have hZ₂ : Finite (Subquotient ψZ φZ) :=
    finite_of_exact _ _ S.swap.ker_connecting_eq_range_map_p
  refine ⟨hZ₁, hZ₂, ?_⟩
  have key := S.card_subquotients_rat
  rw [hX, hY] at key
  rw [div_mul_eq_mul_div, eq_div_iff hqX]
  apply mul_right_cancel₀ (mul_ne_zero (card_subquotient_pos (φ := ψX) (ψ := φX)).ne'
    (card_subquotient_pos (φ := ψY) (ψ := φY)).ne')
  linear_combination key

/-- With a finite right term, the left and middle terms have the same ratio. -/
theorem hasSubquotientRatio_iff_of_finite_right [Finite Z] {q : ℚ} :
    HasSubquotientRatio φX ψX q ↔ HasSubquotientRatio φY ψY q := by
  have hZ := hasSubquotientRatio_of_finite S.φψZ S.ψφZ
  constructor
  · intro h
    simpa using S.hasSubquotientRatio_mid h hZ
  · intro h
    simpa using S.hasSubquotientRatio_left h hZ

/-- With a finite left term, the middle and right terms have the same ratio. -/
theorem hasSubquotientRatio_iff_of_finite_left [Finite X] {q : ℚ} :
    HasSubquotientRatio φY ψY q ↔ HasSubquotientRatio φZ ψZ q := by
  have hX := hasSubquotientRatio_of_finite S.φψX S.ψφX
  constructor
  · intro h
    simpa using S.hasSubquotientRatio_right hX h
  · intro h
    simpa using S.hasSubquotientRatio_mid hX h

end CompatibleExact

/-- The endomorphism of `Y ⧸ range i` induced by `f` when `range i` is `f`-stable. -/
abbrev rangeMapQ (i : X →ₗ[R] Y) (f : Y →ₗ[R] Y) (hf : ∀ x, f (i x) ∈ LinearMap.range i) :
    (Y ⧸ LinearMap.range i) →ₗ[R] (Y ⧸ LinearMap.range i) :=
  (LinearMap.range i).mapQ (LinearMap.range i) f (by
    rintro _ ⟨x, rfl⟩
    exact hf x)

/-- An injective compatible map and its cokernel form a compatible short exact sequence. -/
theorem compatibleExact_mkQ {φX ψX : X →ₗ[R] X} {φY ψY : Y →ₗ[R] Y} (i : X →ₗ[R] Y)
    (hi : Function.Injective i) (iφ : ∀ x, i (φX x) = φY (i x)) (iψ : ∀ x, i (ψX x) = ψY (i x))
    (φψX : ∀ x, φX (ψX x) = 0) (ψφX : ∀ x, ψX (φX x) = 0) (φψY : ∀ y, φY (ψY y) = 0)
    (ψφY : ∀ y, ψY (φY y) = 0) :
    CompatibleExact φX ψX φY ψY (rangeMapQ i φY fun x => ⟨φX x, iφ x⟩)
      (rangeMapQ i ψY fun x => ⟨ψX x, iψ x⟩) i (LinearMap.range i).mkQ where
  injective := hi
  surjective := (LinearMap.range i).mkQ_surjective
  exact := (LinearMap.range i).ker_mkQ
  iφ := iφ
  iψ := iψ
  pφ _ := rfl
  pψ _ := rfl
  φψX := φψX
  ψφX := ψφX
  φψY := φψY
  ψφY := ψφY
  φψZ z := by
    obtain ⟨y, rfl⟩ := (LinearMap.range i).mkQ_surjective z
    change Submodule.Quotient.mk (φY (ψY y)) = 0
    rw [φψY, Submodule.Quotient.mk_zero]
  ψφZ z := by
    obtain ⟨y, rfl⟩ := (LinearMap.range i).mkQ_surjective z
    change Submodule.Quotient.mk (ψY (φY y)) = 0
    rw [ψφY, Submodule.Quotient.mk_zero]

/-- A compatible injection with finite cokernel preserves the subquotient ratio. -/
theorem hasSubquotientRatio_iff_of_injective {φX ψX : X →ₗ[R] X} {φY ψY : Y →ₗ[R] Y}
    (i : X →ₗ[R] Y) (hi : Function.Injective i) (iφ : ∀ x, i (φX x) = φY (i x))
    (iψ : ∀ x, i (ψX x) = ψY (i x)) (φψX : ∀ x, φX (ψX x) = 0) (ψφX : ∀ x, ψX (φX x) = 0)
    (φψY : ∀ y, φY (ψY y) = 0) (ψφY : ∀ y, ψY (φY y) = 0) [Finite (Y ⧸ LinearMap.range i)]
    {q : ℚ} : HasSubquotientRatio φX ψX q ↔ HasSubquotientRatio φY ψY q :=
  (compatibleExact_mkQ i hi iφ iψ φψX ψφX φψY ψφY).hasSubquotientRatio_iff_of_finite_right

/-- A surjective compatible map and its kernel form a compatible short exact sequence. -/
theorem compatibleExact_subtype {φY ψY : Y →ₗ[R] Y} {φZ ψZ : Z →ₗ[R] Z} (p : Y →ₗ[R] Z)
    (hp : Function.Surjective p) (pφ : ∀ y, p (φY y) = φZ (p y))
    (pψ : ∀ y, p (ψY y) = ψZ (p y)) (φψY : ∀ y, φY (ψY y) = 0) (ψφY : ∀ y, ψY (φY y) = 0)
    (φψZ : ∀ z, φZ (ψZ z) = 0) (ψφZ : ∀ z, ψZ (φZ z) = 0) :
    CompatibleExact
      (φY.restrict (p := LinearMap.ker p) (q := LinearMap.ker p) fun y hy => by
        rw [LinearMap.mem_ker] at hy ⊢; rw [pφ, hy, map_zero])
      (ψY.restrict (p := LinearMap.ker p) (q := LinearMap.ker p) fun y hy => by
        rw [LinearMap.mem_ker] at hy ⊢; rw [pψ, hy, map_zero])
      φY ψY φZ ψZ (LinearMap.ker p).subtype p where
  injective := Subtype.val_injective
  surjective := hp
  exact := (Submodule.range_subtype _).symm
  iφ _ := rfl
  iψ _ := rfl
  pφ := pφ
  pψ := pψ
  φψX x := Subtype.ext (φψY x)
  ψφX x := Subtype.ext (ψφY x)
  φψY := φψY
  ψφY := ψφY
  φψZ := φψZ
  ψφZ := ψφZ

/-- A compatible surjection with finite kernel preserves the subquotient ratio. -/
theorem hasSubquotientRatio_iff_of_surjective {φY ψY : Y →ₗ[R] Y} {φZ ψZ : Z →ₗ[R] Z}
    (p : Y →ₗ[R] Z) (hp : Function.Surjective p) (pφ : ∀ y, p (φY y) = φZ (p y))
    (pψ : ∀ y, p (ψY y) = ψZ (p y)) (φψY : ∀ y, φY (ψY y) = 0) (ψφY : ∀ y, ψY (φY y) = 0)
    (φψZ : ∀ z, φZ (ψZ z) = 0) (ψφZ : ∀ z, ψZ (φZ z) = 0) [Finite (LinearMap.ker p)]
    {q : ℚ} : HasSubquotientRatio φY ψY q ↔ HasSubquotientRatio φZ ψZ q :=
  (compatibleExact_subtype p hp pφ pψ φψY ψφY φψZ ψφZ).hasSubquotientRatio_iff_of_finite_left

end Ratio

section Representation

variable {k G V W : Type*} [CommRing k] [Group G] [Fintype G]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem sub_one_norm_apply (ρ : Representation k G V) (g : G) (x : V) :
    (ρ g - 1) (ρ.norm x) = 0 := by
  rw [LinearMap.sub_apply, Representation.self_norm_apply, Module.End.one_apply, sub_self]

theorem norm_sub_one_apply (ρ : Representation k G V) (g : G) (x : V) :
    ρ.norm ((ρ g - 1) x) = 0 := by
  rw [LinearMap.sub_apply, map_sub, Representation.norm_self_apply, Module.End.one_apply,
    sub_self]

omit [Fintype G] in
theorem intertwiningMap_sub_one_apply {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (g : G) (x : V) :
    f.toLinearMap ((ρ g - 1) x) = (σ g - 1) (f.toLinearMap x) := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [← LinearMap.comp_apply, f.isIntertwining', LinearMap.comp_apply]

theorem intertwiningMap_norm_apply {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (x : V) :
    f.toLinearMap (ρ.norm x) = σ.norm (f.toLinearMap x) := by
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← LinearMap.comp_apply, f.isIntertwining', LinearMap.comp_apply]

end Representation

section Definition

variable {k G : Type u} [CommRing k] [Group G]

/-- `A` has Herbrand quotient `q`: the cohomology groups `H¹(G, A)` and `H²(G, A)` are finite
and `|H²(G, A)| = q * |H¹(G, A)|`. For a finite cyclic group `G`, where `H²(G, A) ≅ Ĥ⁰(G, A)`,
this says that the Herbrand quotient `h(A) = |Ĥ⁰(G, A)| / |H¹(G, A)|` is defined and equals
`q`. -/
def HasHerbrandQuotient (A : Rep k G) (q : ℚ) : Prop :=
  Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
    (Nat.card (groupCohomology A 2) : ℚ) = q * Nat.card (groupCohomology A 1)

end Definition

section Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- A natural-number Herbrand quotient, in the form `|H²| = n * |H¹|` of natural numbers. -/
theorem hasHerbrandQuotient_natCast_iff (A : Rep k G) (n : ℕ) :
    HasHerbrandQuotient A n ↔ Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 2) = n * Nat.card (groupCohomology A 1) := by
  unfold HasHerbrandQuotient
  norm_cast

theorem HasHerbrandQuotient.pos {A : Rep k G} {q : ℚ} (h : HasHerbrandQuotient A q) : 0 < q := by
  obtain ⟨h₁, h₂, h⟩ := h
  have hpos : (0 : ℚ) < Nat.card (groupCohomology A 2) := Nat.cast_pos.2 Nat.card_pos
  have hpos' : (0 : ℚ) < Nat.card (groupCohomology A 1) := Nat.cast_pos.2 Nat.card_pos
  rw [h] at hpos
  exact pos_of_mul_pos_left hpos hpos'.le

/-- The Herbrand quotient is unique. -/
theorem HasHerbrandQuotient.eq {A : Rep k G} {q q' : ℚ} (h : HasHerbrandQuotient A q)
    (h' : HasHerbrandQuotient A q') : q = q' := by
  have := h.1
  exact mul_right_cancel₀ (Nat.cast_pos.2 Nat.card_pos).ne' (h.2.2.symm.trans h'.2.2)

/-- Isomorphic cohomology groups give the same Herbrand quotient. -/
theorem HasHerbrandQuotient.of_linearEquiv {A B : Rep k G}
    (e₁ : groupCohomology A 1 ≃ₗ[k] groupCohomology B 1)
    (e₂ : groupCohomology A 2 ≃ₗ[k] groupCohomology B 2) {q : ℚ}
    (h : HasHerbrandQuotient A q) : HasHerbrandQuotient B q := by
  obtain ⟨h₁, h₂, h⟩ := h
  refine ⟨e₁.toEquiv.finite_iff.1 h₁, e₂.toEquiv.finite_iff.1 h₂, ?_⟩
  rw [← Nat.card_congr e₁.toEquiv, ← Nat.card_congr e₂.toEquiv, h]

omit [CommRing k] [Group G] in
private theorem epi_iso_inv {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) : Epi e.inv :=
  inferInstance

section Generator

variable [Fintype G] {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G)
include hg

/-- For a finite cyclic group generated by `g`, `H²(G, A) ≅ ker (ρ(g) - 1) ⧸ range N`. -/
theorem nonempty_linearEquiv_two :
    Nonempty (groupCohomology A 2 ≃ₗ[k] Subquotient (A.ρ g - 1) A.ρ.norm) := by
  have : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.2 ⟨g, eq_top_iff.2 fun x _ => hg x⟩
  let : CommGroup G := IsCyclic.commGroup
  exact nonempty_linearEquiv_subquotient (φ := (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (ψ := A.norm.hom.toLinearMap)
    (Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 even_two).hom (by
      exact (ModuleCat.epi_iff_surjective _).1
        (epi_comp' (epi_iso_inv _) (epi_comp' inferInstance inferInstance)))
    (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff A g hg 2 even_two)

/-- For a finite cyclic group generated by `g`, `H¹(G, A) ≅ ker N ⧸ range (ρ(g) - 1)`. -/
theorem nonempty_linearEquiv_one :
    Nonempty (groupCohomology A 1 ≃ₗ[k] Subquotient A.ρ.norm (A.ρ g - 1)) := by
  have : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.2 ⟨g, eq_top_iff.2 fun x _ => hg x⟩
  let : CommGroup G := IsCyclic.commGroup
  exact nonempty_linearEquiv_subquotient (φ := A.norm.hom.toLinearMap)
    (ψ := (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (Rep.FiniteCyclicGroup.groupCohomologyπOdd A g hg 1 odd_one).hom (by
      exact (ModuleCat.epi_iff_surjective _).1
        (epi_comp' (epi_iso_inv _) (epi_comp' inferInstance inferInstance)))
    (Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff A g hg 1 odd_one)

/-- For a finite cyclic group generated by `g`, the Herbrand quotient is the subquotient ratio
of `ρ(g) - 1` and the norm `N`. -/
theorem hasHerbrandQuotient_iff_hasSubquotientRatio {q : ℚ} :
    HasHerbrandQuotient A q ↔ HasSubquotientRatio (A.ρ g - 1) A.ρ.norm q := by
  obtain ⟨e₂⟩ := nonempty_linearEquiv_two hg A
  obtain ⟨e₁⟩ := nonempty_linearEquiv_one hg A
  unfold HasHerbrandQuotient HasSubquotientRatio
  rw [e₂.toEquiv.finite_iff, e₁.toEquiv.finite_iff, Nat.card_congr e₂.toEquiv,
    Nat.card_congr e₁.toEquiv]
  exact ⟨fun ⟨h₁, h₂, h⟩ => ⟨h₂, h₁, h⟩, fun ⟨h₂, h₁, h⟩ => ⟨h₁, h₂, h⟩⟩

omit hg in
/-- A short exact sequence of representations gives compatible short exact sequences for
`ρ(g) - 1` and the norm. -/
theorem compatibleExact_of_rep {A B C : Rep k G} (g : G) (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hp : Function.Surjective p.hom)
    (hex : LinearMap.range i.hom.toLinearMap = LinearMap.ker p.hom.toLinearMap) :
    CompatibleExact (A.ρ g - 1) A.ρ.norm (B.ρ g - 1) B.ρ.norm (C.ρ g - 1) C.ρ.norm
      i.hom.toLinearMap p.hom.toLinearMap where
  injective := hi
  surjective := hp
  exact := hex.symm
  iφ := intertwiningMap_sub_one_apply i.hom g
  iψ := intertwiningMap_norm_apply i.hom
  pφ := intertwiningMap_sub_one_apply p.hom g
  pψ := intertwiningMap_norm_apply p.hom
  φψX := sub_one_norm_apply A.ρ g
  ψφX := norm_sub_one_apply A.ρ g
  φψY := sub_one_norm_apply B.ρ g
  ψφY := norm_sub_one_apply B.ρ g
  φψZ := sub_one_norm_apply C.ρ g
  ψφZ := norm_sub_one_apply C.ρ g

end Generator

section Cyclic

variable [Finite G] [IsCyclic G]

omit [IsCyclic G] [Finite G] in
/-- In a short exact sequence of representations, the image of the first map is the kernel of the
second. -/
theorem range_eq_ker_of_exact {S : ShortComplex (Rep k G)} (hS : S.Exact) :
    LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    ((S.exact_map_iff_of_faithful (forget₂ (Rep k G) (ModuleCat k))).2 hS)

omit [IsCyclic G] [Finite G] in
theorem compatibleExact_of_shortExact [Fintype G] {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    (g : G) :
    CompatibleExact (S.X₁.ρ g - 1) S.X₁.ρ.norm (S.X₂.ρ g - 1) S.X₂.ρ.norm (S.X₃.ρ g - 1)
      S.X₃.ρ.norm S.f.hom.toLinearMap S.g.hom.toLinearMap :=
  compatibleExact_of_rep g S.f S.g ((Rep.mono_iff_injective _).1 hS.mono_f)
    ((Rep.epi_iff_surjective _).1 hS.epi_g) (range_eq_ker_of_exact hS.exact)

/-- Multiplicativity: in a short exact sequence `0 → A → B → C → 0` of representations of a
finite cyclic group, `h(B) = h(A) h(C)`. -/
theorem HasHerbrandQuotient.of_shortExact {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    {qA qC : ℚ} (hA : HasHerbrandQuotient S.X₁ qA) (hC : HasHerbrandQuotient S.X₃ qC) :
    HasHerbrandQuotient S.X₂ (qA * qC) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let := Fintype.ofFinite G
  rw [hasHerbrandQuotient_iff_hasSubquotientRatio hg] at hA hC ⊢
  exact (compatibleExact_of_shortExact hS g).hasSubquotientRatio_mid hA hC

/-- Two out of three: in a short exact sequence `0 → A → B → C → 0`, `h(A) = h(B) / h(C)`. -/
theorem HasHerbrandQuotient.of_shortExact_left {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    {qB qC : ℚ} (hB : HasHerbrandQuotient S.X₂ qB) (hC : HasHerbrandQuotient S.X₃ qC) :
    HasHerbrandQuotient S.X₁ (qB / qC) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let := Fintype.ofFinite G
  rw [hasHerbrandQuotient_iff_hasSubquotientRatio hg] at hB hC ⊢
  exact (compatibleExact_of_shortExact hS g).hasSubquotientRatio_left hB hC

/-- Two out of three: in a short exact sequence `0 → A → B → C → 0`, `h(C) = h(B) / h(A)`. -/
theorem HasHerbrandQuotient.of_shortExact_right {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    {qA qB : ℚ} (hA : HasHerbrandQuotient S.X₁ qA) (hB : HasHerbrandQuotient S.X₂ qB) :
    HasHerbrandQuotient S.X₃ (qB / qA) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let := Fintype.ofFinite G
  rw [hasHerbrandQuotient_iff_hasSubquotientRatio hg] at hA hB ⊢
  exact (compatibleExact_of_shortExact hS g).hasSubquotientRatio_right hA hB

/-- A finite representation of a finite cyclic group has Herbrand quotient `1`. -/
theorem hasHerbrandQuotient_of_finite (A : Rep k G) [Finite A] : HasHerbrandQuotient A 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let := Fintype.ofFinite G
  rw [hasHerbrandQuotient_iff_hasSubquotientRatio hg]
  exact hasSubquotientRatio_of_finite (sub_one_norm_apply A.ρ g) (norm_sub_one_apply A.ρ g)

/-- An injective map of representations with finite cokernel preserves the Herbrand
quotient. -/
theorem hasHerbrandQuotient_iff_of_injective {A B : Rep k G} (i : A ⟶ B)
    (hi : Function.Injective i.hom) [Finite (B ⧸ LinearMap.range i.hom.toLinearMap)] {q : ℚ} :
    HasHerbrandQuotient A q ↔ HasHerbrandQuotient B q := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let := Fintype.ofFinite G
  rw [hasHerbrandQuotient_iff_hasSubquotientRatio hg, hasHerbrandQuotient_iff_hasSubquotientRatio hg]
  exact hasSubquotientRatio_iff_of_injective i.hom.toLinearMap hi
    (intertwiningMap_sub_one_apply i.hom g) (intertwiningMap_norm_apply i.hom)
    (sub_one_norm_apply A.ρ g) (norm_sub_one_apply A.ρ g)
    (sub_one_norm_apply B.ρ g) (norm_sub_one_apply B.ρ g)

/-- A surjective map of representations with finite kernel preserves the Herbrand quotient. -/
theorem hasHerbrandQuotient_iff_of_surjective {B C : Rep k G} (p : B ⟶ C)
    (hp : Function.Surjective p.hom) [Finite (LinearMap.ker p.hom.toLinearMap)] {q : ℚ} :
    HasHerbrandQuotient B q ↔ HasHerbrandQuotient C q := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let := Fintype.ofFinite G
  rw [hasHerbrandQuotient_iff_hasSubquotientRatio hg, hasHerbrandQuotient_iff_hasSubquotientRatio hg]
  exact hasSubquotientRatio_iff_of_surjective p.hom.toLinearMap hp
    (intertwiningMap_sub_one_apply p.hom g) (intertwiningMap_norm_apply p.hom)
    (sub_one_norm_apply B.ρ g) (norm_sub_one_apply B.ρ g)
    (sub_one_norm_apply C.ρ g) (norm_sub_one_apply C.ρ g)

omit [Finite G] [IsCyclic G] in
/-- With finite `H¹` and `H²`, the Herbrand quotient is `|H²| / |H¹|`. -/
theorem hasHerbrandQuotient_of_finite_cohomology (A : Rep k G) [Finite (groupCohomology A 1)]
    [Finite (groupCohomology A 2)] :
    HasHerbrandQuotient A
      ((Nat.card (groupCohomology A 2) : ℚ) / Nat.card (groupCohomology A 1)) := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  have : (Nat.card (groupCohomology A 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  field_simp

/-- Division-free multiplicativity, middle term: if `H¹` and `H²` of `S.X₁` and `S.X₃` are
finite, then so are those of `S.X₂`, and
`h₂(X₂) h₁(X₁) h₁(X₃) = h₁(X₂) h₂(X₁) h₂(X₃)` with `hᵢ(X) = |Hⁱ(G, X)|`. -/
theorem natCard_of_shortExact_mid {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    [Finite (groupCohomology S.X₁ 1)] [Finite (groupCohomology S.X₁ 2)]
    [Finite (groupCohomology S.X₃ 1)] [Finite (groupCohomology S.X₃ 2)] :
    Finite (groupCohomology S.X₂ 1) ∧ Finite (groupCohomology S.X₂ 2) ∧
      Nat.card (groupCohomology S.X₂ 2) * Nat.card (groupCohomology S.X₁ 1) *
          Nat.card (groupCohomology S.X₃ 1) =
        Nat.card (groupCohomology S.X₂ 1) * Nat.card (groupCohomology S.X₁ 2) *
          Nat.card (groupCohomology S.X₃ 2) := by
  obtain ⟨h₁, h₂, h⟩ := (hasHerbrandQuotient_of_finite_cohomology S.X₁).of_shortExact hS
    (hasHerbrandQuotient_of_finite_cohomology S.X₃)
  refine ⟨h₁, h₂, ?_⟩
  have hA : (Nat.card (groupCohomology S.X₁ 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hC : (Nat.card (groupCohomology S.X₃ 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [div_mul_div_comm, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hA hC)] at h
  exact_mod_cast (by rw [mul_assoc, h]; ring :
    (Nat.card (groupCohomology S.X₂ 2) : ℚ) * Nat.card (groupCohomology S.X₁ 1) *
        Nat.card (groupCohomology S.X₃ 1) =
      Nat.card (groupCohomology S.X₂ 1) * Nat.card (groupCohomology S.X₁ 2) *
        Nat.card (groupCohomology S.X₃ 2))

/-- Division-free multiplicativity, left term: if `H¹` and `H²` of `S.X₂` and `S.X₃` are finite,
then so are those of `S.X₁`, and `h₂(X₂) h₁(X₁) h₁(X₃) = h₁(X₂) h₂(X₁) h₂(X₃)`. -/
theorem natCard_of_shortExact_left {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    [Finite (groupCohomology S.X₂ 1)] [Finite (groupCohomology S.X₂ 2)]
    [Finite (groupCohomology S.X₃ 1)] [Finite (groupCohomology S.X₃ 2)] :
    Finite (groupCohomology S.X₁ 1) ∧ Finite (groupCohomology S.X₁ 2) ∧
      Nat.card (groupCohomology S.X₂ 2) * Nat.card (groupCohomology S.X₁ 1) *
          Nat.card (groupCohomology S.X₃ 1) =
        Nat.card (groupCohomology S.X₂ 1) * Nat.card (groupCohomology S.X₁ 2) *
          Nat.card (groupCohomology S.X₃ 2) := by
  obtain ⟨h₁, h₂, h⟩ := (hasHerbrandQuotient_of_finite_cohomology S.X₂).of_shortExact_left hS
    (hasHerbrandQuotient_of_finite_cohomology S.X₃)
  refine ⟨h₁, h₂, ?_⟩
  have hB : (Nat.card (groupCohomology S.X₂ 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hC : (Nat.card (groupCohomology S.X₃ 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hC' : (Nat.card (groupCohomology S.X₃ 2) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have key : (Nat.card (groupCohomology S.X₂ 2) : ℚ) * Nat.card (groupCohomology S.X₁ 1) *
        Nat.card (groupCohomology S.X₃ 1) =
      Nat.card (groupCohomology S.X₂ 1) * Nat.card (groupCohomology S.X₁ 2) *
        Nat.card (groupCohomology S.X₃ 2) := by
    rw [h]; field_simp
  exact_mod_cast key

/-- Division-free multiplicativity, right term: if `H¹` and `H²` of `S.X₁` and `S.X₂` are finite,
then so are those of `S.X₃`, and `h₂(X₂) h₁(X₁) h₁(X₃) = h₁(X₂) h₂(X₁) h₂(X₃)`. -/
theorem natCard_of_shortExact_right {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    [Finite (groupCohomology S.X₁ 1)] [Finite (groupCohomology S.X₁ 2)]
    [Finite (groupCohomology S.X₂ 1)] [Finite (groupCohomology S.X₂ 2)] :
    Finite (groupCohomology S.X₃ 1) ∧ Finite (groupCohomology S.X₃ 2) ∧
      Nat.card (groupCohomology S.X₂ 2) * Nat.card (groupCohomology S.X₁ 1) *
          Nat.card (groupCohomology S.X₃ 1) =
        Nat.card (groupCohomology S.X₂ 1) * Nat.card (groupCohomology S.X₁ 2) *
          Nat.card (groupCohomology S.X₃ 2) := by
  obtain ⟨h₁, h₂, h⟩ := (hasHerbrandQuotient_of_finite_cohomology S.X₁).of_shortExact_right hS
    (hasHerbrandQuotient_of_finite_cohomology S.X₂)
  refine ⟨h₁, h₂, ?_⟩
  have hA : (Nat.card (groupCohomology S.X₁ 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hA' : (Nat.card (groupCohomology S.X₁ 2) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hB : (Nat.card (groupCohomology S.X₂ 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have key : (Nat.card (groupCohomology S.X₂ 2) : ℚ) * Nat.card (groupCohomology S.X₁ 1) *
        Nat.card (groupCohomology S.X₃ 1) =
      Nat.card (groupCohomology S.X₂ 1) * Nat.card (groupCohomology S.X₁ 2) *
        Nat.card (groupCohomology S.X₃ 2) := by
    rw [h]; field_simp
  exact_mod_cast key

/-- Finite coefficients: if `A` is finite, then `H¹(G, A)` and `H²(G, A)` are finite of the same
cardinality. -/
theorem natCard_two_eq_natCard_one_of_finite (A : Rep k G) [Finite A] :
    Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 2) = Nat.card (groupCohomology A 1) := by
  obtain ⟨h₁, h₂, h⟩ := hasHerbrandQuotient_of_finite A
  exact ⟨h₁, h₂, by exact_mod_cast (h.trans (one_mul _))⟩

end Cyclic

section TrivialIntegers

open Langlands.Tate (integralTrivial)

variable {G : Type u} [Group G]

theorem trivialIntegers_norm_apply [Fintype G] (x : ULift.{u} ℤ) :
    (integralTrivial G).ρ.norm x = Fintype.card G • x := by
  simp [Representation.norm, LinearMap.sum_apply]

theorem trivialIntegers_sub_one_apply (g : G) (x : ULift.{u} ℤ) :
    ((integralTrivial G).ρ g - 1) x = 0 := by
  simp

theorem mem_range_norm_trivialIntegers_iff [Fintype G] (x : ULift.{u} ℤ) :
    x ∈ LinearMap.range (integralTrivial G).ρ.norm ↔ (Fintype.card G : ℤ) ∣ x.down := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y.down, ?_⟩
    rw [trivialIntegers_norm_apply]
    show (Fintype.card G • y.down : ℤ) = _
    rw [nsmul_eq_mul]
  · rintro ⟨c, hc⟩
    refine ⟨ULift.up c, ?_⟩
    rw [trivialIntegers_norm_apply]
    refine ULift.ext _ _ ?_
    show (Fintype.card G • c : ℤ) = x.down
    rw [nsmul_eq_mul, hc]

variable [Finite G] [IsCyclic G]

/-- `H¹(G, ℤ) = 0` for a finite cyclic group `G` acting trivially on `ℤ`. -/
theorem subsingleton_groupCohomology_one_trivialIntegers :
    Subsingleton (groupCohomology (integralTrivial G) 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let := Fintype.ofFinite G
  obtain ⟨e⟩ := nonempty_linearEquiv_one hg (integralTrivial G)
  have hker : Subsingleton (LinearMap.ker (integralTrivial G).ρ.norm) := by
    refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_⟩
    rw [LinearMap.mem_ker, trivialIntegers_norm_apply] at hx hy
    have hx' : Fintype.card G • x.down = 0 := by simpa using congrArg ULift.down hx
    have hy' : Fintype.card G • y.down = 0 := by simpa using congrArg ULift.down hy
    rw [smul_eq_zero] at hx' hy'
    refine Subtype.ext (ULift.ext _ _ ?_)
    rw [hx'.resolve_left Fintype.card_ne_zero, hy'.resolve_left Fintype.card_ne_zero]
  exact e.toEquiv.subsingleton_congr.2 ((Submodule.mkQ_surjective _).subsingleton)

/-- `|H²(G, ℤ)| = |G|` for a finite cyclic group `G` acting trivially on `ℤ`. -/
theorem natCard_groupCohomology_two_trivialIntegers :
    Nat.card (groupCohomology (integralTrivial G) 2) = Nat.card G := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let := Fintype.ofFinite G
  obtain ⟨e⟩ := nonempty_linearEquiv_two hg (integralTrivial G)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card (α := G)]
  set n := Fintype.card G
  let K := LinearMap.ker ((integralTrivial G).ρ g - 1)
  let P := (LinearMap.range (integralTrivial G).ρ.norm).submoduleOf K
  let f : K →+ ZMod n := (Int.castAddHom (ZMod n)).comp
    (AddEquiv.ulift.toAddMonoidHom.comp K.subtype.toAddMonoidHom)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨⟨ULift.up m, trivialIntegers_sub_one_apply g _⟩, rfl⟩
  have hker : P.toAddSubgroup = f.ker := by
    ext ⟨x, hx⟩
    rw [Submodule.mem_toAddSubgroup, mem_submoduleOf_iff, mem_range_norm_trivialIntegers_iff,
      AddMonoidHom.mem_ker]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
  calc Nat.card (Subquotient ((integralTrivial G).ρ g - 1) (integralTrivial G).ρ.norm)
      = Nat.card (K ⧸ P.toAddSubgroup) := rfl
    _ = Nat.card (ZMod n) := Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective f hf)).toEquiv
    _ = n := Nat.card_zmod n

/-- For a finite cyclic group `G` acting trivially on `ℤ`, `H¹(G, ℤ)` is trivial, `H²(G, ℤ)` is
finite and `|H²(G, ℤ)| = |G|`. -/
theorem groupCohomology_trivialIntegers :
    Subsingleton (groupCohomology (integralTrivial G) 1) ∧
      Finite (groupCohomology (integralTrivial G) 2) ∧
      Nat.card (groupCohomology (integralTrivial G) 2) = Nat.card G := by
  refine ⟨subsingleton_groupCohomology_one_trivialIntegers,
    Nat.finite_of_card_ne_zero ?_, natCard_groupCohomology_two_trivialIntegers⟩
  rw [natCard_groupCohomology_two_trivialIntegers]
  exact Nat.card_pos.ne'

/-- The Herbrand quotient of `ℤ` with trivial action of a finite cyclic group `G` is `|G|`. -/
theorem hasHerbrandQuotient_trivialIntegers :
    HasHerbrandQuotient (integralTrivial G) (Nat.card G) := by
  obtain ⟨h₁, h₂, h⟩ := groupCohomology_trivialIntegers (G := G)
  refine ⟨Finite.of_subsingleton, h₂, ?_⟩
  rw [h, Nat.card_of_subsingleton (0 : groupCohomology (integralTrivial G) 1), Nat.cast_one,
    mul_one]

end TrivialIntegers

end Rep

end Langlands.Cohomology.Herbrand
