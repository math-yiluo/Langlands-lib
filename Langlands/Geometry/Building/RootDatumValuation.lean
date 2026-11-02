import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.Geometry.Building.RealTorusAction
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Valuations of the root datum on the actual relative root groups

For a homomorphism `i : S ⟶ G` from a commutative group scheme over a field `k` (meant: a
maximal split torus of a connected reductive group), this module states Kaletha–Prasad
Definition 6.1.2 (axioms V 0–V 5), the split-torus part of V 6, the translation action of
`V(S)` (KP Lemma 6.1.6), equipollence (KP Definition 6.1.7) and the action of the normalizer
points `N(k)` (KP 6.1.8). The root groups are the rational points of the actual relative root
subgroup functors `RelativeRoot.subgroup i a`; for a multipliable root `a` the functor for
`2a` is the actual `U_{2a}`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The rational points `U_a(k)` of the actual relative root subgroup functor of `a`. -/
def rootGroupPoints (i : S.toGrp ⟶ G) (a : characterLattice S) : Subgroup (rationalPoints G) :=
  (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _))

theorem mem_rootGroupPoints {i : S.toGrp ⟶ G} {a : characterLattice S} {g : rationalPoints G} :
    g ∈ rootGroupPoints i a ↔
      ∃ e, RelativeRoot.IsOrbitExtension i a g e ∧ Dynamic.evalZero e = 1 :=
  Iff.rfl

/-! ### Evaluation of characters on `V(S)` -/

theorem eval_zero_char (v : V S) : eval S 0 v = 0 := by
  rw [eval_eq_pair, TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply]

theorem eval_add_char (a b : characterLattice S) (v : V S) :
    eval S (a + b) v = eval S a v + eval S b v := by
  rw [eval_eq_pair, eval_eq_pair, eval_eq_pair, TensorProduct.tmul_add, map_add,
    LinearMap.add_apply]

theorem eval_neg_char (a : characterLattice S) (v : V S) : eval S (-a) v = -eval S a v := by
  rw [eval_eq_pair, eval_eq_pair, TensorProduct.tmul_neg, map_neg, LinearMap.neg_apply]

theorem eval_nsmul_char (p : ℕ) (a : characterLattice S) (v : V S) :
    eval S (p • a) v = p * eval S a v := by
  induction p with
  | zero => rw [zero_smul, eval_zero_char, Nat.cast_zero, zero_mul]
  | succ p ih => rw [succ_nsmul, eval_add_char, ih, Nat.cast_succ, add_one_mul]

variable (S G) in
/-- Families `(φ_a)_a` of functions `φ_a : G(k) → ℝ ∪ {∞}` indexed by the characters of `S`.
A valuation of the root datum uses only `φ_a` on `U_a(k)` for roots `a`; its normalization
axioms set every other value to `∞`. -/
structure RootFunctionFamily : Type u where
  /-- The function `φ_a : G(k) → ℝ ∪ {∞}` attached to the character `a`. -/
  toFun : characterLattice S → rationalPoints G → WithTop ℝ

namespace RootFunctionFamily

instance : CoeFun (RootFunctionFamily S G)
    fun _ => characterLattice S → rationalPoints G → WithTop ℝ :=
  ⟨toFun⟩

@[simp] theorem coe_mk (f : characterLattice S → rationalPoints G → WithTop ℝ) :
    ((⟨f⟩ : RootFunctionFamily S G) : characterLattice S → rationalPoints G → WithTop ℝ) = f :=
  rfl

@[ext] theorem ext {φ ψ : RootFunctionFamily S G} (h : ∀ a g, φ a g = ψ a g) : φ = ψ := by
  cases φ
  cases ψ
  congr
  funext a g
  exact h a g

/-! ### Translation by `V(S)` (KP Lemma 6.1.6) -/

/-- `(v +ᵥ φ)_a(u) = φ_a(u) + a(v)`. -/
instance : VAdd (V S) (RootFunctionFamily S G) where
  vadd v φ := ⟨fun a g => φ a g + ((eval S a v : ℝ) : WithTop ℝ)⟩

theorem vadd_apply (v : V S) (φ : RootFunctionFamily S G) (a : characterLattice S)
    (g : rationalPoints G) : (v +ᵥ φ) a g = φ a g + ((eval S a v : ℝ) : WithTop ℝ) :=
  rfl

instance : AddAction (V S) (RootFunctionFamily S G) where
  zero_vadd φ := by
    ext a g
    rw [vadd_apply, map_zero, WithTop.coe_zero, add_zero]
  add_vadd v w φ := by
    ext a g
    rw [vadd_apply, vadd_apply, vadd_apply, map_add, WithTop.coe_add, add_assoc,
      add_comm ((eval S a v : ℝ) : WithTop ℝ)]

/-! ### The action of the normalizer points (KP 6.1.8) -/

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- `(n φ)_a(u) = φ_{n⁻¹·a}(n⁻¹ u n)`, with `n·a` the published `weylAction`. -/
instance : SMul (normalizerPoints i) (RootFunctionFamily S G) where
  smul n φ := ⟨fun a g =>
    φ (weylAction i n⁻¹ a) ((n : rationalPoints G)⁻¹ * g * (n : rationalPoints G))⟩

theorem smul_apply (n : normalizerPoints i) (φ : RootFunctionFamily S G)
    (a : characterLattice S) (g : rationalPoints G) :
    (n • φ) a g =
      φ (weylAction i n⁻¹ a) ((n : rationalPoints G)⁻¹ * g * (n : rationalPoints G)) :=
  rfl

instance : MulAction (normalizerPoints i) (RootFunctionFamily S G) where
  one_smul φ := by
    ext a g
    rw [smul_apply, inv_one, map_one, LinearEquiv.coe_one, id, OneMemClass.coe_one, inv_one,
      one_mul, mul_one]
  mul_smul n m φ := by
    ext a g
    rw [smul_apply, smul_apply, smul_apply, mul_inv_rev, map_mul, LinearEquiv.mul_apply,
      Subgroup.coe_mul, mul_inv_rev]
    simp only [mul_assoc]

/-- The two actions fuse: `n(φ + v) = nφ + n·v` (KP 6.1.8). -/
theorem smul_vadd (n : normalizerPoints i) (v : V S) (φ : RootFunctionFamily S G) :
    n • (v +ᵥ φ) = (n • v) +ᵥ (n • φ) := by
  ext a g
  rw [smul_apply, vadd_apply, vadd_apply, smul_apply, eval_normalizer_smul]

end RootFunctionFamily

open RootFunctionFamily

variable (i : S.toGrp ⟶ G)

/-- The filtration set `U_{a,φ,r} = {u ∈ U_a(k) | r ≤ φ_a(u)}` (KP Definition 6.1.2, V 1). -/
def rootFiltration (φ : RootFunctionFamily S G) (a : characterLattice S) (r : ℝ) :
    Set (rationalPoints G) :=
  {g | g ∈ rootGroupPoints i a ∧ (r : WithTop ℝ) ≤ φ a g}

variable {i}

theorem mem_rootFiltration {φ : RootFunctionFamily S G} {a : characterLattice S} {r : ℝ}
    {g : rationalPoints G} :
    g ∈ rootFiltration i φ a r ↔ g ∈ rootGroupPoints i a ∧ (r : WithTop ℝ) ≤ φ a g :=
  Iff.rfl

private theorem coe_le_add_coe_iff (r c : ℝ) (x : WithTop ℝ) :
    ((r + c : ℝ) : WithTop ℝ) ≤ x + (c : WithTop ℝ) ↔ (r : WithTop ℝ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe y =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    exact add_le_add_iff_right c

/-- `U_{a,φ+v,r+a(v)} = U_{a,φ,r}` (KP Lemma 6.1.6). -/
theorem rootFiltration_vadd (φ : RootFunctionFamily S G) (v : V S) (a : characterLattice S)
    (r : ℝ) : rootFiltration i (v +ᵥ φ) a (r + eval S a v) = rootFiltration i φ a r := by
  ext g
  simp only [mem_rootFiltration, vadd_apply, coe_le_add_coe_iff]

theorem rootFiltration_vadd' (φ : RootFunctionFamily S G) (v : V S) (a : characterLattice S)
    (r : ℝ) : rootFiltration i (v +ᵥ φ) a r = rootFiltration i φ a (r - eval S a v) := by
  rw [← rootFiltration_vadd φ v a (r - eval S a v), sub_add_cancel]

/-- Two families are equipollent if they differ by a translation `v ∈ V(S)`
(KP Definition 6.1.7). -/
def Equipollent (φ ψ : RootFunctionFamily S G) : Prop :=
  ∃ v : V S, ψ = v +ᵥ φ

theorem equipollent_iff_mem_orbit {φ ψ : RootFunctionFamily S G} :
    Equipollent φ ψ ↔ ψ ∈ AddAction.orbit (V S) φ := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl⟩

theorem Equipollent.refl (φ : RootFunctionFamily S G) : Equipollent φ φ :=
  ⟨0, (zero_vadd _ _).symm⟩

theorem Equipollent.symm {φ ψ : RootFunctionFamily S G} (h : Equipollent φ ψ) :
    Equipollent ψ φ := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨-v, by rw [vadd_vadd, neg_add_cancel, zero_vadd]⟩

theorem Equipollent.trans {φ ψ χ : RootFunctionFamily S G} (h : Equipollent φ ψ)
    (h' : Equipollent ψ χ) : Equipollent φ χ := by
  obtain ⟨v, rfl⟩ := h
  obtain ⟨w, rfl⟩ := h'
  exact ⟨w + v, (add_vadd w v φ).symm⟩

variable (i) [Mono i.hom.hom.left]

/-- `n ∈ N(k)` realizes the reflection along `a`: it sends `a` to `-a` and fixes the hyperplane
`ker a ⊆ V(S)` pointwise. -/
def RealizesReflection (a : characterLattice S) (n : normalizerPoints i) : Prop :=
  weylAction i n a = -a ∧ ∀ v : V S, eval S a v = 0 → n • v = v

variable [IsAffineHom G.X.hom]

/-- A valuation of the root datum of `(G, S)` (KP Definition 6.1.2, axioms V 0–V 5), on the
actual root groups `U_a(k) = rootGroupPoints i a`. The first two fields set the values off
the roots and off `U_a(k)` to `∞`, so that a valuation is the same as KP's family
`(φ_a : U_a(k) → ℝ ∪ {∞})_{a ∈ Φ}`. -/
structure IsRootDatumValuation (φ : RootFunctionFamily S G) : Prop where
  /-- Normalization: `φ_a = ∞` when `a` is not a relative root. -/
  eq_top_of_not_mem_roots : ∀ a ∉ relativeRoots i, ∀ g, φ a g = ⊤
  /-- Normalization: `φ_a = ∞` off `U_a(k)`. -/
  eq_top_of_not_mem : ∀ a ∈ relativeRoots i, ∀ g ∉ rootGroupPoints i a, φ a g = ⊤
  /-- V 0: `φ_a(U_a(k))` has at least three elements. -/
  three_le_encard : ∀ a ∈ relativeRoots i, 3 ≤ (φ a '' rootGroupPoints i a).encard
  /-- V 1: `U_{a,φ,r}` contains `1`. -/
  one_mem : ∀ a ∈ relativeRoots i, ∀ r : ℝ, (1 : rationalPoints G) ∈ rootFiltration i φ a r
  /-- V 1: `U_{a,φ,r}` is closed under products. -/
  mul_mem : ∀ a ∈ relativeRoots i, ∀ r : ℝ, ∀ g h : rationalPoints G,
    g ∈ rootFiltration i φ a r → h ∈ rootFiltration i φ a r → g * h ∈ rootFiltration i φ a r
  /-- V 1: `U_{a,φ,r}` is closed under inverses. -/
  inv_mem : ∀ a ∈ relativeRoots i, ∀ r : ℝ, ∀ g : rationalPoints G,
    g ∈ rootFiltration i φ a r → g⁻¹ ∈ rootFiltration i φ a r
  /-- V 1: `U_{a,φ,∞} = φ_a⁻¹(∞) = {1}`. -/
  eq_top_iff : ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a, φ a g = ⊤ ↔ g = 1
  /-- V 2: for `n` realizing the reflection along `a`, `φ_a(u) - φ_{-a}(n u n⁻¹)` is constant
  on `U_a(k) ∖ {1}`. -/
  reflection : ∀ a ∈ relativeRoots i, ∀ n : normalizerPoints i, RealizesReflection i a n →
    ∃ c : ℝ, ∀ u ∈ rootGroupPoints i a, u ≠ 1 →
      φ a u = φ (-a) ((n : rationalPoints G) * u * (n : rationalPoints G)⁻¹) + (c : WithTop ℝ)
  /-- V 3: for `b ∉ -ℝ_{>0} a`, the commutator subgroup `(U_{a,φ,r}, U_{b,φ,s})` lies in the
  group generated by the `U_{pa+qb,φ,pr+qs}` with `p, q > 0` and `pa + qb ∈ Φ`. -/
  commutator : ∀ a ∈ relativeRoots i, ∀ b ∈ relativeRoots i,
    (∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] b : Vstar S) ≠ -(t • (1 : ℝ) ⊗ₜ[ℤ] a)) →
    ∀ r s : ℝ,
      ⁅Subgroup.closure (rootFiltration i φ a r), Subgroup.closure (rootFiltration i φ b s)⁆ ≤
        Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
          (_ : p • a + q • b ∈ relativeRoots i),
          rootFiltration i φ (p • a + q • b) (p * r + q * s))
  /-- V 4: if `a, 2a ∈ Φ`, then `φ_{2a} = 2 φ_a` on `U_{2a}(k)`. -/
  double : ∀ a ∈ relativeRoots i, 2 • a ∈ relativeRoots i →
    ∀ u ∈ rootGroupPoints i (2 • a), φ (2 • a) u = 2 • φ a u
  /-- V 5: if `u ∈ U_a(k) ∖ {1}` and `u', u'' ∈ U_{-a}(k)` with `u' u u'' ∈ N(k)`
  (KP Proposition 2.11.17), then `φ_{-a}(u') = -φ_a(u)`. -/
  opposite : ∀ a ∈ relativeRoots i, ∀ u ∈ rootGroupPoints i a, u ≠ 1 →
    ∀ u' ∈ rootGroupPoints i (-a), ∀ u'' ∈ rootGroupPoints i (-a),
      u' * u * u'' ∈ normalizerPoints i → φ (-a) u' + φ a u = 0

omit [Mono i.hom.hom.left] in
/-- The part of KP axiom V 6 that concerns `S(k) ⊆ Z(k)`, for a valuation `ω : kˣ → ℝ` of
`k`: `φ_a(s⁻¹ u s) = φ_a(u) - ω(a(s))`. The full axiom on `Z(k)` needs the homomorphism
`ν : Z(k) → V(S)` of KP Axiom 4.1.4, which is not used here. -/
def IsSplitTorusCompatible (ω : kˣ → ℝ) (φ : RootFunctionFamily S G) : Prop :=
  ∀ a ∈ relativeRoots i, ∀ s : rationalPoints S.toGrp, ∀ u ∈ rootGroupPoints i a,
    φ a ((rationalPoints.map i s)⁻¹ * u * rationalPoints.map i s) =
      φ a u +
        ((-ω (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s) :
          ℝ) : WithTop ℝ)

namespace IsRootDatumValuation

variable {i} {φ : RootFunctionFamily S G}

/-- Translates of a valuation are valuations (KP Lemma 6.1.6). -/
theorem vadd (h : IsRootDatumValuation i φ) (v : V S) : IsRootDatumValuation i (v +ᵥ φ) where
  eq_top_of_not_mem_roots a ha g := by
    rw [vadd_apply, h.eq_top_of_not_mem_roots a ha g, WithTop.top_add]
  eq_top_of_not_mem a ha g hg := by
    rw [vadd_apply, h.eq_top_of_not_mem a ha g hg, WithTop.top_add]
  three_le_encard a ha := by
    have himage : (v +ᵥ φ) a '' rootGroupPoints i a =
        (fun x => x + ((eval S a v : ℝ) : WithTop ℝ)) '' (φ a '' rootGroupPoints i a) := by
      rw [Set.image_image]
      rfl
    rw [himage, (add_left_injective_of_ne_top _ WithTop.coe_ne_top).encard_image]
    exact h.three_le_encard a ha
  one_mem a ha r := by
    rw [rootFiltration_vadd']
    exact h.one_mem a ha _
  mul_mem a ha r g g' := by
    rw [rootFiltration_vadd']
    exact h.mul_mem a ha _ g g'
  inv_mem a ha r g := by
    rw [rootFiltration_vadd']
    exact h.inv_mem a ha _ g
  eq_top_iff a ha g hg := by
    rw [vadd_apply, WithTop.add_eq_top, or_iff_left WithTop.coe_ne_top]
    exact h.eq_top_iff a ha g hg
  reflection a ha n hn := by
    obtain ⟨c, hc⟩ := h.reflection a ha n hn
    refine ⟨c + 2 * eval S a v, fun u hu hu1 => ?_⟩
    rw [vadd_apply, vadd_apply, hc u hu hu1, add_assoc, add_assoc, ← WithTop.coe_add,
      ← WithTop.coe_add, eval_neg_char]
    congr 2
    ring
  commutator a ha b hb hab r s := by
    have key : ∀ p q : ℕ, (p * r + q * s : ℝ) - eval S (p • a + q • b) v =
        p * (r - eval S a v) + q * (s - eval S b v) := by
      intro p q
      rw [eval_add_char, eval_nsmul_char, eval_nsmul_char]
      ring
    simp only [rootFiltration_vadd', key]
    exact h.commutator a ha b hb hab _ _
  double a ha h2a u hu := by
    rw [vadd_apply, vadd_apply, h.double a ha h2a u hu, eval_nsmul_char, two_nsmul, two_nsmul,
      show ((2 : ℕ) : ℝ) * eval S a v = eval S a v + eval S a v by push_cast; ring,
      WithTop.coe_add]
    abel
  opposite a ha u hu hu1 u' hu' u'' hu'' hn := by
    rw [vadd_apply, vadd_apply, eval_neg_char, add_add_add_comm,
      h.opposite a ha u hu hu1 u' hu' u'' hu'' hn, ← WithTop.coe_add, neg_add_cancel,
      WithTop.coe_zero, add_zero]

end IsRootDatumValuation

omit [Mono i.hom.hom.left] in
/-- A translate of an `ω`-compatible family is `ω`-compatible (KP, after Definition 6.1.7). -/
theorem IsSplitTorusCompatible.vadd {ω : kˣ → ℝ} {φ : RootFunctionFamily S G}
    (h : IsSplitTorusCompatible i ω φ) (v : V S) : IsSplitTorusCompatible i ω (v +ᵥ φ) := by
  intro a ha s u hu
  rw [vadd_apply, vadd_apply, h a ha s u hu, add_right_comm]

end Langlands.Geometry.Building
