import Langlands.Group.GL.TwoBlockShape
import Langlands.Representation.Whittaker.UpperUnipotentCharacterFactorization

/-!
# Reductions for character-localized upper-unipotent coinvariants

Two reductions of the actual quotient `V_(U,η)` by the span of `ρ(u)v - η(u) • v`:

* degenerate vanishing: if `η` is trivial on the adjacent elementary matrices in position
  `(k, k+1)`, then `η` is trivial on the unipotent radical of the standard two-block
  parabolic `(k+1, n-k)`, so `V_(U,η)` is a quotient of the zero Jacquet quotient of a
  supercuspidal representation;
* conjugation: if `η(g⁻¹ u g) = θ(u)`, then `V_(U,η)` is a quotient of `V_(U,θ)`.
-/

noncomputable section

namespace Langlands.Whittaker.UpperUnipotentCoinvariant

open GeneralLinear UpperUnipotentCharacter
open ProductLeviChamber (twoBlock twoBlock_index_val)
open Classification.SupercuspidalDerivativeVanishing (IsBlockUnipotent
  mem_upperUnipotent_of_isBlockUnipotent)

universe uR uG uF uV

/-! ## The two-block shape `(a, N - a)` -/

variable {F : Type uF} [Field F]

theorem cutShape_length (N a : ℕ) (ha : 0 < a) (haN : a < N) :
    (twoBlock N a ha haN).length = 2 := rfl

/-- The first block of `(a, N - a)`. -/
def cutFirst (N a : ℕ) (ha : 0 < a) (haN : a < N) : Fin (twoBlock N a ha haN).length :=
  ⟨0, by rw [cutShape_length]; omega⟩

/-- The second block of `(a, N - a)`. -/
def cutSecond (N a : ℕ) (ha : 0 < a) (haN : a < N) : Fin (twoBlock N a ha haN).length :=
  ⟨1, by rw [cutShape_length]; omega⟩

/-- The two-block parabolic `(a, N - a)` with `0 < a < N` is proper. -/
theorem cutShape_parabolic_ne_top (N a : ℕ) (ha : 0 < a) (haN : a < N) :
    (twoBlock N a ha haN).parabolic F ≠ ⊤ := by
  intro htop
  let x : Fin ((twoBlock N a ha haN).size (cutSecond N a ha haN)) :=
    ⟨0, by simp [twoBlock, cutSecond]; omega⟩
  let y : Fin ((twoBlock N a ha haN).size (cutFirst N a ha haN)) :=
    ⟨0, by simp [twoBlock, cutFirst]; omega⟩
  have hxy : (twoBlock N a ha haN).index (cutSecond N a ha haN) x ≠
      (twoBlock N a ha haN).index (cutFirst N a ha haN) y := by
    intro h
    have h' := congrArg Fin.val h
    rw [twoBlock_index_val, twoBlock_index_val] at h'
    simp [x, y, cutFirst, cutSecond] at h'
    omega
  let g := transvectionUnit ((twoBlock N a ha haN).index (cutSecond N a ha haN) x)
    ((twoBlock N a ha haN).index (cutFirst N a ha haN) y) hxy (1 : F)
  have hg : g ∈ (twoBlock N a ha haN).parabolic F := htop ▸ Subgroup.mem_top _
  have hz := ((twoBlock N a ha haN).mem_parabolic_iff F g).mp hg (cutSecond N a ha haN)
    (cutFirst N a ha haN) x y (Fin.mk_lt_mk.mpr (by omega))
  have hone : g.val ((twoBlock N a ha haN).index (cutSecond N a ha haN) x)
      ((twoBlock N a ha haN).index (cutFirst N a ha haN) y) = 1 := by
    change Matrix.transvection ((twoBlock N a ha haN).index (cutSecond N a ha haN) x)
      ((twoBlock N a ha haN).index (cutFirst N a ha haN) y) (1 : F)
      ((twoBlock N a ha haN).index (cutSecond N a ha haN) x)
      ((twoBlock N a ha haN).index (cutFirst N a ha haN) y) = 1
    rw [transvection_apply]
    simp [hxy]
  exact one_ne_zero (hone.symm.trans hz)

/-- An element of the unipotent radical of the two-block parabolic `(a, N - a)` is block
unipotent: `[[I_a, Y], [0, I]]`. -/
theorem isBlockUnipotent_of_mem_cutShape {N a : ℕ} (ha : 0 < a) (haN : a < N)
    {g : GeneralLinear N F} (hg : g ∈ (twoBlock N a ha haN).unipotentSubgroup F) :
    IsBlockUnipotent a g := by
  rw [BlockShape.mem_unipotentSubgroup_iff] at hg
  obtain ⟨hP, hD⟩ := hg
  rw [BlockShape.mem_parabolic_iff] at hP
  intro i j hij
  obtain ⟨⟨bi, ri⟩, rfl⟩ := (twoBlock N a ha haN).indexEquiv.surjective i
  obtain ⟨⟨bj, rj⟩, rfl⟩ := (twoBlock N a ha haN).indexEquiv.surjective j
  change g.val ((twoBlock N a ha haN).index bi ri) ((twoBlock N a ha haN).index bj rj) =
    if (twoBlock N a ha haN).index bi ri = (twoBlock N a ha haN).index bj rj then 1 else 0
  change (((twoBlock N a ha haN).index bj rj : Fin N) : ℕ) < a ∨
    a ≤ (((twoBlock N a ha haN).index bi ri : Fin N) : ℕ) at hij
  rw [twoBlock_index_val, twoBlock_index_val] at hij
  have hri : (ri : ℕ) < (twoBlock N a ha haN).size bi := ri.isLt
  rcases bi with ⟨bi, hbi⟩
  rcases bj with ⟨bj, hbj⟩
  have hbi2 : bi < 2 := hbi
  have hbj2 : bj < 2 := hbj
  by_cases hb : bi = bj
  · subst hb
    rw [hD]
    by_cases hr : ri = rj
    · subst hr
      simp
    · have hne : (twoBlock N a ha haN).index ⟨bi, hbi⟩ ri ≠
          (twoBlock N a ha haN).index ⟨bi, hbj⟩ rj :=
        fun h => hr (((twoBlock N a ha haN).index ⟨bi, hbi⟩).injective h)
      simp only [hr, hne, ↓reduceIte]
  · have hne : (twoBlock N a ha haN).index ⟨bi, hbi⟩ ri ≠
        (twoBlock N a ha haN).index ⟨bj, hbj⟩ rj := by
      intro h
      have h' : (⟨⟨bi, hbi⟩, ri⟩ : (twoBlock N a ha haN).Index) = ⟨⟨bj, hbj⟩, rj⟩ :=
        (twoBlock N a ha haN).indexEquiv.injective h
      exact hb (congrArg (fun z => z.1.val) h')
    simp only [hne, ↓reduceIte]
    interval_cases bi <;> interval_cases bj
    · exact absurd rfl hb
    · exfalso
      have hri' : (ri : ℕ) < a := by simpa [twoBlock] using hri
      simp only [↓reduceIte, zero_add, one_ne_zero] at hij
      omega
    · exact hP ⟨1, hbi⟩ ⟨0, hbj⟩ ri rj (Fin.mk_lt_mk.mpr (by omega))
    · exact absurd rfl hb

/-! ## Degenerate vanishing -/

/-- If `η` is trivial on the adjacent elementary matrices in position `(k, k+1)`, the
`η`-localized upper-unipotent coinvariants of a supercuspidal representation vanish. -/
theorem subsingleton_coinvariants_of_adjacentUnit [TopologicalSpace F] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V) (hρ : IsSupercuspidal ρ)
    (η : upperUnipotent (n + 1) F →* ℂˣ) (k : Fin n)
    (hk : ∀ x : F, η (adjacentUnit k x) = 1) :
    Subsingleton (Jacquet.Localization.Coinvariants ρ (upperUnipotent (n + 1) F) η) := by
  have hk1 : k.val + 1 < n + 1 := by omega
  let B := twoBlock (n + 1) (k.val + 1) (Nat.succ_pos _) hk1
  have hJ := hρ.2 B (cutShape_parabolic_ne_top (F := F) (n + 1) (k.val + 1)
    (Nat.succ_pos _) hk1) 1
  let q := Jacquet.Localization.mk ρ (upperUnipotent (n + 1) F) η
  have hinv : ∀ u : B.conjugateUnipotent 1, q ∘ₗ ρ u.val = q := by
    rintro ⟨u, hu⟩
    have hu' : u ∈ B.unipotentSubgroup F := by
      obtain ⟨u', hu', rfl⟩ := hu
      simpa using hu'
    have hb := isBlockUnipotent_of_mem_cutShape (Nat.succ_pos _) hk1 hu'
    have hU := mem_upperUnipotent_of_isBlockUnipotent hb
    apply LinearMap.ext
    intro v
    have h := Jacquet.Localization.mk_apply_subgroup ρ _ η ⟨u, hU⟩ v
    rw [character_eq_one_of_isBlockUnipotent η k hk ⟨u, hU⟩ hb, Units.val_one,
      one_smul] at h
    exact h
  refine ⟨fun x y => ?_⟩
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective ρ _ η x
  obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective ρ _ η y
  have hl := Jacquet.lift_mk ρ (B.conjugateUnipotent 1) q hinv
  rw [← hl v, ← hl w, Subsingleton.elim (Jacquet.mk ρ (B.conjugateUnipotent 1) v)
    (Jacquet.mk ρ (B.conjugateUnipotent 1) w)]

/-! ## Conjugation -/

section Conjugation

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module R V]

/-- If `η(g⁻¹ u g) = θ(u)` on `U`, translation by `g⁻¹` maps `V_(U,θ)` onto `V_(U,η)`. -/
def conjugationMap (ρ : Representation R G V) (U : Subgroup G) (θ η : U →* Rˣ) (g : G)
    (hg : ∀ u : U, g⁻¹ * u.val * g ∈ U) (hη : ∀ u : U, η ⟨g⁻¹ * u.val * g, hg u⟩ = θ u) :
    Jacquet.Localization.Coinvariants ρ U θ →ₗ[R] Jacquet.Localization.Coinvariants ρ U η :=
  Jacquet.Localization.lift ρ U θ (Jacquet.Localization.mk ρ U η ∘ₗ ρ g⁻¹) (by
    intro u v
    change Jacquet.Localization.mk ρ U η (ρ g⁻¹ (ρ u v)) =
      (θ u : R) • Jacquet.Localization.mk ρ U η (ρ g⁻¹ v)
    have he : ρ g⁻¹ (ρ u v) = ρ (⟨g⁻¹ * u.val * g, hg u⟩ : U) (ρ g⁻¹ v) := by
      change ρ g⁻¹ (ρ u v) = ρ (g⁻¹ * u.val * g) (ρ g⁻¹ v)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
        mul_assoc, mul_inv_cancel, mul_one]
    rw [he, Jacquet.Localization.mk_apply_subgroup, hη])

theorem conjugationMap_surjective (ρ : Representation R G V) (U : Subgroup G)
    (θ η : U →* Rˣ) (g : G) (hg : ∀ u : U, g⁻¹ * u.val * g ∈ U)
    (hη : ∀ u : U, η ⟨g⁻¹ * u.val * g, hg u⟩ = θ u) :
    Function.Surjective (conjugationMap ρ U θ η g hg hη) := by
  intro x
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective ρ U η x
  refine ⟨Jacquet.Localization.mk ρ U θ (ρ g v), ?_⟩
  change Jacquet.Localization.mk ρ U η (ρ g⁻¹ (ρ g v)) = _
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- Finiteness passes from `V_(U,θ)` to `V_(U,η)` when `η(g⁻¹ u g) = θ(u)`. -/
theorem finite_coinvariants_of_conj (ρ : Representation R G V) (U : Subgroup G)
    (θ η : U →* Rˣ) (g : G) (hg : ∀ u : U, g⁻¹ * u.val * g ∈ U)
    (hη : ∀ u : U, η ⟨g⁻¹ * u.val * g, hg u⟩ = θ u)
    [Module.Finite R (Jacquet.Localization.Coinvariants ρ U θ)] :
    Module.Finite R (Jacquet.Localization.Coinvariants ρ U η) :=
  Module.Finite.of_surjective _ (conjugationMap_surjective ρ U θ η g hg hη)

end Conjugation

/-! ## Diagonal conjugation of upper-unipotent characters -/

theorem diagonalUnit_inv {m : ℕ} (d : Fin m → Fˣ) :
    (diagonalUnit d)⁻¹ = diagonalUnit d⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  apply Units.ext
  change Matrix.diagonal (fun i => (d i : F)) *
    Matrix.diagonal (fun i => (((d i)⁻¹ : Fˣ) : F)) = 1
  rw [Matrix.diagonal_mul_diagonal]
  simp

/-- If `η(u) = θ(t u t⁻¹)` for the diagonal matrix `t = diag(d)`, then finiteness passes
from `V_(U,θ)` to `V_(U,η)`. -/
theorem finite_coinvariants_of_diagonalConj {m : ℕ} {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GeneralLinear m F) V)
    (θ η : upperUnipotent m F →* ℂˣ) (d : Fin m → Fˣ)
    (hη : ∀ u, η u = θ (diagonalConj d u))
    [Module.Finite ℂ (Jacquet.Localization.Coinvariants ρ (upperUnipotent m F) θ)] :
    Module.Finite ℂ (Jacquet.Localization.Coinvariants ρ (upperUnipotent m F) η) := by
  have hg : ∀ u : upperUnipotent m F,
      (diagonalUnit d)⁻¹ * u.val * diagonalUnit d ∈ upperUnipotent m F := by
    intro u
    have h := diagonalUnit_conj_mem d⁻¹ u.property
    rwa [← diagonalUnit_inv, inv_inv] at h
  refine finite_coinvariants_of_conj ρ (upperUnipotent m F) θ η (diagonalUnit d) hg ?_
  intro u
  rw [hη]
  congr 1
  apply Subtype.ext
  rw [diagonalConj_val]
  change diagonalUnit d * ((diagonalUnit d)⁻¹ * u.val * diagonalUnit d) *
    (diagonalUnit d)⁻¹ = u.val
  group

end Langlands.Whittaker.UpperUnipotentCoinvariant
