import Langlands.BushnellKutzko.SplitStratumBlocks
import Langlands.BushnellKutzko.SplitTypeRefinement
import Langlands.BushnellKutzko.DiagonalPositiveSplitType
import Langlands.BushnellKutzko.SplitObstructionLattice
import Langlands.BushnellKutzko.UnitFiltrationQuotient
import Langlands.BushnellKutzko.AdditiveDualityProof

/-! # Jacquet nonvanishing for a split type of level `(x, x)`: the refinement in `Aut_F(V)`

The refinement argument of Bushnell–Kutzko (8.2.14)–(8.2.16) for the pair `(U^n(𝔄), ψ_b)`
attached to a split fundamental stratum `[𝔄, n, n−1, b]` with `n > 0` and
`gcd(n, e(𝔄)) = 1`, in the simplified form available when `E = F`. All statements are about
an arbitrary representation of `Aut_F(V)`; no topology is used.
-/

noncomputable section

open ValuativeRel
open scoped BigOperators

namespace Langlands.BushnellKutzko.SplitBlocks

universe uK uV uW uF

/-! ### Block unipotent subgroups -/

section BlockUnipotent

variable {K : Type uK} {V : Type uV} [Field K] [AddCommGroup V] [Module K V]

local notation "A" => Module.End K V
local notation "Aut" => (Module.End K V)ˣ

/-- The subgroup of units `u` with `u - 1 = e₁ (u - 1) e₂ ∈ P`, for an additive subgroup `P`
of `A`. When `e₂ e₁ = 0` these units form an abelian group. If moreover `e₁` and `e₂` are
idempotent, an element `x` of `A` satisfies `x = e₁ x e₂` exactly when `x ∈ e₁ A e₂`, so the
image of the group in `A` is `1 + (e₁ A e₂ ∩ P)`. -/
def blockUnipotent (e₁ e₂ : A) (h₂₁ : e₂ * e₁ = 0) (P : AddSubgroup A) : Subgroup Aut where
  carrier := {u | e₁ * ((u : A) - 1) * e₂ = (u : A) - 1 ∧ (u : A) - 1 ∈ P}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    have hprod : ((u : A) - 1) * ((v : A) - 1) = 0 := by
      rw [← hu, ← hv]
      calc e₁ * ((u : A) - 1) * e₂ * (e₁ * ((v : A) - 1) * e₂)
          = e₁ * ((u : A) - 1) * (e₂ * e₁) * ((v : A) - 1) * e₂ := by noncomm_ring
        _ = 0 := by rw [h₂₁]; noncomm_ring
    have heq : ((u * v : Aut) : A) - 1 = ((u : A) - 1) + ((v : A) - 1) := by
      have : ((u * v : Aut) : A) - 1 =
          ((u : A) - 1) + ((v : A) - 1) + ((u : A) - 1) * ((v : A) - 1) := by
        rw [Units.val_mul]
        noncomm_ring
      rw [this, hprod, add_zero]
    refine ⟨?_, ?_⟩
    · rw [heq, mul_add, add_mul, hu, hv]
    · rw [heq]
      exact add_mem hu' hv'
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    have hsq : ((u : A) - 1) * ((u : A) - 1) = 0 := by
      rw [← hu]
      calc e₁ * ((u : A) - 1) * e₂ * (e₁ * ((u : A) - 1) * e₂)
          = e₁ * ((u : A) - 1) * (e₂ * e₁) * ((u : A) - 1) * e₂ := by noncomm_ring
        _ = 0 := by rw [h₂₁]; noncomm_ring
    have hinv : ((u⁻¹ : Aut) : A) = 1 - ((u : A) - 1) := by
      have h1 : (u : A) * (1 - ((u : A) - 1)) = 1 := by
        have : (u : A) * (1 - ((u : A) - 1)) = 1 - ((u : A) - 1) * ((u : A) - 1) := by
          noncomm_ring
        rw [this, hsq, sub_zero]
      calc ((u⁻¹ : Aut) : A) = ((u⁻¹ : Aut) : A) * ((u : A) * (1 - ((u : A) - 1))) := by
            rw [h1, mul_one]
        _ = 1 - ((u : A) - 1) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    have hsub : ((u⁻¹ : Aut) : A) - 1 = -((u : A) - 1) := by
      rw [hinv]
      abel
    refine ⟨?_, ?_⟩
    · rw [hsub, mul_neg, neg_mul, hu]
    · rw [hsub]
      exact neg_mem hu'


theorem mem_blockUnipotent {e₁ e₂ : A} {h₂₁ : e₂ * e₁ = 0} {P : AddSubgroup A} {u : Aut} :
    u ∈ blockUnipotent e₁ e₂ h₂₁ P ↔
      e₁ * ((u : A) - 1) * e₂ = (u : A) - 1 ∧ (u : A) - 1 ∈ P :=
  Iff.rfl

theorem blockUnipotent_mono {e₁ e₂ : A} {h₂₁ : e₂ * e₁ = 0} {P Q : AddSubgroup A} (h : P ≤ Q) :
    blockUnipotent e₁ e₂ h₂₁ P ≤ blockUnipotent e₁ e₂ h₂₁ Q :=
  fun _ hu => ⟨hu.1, h hu.2⟩

/-- Any two elements of `1 + e₁ A e₂` commute. -/
theorem blockUnipotent_commute {e₁ e₂ : A} {h₂₁ : e₂ * e₁ = 0} {P Q : AddSubgroup A} {u v : Aut}
    (hu : u ∈ blockUnipotent e₁ e₂ h₂₁ P) (hv : v ∈ blockUnipotent e₁ e₂ h₂₁ Q) :
    u * v = v * u := by
  have hz : ∀ (x y : A), e₁ * x * e₂ * (e₁ * y * e₂) = 0 := fun x y => by
    calc e₁ * x * e₂ * (e₁ * y * e₂) = e₁ * x * (e₂ * e₁) * y * e₂ := by noncomm_ring
      _ = 0 := by rw [h₂₁]; noncomm_ring
  have h1 : ((u : A) - 1) * ((v : A) - 1) = 0 := by rw [← hu.1, ← hv.1]; exact hz _ _
  have h2 : ((v : A) - 1) * ((u : A) - 1) = 0 := by rw [← hu.1, ← hv.1]; exact hz _ _
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have : (u : A) * v - v * u = ((u : A) - 1) * ((v : A) - 1) - ((v : A) - 1) * ((u : A) - 1) := by
    noncomm_ring
  rw [h1, h2, sub_zero] at this
  exact sub_eq_zero.mp this

/-- The unit `1 + e₁ y e₂`, with inverse `1 - e₁ y e₂`. -/
def blockUnit (e₁ e₂ : A) (h₂₁ : e₂ * e₁ = 0) (y : A) : Aut where
  val := 1 + e₁ * y * e₂
  inv := 1 - e₁ * y * e₂
  val_inv := by
    have : e₁ * y * e₂ * (e₁ * y * e₂) = 0 := by
      calc e₁ * y * e₂ * (e₁ * y * e₂) = e₁ * y * (e₂ * e₁) * y * e₂ := by noncomm_ring
        _ = 0 := by rw [h₂₁]; noncomm_ring
    calc (1 + e₁ * y * e₂) * (1 - e₁ * y * e₂) = 1 - e₁ * y * e₂ * (e₁ * y * e₂) := by
          noncomm_ring
      _ = 1 := by rw [this, sub_zero]
  inv_val := by
    have : e₁ * y * e₂ * (e₁ * y * e₂) = 0 := by
      calc e₁ * y * e₂ * (e₁ * y * e₂) = e₁ * y * (e₂ * e₁) * y * e₂ := by noncomm_ring
        _ = 0 := by rw [h₂₁]; noncomm_ring
    calc (1 - e₁ * y * e₂) * (1 + e₁ * y * e₂) = 1 - e₁ * y * e₂ * (e₁ * y * e₂) := by
          noncomm_ring
      _ = 1 := by rw [this, sub_zero]

theorem blockUnit_val (e₁ e₂ : A) (h₂₁ : e₂ * e₁ = 0) (y : A) : ((blockUnit e₁ e₂ h₂₁ y : Aut) : A) =
    1 + e₁ * y * e₂ := rfl

theorem blockUnit_inv_val (e₁ e₂ : A) (h₂₁ : e₂ * e₁ = 0) (y : A) :
    (((blockUnit e₁ e₂ h₂₁ y)⁻¹ : Aut) : A) = 1 - e₁ * y * e₂ := rfl

theorem blockUnit_mem {e₁ e₂ : A} (h₂₁ : e₂ * e₁ = 0) (he₁ : e₁ * e₁ = e₁) (he₂ : e₂ * e₂ = e₂) (y : A) :
    blockUnit e₁ e₂ h₂₁ y ∈ blockUnipotent e₁ e₂ h₂₁ ⊤ := by
  refine ⟨?_, AddSubgroup.mem_top _⟩
  rw [blockUnit_val, add_sub_cancel_left]
  calc e₁ * (e₁ * y * e₂) * e₂ = (e₁ * e₁) * y * (e₂ * e₂) := by noncomm_ring
    _ = e₁ * y * e₂ := by rw [he₁, he₂]

end BlockUnipotent

/-! ### Filtration degrees of products -/

/-- A product of three filtered endomorphisms is filtered by the sum of the degrees. -/
theorem mul_mul_mem_endFiltration {O : Type*} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
    [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (𝓛 : LatticeChain O K V) {i j k l : ℤ} {a x c : Module.End K V}
    (ha : a ∈ 𝓛.endFiltration i) (hx : x ∈ 𝓛.endFiltration j) (hc : c ∈ 𝓛.endFiltration k)
    (hl : i + j + k = l) : a * x * c ∈ 𝓛.endFiltration l := by
  rw [← hl]
  exact 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration ha hx) hc

/-! ### Finite layers and unit groups of a lattice chain -/

section LocalField

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "Aut" => (Module.End F V)ˣ

/-- The additive quotient `𝔓^i / 𝔓^j`. -/
abbrev layerQuotient (𝓛 : LatticeChain 𝒪[F] F V) (i j : ℤ) :=
  (𝓛.endFiltration i) ⧸ (𝓛.endFiltration j).comap (𝓛.endFiltration i).subtype

/-- For `i ≤ j` the quotient `𝔓^i / 𝔓^j` is finite. -/
theorem finite_layerQuotient (𝓛 : LatticeChain 𝒪[F] F V) (i j : ℤ) (hij : i ≤ j) :
    Finite (layerQuotient 𝓛 i j) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hshift (a : ℤ) : 𝓂[F] • 𝓛.endFiltration a = 𝓛.endFiltration (a + 𝓛.period) := by
    rw [hπ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul,
      𝓛.endFiltration_add_period_eq_smul hπ]
  have hpow (k : ℕ) : 𝓂[F] ^ k • 𝓛.endFiltration i =
      𝓛.endFiltration (i + (k : ℤ) * 𝓛.period) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Submodule.mul_smul, ih, hshift]
      congr 1
      push_cast
      ring
  let k := (j - i).toNat
  let I : Ideal 𝒪[F] := 𝓂[F] ^ k
  have hI : I • 𝓛.endFiltration i ≤ 𝓛.endFiltration j := by
    change 𝓂[F] ^ k • 𝓛.endFiltration i ≤ _
    rw [hpow]
    apply 𝓛.endFiltration_antitone
    have hk : (k : ℤ) = j - i := Int.toNat_of_nonneg (by omega)
    have hle : (k : ℤ) * 1 ≤ (k : ℤ) * 𝓛.period :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast 𝓛.period_pos) (Int.natCast_nonneg k)
    omega
  have hann : Module.IsTorsionBySet 𝒪[F] (layerQuotient 𝓛 i j) (I : Set 𝒪[F]) :=
    (Module.isTorsionBySet_quotient_iff _ _).mpr fun x a ha =>
      hI (Submodule.smul_mem_smul ha x.property)
  let := hann.module
  have : IsScalarTower 𝒪[F] (𝒪[F] ⧸ I) (layerQuotient 𝓛 i j) :=
    hann.isScalarTower
  have : Module.Finite 𝒪[F] (𝓛.endFiltration i) :=
    Module.Finite.iff_fg.mpr (𝓛.fg_endFiltration i)
  have : Finite (𝒪[F] ⧸ 𝓂[F]) := inferInstanceAs (Finite 𝓀[F])
  have : Finite (𝒪[F] ⧸ I) := Ideal.finite_quotient_pow (IsNoetherian.noetherian 𝓂[F]) k
  have : Module.Finite (𝒪[F] ⧸ I) (layerQuotient 𝓛 i j) :=
    Module.Finite.of_restrictScalars_finite 𝒪[F] _ _
  exact Module.finite_of_finite (𝒪[F] ⧸ I)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- For `m ≥ 1`, a unit `g` with `g - 1 ∈ 𝔓^m` lies in `U^m(𝔄)`. -/
theorem mem_unitFiltration_of_sub_one_mem (𝓛 : LatticeChain 𝒪[F] F V) {m : ℕ} (hm : 1 ≤ m)
    {g : Aut} (hg : (g : A) - 1 ∈ 𝓛.endFiltration m) : g ∈ 𝓛.unitFiltration m := by
  obtain ⟨g', hg', hg'eq⟩ := 𝓛.exists_mem_unitFiltration hm hg
  have : g' = g := Units.ext (by rw [hg'eq]; abel)
  exact this ▸ hg'

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A unit `g` with `g, g⁻¹ ∈ 𝔄` normalizes `U^m(𝔄)` for `m ≥ 1`. -/
theorem conj_mem_unitFiltration (𝓛 : LatticeChain 𝒪[F] F V) {m : ℕ} (hm : 1 ≤ m) {g k : Aut}
    (hg : (g : A) ∈ 𝓛.endFiltration 0) (hg' : ((g⁻¹ : Aut) : A) ∈ 𝓛.endFiltration 0)
    (hk : k ∈ 𝓛.unitFiltration m) : g * k * g⁻¹ ∈ 𝓛.unitFiltration m := by
  apply mem_unitFiltration_of_sub_one_mem 𝓛 hm
  have : ((g * k * g⁻¹ : Aut) : A) - 1 = (g : A) * ((k : A) - 1) * ((g⁻¹ : Aut) : A) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [this]
  simpa using 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hg hk.2.2) hg'

/-- `ψ_F(tr x) = 1` for `x ∈ 𝔓`. -/
theorem traceCharacter_eq_one (𝓛 : LatticeChain 𝒪[F] F V) {ψF : AddChar F ℂ}
    (hψ : IsBKAdditiveCharacter ψF) {x : A} (hx : x ∈ 𝓛.endFiltration 1) :
    traceCharacter ψF x = 1 := by
  obtain ⟨a, ha, h⟩ := 𝓛.trace_mem_maximalIdealInField hx
  rw [traceCharacter_apply, ← h]
  exact hψ.1 a ha

/-- The character `y ↦ ψ_A(e₁ y e₂ w)` of `𝔓⁰/𝔓¹`, for `e₁, e₂, w ∈ 𝔄`. -/
def blockCharacter (𝓛 : LatticeChain 𝒪[F] F V) {ψF : AddChar F ℂ}
    (hψ : IsBKAdditiveCharacter ψF) {e₁ e₂ w : A} (he₁ : e₁ ∈ 𝓛.endFiltration 0)
    (he₂ : e₂ ∈ 𝓛.endFiltration 0) (hw : w ∈ 𝓛.endFiltration 0) :
    AddChar (layerQuotient 𝓛 0 1) ℂ :=
  let ψ := (traceCharacter ψF).compAddMonoidHom
    ((AddMonoidHom.mulRight w).comp ((AddMonoidHom.mulRight e₂).comp
      ((AddMonoidHom.mulLeft e₁).comp (𝓛.endFiltration 0).subtype.toAddMonoidHom)))
  AddChar.toAddMonoidHomEquiv.symm <|
    QuotientAddGroup.lift ((𝓛.endFiltration 1).comap (𝓛.endFiltration 0).subtype).toAddSubgroup
      ψ.toAddMonoidHom (fun y hy => by
        change traceCharacter ψF (e₁ * (y : A) * e₂ * w) = 1
        exact traceCharacter_eq_one 𝓛 hψ
          (mul_mul_mem_endFiltration 𝓛 (𝓛.mul_mem_endFiltration he₁ hy) he₂ hw (by norm_num)))

theorem blockCharacter_mk (𝓛 : LatticeChain 𝒪[F] F V) {ψF : AddChar F ℂ}
    (hψ : IsBKAdditiveCharacter ψF) {e₁ e₂ w : A} (he₁ : e₁ ∈ 𝓛.endFiltration 0)
    (he₂ : e₂ ∈ 𝓛.endFiltration 0) (hw : w ∈ 𝓛.endFiltration 0) (y : 𝓛.endFiltration 0) :
    blockCharacter 𝓛 hψ he₁ he₂ hw (Submodule.Quotient.mk y) =
      traceCharacter ψF (e₁ * (y : A) * e₂ * w) :=
  rfl

/-- For `ψ_F` trivial on `𝔭_F` and nontrivial on `𝔬_F`, the character `y ↦ ψ_A(e₁ y e₂ w)` of
`𝔓⁰/𝔓¹` is trivial exactly when `e₂ w e₁ ∈ 𝔓`. -/
theorem blockCharacter_eq_zero_iff (𝓛 : LatticeChain 𝒪[F] F V) {ψF : AddChar F ℂ}
    (hψ : IsBKAdditiveCharacter ψF) {e₁ e₂ w : A} (he₁ : e₁ ∈ 𝓛.endFiltration 0)
    (he₂ : e₂ ∈ 𝓛.endFiltration 0) (hw : w ∈ 𝓛.endFiltration 0) :
    blockCharacter 𝓛 hψ he₁ he₂ hw = 0 ↔ e₂ * w * e₁ ∈ 𝓛.endFiltration 1 := by
  have hcyc : ∀ y : A, LinearMap.trace F V (e₁ * y * e₂ * w) =
      LinearMap.trace F V (e₂ * w * e₁ * y) := fun y => by
    rw [show e₁ * y * e₂ * w = (e₁ * y) * (e₂ * w) by noncomm_ring,
      LinearMap.trace_mul_comm, show e₂ * w * (e₁ * y) = e₂ * w * e₁ * y by noncomm_ring]
  constructor
  · intro h0
    have hdual := (additiveDuality F V 𝓛 ψF hψ.1 hψ.2).1 0
    have hmem : e₂ * w * e₁ ∈ additiveDual (traceCharacter ψF)
        (𝓛.endFiltration 0 : Set A) := by
      intro s hs
      have h := AddChar.ext_iff.mp h0 (Submodule.Quotient.mk ⟨s, hs⟩)
      rw [blockCharacter_mk, AddChar.zero_apply] at h
      rw [traceCharacter_apply, ← hcyc]
      exact h
    rw [hdual] at hmem
    simpa using hmem
  · intro h1
    ext q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [blockCharacter_mk, AddChar.zero_apply, traceCharacter_apply, hcyc,
      ← traceCharacter_apply]
    exact traceCharacter_eq_one 𝓛 hψ (by simpa using 𝓛.mul_mem_endFiltration h1 y.2)

end LocalField

/-! ### The shift element of the block data -/

namespace SplitBlockData

variable {O : Type*} {K : Type uK} {V : Type uV} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  {S : Stratum O K V} (D : SplitBlockData S)

local notation "A" => Module.End K V
local notation "Aut" => (Module.End K V)ˣ

theorem e₂_mul_e₁ : D.e₂ * D.e₁ = 0 := by
  have h1 : D.e₁ * D.e₁ = D.e₁ := by
    calc D.e₁ * D.e₁ = D.e₁ * (D.e₁ + D.e₂) := by rw [mul_add, D.mul_eq, add_zero]
      _ = D.e₁ := by rw [D.add_eq, mul_one]
  calc D.e₂ * D.e₁ = (D.e₁ + D.e₂) * D.e₁ - D.e₁ * D.e₁ := by noncomm_ring
    _ = 0 := by rw [D.add_eq, one_mul, h1, sub_self]

theorem e₁_mul_e₁ : D.e₁ * D.e₁ = D.e₁ := by
  calc D.e₁ * D.e₁ = D.e₁ * (D.e₁ + D.e₂) := by rw [mul_add, D.mul_eq, add_zero]
    _ = D.e₁ := by rw [D.add_eq, mul_one]

theorem e₂_mul_e₂ : D.e₂ * D.e₂ = D.e₂ := by
  calc D.e₂ * D.e₂ = (D.e₁ + D.e₂) * D.e₂ := by rw [add_mul, D.mul_eq, zero_add]
    _ = D.e₂ := by rw [D.add_eq, one_mul]

theorem ζ_mul_e₂ : D.ζ * D.e₂ = 0 := by
  rw [← D.ζ_mul_e₁, mul_assoc, D.mul_eq, mul_zero]

theorem e₂_mul_ζ : D.e₂ * D.ζ = 0 := by
  rw [← D.e₁_mul_ζ, ← mul_assoc, D.e₂_mul_e₁, zero_mul]

theorem ζ'_mul_e₂ : D.ζ' * D.e₂ = 0 := by
  rw [← D.ζ'_mul_e₁, mul_assoc, D.mul_eq, mul_zero]

theorem e₂_mul_ζ' : D.e₂ * D.ζ' = 0 := by
  rw [← D.e₁_mul_ζ', ← mul_assoc, D.e₂_mul_e₁, zero_mul]

/-- The unit `ζ + e₂`, with inverse `ζ' + e₂`: the element `ζ` of BK93 (8.2.9). -/
def shift : Aut where
  val := D.ζ + D.e₂
  inv := D.ζ' + D.e₂
  val_inv := by
    calc (D.ζ + D.e₂) * (D.ζ' + D.e₂) =
        D.ζ * D.ζ' + D.ζ * D.e₂ + D.e₂ * D.ζ' + D.e₂ * D.e₂ := by noncomm_ring
      _ = 1 := by rw [D.ζ_mul_ζ', D.ζ_mul_e₂, D.e₂_mul_ζ', D.e₂_mul_e₂, add_zero, add_zero,
          D.add_eq]
  inv_val := by
    calc (D.ζ' + D.e₂) * (D.ζ + D.e₂) =
        D.ζ' * D.ζ + D.ζ' * D.e₂ + D.e₂ * D.ζ + D.e₂ * D.e₂ := by noncomm_ring
      _ = 1 := by rw [D.ζ'_mul_ζ, D.ζ'_mul_e₂, D.e₂_mul_ζ, D.e₂_mul_e₂, add_zero, add_zero,
          D.add_eq]

theorem shift_val : ((D.shift : Aut) : A) = D.ζ + D.e₂ := rfl

theorem shift_inv_val : ((D.shift⁻¹ : Aut) : A) = D.ζ' + D.e₂ := rfl

theorem shift_conj_sub_one (k : Aut) :
    ((D.shift * k * D.shift⁻¹ : Aut) : A) - 1 =
      (D.ζ + D.e₂) * ((k : A) - 1) * (D.ζ' + D.e₂) := by
  rw [Units.val_mul, Units.val_mul, ← shift_val, ← shift_inv_val, mul_sub, sub_mul, mul_one,
    Units.mul_inv]

/-- On the block `e₁ A e₂`, conjugation by `ζ + e₂` is left multiplication by `ζ`. -/
theorem shift_conj_block {y : A} (hy : D.e₁ * y * D.e₂ = y) :
    (D.ζ + D.e₂) * y * (D.ζ' + D.e₂) = D.ζ * y := by
  have h1 : (D.ζ + D.e₂) * D.e₁ = D.ζ := by rw [add_mul, D.ζ_mul_e₁, D.e₂_mul_e₁, add_zero]
  have h2 : D.e₂ * (D.ζ' + D.e₂) = D.e₂ := by rw [mul_add, D.e₂_mul_ζ', D.e₂_mul_e₂, zero_add]
  rw [← hy]
  calc (D.ζ + D.e₂) * (D.e₁ * y * D.e₂) * (D.ζ' + D.e₂)
      = ((D.ζ + D.e₂) * D.e₁) * y * (D.e₂ * (D.ζ' + D.e₂)) := by noncomm_ring
    _ = D.ζ * (D.e₁ * y * D.e₂) := by
      rw [h1, h2, ← mul_assoc, ← mul_assoc, D.ζ_mul_e₁]

theorem shift_comm_b : (D.ζ + D.e₂) * S.b = S.b * (D.ζ + D.e₂) := by
  rw [add_mul, mul_add, D.ζ_comm.eq, D.e₂_comm.eq]

theorem shift_inv_comm_b : (D.ζ' + D.e₂) * S.b = S.b * (D.ζ' + D.e₂) := by
  rw [add_mul, mul_add, D.ζ'_comm.eq, D.e₂_comm.eq]

/-- Conjugation by `ζ + e₂` keeps `x ∈ 𝔓^m` in `𝔓^m` exactly when `e₂ x e₁ ∈ 𝔓^{m+1}`. -/
theorem shift_conj_mem_iff {m : ℤ} {x : A} (hx : x ∈ S.chain.endFiltration m) :
    (D.ζ + D.e₂) * x * (D.ζ' + D.e₂) ∈ S.chain.endFiltration m ↔
      D.e₂ * x * D.e₁ ∈ S.chain.endFiltration (m + 1) := by
  have h₁ : D.ζ * x * D.ζ' ∈ S.chain.endFiltration m :=
    mul_mul_mem_endFiltration S.chain D.ζ_mem hx D.ζ'_mem (by ring)
  have h₂ : D.ζ * x * D.e₂ ∈ S.chain.endFiltration m :=
    S.chain.endFiltration_antitone (by omega : m ≤ 1 + m + 0)
      (mul_mul_mem_endFiltration S.chain D.ζ_mem hx D.e₂_mem rfl)
  have h₄ : D.e₂ * x * D.e₂ ∈ S.chain.endFiltration m :=
    mul_mul_mem_endFiltration S.chain D.e₂_mem hx D.e₂_mem (by ring)
  have hexp : (D.ζ + D.e₂) * x * (D.ζ' + D.e₂) =
      D.ζ * x * D.ζ' + D.ζ * x * D.e₂ + D.e₂ * x * D.ζ' + D.e₂ * x * D.e₂ := by noncomm_ring
  have hiff : (D.ζ + D.e₂) * x * (D.ζ' + D.e₂) ∈ S.chain.endFiltration m ↔
      D.e₂ * x * D.ζ' ∈ S.chain.endFiltration m := by
    rw [hexp]
    constructor
    · intro h
      have : D.e₂ * x * D.ζ' = (D.ζ * x * D.ζ' + D.ζ * x * D.e₂ + D.e₂ * x * D.ζ' +
          D.e₂ * x * D.e₂) - D.ζ * x * D.ζ' - D.ζ * x * D.e₂ - D.e₂ * x * D.e₂ := by abel
      rw [this]
      exact sub_mem (sub_mem (sub_mem h h₁) h₂) h₄
    · intro h
      exact add_mem (add_mem (add_mem h₁ h₂) h) h₄
  rw [hiff]
  constructor
  · intro h
    have : D.e₂ * x * D.e₁ = D.e₂ * x * D.ζ' * D.ζ := by rw [mul_assoc _ D.ζ', D.ζ'_mul_ζ]
    rw [this]
    exact S.chain.mul_mem_endFiltration h D.ζ_mem
  · intro h
    have : D.e₂ * x * D.ζ' = D.e₂ * x * D.e₁ * D.ζ' := by rw [mul_assoc _ D.e₁, D.e₁_mul_ζ']
    rw [this]
    simpa using S.chain.mul_mem_endFiltration h D.ζ'_mem

end SplitBlockData

/-! ### Isotypic subspaces and conjugation -/

section Generic

variable {G : Type*} [Group G] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The `ϑ`-isotypic subspace `{w | ρ(k) w = ϑ(k) w for all k ∈ K}` of a representation `ρ`,
for a character `ϑ` of a subgroup `K`. -/
def characterSubspace (ρ : Representation ℂ G W) (K : Subgroup G) (ϑ : K →* ℂˣ) :
    Submodule ℂ W where
  carrier := {w | ∀ k : K, ρ k w = (ϑ k : ℂ) • w}
  add_mem' := by
    intro v w hv hw k
    rw [map_add, hv k, hw k, smul_add]
  zero_mem' := by
    intro k
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro c w hw k
    rw [map_smul, hw k, smul_comm]

theorem mem_characterSubspace {ρ : Representation ℂ G W} {K : Subgroup G} {ϑ : K →* ℂˣ}
    {w : W} : w ∈ characterSubspace ρ K ϑ ↔ ∀ k : K, ρ k w = (ϑ k : ℂ) • w :=
  Iff.rfl

/-- Conjugation by an element `g` normalizing `K`, as an endomorphism of `K`. -/
def conjEndo (K : Subgroup G) (g : G) (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : K →* K where
  toFun k := ⟨g * k * g⁻¹, hg k k.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjEndo_val (K : Subgroup G) (g : G) (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K) (k : K) :
    ((conjEndo K g hg k : K) : G) = g * k * g⁻¹ :=
  rfl

end Generic

/-! ### The refinement step -/

section Refinement

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local notation "A" => Module.End F V
local notation "Aut" => (Module.End F V)ˣ

variable {S : Stratum 𝒪[F] F V} (D : SplitBlockData S)

namespace SplitBlockData

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockUnit_mem_order {y : A} (hy : y ∈ S.chain.endFiltration 0) :
    ((blockUnit D.e₁ D.e₂ D.e₂_mul_e₁ y : Aut) : A) ∈ S.chain.endFiltration 0 ∧
      (((blockUnit D.e₁ D.e₂ D.e₂_mul_e₁ y)⁻¹ : Aut) : A) ∈ S.chain.endFiltration 0 := by
  have h : D.e₁ * y * D.e₂ ∈ S.chain.endFiltration 0 :=
    mul_mul_mem_endFiltration S.chain D.e₁_mem hy D.e₂_mem (by ring)
  have h1 : (1 : A) ∈ S.chain.endFiltration 0 := S.chain.order.one_mem
  exact ⟨add_mem h1 h, sub_mem h1 h⟩

variable {m : ℕ} (hm1 : 1 ≤ m)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hm1 in
theorem blockUnit_conj_mem {y : A} (hy : y ∈ S.chain.endFiltration 0) :
    ∀ k ∈ S.chain.unitFiltration m, blockUnit D.e₁ D.e₂ D.e₂_mul_e₁ y * k *
      (blockUnit D.e₁ D.e₂ D.e₂_mul_e₁ y)⁻¹ ∈ S.chain.unitFiltration m :=
  fun _ hk => conj_mem_unitFiltration S.chain hm1 (D.blockUnit_mem_order hy).1
    (by simpa using (D.blockUnit_mem_order hy).2) hk

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hm1 in
theorem blockUnit_inv_conj_mem {y : A} (hy : y ∈ S.chain.endFiltration 0) :
    ∀ k ∈ S.chain.unitFiltration m, (blockUnit D.e₁ D.e₂ D.e₂_mul_e₁ y)⁻¹ * k *
      (blockUnit D.e₁ D.e₂ D.e₂_mul_e₁ y)⁻¹⁻¹ ∈ S.chain.unitFiltration m :=
  fun _ hk => conj_mem_unitFiltration S.chain hm1 (D.blockUnit_mem_order hy).2
    (by simpa using (D.blockUnit_mem_order hy).1) hk

variable {ψF : AddChar F ℂ} (ϑ : S.chain.unitFiltration m →* ℂˣ)
  (hϑ : ∀ g, (ϑ g : ℂ) = elementCharacter (traceCharacter ψF) S.b g)

/-- The character `k ↦ ϑ(g k g⁻¹)` of `U^m(𝔄)` for `g = 1 + e₁ y e₂`. -/
def conjChar (y : S.chain.endFiltration 0) : S.chain.unitFiltration m →* ℂˣ :=
  ϑ.comp (conjEndo _ (blockUnit D.e₁ D.e₂ D.e₂_mul_e₁ y) (D.blockUnit_conj_mem hm1 y.2))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϑ in
/-- `ϑ(g k g⁻¹) ψ_A(e₁ y e₂ (b x − x b)) = ϑ(k)` for `g = 1 + e₁ y e₂` and `k = 1 + x`. -/
theorem conjChar_mul (y : S.chain.endFiltration 0) (k : S.chain.unitFiltration m) :
    (D.conjChar hm1 ϑ y k : ℂ) * traceCharacter ψF (D.e₁ * (y : A) * D.e₂ *
      (S.b * (((k : Aut) : A) - 1) - (((k : Aut) : A) - 1) * S.b)) = ϑ k := by
  set Y := D.e₁ * (y : A) * D.e₂ with hYdef
  set x := ((k : Aut) : A) - 1 with hx
  have hY2 : Y * Y = 0 := by
    rw [hYdef]
    calc D.e₁ * (y : A) * D.e₂ * (D.e₁ * (y : A) * D.e₂)
        = D.e₁ * (y : A) * (D.e₂ * D.e₁) * (y : A) * D.e₂ := by noncomm_ring
      _ = 0 := by rw [D.e₂_mul_e₁]; noncomm_ring
  have hYbY : Y * S.b * Y = 0 := by
    rw [hYdef]
    calc D.e₁ * (y : A) * D.e₂ * S.b * (D.e₁ * (y : A) * D.e₂)
        = D.e₁ * (y : A) * S.b * (D.e₂ * D.e₁) * (y : A) * D.e₂ := by
          rw [show D.e₁ * (y : A) * D.e₂ * S.b * (D.e₁ * (y : A) * D.e₂) =
            D.e₁ * (y : A) * (D.e₂ * S.b) * D.e₁ * (y : A) * D.e₂ by noncomm_ring, D.e₂_comm.eq]
          noncomm_ring
      _ = 0 := by rw [D.e₂_mul_e₁]; noncomm_ring
  have hconj : ((D.conjChar hm1 ϑ y k : ℂ)) =
      traceCharacter ψF (S.b * ((1 + Y) * x * (1 - Y))) := by
    rw [conjChar, MonoidHom.comp_apply, hϑ, elementCharacter_apply, conjEndo_val,
      Units.val_mul, Units.val_mul, blockUnit_val, blockUnit_inv_val]
    congr 2
    have : (1 + Y) * ((k : Aut) : A) * (1 - Y) - 1 =
        (1 + Y) * (((k : Aut) : A) - 1) * (1 - Y) + ((1 + Y) * (1 - Y) - 1) := by noncomm_ring
    rw [this, show (1 + Y) * (1 - Y) = 1 - Y * Y by noncomm_ring, hY2, sub_zero, sub_self,
      add_zero]
  rw [hconj, hϑ, elementCharacter_apply, ← AddChar.map_add_eq_mul, traceCharacter_apply,
    traceCharacter_apply, map_add]
  congr 1
  have h1 : LinearMap.trace F V (S.b * ((1 + Y) * x * (1 - Y))) =
      LinearMap.trace F V ((1 - Y) * (S.b * (1 + Y) * x)) := by
    rw [LinearMap.trace_mul_comm F (1 - Y)]
    congr 1
  have h2 : (1 - Y) * (S.b * (1 + Y) * x) = S.b * x + S.b * Y * x - Y * S.b * x := by
    have : (1 - Y) * (S.b * (1 + Y) * x) =
        S.b * x + S.b * Y * x - Y * S.b * x - (Y * S.b * Y) * x := by noncomm_ring
    rw [this, hYbY, zero_mul, sub_zero]
  have h3 : LinearMap.trace F V (Y * x * S.b) = LinearMap.trace F V (S.b * Y * x) := by
    rw [LinearMap.trace_mul_comm F (Y * x) S.b, ← mul_assoc]
  have h4 : Y * (S.b * x - x * S.b) = Y * S.b * x - Y * x * S.b := by noncomm_ring
  rw [h1, h2, h4]
  simp only [map_sub, map_add]
  rw [h3]
  ring

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϑ in
/-- Conjugation by the shift element preserves `ϑ` wherever both sides are defined. -/
theorem theta_shift_conj (k : S.chain.unitFiltration m)
    (hk : D.shift * k * D.shift⁻¹ ∈ S.chain.unitFiltration m) :
    ϑ ⟨D.shift * k * D.shift⁻¹, hk⟩ = ϑ k := by
  apply Units.ext
  rw [hϑ, hϑ, elementCharacter_apply, elementCharacter_apply, traceCharacter_apply,
    traceCharacter_apply]
  congr 1
  change LinearMap.trace F V (S.b * (((D.shift * k * D.shift⁻¹ : Aut) : A) - 1)) = _
  rw [D.shift_conj_sub_one]
  have hZZ : (D.ζ' + D.e₂) * (D.ζ + D.e₂) = 1 := D.shift.inv_val
  rw [show S.b * ((D.ζ + D.e₂) * (((k : Aut) : A) - 1) * (D.ζ' + D.e₂)) =
      (S.b * (D.ζ + D.e₂) * (((k : Aut) : A) - 1)) * (D.ζ' + D.e₂) by noncomm_ring,
    LinearMap.trace_mul_comm,
    show (D.ζ' + D.e₂) * (S.b * (D.ζ + D.e₂) * (((k : Aut) : A) - 1)) =
      ((D.ζ' + D.e₂) * S.b) * (D.ζ + D.e₂) * (((k : Aut) : A) - 1) by noncomm_ring,
    D.shift_inv_comm_b, mul_assoc S.b, hZZ, mul_one]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hm1 in
/-- For `k = 1 + x ∈ U^n(𝔄)`, the conjugate `ζ k ζ⁻¹` lies in `U^n(𝔄)` exactly when
`e₂ (b x − x b) e₁ ∈ 𝔓`. -/
theorem shift_conj_mem_unitFiltration_iff (hm : (m : ℤ) = S.n)
    (hb : S.b ∈ S.chain.endFiltration (-S.n)) (k : S.chain.unitFiltration m) :
    D.shift * k * D.shift⁻¹ ∈ S.chain.unitFiltration m ↔
      D.e₂ * (S.b * (((k : Aut) : A) - 1) - (((k : Aut) : A) - 1) * S.b) * D.e₁ ∈
        S.chain.endFiltration 1 := by
  set x := ((k : Aut) : A) - 1 with hxdef
  have hx : x ∈ S.chain.endFiltration S.n := by rw [← hm]; exact k.2.2.2
  have hcomm : D.e₂ * (S.b * x - x * S.b) * D.e₁ =
      S.b * (D.e₂ * x * D.e₁) - (D.e₂ * x * D.e₁) * S.b := by
    calc D.e₂ * (S.b * x - x * S.b) * D.e₁
        = (D.e₂ * S.b) * x * D.e₁ - D.e₂ * x * (S.b * D.e₁) := by noncomm_ring
      _ = S.b * (D.e₂ * x * D.e₁) - (D.e₂ * x * D.e₁) * S.b := by
        rw [D.e₂_comm.eq, ← D.e₁_comm.eq]
        noncomm_ring
  rw [hcomm]
  constructor
  · intro h
    have h1 : (D.ζ + D.e₂) * x * (D.ζ' + D.e₂) ∈ S.chain.endFiltration S.n := by
      rw [← D.shift_conj_sub_one, ← hm]
      exact h.2.2
    have h2 := (D.shift_conj_mem_iff hx).mp h1
    have h3 := S.chain.mul_mem_endFiltration hb h2
    have h4 := S.chain.mul_mem_endFiltration h2 hb
    rw [show -S.n + (S.n + 1) = 1 by ring] at h3
    rw [show S.n + 1 + -S.n = 1 by ring] at h4
    exact sub_mem h3 h4
  · intro h
    have h21 : D.e₂ * x * D.e₁ ∈ S.chain.endFiltration (S.n + 1) := by
      apply D.inj₂₁ S.n
      · exact mul_mul_mem_endFiltration S.chain D.e₂_mem hx D.e₁_mem (by ring)
      · rw [show D.e₂ * (D.e₂ * x * D.e₁) * D.e₁ = (D.e₂ * D.e₂) * x * (D.e₁ * D.e₁) by
          noncomm_ring, D.e₂_mul_e₂, D.e₁_mul_e₁]
      · rw [show S.n - S.n + 1 = (1 : ℤ) by ring]
        exact h
    have h1 := (D.shift_conj_mem_iff hx).mpr h21
    apply mem_unitFiltration_of_sub_one_mem S.chain hm1
    rw [D.shift_conj_sub_one, hm]
    exact h1

include hm1 hϑ in
/-- **The refinement for a split type of level `(x, x)`.** Let `S = [𝔄, n, r, b]` be a stratum
with `n = m ≥ 1`, `b ∈ 𝔓^{−n}` and block data `(e₁, e₂, ζ, ζ')`, which exist for a split
fundamental stratum with `gcd(n, e(𝔄)) = 1`. Let `ψ_F` be trivial on `𝔭_F` and nontrivial on
`𝔬_F`, let `ϑ` be the character `ψ_b` of `U^n(𝔄)` for `ψ_A = ψ_F ∘ tr`, and
let `ρ` be a representation of `Aut_F(V)` whose `ϑ`-isotypic subspace is finite-dimensional
and not contained in the coinvariant relations of `ker ϑ`. Then this subspace is not contained
in the coinvariant relations of `U = 1 + e₁ A e₂`. -/
theorem not_le_relations_blockUnipotent (hm : (m : ℤ) = S.n)
    (hb : S.b ∈ S.chain.endFiltration (-S.n)) (hψ : IsBKAdditiveCharacter ψF)
    (ρ : Representation ℂ Aut W)
    [FiniteDimensional ℂ (characterSubspace ρ (S.chain.unitFiltration m) ϑ)]
    (h₀ : ¬ characterSubspace ρ (S.chain.unitFiltration m) ϑ ≤
      Jacquet.relations ρ (ϑ.ker.map (S.chain.unitFiltration m).subtype)) :
    ¬ characterSubspace ρ (S.chain.unitFiltration m) ϑ ≤
      Jacquet.relations ρ (blockUnipotent D.e₁ D.e₂ D.e₂_mul_e₁ ⊤) := by
  classical
  let K := S.chain.unitFiltration m
  let M : ℤ → Subgroup Aut := fun j =>
    blockUnipotent D.e₁ D.e₂ D.e₂_mul_e₁ (S.chain.endFiltration j).toAddSubgroup
  have hanti : Antitone M := fun i j hij =>
    blockUnipotent_mono (fun x hx => (Submodule.mem_toAddSubgroup _).mpr
      (S.chain.endFiltration_antitone hij ((Submodule.mem_toAddSubgroup _).mp hx)))
  have hexh : ∀ u ∈ blockUnipotent D.e₁ D.e₂ D.e₂_mul_e₁ ⊤, ∃ j, u ∈ M j := by
    intro u hu
    obtain ⟨j, hj⟩ := SplitObstruction.exists_mem_endFiltration S.chain ((u : A) - 1)
    exact ⟨j, hu.1, (Submodule.mem_toAddSubgroup _).mpr hj⟩
  refine Jacquet.not_le_relations_of_refinement ρ _ M hanti hexh
    (characterSubspace ρ (S.chain.unitFiltration m) ϑ) S.n ?_ ?_
  · -- the starting level: `ϑ` is trivial on `1 + (e₁ A e₂ ∩ 𝔓^n)`
    intro hle
    apply h₀
    refine hle.trans (Jacquet.relations_mono ρ ?_)
    intro u hu
    have hu2 : (u : A) - 1 ∈ S.chain.endFiltration S.n := (Submodule.mem_toAddSubgroup _).mp hu.2
    have huK : u ∈ K := mem_unitFiltration_of_sub_one_mem S.chain hm1 (by rw [hm]; exact hu2)
    refine ⟨⟨u, huK⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [hϑ, elementCharacter_apply, Units.val_one, traceCharacter_apply]
    change ψF (LinearMap.trace F V (S.b * ((u : A) - 1))) = 1
    have htr : LinearMap.trace F V (S.b * ((u : A) - 1)) = 0 := by
      rw [← hu.1, show S.b * (D.e₁ * ((u : A) - 1) * D.e₂) =
          (S.b * D.e₁ * ((u : A) - 1)) * D.e₂ by noncomm_ring, LinearMap.trace_mul_comm,
        show D.e₂ * (S.b * D.e₁ * ((u : A) - 1)) = (D.e₂ * S.b) * D.e₁ * ((u : A) - 1) by
          noncomm_ring, D.e₂_comm.eq, mul_assoc S.b, D.e₂_mul_e₁, mul_zero, zero_mul, map_zero]
    rw [htr, AddChar.map_zero_eq_one]
  · -- the refinement step from `M j` to `M (j - 1)`
    intro j hj
    obtain ⟨v₁, hv₁P, hv₁M⟩ := Set.not_subset.mp hj
    have hv₁ : ∀ k : K, ρ k v₁ = (ϑ k : ℂ) • v₁ := hv₁P
    set z := D.shift with hz
    have hzM : ∀ n ∈ M (j - 1), z * n * z⁻¹ ∈ M j := by
      intro n hn
      have hn2 : (n : A) - 1 ∈ S.chain.endFiltration (j - 1) :=
        (Submodule.mem_toAddSubgroup _).mp hn.2
      have hblock : (D.ζ + D.e₂) * ((n : A) - 1) * (D.ζ' + D.e₂) = D.ζ * ((n : A) - 1) :=
        D.shift_conj_block hn.1
      have hye : ((n : A) - 1) * D.e₂ = (n : A) - 1 := by
        conv_lhs => rw [← hn.1]
        rw [mul_assoc, D.e₂_mul_e₂]
        exact hn.1
      refine ⟨?_, ?_⟩
      · rw [D.shift_conj_sub_one, hblock, show D.e₁ * (D.ζ * ((n : A) - 1)) * D.e₂ =
          (D.e₁ * D.ζ) * (((n : A) - 1) * D.e₂) by noncomm_ring, D.e₁_mul_ζ, hye]
      · rw [D.shift_conj_sub_one, hblock]
        have := S.chain.mul_mem_endFiltration D.ζ_mem hn2
        rw [show (1 : ℤ) + (j - 1) = j by ring] at this
        exact (Submodule.mem_toAddSubgroup _).mpr this
    set v₂ := ρ z⁻¹ v₁ with hv₂
    have hv₂M : v₂ ∉ Jacquet.relations ρ (M (j - 1)) := by
      intro hmem
      have h := Jacquet.apply_mem_relations ρ z hzM hmem
      rw [hv₂, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] at h
      exact hv₁M h
    -- the intermediate group `K ∩ ζ⁻¹ K ζ`
    let 𝒦 : Subgroup Aut := K ⊓ K.comap (MulAut.conj z).toMonoidHom
    have hmem𝒦 : ∀ k : Aut, k ∈ 𝒦 ↔ k ∈ K ∧ z * k * z⁻¹ ∈ K := fun k => by
      simp [𝒦, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]
    have hU : ∀ k ∈ S.chain.unitFiltration (m + 1), k ∈ 𝒦 := by
      intro k hk
      rw [hmem𝒦]
      refine ⟨S.chain.unitFiltration_antitone (Nat.le_succ m) hk, ?_⟩
      apply mem_unitFiltration_of_sub_one_mem S.chain hm1
      rw [D.shift_conj_sub_one]
      have hZ : D.ζ + D.e₂ ∈ S.chain.endFiltration 0 :=
        add_mem (S.chain.endFiltration_antitone (by norm_num) D.ζ_mem) D.e₂_mem
      have hZ' : D.ζ' + D.e₂ ∈ S.chain.endFiltration (-1) :=
        add_mem D.ζ'_mem (S.chain.endFiltration_antitone (by norm_num) D.e₂_mem)
      exact mul_mul_mem_endFiltration S.chain hZ hk.2.2 hZ' (by push_cast; ring)
    let f := S.chain.unitFiltrationToQuotient (i := m) (j := m + 1) (by omega)
    have : Finite (layerQuotient S.chain m ((m + 1 : ℕ) : ℤ)) :=
      finite_layerQuotient S.chain _ _ (by push_cast; omega)
    have : Finite f.range := inferInstance
    have hker : f.ker ≤ 𝒦.subgroupOf K := by
      intro k hk
      rw [Subgroup.mem_subgroupOf]
      exact hU _ ((S.chain.mem_ker_unitFiltrationToQuotient _ k).mp hk)
    have : (𝒦.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_le hker
    let : Fintype (K ⧸ 𝒦.subgroupOf K) := Fintype.ofFinite _
    -- the conjugating family
    let Z := layerQuotient S.chain 0 1
    have : Finite Z := finite_layerQuotient S.chain 0 1 (by norm_num)
    let : Fintype Z := Fintype.ofFinite Z
    have : Nonempty Z := ⟨0⟩
    let χ : Z → K →* ℂˣ := fun q => D.conjChar hm1 ϑ (Quotient.out q)
    let g : Z → Aut := fun q =>
      blockUnit D.e₁ D.e₂ D.e₂_mul_e₁ ((Quotient.out q : S.chain.endFiltration 0) : A)
    have hw : ∀ k : K, S.b * (((k : Aut) : A) - 1) - (((k : Aut) : A) - 1) * S.b ∈
        S.chain.endFiltration 0 := by
      intro k
      have hx : ((k : Aut) : A) - 1 ∈ S.chain.endFiltration S.n := by rw [← hm]; exact k.2.2.2
      refine sub_mem ?_ ?_
      · simpa using S.chain.mul_mem_endFiltration hb hx
      · simpa using S.chain.mul_mem_endFiltration hx hb
    let Φ : K → AddChar Z ℂ := fun k => blockCharacter S.chain hψ D.e₁_mem D.e₂_mem (hw k)
    have hΦ : ∀ (k : K) (q : Z), Φ k q = traceCharacter ψF
        (D.e₁ * ((Quotient.out q : S.chain.endFiltration 0) : A) * D.e₂ *
          (S.b * (((k : Aut) : A) - 1) - (((k : Aut) : A) - 1) * S.b)) := by
      intro k q
      rw [← blockCharacter_mk S.chain hψ D.e₁_mem D.e₂_mem (hw k)]
      exact congrArg _ (Quotient.out_eq q).symm
    have hmul : ∀ (q : Z) (k : K), (χ q k : ℂ) * Φ k q = ϑ k := fun q k => by
      rw [hΦ]
      exact D.conjChar_mul hm1 ϑ hϑ (Quotient.out q) k
    have hΦne : ∀ (k : K) (q : Z), Φ k q ≠ 0 := fun k q h => by
      have := (Φ k).map_add_eq_mul q (-q)
      rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
      exact one_ne_zero this
    have hfac : ∀ (q : Z) (k : K),
        (((χ q k)⁻¹ : ℂˣ) : ℂ) = Φ k q * (((ϑ k)⁻¹ : ℂˣ) : ℂ) := by
      intro q k
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, ← hmul q k]
      have h0 : (χ q k : ℂ) ≠ 0 := Units.ne_zero _
      have h1 := hΦne k q
      field_simp
    have hcrit : ∀ k : K, Φ k = 0 ↔ (k : Aut) ∈ 𝒦 := by
      intro k
      change blockCharacter S.chain hψ D.e₁_mem D.e₂_mem (hw k) = 0 ↔ _
      rw [blockCharacter_eq_zero_iff, hmem𝒦]
      exact ⟨fun h => ⟨k.2, (D.shift_conj_mem_unitFiltration_iff hm1 hm hb k).mpr h⟩,
        fun h => (D.shift_conj_mem_unitFiltration_iff hm1 hm hb k).mp h.2⟩
    have hχ𝒦 : ∀ (q : Z) (k : K), (k : Aut) ∈ 𝒦 → χ q k = ϑ k := by
      intro q k hk
      apply Units.ext
      have h1 : Φ k q = 1 := by rw [(hcrit k).mpr hk, AddChar.zero_apply]
      rw [← hmul q k, h1, mul_one]
    have horth : ∀ k : K, ∑ q, (((χ q k)⁻¹ : ℂˣ) : ℂ) =
        if (k : Aut) ∈ 𝒦 then (Fintype.card Z : ℂ) * (((ϑ k)⁻¹ : ℂˣ) : ℂ) else 0 := by
      intro k
      rw [Finset.sum_congr rfl (fun q _ => hfac q k), ← Finset.sum_mul, AddChar.sum_eq_ite]
      by_cases hk : (k : Aut) ∈ 𝒦
      · simp only [show Φ k = 0 from (hcrit k).mpr hk, hk, ↓reduceIte]
      · simp only [show ¬ Φ k = 0 from fun h => hk ((hcrit k).mp h), hk, ↓reduceIte, zero_mul]
    have hg : ∀ (q : Z) (w : W), (∀ k : K, ρ k w = (χ q k : ℂ) • w) →
        ∀ k : K, ρ k (ρ (g q) w) = (ϑ k : ℂ) • ρ (g q) w := by
      intro q w hw' k
      have hk' : (g q)⁻¹ * (k : Aut) * (g q)⁻¹⁻¹ ∈ K :=
        D.blockUnit_inv_conj_mem hm1 (Quotient.out q).2 k k.2
      have hχk : χ q ⟨(g q)⁻¹ * (k : Aut) * (g q)⁻¹⁻¹, hk'⟩ = ϑ k := by
        change ϑ (conjEndo _ _ _ ⟨_, hk'⟩) = ϑ k
        congr 1
        apply Subtype.ext
        rw [conjEndo_val]
        change g q * ((g q)⁻¹ * (k : Aut) * (g q)⁻¹⁻¹) * (g q)⁻¹ = (k : Aut)
        group
      calc ρ k (ρ (g q) w) = ρ (g q) (ρ ((g q)⁻¹ * (k : Aut) * (g q)⁻¹⁻¹) w) := by
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
            congr 2
            group
        _ = ρ (g q) ((χ q ⟨_, hk'⟩ : ℂ) • w) := by
            congr 1
            exact hw' ⟨_, hk'⟩
        _ = (ϑ k : ℂ) • ρ (g q) w := by rw [hχk, map_smul]
    have hgM : ∀ q, ∀ n ∈ M (j - 1), (g q)⁻¹ * n * (g q)⁻¹⁻¹ ∈ M (j - 1) := by
      intro q n hn
      have hc : g q * n = n * g q := blockUnipotent_commute
        (blockUnit_mem D.e₂_mul_e₁ D.e₁_mul_e₁ D.e₂_mul_e₂ _) (blockUnipotent_mono le_top hn)
      rw [inv_inv, mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hn
    have hv : ∀ κ : K, (κ : Aut) ∈ 𝒦 → ρ κ v₂ = (ϑ κ : ℂ) • v₂ := by
      intro κ hκ
      have hκ' : z * κ * z⁻¹ ∈ K := ((hmem𝒦 κ).mp hκ).2
      calc ρ κ v₂ = ρ z⁻¹ (ρ (z * κ * z⁻¹) v₁) := by
            rw [hv₂, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
            congr 2
            group
        _ = ρ z⁻¹ ((ϑ ⟨_, hκ'⟩ : ℂ) • v₁) := by
            congr 1
            exact hv₁ ⟨_, hκ'⟩
        _ = (ϑ κ : ℂ) • v₂ := by rw [D.theta_shift_conj ϑ hϑ κ hκ', map_smul]
    obtain ⟨w, hwP, hwM⟩ := Jacquet.exists_isotypic_not_mem_relations (ρ := ρ) (K := K)
      (𝒦 := 𝒦) (M (j - 1)) ϑ χ g hχ𝒦 horth hg hgM hv hv₂M
    exact fun hle => hwM (hle hwP)

end SplitBlockData

end Refinement

end Langlands.BushnellKutzko.SplitBlocks
