import Langlands.Shimura.Unitary.HarrisDivisionLevels
import Langlands.Shimura.Unitary.HarrisSplitPrimeLevels
import Langlands.Shimura.Unitary.HarrisLevelFreeSmall
import Langlands.Shimura.Unitary.HarrisSmallLevels
import Langlands.Shimura.Unitary.OppositePointsSplit
import Langlands.Shimura.Unitary.FiniteAdelicCompactOpenLevels

/-! # Harris's levels `K_p × K^p` and their opposite levels

For a prime `p` and the place `v` of `ℚ` above it, a level `K_p` of `GG(ℚ_v)` and a level `K^p` of
`GG(A_f^p)` give the level `K_p × K^p` of `GG(A_f)` (`primeAdelicLevel`). Its opposite level is the
level `e⁻¹ (K_pᵐᵒᵖ × K^pᵐᵒᵖ)` of `GG(A_f)ᵐᵒᵖ` built from the published opposite splitting at the
places dividing `p`; this is how the level enters the actual CM scheme tower. If `K^p` has no
nontrivial element of finite order in its component at one place not dividing `p`, every such level
is sufficiently small, whatever `K_p` is. For Harris's `K(N)_p` this gives `K(N, m) = K(N)_p ×
K(m)^p` (Harris 1999, §4, p.309). See `HarrisPrimeAdelicLevels.md`.
-/

noncomputable section

open Langlands.Global
open scoped NumberField

set_option autoImplicit false

universe u v w z

namespace Langlands.Shimura

namespace CompactOpenLevel

section Opposite

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- The opposite `Kᵐᵒᵖ` of a compact open level `K` of `G`, as a compact open level of `Gᵐᵒᵖ`. -/
def op (K : CompactOpenLevel G) : CompactOpenLevel Gᵐᵒᵖ :=
  opOfCompact K.openSubgroup K.isCompact

@[simp] theorem mem_op (K : CompactOpenLevel G) (g : Gᵐᵒᵖ) :
    g ∈ K.op.subgroup ↔ MulOpposite.unop g ∈ K.subgroup :=
  Iff.rfl

theorem op_mono {K L : CompactOpenLevel G} (h : K.subgroup ≤ L.subgroup) :
    K.op.subgroup ≤ L.op.subgroup :=
  fun _ hg => h hg

theorem op_le_op_iff {K L : CompactOpenLevel G} :
    K.op.subgroup ≤ L.op.subgroup ↔ K.subgroup ≤ L.subgroup :=
  ⟨fun h g hg => @h (MulOpposite.op g) hg, op_mono⟩

theorem op_injective : Function.Injective (op : CompactOpenLevel G → CompactOpenLevel Gᵐᵒᵖ) := by
  intro K L h
  ext g
  exact (show MulOpposite.op g ∈ K.op.subgroup ↔ MulOpposite.op g ∈ L.op.subgroup by rw [h])

end Opposite

variable {G : Type v} {H : Type w} {H' : Type z} [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] [Group H'] [TopologicalSpace H']

/-- For a splitting `e : G ≃ₜ* H × H'`, the opposite of `e⁻¹ (K × K')` is the level
`(eᵐᵒᵖ)⁻¹ (Kᵐᵒᵖ × K'ᵐᵒᵖ)` for the induced splitting of the opposite groups. -/
theorem transport_oppositeSplit_symm_prod_op (e : G ≃ₜ* H × H') (K : CompactOpenLevel H)
    (K' : CompactOpenLevel H') :
    transport (oppositeSplit e).symm (prod K.op K'.op) = (transport e.symm (prod K K')).op := by
  ext g
  exact Iff.rfl

end CompactOpenLevel

namespace AlgebraInvolution

open CompactOpenLevel

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (σ : AlgebraInvolution ℚ A)

/-! ## The levels `K_p × K^p` -/

section Prime

variable (p : ℕ) (hp : p.Prime) (v : {v : FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})

/-- The level `K_p × K^p` of `GG(A_f)`, for a level `K_p` of `GG(ℚ_v)` at the place `v` above the
prime `p` and a level `K^p` of `GG(A_f^p)`: the inverse image, under the published splitting
`GG(A_f) ≃ₜ* GG(Π_{w ∣ p} ℚ_w) × GG(A_f^p)`, of the product of the transport of `K_p` and `K^p`. -/
def primeAdelicLevel (Kp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1)))
    (K' : CompactOpenLevel (σ.PrimeToPoints p)) : CompactOpenLevel σ.FiniteAdelicPoints :=
  transport (σ.finiteAdelicPointsSplit p hp.ne_zero).symm
    (prod (transport (σ.dividingPrimePointsEquiv p hp v).symm Kp) K')

/-- A finite adelic point lies in `K_p × K^p` exactly when its component at `v` lies in `K_p` and
its prime-to-`p` component lies in `K^p`. -/
theorem mem_primeAdelicLevel (Kp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1)))
    (K' : CompactOpenLevel (σ.PrimeToPoints p)) (g : σ.FiniteAdelicPoints) :
    g ∈ (σ.primeAdelicLevel p hp v Kp K').subgroup ↔
      σ.finiteLocalMap v.1 g ∈ Kp.subgroup ∧
        (σ.finiteAdelicPointsSplit p hp.ne_zero g).2 ∈ K'.subgroup := by
  change σ.dividingLocalMap p v (σ.finiteAdelicPointsSplit p hp.ne_zero g).1 ∈ Kp.subgroup ∧
      (σ.finiteAdelicPointsSplit p hp.ne_zero g).2 ∈ K'.subgroup ↔ _
  rw [σ.dividingLocalMap_finiteAdelicPointsSplit p hp.ne_zero v]

/-- `K_p × K^p` is monotone in both factors. -/
theorem primeAdelicLevel_mono {Kp Lp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1))}
    {K' L' : CompactOpenLevel (σ.PrimeToPoints p)} (hKp : Kp.subgroup ≤ Lp.subgroup)
    (hK' : K'.subgroup ≤ L'.subgroup) :
    (σ.primeAdelicLevel p hp v Kp K').subgroup ≤ (σ.primeAdelicLevel p hp v Lp L').subgroup :=
  fun _ hg => ⟨hKp hg.1, hK' hg.2⟩

/-- The opposite of the transport of `K_p` to the points at the places dividing `p`, a level of
`GG(Π_{w ∣ p} ℚ_w)ᵐᵒᵖ`. This is the fixed level `K₀` of the prime-to-`p` CM tower. -/
def primeDividingOpLevel (Kp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1))) :
    CompactOpenLevel (σ.DividingPoints p)ᵐᵒᵖ :=
  (transport (σ.dividingPrimePointsEquiv p hp v).symm Kp).op

theorem mem_primeDividingOpLevel (Kp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1)))
    (h : (σ.DividingPoints p)ᵐᵒᵖ) :
    h ∈ (σ.primeDividingOpLevel p hp v Kp).subgroup ↔
      σ.dividingLocalMap p v (MulOpposite.unop h) ∈ Kp.subgroup :=
  Iff.rfl

/-- The level `e⁻¹ (K₀ × K^pᵐᵒᵖ)` of `GG(A_f)ᵐᵒᵖ`, for the opposite splitting at the places
dividing `p` and `K₀ = primeDividingOpLevel K_p`, is the opposite of `K_p × K^p`. -/
theorem transport_finiteAdelicPointsOpSplit_symm_prod
    (Kp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1)))
    (K' : CompactOpenLevel (σ.PrimeToPoints p)) :
    transport (σ.finiteAdelicPointsOpSplit p hp.ne_zero).symm
        (prod (σ.primeDividingOpLevel p hp v Kp) K'.op) =
      (σ.primeAdelicLevel p hp v Kp K').op :=
  transport_oppositeSplit_symm_prod_op _ _ _

end Prime

/-! ## Smallness away from `n` -/

section PrimeToSmall

variable (n : ℕ)

/-- The condition at a place `w` not dividing `n`, on a level of the opposite prime-to-`n` points:
every element whose component at `w` has finite order has trivial component at `w`. -/
def PrimeToLevelSmallAt (K' : CompactOpenLevel (σ.PrimeToPoints n)ᵐᵒᵖ)
    (w : PrimeToFinitePlace n) : Prop :=
  ∀ h ∈ K'.subgroup, IsOfFinOrder (DefiniteForms.primeToLocalMap σ n w (MulOpposite.unop h)) →
    DefiniteForms.primeToLocalMap σ n w (MulOpposite.unop h) = 1

/-- The condition `PrimeToLevelSmallAt` at some place not dividing `n`. -/
def PrimeToLevelSufficientlySmall (K' : CompactOpenLevel (σ.PrimeToPoints n)ᵐᵒᵖ) : Prop :=
  ∃ w : PrimeToFinitePlace n, σ.PrimeToLevelSmallAt n K' w

variable {σ n}

omit [Module.Finite ℚ A] in
/-- The local condition is inherited by every subgroup level. -/
theorem PrimeToLevelSmallAt.mono {K' L' : CompactOpenLevel (σ.PrimeToPoints n)ᵐᵒᵖ}
    {w : PrimeToFinitePlace n} (hL' : σ.PrimeToLevelSmallAt n L' w)
    (hKL : K'.subgroup ≤ L'.subgroup) : σ.PrimeToLevelSmallAt n K' w :=
  fun h hh hfin => hL' h (hKL hh) hfin

omit [Module.Finite ℚ A] in
/-- Sufficient smallness away from `n` is inherited by every subgroup level. -/
theorem PrimeToLevelSufficientlySmall.mono {K' L' : CompactOpenLevel (σ.PrimeToPoints n)ᵐᵒᵖ}
    (hL' : σ.PrimeToLevelSufficientlySmall n L') (hKL : K'.subgroup ≤ L'.subgroup) :
    σ.PrimeToLevelSufficientlySmall n K' := by
  obtain ⟨w, hw⟩ := hL'
  exact ⟨w, hw.mono hKL⟩

omit [Module.Finite ℚ A] in
/-- For the opposite of an ordinary level `K^p`, the local condition says that every element of
`K^p` whose component at `w` has finite order has trivial component at `w`. -/
theorem primeToLevelSmallAt_op_iff {K' : CompactOpenLevel (σ.PrimeToPoints n)}
    {w : PrimeToFinitePlace n} :
    σ.PrimeToLevelSmallAt n K'.op w ↔
      ∀ k ∈ K'.subgroup, IsOfFinOrder (DefiniteForms.primeToLocalMap σ n w k) →
        DefiniteForms.primeToLocalMap σ n w k = 1 :=
  ⟨fun h k hk => h (MulOpposite.op k) hk, fun h k hk => h (MulOpposite.unop k) hk⟩

variable (hn : n ≠ 0)

/-- If `K'` satisfies the local condition at a place `w` not dividing `n`, then for every level
`K₀` at the places dividing `n` the level `e⁻¹ (K₀ × K')` of `GG(A_f)ᵐᵒᵖ` satisfies the local
condition at `w`. -/
theorem levelSmallAt_transport_prod_of_primeTo
    (K₀ : CompactOpenLevel (σ.DividingPoints n)ᵐᵒᵖ)
    {K' : CompactOpenLevel (σ.PrimeToPoints n)ᵐᵒᵖ} {w : PrimeToFinitePlace n}
    (hK' : σ.PrimeToLevelSmallAt n K' w) :
    σ.LevelSmallAt (transport (σ.finiteAdelicPointsOpSplit n hn).symm (prod K₀ K')) w.1 := by
  intro g hg
  have hg' : MulOpposite.op (σ.finiteAdelicPointsSplit n hn (MulOpposite.unop g)).2 ∈
      K'.subgroup :=
    ((mem_transport_symm_prod (σ.finiteAdelicPointsOpSplit n hn)).1 hg).2
  change IsOfFinOrder (σ.finiteLocalMap w.1 (MulOpposite.unop g)) →
    σ.finiteLocalMap w.1 (MulOpposite.unop g) = 1
  rw [← DefiniteForms.primeToLocalMap_finiteAdelicPointsSplit σ hn w]
  exact hK' _ hg'

/-- If `K'` is sufficiently small away from `n`, then every level `e⁻¹ (K₀ × K')` of
`GG(A_f)ᵐᵒᵖ` is sufficiently small. -/
theorem levelSufficientlySmall_transport_prod_of_primeTo
    (K₀ : CompactOpenLevel (σ.DividingPoints n)ᵐᵒᵖ)
    {K' : CompactOpenLevel (σ.PrimeToPoints n)ᵐᵒᵖ}
    (hK' : σ.PrimeToLevelSufficientlySmall n K') :
    σ.LevelSufficientlySmall (transport (σ.finiteAdelicPointsOpSplit n hn).symm (prod K₀ K')) := by
  obtain ⟨w, hw⟩ := hK'
  exact ⟨w.1, levelSmallAt_transport_prod_of_primeTo hn K₀ hw⟩

/-! ### Existence of levels that are small away from `n` -/

/-- The level `K^p` shrunk at a place `w` not dividing `n`: the elements of `K^p` whose component
at `w` lies in the principal congruence level modulo `q` (the published `smallAwayLevel`). -/
def primeToCongruenceShrink (w : PrimeToFinitePlace n) {q : ℕ} (hq : q ≠ 0)
    (K' : CompactOpenLevel (σ.PrimeToPoints n)) : CompactOpenLevel (σ.PrimeToPoints n) where
  openSubgroup :=
    { toSubgroup := DefiniteForms.smallAwayLevel σ n w q K'.subgroup
      isOpen' := DefiniteForms.isOpen_smallAwayLevel w hq K'.openSubgroup.isOpen }
  isCompact := DefiniteForms.isCompact_smallAwayLevel w hq K'.isCompact

theorem primeToCongruenceShrink_le (w : PrimeToFinitePlace n) {q : ℕ} (hq : q ≠ 0)
    (K' : CompactOpenLevel (σ.PrimeToPoints n)) :
    (σ.primeToCongruenceShrink w hq K').subgroup ≤ K'.subgroup :=
  DefiniteForms.smallAwayLevel_le

/-- For a prime `q ≥ 3` in the prime ideal of `w`, the shrunk level satisfies the local condition
at `w`. -/
theorem primeToLevelSmallAt_primeToCongruenceShrink [Nontrivial A] {w : PrimeToFinitePlace n}
    {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) (hw : (q : 𝓞 ℚ) ∈ w.1.asIdeal)
    (K' : CompactOpenLevel (σ.PrimeToPoints n)) :
    σ.PrimeToLevelSmallAt n (σ.primeToCongruenceShrink w hq.ne_zero K').op w :=
  primeToLevelSmallAt_op_iff.2 fun _ hk hfin =>
    SmallLevels.congruenceLevel_torsionFree σ hq hq3 hw _ (Subgroup.mem_inf.1 hk).2 hfin

omit [Module.Finite ℚ A] in
/-- If a prime `q` does not divide `n` and lies in the prime ideal of a finite place `w` of `ℚ`,
then `n` does not lie in that ideal. -/
theorem natCast_not_mem_asIdeal_of_prime_mem {q : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ n)
    (w : FinitePlace ℚ) (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : (n : 𝓞 ℚ) ∉ w.asIdeal := by
  intro hnw
  obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hqn)
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a : 𝓞 ℚ) * (q : 𝓞 ℚ) + (b : 𝓞 ℚ) * (n : 𝓞 ℚ)) = 1 := by
    have := congrArg (fun z : ℤ => (z : 𝓞 ℚ)) hab
    push_cast at this
    exact this
  rw [← h1]
  exact add_mem (Ideal.mul_mem_left _ _ hw) (Ideal.mul_mem_left _ _ hnw)

include hn in
/-- Every level `K^p` of `GG(A_f^n)` contains a level whose opposite is sufficiently small away
from `n`. -/
theorem exists_primeToLevelSufficientlySmall_le [Nontrivial A]
    (K' : CompactOpenLevel (σ.PrimeToPoints n)) :
    ∃ L' : CompactOpenLevel (σ.PrimeToPoints n),
      L'.subgroup ≤ K'.subgroup ∧ σ.PrimeToLevelSufficientlySmall n L'.op := by
  obtain ⟨q, hqn, hq⟩ := Nat.exists_infinite_primes (n + 3)
  obtain ⟨w, hw, -⟩ := existsUnique_finitePlace_natCast_mem q hq
  have hqn' : ¬ q ∣ n := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn) (by omega)
  let w' : PrimeToFinitePlace n := ⟨w, natCast_not_mem_asIdeal_of_prime_mem hq hqn' w hw⟩
  exact ⟨σ.primeToCongruenceShrink w' hq.ne_zero K', primeToCongruenceShrink_le w' _ K',
    w', primeToLevelSmallAt_primeToCongruenceShrink hq (by omega) hw K'⟩

variable (σ n) in
/-- A compact open level of `GG(A_f^n)` exists (van Dantzig). -/
theorem nonempty_primeToPoints_compactOpenLevel :
    Nonempty (CompactOpenLevel (σ.PrimeToPoints n)) :=
  haveI := t2Space_primeToFiniteAdeles n
  haveI := locallyCompactSpace_primeToFiniteAdeles n
  haveI := totallyDisconnectedSpace_primeToFiniteAdeles n
  let ⟨H, hHc, _⟩ := σ.exists_compact_openSubgroup_subset_points _ Filter.univ_mem
  ⟨⟨H, hHc⟩⟩

variable (σ) in
include hn in
/-- A level of `GG(A_f^n)` whose opposite is sufficiently small away from `n` exists. -/
theorem exists_primeToLevelSufficientlySmall [Nontrivial A] :
    ∃ K' : CompactOpenLevel (σ.PrimeToPoints n), σ.PrimeToLevelSufficientlySmall n K'.op :=
  let ⟨K'⟩ := nonempty_primeToPoints_compactOpenLevel σ n
  let ⟨L', _, hL'⟩ := exists_primeToLevelSufficientlySmall_le hn K'
  ⟨L', hL'⟩

end PrimeToSmall

/-- If `K^p` is sufficiently small away from `p`, the opposite of `K_p × K^p` is sufficiently
small, for every level `K_p` at `p`. -/
theorem levelSufficientlySmall_primeAdelicLevel_op {p : ℕ} (hp : p.Prime)
    (v : {v : FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})
    (Kp : CompactOpenLevel (σ.Points (FiniteCompletion ℚ v.1)))
    {K' : CompactOpenLevel (σ.PrimeToPoints p)}
    (hK' : σ.PrimeToLevelSufficientlySmall p K'.op) :
    σ.LevelSufficientlySmall (σ.primeAdelicLevel p hp v Kp K').op := by
  rw [← σ.transport_finiteAdelicPointsOpSplit_symm_prod p hp v Kp K']
  exact levelSufficientlySmall_transport_prod_of_primeTo hp.ne_zero _ hK'

end AlgebraInvolution

/-! ## Harris's levels -/

section Harris

open NumberField IsDedekindDomain
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension
open Global AdelicFunctoriality CompactOpenLevel

variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {F : Type w} [Field F] [NumberField F] [IsCMField F] [Algebra.IsQuadraticExtension ℚ F]
variable {A : Type z} [Ring A] [Algebra K A] [Algebra ℚ A] [IsScalarTower ℚ K A]
  [Module.Finite ℚ A] [Algebra E A] [IsScalarTower E K A] [IsScalarTower ℚ E A]

namespace SecondKindInvolution

variable (σ : SecondKindInvolution E K A) (ι : F →+* K) (p : ℕ) (hp : p.Prime)
  (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})

omit [IsScalarTower ℚ K A] [IsScalarTower E K A] in
/-- The published split-prime level `K_p × K^p` with `K_p = C × ℤ_vˣ` is `primeAdelicLevel` of
`splitPrimeLevel C`. -/
theorem splitPrimeAdelicLevel_eq_primeAdelicLevel (u : F →+* FiniteCompletion ℚ v.1)
    (C : CompactOpenLevel (SplitPrimeUnits A ι v.1 u))
    (K' : CompactOpenLevel (σ.rationalInvolution.PrimeToPoints p)) :
    σ.splitPrimeAdelicLevel ι p hp v u C K' =
      σ.rationalInvolution.primeAdelicLevel p hp v (σ.splitPrimeLevel ι v.1 u C) K' :=
  rfl

variable (𝔭 : FinitePlacesAbove F v.1)
  (h𝔭 : Function.Bijective (FiniteExtension.completionMap v.1 𝔭.1))
  (hdiv : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1), IsDivisionAt A w.1)
  (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) (r : ℝ) (hr0 : 0 < r) (hr : r < 1)

/-- Harris's level `K(N, m) = K(N)_p × K(m)^p` of `GG(A_f)` (Harris 1999, §4, p.309): the level
`K(N)_p = harrisLevel` at the place `v` above `p`, with congruence radius `r`, times a level
`K(m)^p` of `GG(A_f^p)`. -/
def harrisPrimeAdelicLevel (K' : CompactOpenLevel (σ.rationalInvolution.PrimeToPoints p)) :
    CompactOpenLevel σ.rationalInvolution.FiniteAdelicPoints :=
  σ.rationalInvolution.primeAdelicLevel p hp v (σ.harrisLevel ι v.1 𝔭 h𝔭 hdiv w₀ r hr0 hr) K'

omit [IsScalarTower E K A] in
/-- A finite adelic point lies in `K(N, m)` exactly when its component at `v` lies in `K(N)_p`
and its prime-to-`p` component lies in `K(m)^p`. -/
theorem mem_harrisPrimeAdelicLevel (K' : CompactOpenLevel (σ.rationalInvolution.PrimeToPoints p))
    (g : σ.rationalInvolution.FiniteAdelicPoints) :
    g ∈ (σ.harrisPrimeAdelicLevel ι p hp v 𝔭 h𝔭 hdiv w₀ r hr0 hr K').subgroup ↔
      σ.rationalInvolution.finiteLocalMap v.1 g ∈
          (σ.harrisLevel ι v.1 𝔭 h𝔭 hdiv w₀ r hr0 hr).subgroup ∧
        (σ.rationalInvolution.finiteAdelicPointsSplit p hp.ne_zero g).2 ∈ K'.subgroup :=
  σ.rationalInvolution.mem_primeAdelicLevel p hp v _ K' g

/-- The fixed level `K₀` at the places dividing `p` attached to Harris's `K(N)_p`, a level of
`GG(Π_{w ∣ p} ℚ_w)ᵐᵒᵖ`. -/
def harrisDividingOpLevel : CompactOpenLevel (σ.rationalInvolution.DividingPoints p)ᵐᵒᵖ :=
  σ.rationalInvolution.primeDividingOpLevel p hp v (σ.harrisLevel ι v.1 𝔭 h𝔭 hdiv w₀ r hr0 hr)

omit [IsScalarTower E K A] in
/-- The level `e⁻¹ (K₀ × K(m)^pᵐᵒᵖ)` of `GG(A_f)ᵐᵒᵖ` is the opposite of Harris's `K(N, m)`. -/
theorem transport_harrisDividingOpLevel_prod
    (K' : CompactOpenLevel (σ.rationalInvolution.PrimeToPoints p)) :
    transport (σ.rationalInvolution.finiteAdelicPointsOpSplit p hp.ne_zero).symm
        (prod (σ.harrisDividingOpLevel ι p hp v 𝔭 h𝔭 hdiv w₀ r hr0 hr) K'.op) =
      (σ.harrisPrimeAdelicLevel ι p hp v 𝔭 h𝔭 hdiv w₀ r hr0 hr K').op :=
  σ.rationalInvolution.transport_finiteAdelicPointsOpSplit_symm_prod p hp v _ K'

end SecondKindInvolution

end Harris

end Langlands.Shimura
