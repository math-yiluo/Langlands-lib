module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.PUnit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroTor
public import StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroCriterion
import all StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroTor
import all StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroCriterion

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Criteria for flatness over a Noetherian local base: 00ME to 00MI

The Noetherian step and statement of Stacks 00ME, and its consequences: lifting a
nonzerodivisor (00MF) and a regular sequence (00MG) from the fibre, freeness from a free fibre
(00MH) and exactness of a complex from exactness of its fibre (00MI).
-/

section

universe u v w

@[expose] public section

section

open Function TensorProduct IsLocalRing

namespace Stacks.Flatness.LocalCriterion

/-- The fibre of a quotient is the quotient of the fibre: the class of `x` lies in `J(M/p)` exactly
when `x` lies in `JM + p`. -/
private lemma mk_mem_smul_top_iff {A B : Type*} [CommRing A] [AddCommGroup B] [Module A B]
    (J : Ideal A) (p : Submodule A B) (x : B) :
    (Submodule.Quotient.mk x : B ⧸ p) ∈ J • (⊤ : Submodule A (B ⧸ p)) ↔
      x ∈ J • (⊤ : Submodule A B) ⊔ p := by
  have hmap : J • (⊤ : Submodule A (B ⧸ p)) = Submodule.map p.mkQ (J • ⊤) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [hmap, ← Submodule.mkQ_apply, ← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_comm]

section Noetherian

variable {R S N M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Krull's intersection theorem for the finite `S`-module `N/IN`, whose `𝔪S`-adic filtration is
the image of the filtration by `𝔪ⁿ + I`, turns
`Stacks.Flatness.LocalCriterion.comap_smul_top_pow_add_le` into `u⁻¹(IM) ⊆ IN`. -/
private lemma comap_smul_top_le [Module.Flat R M] [Module.Finite S N] (u : N →ₗ[R] M)
    (hu : Injective (u.lTensor (R ⧸ maximalIdeal R))) (I : Ideal R) :
    ((I • (⊤ : Submodule R M)).comap u) ≤ I • (⊤ : Submodule R N) := by
  have hmax := IsLocalRing.maximalIdeal.isMaximal R
  set 𝔪 := maximalIdeal R
  intro y hy
  rw [Submodule.mem_comap] at hy
  -- `IN` is an `S`-submodule of `N`, so Krull's intersection theorem applies to `N/IN`.
  set K : Submodule S N := (I.map (algebraMap R S)) • ⊤ with hK
  rw [← Module.Flat.mem_map_smul_top_iff (S := S) I y, ← hK]
  have : Module.Finite S (N ⧸ K) := Module.Finite.of_surjective K.mkQ (Submodule.mkQ_surjective K)
  have hmk : K.mkQ y = 0 := by
    have hmem : K.mkQ y ∈
        ⨅ n : ℕ, (𝔪.map (algebraMap R S)) ^ n • (⊤ : Submodule S (N ⧸ K)) := by
      rw [Submodule.mem_iInf]
      intro n
      have h1 : y ∈ (𝔪 ^ n + I) • (⊤ : Submodule R N) :=
        comap_smul_top_pow_add_le u hu I n (Submodule.smul_mono_left le_sup_right hy)
      rw [Ideal.add_eq_sup, Submodule.sup_smul, Submodule.mem_sup] at h1
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := h1
      rw [Submodule.mkQ_apply, mk_mem_smul_top_iff]
      refine Submodule.add_mem_sup ?_ ((Module.Flat.mem_map_smul_top_iff (S := S) I y₂).2 hy₂)
      rw [← Ideal.map_pow]
      exact (Module.Flat.mem_map_smul_top_iff (S := S) (𝔪 ^ n) y₁).2 hy₁
    rwa [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N ⧸ K) _
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne] at hmem
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk

end Noetherian

section Fibre

variable {R N M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The fibre `ū : N/IN → M/IM` of `u` is injective exactly when `R/I ⊗ u` is; this is the
direction the source's hypothesis is used in. -/
private lemma injective_lTensor_of_injective_mapQ {I : Ideal R} (u : N →ₗ[R] M)
    (hu : Injective (Submodule.mapQ (I • (⊤ : Submodule R N)) (I • (⊤ : Submodule R M)) u
      (Submodule.smul_top_le_comap_smul_top I u))) :
    Injective (u.lTensor (R ⧸ I)) := by
  have hmkN : Surjective (TensorProduct.mk R (R ⧸ I) N 1) := by
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_comp_mkQ]
    exact (TensorProduct.quotTensorEquivQuotSMul N I).symm.surjective.comp
      (Submodule.mkQ_surjective _)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := hmkN z
  rw [show (u.lTensor (R ⧸ I)) (TensorProduct.mk R (R ⧸ I) N 1 y)
      = TensorProduct.mk R (R ⧸ I) M 1 (u y) from by simp,
    ← LinearMap.mem_ker, LinearMap.ker_tensorProductMk] at hz
  have h3 : (I • (⊤ : Submodule R N)).mkQ y = 0 := by
    refine hu ?_
    rw [map_zero, Submodule.mkQ_apply, Submodule.mapQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2 hz
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h3
  rw [← LinearMap.mem_ker, LinearMap.ker_tensorProductMk]
  exact h3

end Fibre

open IsLocalRing in
/-- **Stacks 00ME.** -/
private theorem solution
    {R S N M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N]
    (u : N →ₗ[R] M)
    (hu : Function.Injective (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R N))
      (maximalIdeal R • (⊤ : Submodule R M)) u
      (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) u))) :
    Function.Injective u ∧ Module.Flat R (M ⧸ LinearMap.range u) := by
  have hkey := comap_smul_top_le (S := S) u (injective_lTensor_of_injective_mapQ u hu)
  refine ⟨?_, flat_quotient_range_of_comap_smul_top_le u hkey⟩
  have h := hkey ⊥
  rw [Submodule.bot_smul, Submodule.bot_smul, le_bot_iff] at h
  exact LinearMap.ker_eq_bot.1 h

end Stacks.Flatness.LocalCriterion

end

section

open IsLocalRing in
/-- **Stacks 00ME.** Let `R → S` be a local homomorphism of local rings with `S` Noetherian, let
`𝔪` be the maximal ideal of `R`, let `M` be a flat `R`-module, let `N` be a finite `S`-module and
let `u : N → M` be a map of `R`-modules. If the induced map `ū : N/𝔪N → M/𝔪M` is injective, then
`u` is injective and `M/u(N)` is flat over `R`.

Here `N/𝔪N` is `N ⧸ 𝔪 • ⊤` and `ū` is the canonical `Submodule.mapQ`, which sends the class of `x`
to the class of `u x`; see the module docstring. -/
@[stacks 00ME "`N/𝔪N` is `N ⧸ 𝔪 • (⊤ : Submodule R N)` and `ū` the canonical `Submodule.mapQ` of
`u`. The cokernel `M/u(N)` is `M ⧸ LinearMap.range u`, and the two conclusions are conjoined; see
the module docstring. The non-Noetherian generalization is 046Y."]
theorem
    Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
    {R S N M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N]
    (u : N →ₗ[R] M)
    (hu : Function.Injective (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R N))
      (maximalIdeal R • (⊤ : Submodule R M)) u
      (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) u))) :
    Function.Injective u ∧ Module.Flat R (M ⧸ LinearMap.range u) :=
      Stacks.Flatness.LocalCriterion.solution (S := S) u hu

end

/-! ### Stacks 00MF -/

section

namespace Stacks.Flatness.FibreNonZeroDivisor

/-- The map induced by `g` on the quotients `M ⧸ p → N ⧸ q` is injective exactly when `g` reflects
membership, that is when `q.comap g ≤ p`. -/
public lemma mapQ_injective_iff {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {p : Submodule R M} {q : Submodule R N} {g : M →ₗ[R] N}
    (h : p ≤ q.comap g) :
    Function.Injective (Submodule.mapQ p q g h) ↔ q.comap g ≤ p := by
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, eq_bot_iff, Submodule.map_le_iff_le_comap,
    Submodule.comap_bot, Submodule.ker_mkQ]

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

end

end Stacks.Flatness.FibreNonZeroDivisor

end

section

namespace Module.Flat

/-- The map of `R`-fibres `N/IN → M/IM` induced by an `S`-linear map `u : N → M` over an
`R`-algebra `S` is injective as soon as `u a ∈ (IS) • ⊤` forces `a ∈ (IS) • ⊤`, a condition on the
`S`-side: the `R`- and `S`-side fibres are quotients by submodules with the same elements. -/
public lemma injective_mapQ_restrictScalars_of_forall_mem {R S M N : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (I : Ideal R) (u : N →ₗ[S] M)
    (h : ∀ a : N, u a ∈ Ideal.map (algebraMap R S) I • (⊤ : Submodule S M) →
      a ∈ Ideal.map (algebraMap R S) I • (⊤ : Submodule S N)) :
    Function.Injective (Submodule.mapQ (I • (⊤ : Submodule R N)) (I • (⊤ : Submodule R M))
      (u.restrictScalars R) (Submodule.smul_top_le_comap_smul_top _ _)) := by
  refine (Stacks.Flatness.FibreNonZeroDivisor.mapQ_injective_iff _).2 fun a ha => ?_
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply,
    ← mem_map_smul_top_iff (S := S)] at ha
  exact (mem_map_smul_top_iff (S := S) I a).1 (h a ha)

end Module.Flat

end

section

namespace Module.Flat

end Module.Flat

end

/-! ### Stacks 00MG -/

section

namespace Module.Flat

end Module.Flat

end

section

namespace Stacks.Flatness.RegularSequenceQuotient

open RingTheory.Sequence
open scoped Pointwise

end Stacks.Flatness.RegularSequenceQuotient

end

section

end

/-! ### Stacks 00MH -/

section

namespace Stacks.Flatness.FreeFromFreeFibre

open IsLocalRing Module.Flat

/-- A tuple over a finite index type all of whose entries lie in `I` lies in `I • ⊤`. -/
private theorem mem_smul_top_of_forall_mem {S ι : Type*} [CommRing S] [Finite ι] {I : Ideal S}
    {a : ι → S} (ha : ∀ i, a i ∈ I) : a ∈ I • (⊤ : Submodule S (ι → S)) := by
  classical
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single a]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h : Pi.single i (a i) = a i • (Pi.single i 1 : ι → S) := by
    ext j; by_cases h : j = i <;> simp [h]
  rw [h]
  exact Submodule.smul_mem_smul (ha i) Submodule.mem_top

section Fibre

variable {S M ι : Type*} [CommRing S] [AddCommGroup M] [Module S M] [Fintype ι]

/-- Reducing modulo `I` the map `S^ι → M` defined by a family `x` gives the map `(S/I)^ι → M/IM`
defined by the reductions of the `x i`. -/
private theorem mkQ_linearCombination (I : Ideal S) (x : ι → M) (a : ι → S) :
    (I • (⊤ : Submodule S M)).mkQ (Fintype.linearCombination S x a)
      = Fintype.linearCombination (S ⧸ I) (fun i => (I • (⊤ : Submodule S M)).mkQ (x i))
          (fun i => Ideal.Quotient.mk I (a i)) := by
  simp [Fintype.linearCombination_apply]

/-- The map `S^ι → M` defined by a basis of `M` is surjective. -/
private theorem surjective_linearCombination_basis (b : Module.Basis ι S M) :
    Function.Surjective (Fintype.linearCombination S b) :=
  fun y => ⟨b.repr y, by rw [Fintype.linearCombination_apply]; exact b.sum_repr y⟩

/-- **Nakayama's lemma 00DV (6)** for a family: a finite family `x` generates a finite `S`-module
`M` as soon as its reductions generate the fibre `M/IM` over `S/I`, for `I` inside the Jacobson
radical of `S`. -/
private theorem surjective_linearCombination_of_surjective_linearCombination_mkQ
    [Module.Finite S M] {I : Ideal S} (hI : I ≤ Ideal.jacobson ⊥) (x : ι → M)
    (hx : Function.Surjective (Fintype.linearCombination (S ⧸ I)
      fun i => (I • (⊤ : Submodule S M)).mkQ (x i))) :
    Function.Surjective (Fintype.linearCombination S x) := by
  refine LinearMap.surjective_of_surjective_comp_mkQ _ I hI fun z => ?_
  obtain ⟨c, hc⟩ := hx z
  choose a ha using fun i => Ideal.Quotient.mk_surjective (I := I) (c i)
  exact ⟨a, by rw [LinearMap.comp_apply, mkQ_linearCombination]; simpa [ha] using hc⟩

/-- If the reductions of a family `x` are linearly independent over `S/I`, then a combination
`∑ aᵢ xᵢ` lying in `IM` has all its coefficients in `I`. -/
private theorem mem_of_linearCombination_mem_smul_top {I : Ideal S} {x : ι → M}
    (hx : LinearIndependent (S ⧸ I) fun i => (I • (⊤ : Submodule S M)).mkQ (x i)) {a : ι → S}
    (ha : Fintype.linearCombination S x a ∈ I • (⊤ : Submodule S M)) (i : ι) : a i ∈ I := by
  rw [Fintype.linearIndependent_iff] at hx
  refine Ideal.Quotient.eq_zero_iff_mem.mp (hx (fun i => Ideal.Quotient.mk I (a i)) ?_ i)
  rw [← Fintype.linearCombination_apply, ← mkQ_linearCombination]
  simpa using ha

end Fibre

/-- **The heart of 00MH**, by the local criterion 00ME: for `M` flat over `R` and `S` a Noetherian
local ring over the local ring `R`, the map `S^ι → M` defined by a finite family `x` is injective
as soon as the reductions of the `x i` are linearly independent over the residue algebra `S/𝔪S`.

The relation `∑ aᵢ xᵢ ∈ 𝔪S • ⊤` puts every `aᵢ` in `𝔪S` by that independence, hence the tuple `a`
in `𝔪S • ⊤`, which is exactly injectivity of the fibre map that 00ME asks for. -/
private theorem injective_linearCombination_of_linearIndependent_mkQ {R S M ι : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Flat R M] [Fintype ι] {x : ι → M}
    (hx : LinearIndependent (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
      fun i => (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M)).mkQ (x i)) :
    Function.Injective (Fintype.linearCombination S x) :=
  (injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
    (S := S) (N := ι → S) ((Fintype.linearCombination S x).restrictScalars R)
    (injective_mapQ_restrictScalars_of_forall_mem _ _ fun _ ha =>
      mem_smul_top_of_forall_mem fun i => mem_of_linearCombination_mem_smul_top hx ha i)).1

/-- A nonzero module over an `R`-algebra `S` that is `S`-linearly isomorphic to a product of copies
of `S` has `S` as a direct summand, so flatness over `R` descends from it to `S`. The product is
over a nonempty index type precisely because the module is nonzero. -/
private theorem flat_of_linearEquiv_pi {R S M ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Nontrivial M]
    [Module.Flat R M] (e : (ι → S) ≃ₗ[S] M) : Module.Flat R S := by
  classical
  have : Module.Flat R (ι → S) := Module.Flat.of_linearEquiv (e.restrictScalars R)
  rcases isEmpty_or_nonempty ι with h | h
  · exact absurd e.toEquiv.symm.subsingleton (not_subsingleton M)
  · obtain ⟨i⟩ := h
    exact Module.Flat.of_retract (LinearMap.single R (fun _ : ι => S) i) (LinearMap.proj i)
      (by ext s; simp)

@[nolint unusedArguments]
private theorem solution
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    [Nontrivial M] [Module.Flat R M]
    (hM : Module.Free (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      (M ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule S M))) :
    Module.Free S M ∧ Module.Flat R S := by
  classical
  set J : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  -- a basis of the fibre `M/𝔪M` over `S/𝔪S`, and a lift `x` of it to `M`
  set ι := Module.Free.ChooseBasisIndex (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M))
  have : Fintype ι := Module.Free.ChooseBasisIndex.fintype _ _
  set b := Module.Free.chooseBasis (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M))
  choose x hx using fun i : ι => Submodule.Quotient.mk_surjective (J • (⊤ : Submodule S M)) (b i)
  have hxb : (fun i => (J • (⊤ : Submodule S M)).mkQ (x i)) = b := funext hx
  -- the map `S^ι → M` it defines is injective by 00ME and surjective by 00DV
  have hbij : Function.Bijective (Fintype.linearCombination S x) :=
    ⟨injective_linearCombination_of_linearIndependent_mkQ (by rw [hxb]; exact b.linearIndependent),
      surjective_linearCombination_of_surjective_linearCombination_mkQ
        ((map_maximalIdeal_le (algebraMap R S)).trans
          (jacobson_eq_maximalIdeal (⊥ : Ideal S) bot_ne_top).ge) x
        (by rw [hxb]; exact surjective_linearCombination_basis b)⟩
  have e : (ι → S) ≃ₗ[S] M := LinearEquiv.ofBijective _ hbij
  exact ⟨Module.Free.of_equiv e, flat_of_linearEquiv_pi e⟩

end Stacks.Flatness.FreeFromFreeFibre

end

section

namespace Module.Flat

/-- **Stacks 00MH.** Let `R → S` be a local homomorphism of Noetherian local rings, let `𝔪` be the
maximal ideal of `R`, and let `M` be a nonzero finite `S`-module. If `M/𝔪M` is a free
`S/𝔪S`-module and `M` is flat over `R`, then `M` is free over `S` and `S` is flat over `R`.

Here `S/𝔪S` is the ring quotient `S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)` and
`M/𝔪M` is the quotient `M ⧸ 𝔪S • (⊤ : Submodule S M)` with its canonical `S/𝔪S`-module structure;
see the module docstring. -/
@[stacks 00MH "\"Nonzero\" is `Nontrivial M`. The fibre ring is
`S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)` and `M/𝔪M` is
`M ⧸ 𝔪S • (⊤ : Submodule S M)`, whose `S/𝔪S`-module structure is
`Module.instQuotientIdealSubmoduleHSMulTop`. The two conclusions are conjoined, in the source's
order: `M` is free over `S`, `S` is flat over `R`. `IsNoetherianRing R` is unused but is part of
the tag's hypotheses; see the module docstring."]
theorem free_and_flat_of_free_maximalIdeal
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    [Nontrivial M] [Module.Flat R M]
    (hM : Module.Free (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      (M ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule S M))) :
    Module.Free S M ∧ Module.Flat R S :=
      Stacks.Flatness.FreeFromFreeFibre.solution hM

end Module.Flat

end

/-! ### Stacks 00MI -/

section

namespace Stacks.Flatness.LocalExactnessCriterion

open CategoryTheory Limits IsLocalRing TensorProduct

/-! ### Reduction modulo an ideal -/

section Fibre

variable {S : Type*} [CommRing S] (J : Ideal S) {M : Type*} [AddCommGroup M] [Module S M]

end Fibre

/-! ### The local criterion at one index of a complex -/

/-- **The local criterion 00ME at one index of a complex.** Let `R → S` be a local homomorphism of
local rings with `S` Noetherian, let `𝔪` be the maximal ideal of `R`, let `P →[g] N →[f] M` be a
complex of `S`-modules with `N` finite over `S` and `M` flat over `R`, and assume that
`f x ∈ 𝔪M` forces `x ∈ 𝔪N + g(P)`. Then `Ker f = Im g` and `M/f(N)` is flat over `R`.

This is 00ME applied to the map `u : N/g(P) → M` induced by `f`, whose reduction modulo `𝔪` is
injective by the hypothesis; `LinearMap.ker_eq_bot_range_liftQ_iff` turns the injectivity of `u`
into `Ker f = Im g`, and `Submodule.range_liftQ` identifies the two cokernels. -/
theorem _root_.Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top
    {R S P N M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [AddCommGroup P] [Module S P]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Flat R M]
    (g : P →ₗ[S] N) (f : N →ₗ[S] M) (hfg : f ∘ₗ g = 0)
    (hex : ∀ x : N, f x ∈ Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M) →
      x ∈ Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N) ⊔ LinearMap.range g) :
    LinearMap.ker f = LinearMap.range g ∧ Module.Flat R (M ⧸ LinearMap.range f) := by
  have hle : LinearMap.range g ≤ LinearMap.ker f := LinearMap.range_le_ker_iff.mpr hfg
  obtain ⟨hinj, hflat⟩ :=
    Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
      (S := S) ((Submodule.liftQ _ f hle).restrictScalars R)
      (Module.Flat.injective_mapQ_restrictScalars_of_forall_mem (S := S) _ _ fun q hq => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact (Stacks.Flatness.LocalCriterion.mk_mem_smul_top_iff _ _ x).mpr (hex x hq))
  have hinj' : Function.Injective (Submodule.liftQ (LinearMap.range g) f hle) := hinj
  rw [LinearMap.range_restrictScalars, Submodule.range_liftQ] at hflat
  exact ⟨(LinearMap.ker_eq_bot_range_liftQ_iff hle).mp (LinearMap.ker_eq_bot.mpr hinj'), hflat⟩

/-! ### Exactness of the reduced complex, read on elements -/

/-! ### Stacks 00MI -/

end Stacks.Flatness.LocalExactnessCriterion

end

section

end

end

end
