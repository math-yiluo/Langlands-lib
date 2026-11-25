module

public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.IntermediateFieldInduction
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCohenReduction
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppConditionAscent
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppWeakSolutionBridge
public import StacksFrontier.RingTheory.DiscreteValuationRing.EqualCharacteristicStructure
public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction
public import StacksFrontier.RingTheory.FormallySmooth.Adic
public import StacksFrontier.RingTheory.FormallySmooth.AdicLifting
public import StacksFrontier.RingTheory.FormallySmooth.RegularLocal
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Epp's Theorem (1.3): the complete case over a perfect residue field

Tag 09F8 (`IsDiscreteValuationRing.exists_finite_extension_isWeakSolution`,
`EppAlgClosedResidue.lean`) is the complete case of Epp's theorem over an **algebraically closed**
base residue field.  The published route to Tag 09F9 upgrades *perfect* to *algebraically closed*
using Tag 09ET, and Tag 09ET is false: there is an
extension `A ⊆ B` of discrete valuation rings with no finite weak solution for which **every**
diagram permitted by 09ET's conditions (1) and (2) does have one upstairs, so no such diagram can
satisfy its weak-solution implication.  The upgrade is therefore unavailable.

`IsAlgClosed` cannot be relaxed inside Tag 09F8 either.  It is propagated along every finite
extension by `isAlgClosed_residueField_of_finite` and consumed at the two induction joints where
the two-way residue condition has to ascend.  After the Cohen reduction the base residue field is
`perfectCore κ_B p`, which is perfect and not algebraically closed in general — for
`κ_A = κ_B = 𝔽_p(x)` the perfect core is `𝔽_p`.  So the complete case over a perfect residue field
is a separate theorem, namely Epp's **Theorem (1.3)**, and
`StacksFrontier.RingTheory.DiscreteValuationRing.EppKuhlmannCompleteCase` is groundwork for it.

This module is the **assembly** of that theorem.

## What is proved here, and what is assumed

`exists_finite_extension_isWeakSolution_of_perfectField` is Epp's Theorem (1.3) in the tower shape
Tag 09F8 uses — `A ⊆ B ⊆ C` with `IsWeaklyUnramified A B` and `Module.Finite L M`, which is Epp's
`R ⊆ S₀ ⊆ S` with `S₀ / R` weakly unramified and `S / S₀` `p`-cyclic.  It is proved **from**
`FamilyTowerSolvable`, the layer recursion, which is stated here and is *not* proved here; its
proof consumes the shared prime-degree family solver and the composition back down
(`Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_tensorCancel`,
proved).  So nothing below is an unconditional Tag 09F9 and nothing below is tagged.

Two substitutions turn Tag 09F8's statement into this one, and both are forced.

* `[IsAlgClosed κ_A]` becomes `[PerfectField κ_A]`, which is what Epp's condition forces and what
  the transports take: `Stacks.EppTheorem.EppCondition.of_module_finite` and `of_finite_square`
    carry
  `[PerfectField (ResidueField A)]` and nothing stronger.
* the two-way residue condition becomes `Stacks.EppTheorem.EppCondition A B p`.  **The two-way
  condition
  does not ascend over a merely perfect base** — that is why
  `residueField_forall_exists_pow_iff_of_finite_square` needs `IsAlgClosed` — whereas Epp's
  condition does.  A statement carrying the two-way condition in the perfect setting is stated
  wrong however well it typechecks.

## Why the recursion must be a family statement

The conjugate factors of `(L ⊗[K] K₁)ᵣₑd` are pairwise distinct
(`Stacks.WeakSolution.Obstruction.conjugateFactor_injective`) and the one-factor inference of the
  published proof of Tag
09ET is refuted, so no weak solution transports from one factor to the others compatibly with the
base.  Tag 09F8 can nevertheless recurse *pointwise*, once per conjugate factor, and reconcile the
per-factor fields afterwards by `exists_finite_extension_isWeakSolution_of_factor_solutions`.  That
reconciliation is an amalgamation of independently chosen extensions, and it runs on
`isWeakSolution_of_finite_extension`, whose `IsAlgClosed` hypothesis exists precisely because a
weak solution does **not** survive an arbitrary finite enlargement of the base.  Over a perfect
residue field the step is unavailable, so the extension has to be fixed before any factor is
examined. Hence `FamilyTowerSolvable`'s conclusion is `∃ K₂, ∀ i`, with the existential outside the
family.

What *does* survive an enlargement is a weak solution that is already weakly unramified, and the
statement of that is `isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField`
(`EppAlgClosedResidue.lean`, exposed for this module): no completeness, no `CharP`, no residue
condition.  That is the boundary of the whole difficulty.

## References

* [Epp, *Eliminating wild ramification*, Invent. Math. **19** (1973) 235–249][epp1973]
* Franz-Viktor Kuhlmann, *A correction to Epp's paper "Elimination of wild ramification"*,
  Invent. Math. **153** (2004) 679–681, [arXiv:1003.5687](https://arxiv.org/abs/1003.5687)
* [The Stacks Project, Tag 09F8](https://stacks.math.columbia.edu/tag/09F8),
  [Tag 09F9](https://stacks.math.columbia.edu/tag/09F9),
  [Tag 09ES](https://stacks.math.columbia.edu/tag/09ES)
-/

@[expose] public section

open IsLocalRing
open IsDiscreteValuationRing

universe u v uA uB uL

namespace Stacks.EppTheorem

/-! ### Perfectness of the residue field is inherited by an integral local extension

The perfect-residue analogue of `isAlgClosed_residueField_of_finite`, which is what Tag 09F8
propagates along each finite extension to keep its recursion re-entrant, is
`Stacks.EppTheorem.perfectField_residueField_of_isIntegral`.  It lives in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppConditionAscent`, beside
`perfectField_residueField_of_module_finite` — which it generalises and which is now derived from
it — rather than here, because two near-duplicate statements of one fact in two modules is the
thing to avoid and that file is where the module-finite version already was.

What belongs here is the bundled form, which is specific to this obligation. -/

/-! ### The layer recursion, as an interface

`FamilyTowerSolvable` is `NormalTowerSolvable` — `private` in `EppAlgClosedResidue.lean`, so it
cannot be referred to in Lean from here — with the two substitutions of the module docstring, with
the conclusion's existential pulled outside the family, and with the cyclotomic parameter dropped.
It is a `Prop`-valued `abbrev` with a **proved consumer**,
`exists_finite_extension_isWeakSolution_of_perfectField` below.

Its proof is *not* here.  It consumes the shared prime-degree family solver stated
against a **prescribed** extension (a solver that produces its own extension gives
`∀ i, ∃ K₂ i` and cannot be used), and the composition back down, which is proved
(`Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_tensorCancel`).  The cyclotomic
parameter of the
mixed-characteristic branch is discharged inside it, by the family analogue of Tag 09F8's
char-zero entry branch, for which
`isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField` is the replacement of the
`IsAlgClosed`-dependent `isWeakSolution_of_finite_extension`. -/

/-- **The layer recursion for the complete perfect-residue case, as a statement.**

Read `ι` as the conjugate family to be solved: one base `A ⊆ K`, and per member a tower
`A ⊆ B i ⊆ C i` over `K ⊆ L i ⊆ M i` with `B i / A` weakly unramified and `M i / L i` finite and
normal of degree at most `n`.  The conclusion produces **one** finite `K₂ / K` which is a weak
solution for `A → C i` simultaneously for every `i`.

The single existential outside the `∀ i` is the whole content of the shape; see the module
docstring for why a per-member existential cannot be repaired afterwards over a perfect residue
field.

`[∀ i, ExpChar (ResidueField (B i)) p]` is an explicit instance argument rather than a derived one,
for the reason `Stacks.EliminateRamification.EppTheorem` gives for the same choice: the statement
  then mentions no
instance that is not already in scope.  It is free, from `p.Prime` and `CharP κ_A p` and
injectivity of `κ_A → κ_{B i}`, so it costs no generality. -/
abbrev FamilyTowerSolvable (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∀ (ι : Type u) [Finite ι]
    (A K : Type u) (B C L M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP (ResidueField A) p] [∀ i, ExpChar (ResidueField (B i)) p]
    [PerfectField (ResidueField A)]
    [IsAdicComplete (maximalIdeal A) A]
    [∀ i, IsAdicComplete (maximalIdeal (B i)) (B i)]
    (_hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)] [∀ i, Normal (L i) (M i)]
    (_hepp : ∀ i, EppCondition A (B i) p)
    (_hdegree : ∀ i, Module.finrank (L i) (M i) ≤ n),
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₂,
        D.IsWeakSolution

/-! ### Epp's Theorem (1.3) -/

/-- A ring map between discrete valuation rings that is injective and local is an extension. -/
private theorem isExtension_of_injective_of_isLocalHom (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] (hinj : Function.Injective (algebraMap A B))
    (hloc : IsLocalHom (algebraMap A B)) :
    IsExtension A B :=
  { (faithfulSMul_iff_algebraMap_injective A B).mpr hinj, hloc with }

/-- **Epp's Theorem (1.3): the complete case of Epp's theorem over a perfect residue field.**

Let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction fields `K ⊆ L ⊆ M`, with
`A` and `B` complete, the residue characteristic of `A` a prime `p`, the residue field of `A`
perfect, `B / A` weakly unramified, `M / L` finite, and Epp's condition
`Stacks.EppTheorem.EppCondition A B p` — every element of `⋂_{n ≥ 1} κ_B^{p^n}` separable algebraic
  over
`κ_A`.  Then there is a finite extension `K₁ / K` which is a weak solution for `A → C`.

This is Epp's Theorem (1.3), whose hypotheses are Kuhlmann's `S₀ / R` weakly unramified and
`S / S₀` `p`-cyclic; the degree of `M / L` is not restricted to `p` here because the layer
recursion reduces it.  Note what is **not** assumed: `L / K` is arbitrary, so `κ_B / κ_A` may be an
infinite extension.  That is where Epp's condition does its work, and it is why the tower form is
the theorem and the two-ring form below is only a corollary.

The recursion is consumed at **every** degree, not at `Module.finrank L M`: the proof replaces
`M / L` by its normal closure `N / L`, whose degree is not bounded by that of `M / L`.  Tag 09F8's
entry point has the same shape.

The proof is four steps and contains no residue-field argument of its own; all of the mathematics
is in `FamilyTowerSolvable` and in what that consumes.

1. If `A → C` is already weakly unramified, `K₁ = K` works, by
   `isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField` — which is where perfectness of
   `κ_A` is spent directly.
2. Otherwise replace `M` by the normal closure `N` of `M / L` and `C` by
   `C' = integralClosure C N`, which `integralClosure_isCompleteDVR` makes a complete discrete
   valuation ring, module-finite over `C`, with fraction field `N`.  **The middle ring `B` is
   untouched**, so `hweak` and `hepp` transfer verbatim and no ascent of Epp's condition happens at
   this level; the ascent is the recursion's business and `EppCondition.of_module_finite` is what
serves it there. 3. Apply the recursion once, at the singleton family `ι := PUnit`, degree bound
   `Module.finrank L N`.
4. Descend along `A ⊆ C ⊆ C'` by `exists_isWeakSolution_of_tower`, the go-down half of Tag 09ES. -/
theorem exists_finite_extension_isWeakSolution_of_perfectField
    (p : ℕ) [Fact p.Prime]
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [CharP (ResidueField A) p] [ExpChar (ResidueField B) p]
    [PerfectField (ResidueField A)]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B]
    (hweak : IsWeaklyUnramified A B)
    [Module.Finite L M]
    (hepp : EppCondition A B p)
    (hfam : ∀ n : ℕ, FamilyTowerSolvable.{u} p n) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K₁,
        D.IsWeakSolution := by
  classical
  -- Step 1: the already-weakly-unramified shortcut.
  by_cases hAC : IsWeaklyUnramified A C
  · obtain ⟨D⟩ := nonempty_integralClosureBaseChange A C K M K
    exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      D, isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField A C K M K D hAC⟩
  -- Step 2: replace `M` by the normal closure `N` of `M / L`, and `C` by its integral closure.
  obtain ⟨N, _instFieldN, _instAlgLN, _instAlgMN, _instTowerLMN, _instFinLN, _instNormalLN⟩ :=
    exists_normalClosure_data L M
  let : Module.Finite M N := Module.Finite.right L M N
  let : Algebra K N := ((algebraMap M N).comp (algebraMap K M)).toAlgebra
  let : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq fun k => by
    change algebraMap M N (algebraMap K M k) = algebraMap L N (algebraMap K L k)
    rw [IsScalarTower.algebraMap_apply K L M, ← IsScalarTower.algebraMap_apply L M N]
  let : Algebra C N := ((algebraMap M N).comp (algebraMap C M)).toAlgebra
  let : IsScalarTower C M N := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A N := ((algebraMap C N).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C N := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A K N := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap M N (algebraMap C M (algebraMap A C a)) =
      algebraMap M N (algebraMap K M (algebraMap A K a))
    rw [← IsScalarTower.algebraMap_apply A C M, ← IsScalarTower.algebraMap_apply A K M]
  -- Completeness of the top of the tower is derived, not assumed, exactly as Tag 09F8 derives it:
  -- over a complete middle `B` the top `C` *is* the integral closure of `B` in `M`, hence
  -- module-finite over `B`, hence complete.
  let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
  let : Module.Finite B (integralClosure B M) :=
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
  let : Module.Finite B C := Module.Finite.equiv
    (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv
  let : IsAdicComplete (maximalIdeal C) C := isAdicComplete_of_finite B C
  let C' := integralClosure C N
  obtain ⟨hC', hextCC', hfinCC', hcompC', hfracC'⟩ := integralClosure_isCompleteDVR C M N
  let : IsDiscreteValuationRing C' := hC'
  let : IsExtension C C' := hextCC'
  let : Module.Finite C C' := hfinCC'
  let : IsAdicComplete (maximalIdeal C') C' := hcompC'
  let : IsFractionRing C' N := hfracC'
  let : Algebra A C' := ((algebraMap C C').comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C C' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A C' N := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap C N (algebraMap A C a) =
      algebraMap C' N (algebraMap C C' (algebraMap A C a))
    rw [← IsScalarTower.algebraMap_apply C C' N]
  let : IsExtension A C' := isExtension_of_injective_of_isLocalHom A C'
    ((FaithfulSMul.algebraMap_injective C C').comp (FaithfulSMul.algebraMap_injective A C))
    (RingHom.isLocalHom_comp (algebraMap C C') (algebraMap A C))
  let : Algebra B N := ((algebraMap M N).comp (algebraMap B M)).toAlgebra
  let : IsScalarTower B M N := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B L N := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap M N (algebraMap B M b) = algebraMap L N (algebraMap B L b)
    rw [IsScalarTower.algebraMap_apply B L M, ← IsScalarTower.algebraMap_apply L M N]
  let : IsScalarTower B C N := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap M N (algebraMap B M b) =
      algebraMap M N (algebraMap C M (algebraMap B C b))
    rw [← IsScalarTower.algebraMap_apply B C M]
  let : Algebra B C' := ((algebraMap C C').comp (algebraMap B C)).toAlgebra
  let : IsScalarTower B C C' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B C' N := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap M N (algebraMap B M b) =
      algebraMap C' N (algebraMap C C' (algebraMap B C b))
    rw [← IsScalarTower.algebraMap_apply C C' N]
    exact IsScalarTower.algebraMap_apply B C N b
  let : IsScalarTower A B C' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap C C' (algebraMap A C a) =
      algebraMap C C' (algebraMap B C (algebraMap A B a))
    rw [← IsScalarTower.algebraMap_apply A B C]
  let : IsExtension B C' := isExtension_of_injective_of_isLocalHom B C'
    ((FaithfulSMul.algebraMap_injective C C').comp (FaithfulSMul.algebraMap_injective B C))
    (RingHom.isLocalHom_comp (algebraMap C C') (algebraMap B C))
  -- Step 3: one call to the layer recursion, at the singleton family.
  obtain ⟨K₁, hK₁field, hKK₁, hAK₁, hAKK₁, hfinKK₁, hsol⟩ :=
    hfam (Module.finrank L N) PUnit A K (fun _ => B) (fun _ => C') (fun _ => L) (fun _ => N)
      (fun _ => hweak) (fun _ => hepp) (fun _ => le_rfl)
  let := hK₁field
  let := hKK₁
  let := hAK₁
  let := hAKK₁
  let := hfinKK₁
  -- Step 4: descend along `A ⊆ C ⊆ C'` by the go-down half of Tag 09ES.
  exact exists_isWeakSolution_of_tower A C C' K M N
    ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      hsol PUnit.unit⟩

/-! ### The adic completion of a discrete valuation ring, as an extension

Obligation **O6**, the *ascent* side of the completion step.
`StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionDescent` proves the descent — from a
weak solution for `A^ → B^` to one for `A → B` — with no completeness hypothesis anywhere and the
whole completion-specific content isolated into one hypothesis, that `K₁ / K` is a weak solution
for `A → A^`.  What it does not supply, and what nothing in the tree supplied, is the ascent: that
`AdicCompletion (𝔪 B) B` *is* a discrete valuation ring extending `B` with the same residue field.

Two corrections to the record, both found by looking rather than by recollection.

* `isDiscreteValuationRing_iff_adicCompletion_maximalIdeal`
  (`StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties`, `@[stacks 0AP1]`, public)
  already proves that the completion of a discrete valuation ring is one.  Two comments in the tree
  say otherwise — `EppWildCaseReduction.lean` and `EppFiniteSupportStrong.lean` both record the
  construction as "still missing" — and **those comments are stale**.
* the residue-field half is Mathlib's `AdicCompletion.residueField_map_bijective`, also public.

So the only genuinely missing piece was the assembly into
`IsDiscreteValuationRing.IsExtension`, which is what this section adds. -/

/-! ### The Cohen-ring interposition: the two-ring case with no finiteness upstairs

Obligation **O11**, and a correction to how this note's first version described it.

§2's tower carries `Module.Finite L M`, as Tag 09F8 does — and Tag 09F8 carries it because the
*Stacks statement* of 09F8 carries it, as hypothesis (4), "`M` is a finite extension of `L`".  Tag
09F9 assumes no finiteness anywhere.  One might expect the reduction to be "a directed colimit
over the finite subextensions of `L / K`".  **That is not the published mechanism and there is
no such colimit in the proof.**  Reading Tag 09F9's own proof text settles it: what supplies the
finiteness
is a *Cohen-ring interposition*.  With `A` complete and `κ_A` equal to the perfect core of `κ_B`,
one takes `Λ` a Cohen ring for `κ_B` (mixed characteristic) or `κ_B[[t]]` (equal characteristic),
lifts `A → Λ` over `κ_A → κ_B` carrying a uniformizer to a uniformizer, factors `A → B` as
`A → Λ → B`, and then `Λ` and `B` are complete discrete valuation rings with the *same* residue
field, so `B` is finite over `Λ` by Tag 031D.  The tower `A ⊆ Λ ⊆ B` is then exactly 09F8's input
shape, and no finiteness of `L / K` was ever needed.

Two things make this work over a merely *perfect* base residue field, rather than only over an
algebraically closed one:

* the separability `κ_A ⊆ κ_Λ = κ_B` that Tag 09E7 needs is **free**, because every extension of a
  perfect field is separable — in the published proof this is read off from `k` being the perfect
  core, and perfectness is all that is used;
* the Epp condition is given at `B`, while the tower needs it at the *middle* `Λ`; that is
  `Stacks.EppTheorem.EppCondition.of_tower`, which needs neither finiteness nor perfectness.

So the theorem below is the two-ring case of Epp's theorem in the complete perfect-residue setting,
with **no** finiteness hypothesis on `L / K`. -/

/-- **The two-ring case, with no finiteness upstairs: Epp's theorem for `A → B` itself.**

Let `A ⊆ B` be an extension of complete discrete valuation rings with fraction fields `K ⊆ L`,
residue characteristic `p`, `κ_A` perfect, and Epp's condition `EppCondition A B p`.  **`L / K` is
not assumed finite.**  Suppose given the Cohen-ring interposition of Tag 09F9's proof: a complete
discrete valuation ring `Λ` factoring `A → B`, receiving some uniformizer of `A` as a uniformizer,
and with `κ_Λ → κ_B` surjective.  Then there is a finite `K₁ / K` which is a weak solution for
`A → B`.

The proof is short because every piece is in place: `Module.Finite Λ B` from
`module_finite_of_residueField_map_surjective` (Tag 031D), `Module.Finite E L` from
`finiteDimensional_fractionRing_of_finite`, `IsWeaklyUnramified A Λ` from
`isWeaklyUnramified_of_irreducible_algebraMap`, `EppCondition A Λ p` from `EppCondition.of_tower`,
and then one application of `exists_finite_extension_isWeakSolution_of_perfectField` to the tower
`A ⊆ Λ ⊆ B`, whose conclusion *is* a weak solution for `A → B`.  No descent along Tag 09ES is
needed, because the interposed ring is the middle of the tower and not a new base.

**What remains, named exactly.** The interposition is a hypothesis here, and constructing it
is two things the tree does not have: the existence of `Λ` — a Cohen
ring for `κ_B`, or `κ_B[[t]]` — and the factorisation of `A → B` through it, which in the source is
Tag 07NJ.  `StacksFrontier.RingTheory.DiscreteValuationRing.EppCohenReduction` records both as
hypotheses for the same reason and documents the obstruction: this tree's 07NJ is
`RingHom.FormallySmoothTop.exists_continuous_lift_of_isAdic`, in the *topological* form, and the
bridge to the algebraic form needs the source ring to carry the discrete topology, which `A` does
not.  So the remaining step is reduced to those two named links. -/
theorem exists_finite_extension_isWeakSolution_of_perfectField_of_cohenTower
    (p : ℕ) [Fact p.Prime]
    (A Λ B K E L : Type u)
    [CommRing A] [CommRing Λ] [CommRing B]
    [IsDomain A] [IsDomain Λ] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing Λ] [IsDiscreteValuationRing B]
    [Field K] [Field E] [Field L]
    [Algebra A Λ] [Algebra Λ B] [Algebra A B]
    [Algebra A K] [Algebra Λ E] [Algebra B L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [Algebra A E] [Algebra Λ L] [Algebra A L]
    [IsScalarTower A Λ B] [IsScalarTower A Λ E] [IsScalarTower A K E]
    [IsScalarTower Λ B L] [IsScalarTower Λ E L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower K E L]
    [IsExtension A Λ] [IsExtension Λ B] [IsExtension A B]
    [IsFractionRing A K] [IsFractionRing Λ E] [IsFractionRing B L]
    [CharP (ResidueField A) p] [ExpChar (ResidueField B) p]
    [PerfectField (ResidueField A)]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal Λ) Λ]
    {πA : A} (_hπA : Irreducible πA) (hπΛ : Irreducible (algebraMap A Λ πA))
    (hres : Function.Surjective (ResidueField.map (algebraMap Λ B)))
    (hepp : EppCondition A B p)
    (hfam : ∀ n : ℕ, FamilyTowerSolvable.{u} p n) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L K₁,
        D.IsWeakSolution := by
  -- Tag 031D: `Λ` and `B` have the same residue field, so `B` is finite over `Λ`.
  have hfinΛB : Module.Finite Λ B := module_finite_of_residueField_map_surjective hres
  let := hfinΛB
  -- Hence the fraction fields are finite over each other, which is the finiteness 09F8's tower
  -- wants at the top — supplied here rather than assumed of `L / K`.
  have : Module.Finite E L :=
    finiteDimensional_fractionRing_of_finite Λ B E L (FaithfulSMul.algebraMap_injective Λ B)
  -- The middle of the tower is weakly unramified over the base because a uniformizer goes to one.
  have hweak : IsWeaklyUnramified A Λ := isWeaklyUnramified_of_irreducible_algebraMap A Λ πA hπΛ
  have : ExpChar (ResidueField Λ) p := by
    have : CharP (ResidueField Λ) p := CharP.of_ringHom_of_ne_zero
      (algebraMap (ResidueField A) (ResidueField Λ)) p (Fact.out : p.Prime).ne_zero
    exact ExpChar.prime (Fact.out : p.Prime)
  exact exists_finite_extension_isWeakSolution_of_perfectField p A Λ B K E L hweak
    (EppCondition.of_tower hepp) hfam

/-! ### The cyclotomic parameter, in the perfect setting

Obligation §8.2 of the interface note.  `FamilyTowerSolvable` deliberately carries no `hcyclo`,
unlike `NormalTowerSolvable`: the cyclotomic parameter of the mixed-characteristic branch is to be
discharged inside the recursion, by the family analogue of Tag 09F8's char-zero entry branch.  What
that branch needs, and what this section supplies, is the base change to a field containing the
`p`-th roots of unity *together with* the fact that all of the complete perfect-residue setting's
hypotheses survive at the new base. -/

/-! ### The universe descent, and why it is free at one factor

Obligation §8.3 of the interface note: §2 is monomorphic, and
  `Stacks.EliminateRamification.EppTheorem` needs four
independent universes with the solution field in `uK`.

Tag 09F8 does its own polymorphism by `ULift`ing six carriers onto a same-universe core and then
coming back down in four moves.  Three of them — `exists_isWeakSolution_of_integral_ring_extension`
and `exists_isWeakSolution_of_ulift_fraction_fields`, and the `ULift` setup itself — carry **no**
`IsAlgClosed`.  The fourth does: the last move takes the solution field `E`, which lives in the
joined universe, down to `uK` by `exists_finite_extension_forall_isWeakSolution`, whose proof
embeds `E` into a field `F : Type uK` and then moves the weak solution along `E ⊆ F` by
`isWeakSolution_of_finite_extension` — an `IsAlgClosed` theorem, and necessarily so, because a weak
solution does **not** survive an arbitrary finite enlargement of the base over a merely perfect
residue field.

The observation that unblocks this: `exists_finite_extension_forall_isWeakSolution` pays
`IsAlgClosed` for handling *finitely many* factors at once, by taking a common overfield of the
family.  **At one factor the overfield is the field itself.**  Writing
`f : E →ₐ[K] AlgebraicClosure K` for the lift, `f.fieldRange` lives in `Type uK` and
`AlgHom.equivFieldRange` is an *isomorphism* `E ≃ₐ[K] f.fieldRange` — not a proper enlargement.
Transport along an isomorphism of the extension field needs no residue hypothesis at all, so the
descent is free in the perfect setting, for the single factor of the conclusion here.

`Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_ringEquiv_square` is the
  transport, and it is already stated with all
fourteen universes of the two packages independent, which is what makes it usable here. -/

/-! ### The algebraic form of Tag 07NJ, as a bridge

The first of the two links §8.1 left open. `EppCohenReduction.lean` records step (b) of the
Cohen-ring reduction — the factorisation `A → Λ → B` — as a *hypothesis*, and its module docstring
gives the reason: Tag 07NJ is available here only as
`RingHom.FormallySmoothTop.exists_continuous_lift_of_isAdic`, in the topological form, while Tag
09E7 delivers the algebraic form `FormallySmoothNAdic`, and the only bridge between them
(`formallySmoothTop_iff_formallySmoothNAdic`) required the **source** to carry the discrete
topology, which `A` does not.

That is now fixed at the root rather than worked around: `formallySmoothTop_of_formallySmoothNAdic`
(`StacksFrontier.RingTheory.FormallySmooth.Adic`) is the `mpr` half of that equivalence stated
without
`[DiscreteTopology R]`, the hypothesis being needed only by the forward direction. **Tag 07NJ
itself is not restated**; what follows supplies its topological hypotheses and calls it.

The topological infrastructure the docstring called missing is `WithIdeal`: one instance per ring
installs the adic topology and yields `IsTopologicalRing`, `IsLinearTopology`, a uniform structure,
and makes `IsAdic` hold by `rfl`. -/

/-! ### Link 2 of the Cohen interposition, equal characteristic

Obligation §8.1 of the interface note.  Link 1 (above) factors `A → B` through a given `Λ`; link 2
produces the `Λ`.  In equal characteristic it is concrete: `A ≅ κ_A⟦π⟧` by the structure theorem,
so pushing the coefficients along `κ_A → κ` gives `Λ = κ⟦X⟧` with the uniformizer going to `X`.

What the note recorded as the expensive part of this half — an identification
`κ_{κ⟦X⟧} ≅ κ` with "no ready provider" — was **wrong**: it is
`PowerSeries.residueFieldOfPowerSeries` in Mathlib, and the two 09ET counterexample files that the
note pointed at as the nearest machinery were simply *using* the Mathlib definition.  Nor is a
`constantCoeff`/`map` commutation lemma needed: that identity holds by `rfl`.  So the only thing
this half actually needed built was the map, plus one exposure
(`Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_powerSeries`, for
completeness of `κ⟦X⟧`).

Completeness of `Λ` is *not* a conjunct below because it needs no hypothesis of this lemma: a
caller binds it directly as
`Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_powerSeries κ`. -/

/-! ### Injectivity of link 1's lift — `IsExtension Λ B`

Obligation §8.1 of the interface note, and the debt that section predicted would be discovered
late.  `exists_lift_of_formallySmoothNAdic` returns a **ring map** `φ : Λ →+* B`, while
`exists_finite_extension_isWeakSolution_of_perfectField_of_cohenTower` binds `[IsExtension Λ B]`,
which additionally wants `φ` injective.  Injectivity does not follow from the lifting property: `φ`
is local, so `RingHom.ker φ` is a prime of the discrete valuation ring `Λ`, and formally it could
be `𝔪_Λ` rather than `0`.

It does follow from one extra fact the tower already has, and this is what the note did not see:
`φ` restricted along `A → Λ` **is** `A → B`, which is injective because `[IsExtension A B]`.  So a
uniformizer of `A` cannot die in `B`, hence cannot die in `Λ`, hence `𝔪_Λ ⊄ ker φ`.  That argument
needs no characteristic hypothesis and no completeness, so it closes the debt in **both**
characteristics at once rather than once per branch — which is why it is here and not inside either
half of link 2. -/

end Stacks.EppTheorem

end
