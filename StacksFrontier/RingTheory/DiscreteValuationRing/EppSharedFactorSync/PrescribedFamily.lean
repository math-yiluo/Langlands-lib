module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.WildLayerDescent

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The prescribed family and the base of the layer recursion

`EppMember`, one layer of the prescribed base change at the package level, the prescribed-family
descent, and the base case `familyTowerSolvable_one` of `FamilyTowerSolvable` with the
prime-degree solver obligations.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

universe u

/-! ### The prescribed family at the ring-theoretic level

The three preceding sections are induction principles: `Solves` is a parameter, so none of them is
a weak-solution theorem.  This section instantiates the outer induction
(`Stacks.EppTheorem.forall_solves_of_family_descent`) at the package level, which means choosing
  the member
type, the measure and `Solves` concretely and *proving* the step.

**The setting is complete with a PERFECT residue field, not an algebraically closed one**, and this
is a correction to the setting one might first expect.  The reason is
that after the Cohen reduction the base residue field is
`perfectCore κ_B p`, which is perfect and in general *not* algebraically closed — `κ_A = κ_B =
𝔽_p(x)` has perfect core `𝔽_p` — and the published upgrade from perfect to algebraically closed
runs through Tag 09ET, whose weak-solution clause is false.
So a layer machinery stated over an algebraically
closed residue field would be machinery for a hypothesis the route cannot reach, and the members
here carry `PerfectField (IsLocalRing.ResidueField A)`.

Nothing in the section needed the stronger hypothesis, which is worth stating because it was
checked rather than assumed: `canonicalBaseChange` is unconditional,
`integralClosure_isCompleteDVR` and `integralClosure_factor_isExtension` want only completeness,
`finiteFieldFactors_compatible` and `isWeakSolution_of_iterated_packages` want neither, and the one
place the old setting was used — the residue-field ascent at the new member's base — is discharged
by `perfectField_residueField_of_finite` above, whose proof is shorter than the algebraically
closed one.

**The measure is `Module.finrank d.K K₂`, and that is a correction to the plan this section was
written from.** The plan proposed `deg d := Module.finrank d.K d.L`, the degree of the member's own
extension. That measure does not work with a single prescribed `K₂`, and the reason is worth
recording because it is structural rather than technical.

`isWeakSolution_of_iterated_packages` is the only composition in the tree whose hypotheses and
conclusion speak about **one** base change: it reduces a weak solution for `(A, B, K, L)` over `K₂`
to weak solutions for the factor members `(A₁, B₁, K₁, E i)` over the *same* `K₂`, where
`K ⊆ K₁ ⊆ K₂`.  So it moves the member's base *up* inside `K₂` and replaces `L` by the factors of
`(L ⊗[K] K₁) ⧸ nilradical`.  Those factors satisfy `∑ᵢ [E i : K₁] ≤ [L : K]`, so the extension
degree never increases — and never provably decreases either: with `K₁ = K` the reduction is the
identity, and with `L ⊗[K] K₁` a field the new member has exactly the old degree.  A strict drop in
`[L : K]` requires the *tower* split instead, which is Tag 09ES
(`isWeakSolution_of_prime_layer_of_forall_factor` above); but there the upper layer's base change
is a **factor** `E i` of the lower layer's, not `K₂`, so its members do not inhabit a family whose
resource is one fixed field.  The two are not interchangeable, and with `K₂` fixed only the first
is available.

What does strictly decrease is the part of the prescribed base change still to be made.  The
splitting lemma applied to `K₂ / d.K` produces a prime-degree layer `K₁`, and
`Module.finrank_mul_finrank` (inside
`exists_intermediateField_prime_finrank_of_isSolvable`) gives `[K₂ : K₁] < [K₂ : K]`.  So the
descent walks the prescribed extension one prime layer at a time, re-entering at the factor members
each time, and terminates when the member's base *is* `K₂`.

**Read the residual hypothesis literally.** `hterminal` is applied exactly at the members whose
base field is already `K₂`, where `Solves` unwinds to `d.A → d.B` being weakly unramified: for such
a member the base change is the trivial one.  That is the shared-solver obligation, and it is
*stronger* than a bare degree-`p` solver, since the
descent above does not reduce the extension degree.  Nothing here discharges it, nothing here is
tagged, and no unconditional Tag 09F9 follows.

**Two things that have to be said rather than left for a reader to notice.**

First, `hterminal` is **not** a theorem, and it is not merely unproved: quantified over all members
it is *false*, because a ramified extension of complete discrete valuation rings whose base field
is already `K₂` is a member.  So `forall_solves_of_prescribed_family` is an induction principle
with a concrete `Solves` — not a weak-solution theorem — and what it contributes is that the
package-level step is proved and compiled.  Discharging the obligation means restricting the
members to the ones the route actually produces, which is what `Stacks.EppTheorem.FactorSolutions`
  earlier in this file does.

Second, because the measure counts only the base change, the induction does no work a single step
would not: `exists_factorMembers_of_layer` at `K₁ := K₂` sends every member straight to members of
measure `1`.  That single step is stated unconditionally as
`Stacks.EppTheorem.exists_terminalMembers`, which is therefore the section's non-vacuous content,
  and the
form a consumer should prefer.  A layer induction that genuinely consumes degree-`p` solvers one
layer at a time has to reduce `[L : K]`, which — by the paragraph above — means the 09ES tower
split, and therefore members carrying the factor field they are checked against rather than one
field fixed for the whole family.  That is the next increment, and it is a change to the member
datum, not to the descent.

The Galois and solvability hypotheses are on `K₂ / d.K`, not on the member's own extension, and
they are threaded through the descent rather than assumed for every intermediate field, because the
splitting lemma re-supplies them for the layer it produces.  A caller has them: the wild
construction exposes `IsGalois K₁ K₂`, and a base change built as a tower of degree-`p` layers is
solvable. -/

section PrescribedFamily

open IsDiscreteValuationRing

variable {K₂ : Type u} [Field K₂]

end PrescribedFamily

/-! ### `FamilyTowerSolvable`: the base of the layer recursion

`Stacks.EppTheorem.FamilyTowerSolvable` (`EppPerfectResidueComplete.lean`) is the layer
recursion.  It is proved by
strong induction on the degree bound `n`; what is here is the **base**, `n = 1`, which needs no
recursion, no prescribed extension and no terminal solver, and which the induction's other branches
all reduce to.

Two things make it as short as it is, and both arrived with the perfect-residue complete case rather
than being built here:

* `isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField` — at a member that is *already*
  weakly unramified, **every** finite base change is a weak solution, over a merely perfect residue
  field and with no completeness hypothesis.  This is the replacement of the
  `IsAlgClosed`-dependent `isWeakSolution_of_finite_extension` that §3 note (c) names, and it is
  why `K₂ := K` serves here.
* `canonicalBaseChange`, which supplies the package unconditionally.

So no extension is produced at all in this branch: the existential is discharged by `K` itself,
which is the degenerate case of the discipline that `∃ K₂` sits outside `∀ i` — one field, namely
the base, for every member at once. -/

section TowerFamily

open IsDiscreteValuationRing

/-- A DVR over a complete DVR, with finite fraction extension, is module-finite over it. -/
private theorem module_finite_of_isAdicComplete_of_finite_fractionRing
    (B C L M : Type*)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M] [Algebra B C] [Algebra B L] [Algebra C M]
    [Algebra L M] [Algebra B M] [IsScalarTower B L M] [IsScalarTower B C M]
    [IsFractionRing B L] [IsFractionRing C M] [IsDiscreteValuationRing.IsExtension B C]
    [Module.Finite L M] [IsAdicComplete (IsLocalRing.maximalIdeal B) B] :
    Module.Finite B C := by
  let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
  let : Module.Finite B (integralClosure B M) :=
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
  exact Module.Finite.equiv (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv

/-- **At a member whose upper layer is trivial, the whole tower is weakly unramified.**

Factored out because both the base of the recursion and its mixed levels need it: the degree-one
member is the one that can be *carried* against whatever extension the level produced, and this is
what makes that sound. The three lines establishing `Module.Finite B C` are the opening of Tag
09F8's own `normalTowerSolvable` — `C` is module-finite over `B` because, `B` being complete and
`M / L` finite, it *is* the integral closure. -/
theorem isWeaklyUnramified_of_finrank_eq_one
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra B L] [Algebra C M] [Algebra L M] [Algebra B M]
    [IsScalarTower A B C] [IsScalarTower B C M] [IsScalarTower B L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing B L] [IsFractionRing C M]
    [Module.Finite L M] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (hweak : IsWeaklyUnramified A B) (h1 : Module.finrank L M = 1) :
    IsWeaklyUnramified A C := by
  let : Module.Finite B C := module_finite_of_isAdicComplete_of_finite_fractionRing B C L M
  refine isWeaklyUnramified_trans A B C hweak ?_
  have hd := ramificationIdx_dvd_finrank_of_isLocalRing B C
  rw [← IsFractionRing.finrank_eq B L C M, h1] at hd
  exact (isWeaklyUnramified_iff_ramificationIdx_eq_one B C).mpr (Nat.dvd_one.mp hd)

/-- **The shared prime-degree family solver, per layer, in the producer form the tower step
consumes.**

This interface is in the library because `familyTowerSolvable_of_forall_terminal` below is its
proved consumer.

It is `FamilyTowerSolvable` with two changes, each from that note's design table:

* the degree bound is replaced by the per-member alternative that
  `exists_finite_extension_isWeakSolution_of_prime_degree` takes verbatim — purely inseparable of
  degree exactly `p`, or Galois of prime degree;
* `Normal (L i) (M i)` is dropped, because that theorem does not assume it.

**It is a producer, not a predicate, and that is the whole point of the shape.** A prescribed
predicate — "if `K₂` has property `P` then every terminal member is solved" — does not close the
tower step: something must still produce a `K₂` that has `P` *and* serves the level's non-terminal
members, and combining two independently produced extensions is the amalgamation the route forbids.
So the existential sits outside `∀ i` here, exactly as in `FamilyTowerSolvable`, and O2 owes one
finite `K₂ / K` computed from bounds over the whole family before any member is examined. -/
abbrev FamilyPrimeDegreeSolvable (p : ℕ) [Fact p.Prime] : Prop :=
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
    [CharP (IsLocalRing.ResidueField A) p] [∀ i, ExpChar (IsLocalRing.ResidueField (B i)) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (_hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)]
    (_hepp : ∀ i, EppCondition A (B i) p)
    (_hterminal : ∀ i,
      IsPurelyInseparable (L i) (M i) ∧ Module.finrank (L i) (M i) = p ∨
        IsGalois (L i) (M i) ∧ (Module.finrank (L i) (M i)).Prime),
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₂,
        D.IsWeakSolution

/-- The one-member prime-degree obligation underlying `FamilyPrimeDegreeSolvable`.

This interface deliberately has exactly the hypotheses of one member of the family statement.  It
is separated out because, over a perfect base residue field, weak solutions survive arbitrary
further finite extensions: finitely many independently obtained solution fields can therefore be
embedded in one finite overfield and all the solutions transported there. -/
abbrev PrimeDegreeSolvable (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (A B C K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C] [Algebra A K]
    [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing B L] [IsFractionRing C M] [IsFractionRing A K]
    [CharP (IsLocalRing.ResidueField A) p] [ExpChar (IsLocalRing.ResidueField B) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B],
    IsWeaklyUnramified A B →
    ∀ [Module.Finite L M],
    EppCondition A B p →
    (IsPurelyInseparable L M ∧ Module.finrank L M = p ∨
      IsGalois L M ∧ (Module.finrank L M).Prime) →
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K₂,
        D.IsWeakSolution

/-- The genuinely wild part of the one-member prime-degree obligation: a Galois layer whose
degree equals the residue characteristic. -/
abbrev WildPrimeDegreeSolvable (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (A B C K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C] [Algebra A K]
    [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing B L] [IsFractionRing C M] [IsFractionRing A K]
    [CharP (IsLocalRing.ResidueField A) p] [ExpChar (IsLocalRing.ResidueField B) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B],
    IsWeaklyUnramified A B →
    ∀ [Module.Finite L M] [IsGalois L M],
    EppCondition A B p →
    Module.finrank L M = p →
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K₂,
        D.IsWeakSolution

/-- Purely inseparable layers and Galois layers of degree prime to the residue characteristic are
already solved.  Consequently the only one-member input needed for Epp's prime-degree step is the
Galois degree-`p` case. -/
theorem primeDegreeSolvable_of_wildPrimeDegreeSolvable (p : ℕ) [Fact p.Prime]
    (hwild : WildPrimeDegreeSolvable.{u} p) : PrimeDegreeSolvable.{u} p := by
  intro A B C K L M
  intros
  rename_i hweak _ hepp hterminal
  rcases hterminal with ⟨hpure, hdegree⟩ | ⟨hgal, hdegreePrime⟩
  · let := hpure
    exact exists_finite_extension_isWeakSolution_of_isPurelyInseparable
      A B C K L M p hdegree hweak
  · let := hgal
    by_cases hdegree : Module.finrank L M = p
    · exact hwild A B C K L M hweak hepp hdegree
    · let : Module.Finite B C := module_finite_of_isAdicComplete_of_finite_fractionRing B C L M
      let : IsAdicComplete (IsLocalRing.maximalIdeal C) C := isAdicComplete_of_finite B C
      have htame : ringChar (IsLocalRing.ResidueField A) = 0 ∨
          Nat.Coprime (ringChar (IsLocalRing.ResidueField A))
              (IsDiscreteValuationRing.ramificationIndex A C) ∧
            Algebra.StacksIsSeparableExtension (IsLocalRing.ResidueField A)
              (IsLocalRing.ResidueField C) := by
        refine Or.inr ⟨?_, Algebra.stacks_isSeparableExtension_of_perfectField _ _⟩
        rw [ringChar.eq (IsLocalRing.ResidueField A) p]
        have hd : IsDiscreteValuationRing.ramificationIndex B C ∣ Module.finrank L M := by
          rw [IsFractionRing.finrank_eq B L C M, ramificationIndex_eq_ramificationIdx B C]
          exact ramificationIdx_dvd_finrank_of_isLocalRing B C
        have he : IsDiscreteValuationRing.ramificationIndex A C =
            IsDiscreteValuationRing.ramificationIndex B C := by
          have h := Ideal.ramificationIdx_tower (R := A)
            (IsLocalRing.maximalIdeal B) (IsLocalRing.maximalIdeal C)
          rw [← ramificationIndex_eq_ramificationIdx A C,
            ← ramificationIndex_eq_ramificationIdx A B,
            ← ramificationIndex_eq_ramificationIdx B C] at h
          simpa only [show IsDiscreteValuationRing.ramificationIndex A B = 1 from hweak, one_mul]
            using h
        rw [he]
        exact ((Nat.coprime_primes (Fact.out : p.Prime) hdegreePrime).mpr
          (Ne.symm hdegree)).of_dvd_right hd
      obtain ⟨K₂, hK₂, hKK₂, hAK₂, htower, hfin, -, D, hD⟩ :=
        exists_finite_extension_isWeakSolution_of_tame_or_charZero A C K M htame
      exact ⟨K₂, hK₂, hKK₂, hAK₂, htower, hfin, D, hD⟩

/-- A one-member prime-degree solver automatically gives the synchronized finite-family solver
over a perfect residue field.

Apply the one-member solver independently, embed the finitely many resulting fields in one finite
overfield, and use
`exists_finite_extension_forall_isWeakSolution_of_perfect_residueField` to preserve every weak
solution.  Thus the synchronization once built into the degree induction is not additional
mathematics in the perfect-residue setting. -/
theorem familyPrimeDegreeSolvable_of_primeDegreeSolvable (p : ℕ) [Fact p.Prime]
    (hsingle : PrimeDegreeSolvable.{u} p) : FamilyPrimeDegreeSolvable.{u} p := by
  intro ι _ A K B C L M
  intros
  rename_i hweak _ hepp hterminal
  have hsol : ∀ i, ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
      (_ : IsScalarTower A K E) (_ : Module.Finite K E),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
        A (C i) K (M i) E, D.IsWeakSolution := fun i =>
    hsingle A (B i) (C i) K (L i) (M i) (hweak i) (hepp i) (hterminal i)
  choose E hE hKE hAE htower hfin D hD using hsol
  let := hE
  let := hKE
  let := hAE
  let := htower
  let := hfin
  let : ∀ i, Module.Finite (B i) (C i) := fun i =>
    module_finite_of_isAdicComplete_of_finite_fractionRing (B i) (C i) (L i) (M i)
  let : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (C i)) (C i) := fun i =>
    isAdicComplete_of_finite (B i) (C i)
  exact exists_finite_extension_forall_isWeakSolution_of_perfect_residueField
    A K C M E D hD

end TowerFamily

end Stacks.EppTheorem

end
