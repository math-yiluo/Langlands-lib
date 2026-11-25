module

import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Std.Tactic.BVDecide.Normalize.Prop

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.MinimalPrime.Colon
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import StacksFrontier.RingTheory.Depth.Criteria
import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

/-!
# Depth along the maximal ideal is the minimum of the depths of the localizations

Proof of `Module.depth_eq_iInf_depth_isLocalized_maximal` (Stacks 0AUK): for `(R, 𝔪)` a
Noetherian local ring, `R → S` a finite ring map and `N` a finite `S`-module,

`depth_𝔪(N) = ⨅_{𝔪ᵢ ⊆ S maximal} depth(N_{𝔪ᵢ})`.

Since `S` is integral over `R`, contraction along `R → S` carries the maximal ideals of `S` onto
`𝔪` and reflects maximality, so the maximal ideals of `S` are exactly the primes lying over `𝔪`.
Both sides are computed by the same data, the lists of elements of `𝔪` that are weakly `N`-regular
(Stacks 0AUI), and the proof consists of the two implications relating such a list to the
localizations.

For `≤`: a list of `n` elements of `𝔪` that is weakly `N`-regular stays weakly regular on
`N_{𝔪ᵢ}` over `S_{𝔪ᵢ}`, localization being flat, and there all its terms lie in the maximal ideal,
so `n ≤ depth(N_{𝔪ᵢ})`.

For `≥`, conversely, `n ≤ depth(N_{𝔪ᵢ})` for every `i` produces such a list, by induction on `n`.
For `n + 1` no localization has depth `0`, so no maximal ideal of `S` is associated to `N`: if a
maximal ideal `𝔮` is associated to `N`, witnessed by `m` with `𝔮 = √(0 : m)`, then a nonzerodivisor
on `N_𝔮` lying in the maximal ideal may be taken of the form `a/1` with `a ∈ 𝔮`, whereas `aᵏ m = 0`
for some `k` while `m` survives in `N_𝔮`; so `depth(N_𝔮) = 0`. Hence `𝔪 ∉ Ass_R(N)` (Stacks 05DZ),
so `𝔪` contains an element `x` that is a nonzerodivisor on `N` (Stacks 00LL), and dividing by `x`
drops every depth in sight by exactly one (Stacks 090R). The induction hypothesis applies to
`N/xN`, whose localizations are the `N_{𝔪ᵢ}/xN_{𝔪ᵢ}`, and `x` extends its list.

## Main results

* `Stacks.Depth.LocalizedInfimum.solution`: the tagged statement.

## Implementation notes

Neither side of the equality is ever evaluated: the two sides are compared through
`ENat.forall_natCast_le_iff_le`, which reduces the equality to the two implications above, so the
degenerate case `N = 0` — where both sides are `⊤` — needs no separate treatment.

The induction is run over `S`, not over `R`: it produces a list of elements of `R` whose image in
`S` is weakly `N`-regular, and the passage back to `R` happens once, at the end, through
`RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff`. Keeping the modules on the `S` side is
what lets the inductive step replace `N` by `QuotSMulTop (algebraMap R S x) N` without having to
compare an `R`-submodule of `N` with an `S`-submodule of `N`.

The localizations are carried through the induction as quantified data rather than replaced by
`Localization.AtPrime` and `LocalizedModule`; the inductive step localizes the quotient with
`Submodule.toLocalizedQuotient'`, transported along
`Submodule.localized' Sₘ T g (x • ⊤) = algebraMap S Sₘ x • ⊤` (`localized'_smul_top` below, a
consequence of `Submodule.localized'_smul` for the ideal `span {x}`). This is what avoids
transferring depth along an isomorphism of pairs (ring, module).

Three facts about `Module.depth` (Stacks 00LI) that Mathlib does not state, for lack of the
definition, are proved here as private lemmas; the first two also occur in the companion
statements Stacks 0FCC and 0BK4. They are: a weakly regular sequence in `I` has length at most
`depth_I(M)`; a nonzero `I`-depth produces a nonzerodivisor in `I`; and `n + 1 ≤ depth_I(M)` implies
`n ≤ depth_I(M/xM)` for `x ∈ I` a nonzerodivisor on `M`, the inequality form of Stacks 090R.

## References

* [StacksProject 0AUK](https://stacks.math.columbia.edu/tag/0AUK)
-/

@[expose] public section

namespace Stacks.Depth.LocalizedInfimum

open Ideal IsLocalRing Module Pointwise RingTheory.Sequence

universe u v w x y

section Depth

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
  (I : Ideal R)

/-- Dividing by a nonzerodivisor in `I` drops the `I`-depth by exactly one (Stacks 090R), so
`n + 1 ≤ depth_I(M)` gives `n ≤ depth_I(M/xM)`. -/
private theorem le_depth_quotSMulTop [IsNoetherianRing R] {x : R} (hx : x ∈ I)
    (hreg : IsSMulRegular M x) {n : ℕ} (h : ((n + 1 : ℕ) : ℕ∞) ≤ stacksDepth R I M) :
    (n : ℕ∞) ≤ stacksDepth R I (QuotSMulTop x M) := by
  rw [← (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I M).1 x hx hreg] at h
  push_cast at h
  exact (WithTop.add_le_add_iff_right (z := (1 : ℕ∞)) ENat.one_ne_top).mp h

end Depth

section Restrict

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {M : Type*}
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

end Restrict

section LocalizedQuotient

variable {S : Type*} [CommRing S] (T : Submonoid S) (Sₘ : Type*) [CommRing Sₘ] [Algebra S Sₘ]
  [IsLocalization T Sₘ] {N : Type*} [AddCommGroup N] [Module S N] {Nₘ : Type*} [AddCommGroup Nₘ]
  [Module S Nₘ] [Module Sₘ Nₘ] [IsScalarTower S Sₘ Nₘ] (g : N →ₗ[S] Nₘ) [IsLocalizedModule T g]

end LocalizedQuotient

section AssociatedPrime

variable {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime] (Sₘ : Type*) [CommRing Sₘ]
  [Algebra S Sₘ] [IsLocalization.AtPrime Sₘ q] [IsLocalRing Sₘ]

section

variable {Nₘ : Type*} [AddCommGroup Nₘ] [Module Sₘ Nₘ] [Module.Finite Sₘ Nₘ]

end

variable {N : Type*} [AddCommGroup N] [Module S N] {Nₘ : Type*} [AddCommGroup Nₘ] [Module S Nₘ]
  [Module Sₘ Nₘ] [IsScalarTower S Sₘ Nₘ] [Module.Finite Sₘ Nₘ] (g : N →ₗ[S] Nₘ)
  [IsLocalizedModule q.primeCompl g]

end AssociatedPrime

/-- **Localizing at `𝔭` costs nothing.** The image in `R_𝔭` of a weakly `M`-regular sequence with
all terms in `𝔭` is a weakly `M_𝔭`-regular sequence of the same length with all terms in the
maximal ideal of `R_𝔭`, so its length is at most `depth_{𝔭R_𝔭}(M_𝔭)`. -/
private theorem length_le_depth_localized_of_isWeaklyRegular {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (p : Ideal R) [p.IsPrime]
    (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
    {Mₚ : Type*} [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule p.primeCompl f] {rs : List R}
    (hmem : ∀ r ∈ rs, r ∈ p) (hreg : IsWeaklyRegular M rs) :
    (rs.length : ℕ∞) ≤ stacksDepth Rₚ (maximalIdeal Rₚ) Mₚ := by
  have : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  have hmemₚ : ∀ r ∈ rs.map (algebraMap R Rₚ), r ∈ maximalIdeal Rₚ := by
    rintro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p a).mpr (hmem a ha)
  simpa using Stacks.Depth.ModNonzerodivisor.length_le_depth_of_isWeaklyRegular (maximalIdeal Rₚ)
    hmemₚ (hreg.of_isLocalizedModule Rₚ p.primeCompl f)

section Main

variable {R : Type u} [CommRing R] [IsLocalRing R] {S : Type v} [CommRing S] [Algebra R S]
  [Module.Finite R S]

variable {N : Type*} [AddCommGroup N] [Module S N] [Module.Finite S N] [Module R N]
  [IsScalarTower R S N]

variable (Sₘ : MaximalSpectrum S → Type w) [∀ P, CommRing (Sₘ P)] [∀ P, Algebra S (Sₘ P)]
  [∀ P, IsLocalization.AtPrime (Sₘ P) P.asIdeal] [∀ P, IsLocalRing (Sₘ P)]

end Main

end Stacks.Depth.LocalizedInfimum

end

/-!
# Depth along the maximal ideal is the minimum of the depths of the localizations

Let `(R, 𝔪)` be a Noetherian local ring, let `R → S` be a finite ring map and let `N` be a
finite `S`-module. The maximal ideals of `S` are exactly the primes of `S` lying over `𝔪` and
there are finitely many of them, so `S` is semilocal. Viewing `N` as an `R`-module, its depth
along `𝔪` is computed by the local data of `N` on `Spec(S)`:
`depth_𝔪(N) = min_{𝔪ᵢ ⊂ S maximal} depth(N_{𝔪ᵢ})`, the depth of `N_{𝔪ᵢ}` being taken over the
local ring `S_{𝔪ᵢ}` along its maximal ideal.

The mechanism is an induction on the common value `k`. If `k = 0` then some `N_{𝔪ᵢ}` has depth
`0`, so `𝔪ᵢ S_{𝔪ᵢ} ∈ Ass(N_{𝔪ᵢ})`, hence `𝔪ᵢ ∈ Ass_S(N)` and therefore `𝔪 ∈ Ass_R(N)`, which
says `depth_𝔪(N) = 0`. If `k > 0` then no `𝔪ᵢ` is associated to `N`, so `𝔪 ∉ Ass_R(N)` and there
is `f ∈ 𝔪` which is a nonzerodivisor on `N`; passing to `N/fN` drops every depth in sight by
exactly `1` (tag 090R) and the induction hypothesis applies.

## Main results

* `Module.depth_eq_iInf_depth_isLocalized_maximal`: `depth_𝔪(N) = ⨅_{𝔪ᵢ} depth(N_{𝔪ᵢ})` for
  `(R, 𝔪)` Noetherian local, `R → S` finite and `N` a finite `S`-module.

## Implementation notes

Faithfulness to [StackProject 0AUK]:

1. No dead hypothesis. `IsLocalRing R` supplies the ideal `𝔪` of the left-hand side.
   `Module.Finite R S` is live: for `R = k[x]_{(x)}`, `S = k(x)` and `N = S`, the ring `S` has
   the single maximal ideal `0`, and `depth(N_0) = 0` because `S ≠ 0` and the ideal `0` contains
   no nonzerodivisor-sequence of positive length, whereas `𝔪 • N = N` gives `depth_𝔪(N) = ⊤`.
   `IsNoetherianRing R` and `Module.Finite S N` are the source's hypotheses and are used in its
   proof — the first for the finiteness of `Ass_S(N)` and for `depth = 0 ↔ 𝔪 ∈ Ass(N)`, the
   second for the existence of a nonzerodivisor on `N` in `𝔪` and for the exact drop of the
   depths on passing to `N/fN` (tag 090R, a statement about finite modules). Note that
   `Module.Finite S N` may be replaced by `Module.Finite R N` without change of content, the two
   being equivalent in the presence of `Module.Finite R S`; the source's form is kept.
2. The scalars and the base are the source's. The left-hand side is `Module.depth` of `N` as an
   `R`-module along `𝔪 ⊆ R`, the `R`-action being the one induced by `R → S` through
   `IsScalarTower R S N`; each right-hand term is `Module.depth` over the *localized* ring
   `S_{𝔪ᵢ}` along its maximal ideal, of the localization of `N`. No depth is taken over `S`
   itself, and none over `R` after localization.
3. The localizations are pinned, not merely assumed to exist: `S_{𝔪ᵢ}` is any ring with
   `IsLocalization.AtPrime (Sₘ P) P.asIdeal` and `N_{𝔪ᵢ}` is any module receiving a map
   `f P : N →ₗ[S] Nₘ P` with `IsLocalizedModule P.asIdeal.primeCompl (f P)`, so the canonical
   localization maps of the source are part of the data; the value of each term is independent
   of these choices because depth is invariant under isomorphisms of pairs (ring, module).
   The ideal `IsLocalRing.maximalIdeal (Sₘ P)` is the image of `𝔪ᵢ`, so the source's
   `depth(N_{𝔪ᵢ})` is exactly what is written.
4. Not degenerate. For `R = k[x]_{(x)} → S = R[y]/(y² - x)` (finite) and `N = S` both sides are
   `1`; for `S = R × R` and `N = R × 0` the minimum over the two maximal ideals is `min(1, ⊤)`,
   which is `1`, and `depth_𝔪(N) = 1`. A witness for `R = S`: both sides are `depth_𝔪(N)`.

Three departures from the source's form, none of them a weakening. The source enumerates the
maximal ideals as `𝔪_1, …, 𝔪_n` and writes a minimum over that finite list; here the right-hand
side is an infimum in `ℕ∞` over `MaximalSpectrum S`, which needs no enumeration and no
finiteness hypothesis, and which agrees with the source's minimum because `S` is semilocal
under the stated hypotheses. When `S` is the zero ring the index type is empty and the infimum
is `⊤`, which is also the value of `depth_𝔪(0)`, so the convention costs nothing. Second, the
localizations are given abstractly rather than as `Localization.AtPrime` and `LocalizedModule`,
in the style of `Module.Finite.of_isLocalized_maximal`, so that a reader with a local ring at
hand — the local ring of a scheme at a point, say — can cite the lemma without transporting
along an isomorphism. Third, the equality is oriented with `depth_𝔪(N)` on the left, this being
the invariant the local data computes.

## References

* [StackProject 0AUK](https://stacks.math.columbia.edu/tag/0AUK)

## Tags

depth, finite ring map, semilocal ring, localization
-/

namespace Module

end Module

/-!
# Depth drops by at most `dim(R/𝔭)` under localization at `𝔭`

Proof of `Module.depth_le_depth_localized_add_ringKrullDim_quotient` (Stacks 0FCC): for
`(R, 𝔪)` a Noetherian local ring, `M` a finite `R`-module and `𝔭 ⊆ R` a prime ideal,

`depth_𝔪(M) ≤ depth_{𝔭R_𝔭}(M_𝔭) + dim(R/𝔭)`.

Both sides are read in `WithBot ℕ∞`, where `ringKrullDim` lives; since `R ⧸ 𝔭` is a nonzero ring
its dimension is the coheight of `𝔭` in `Spec(R)`, an element of `ℕ∞`, so the inequality is one
between elements of `ℕ∞` and the whole proof runs there.

The content is on the side of `R`: for every `n ≤ depth_𝔪(M)` there is a weakly `M`-regular
sequence `x₁, …, x_r` with all terms in `𝔭` and `n ≤ r + coheight 𝔭`
(`exists_isWeaklyRegular_length_add_coheight`), by induction on `n`. For `n = 0` the empty
sequence works. For `n + 1`, either `n + 1 ≤ coheight 𝔭` and again the empty sequence works, or
`coheight 𝔭 < n + 1 ≤ depth_𝔪(M)`, and then no associated prime of `M` contains `𝔭`: one would
give `depth_𝔪(M) ≤ coheight 𝔭` (Stacks 0BK4 and antitonicity of the coheight). Prime avoidance
applied to the finitely many associated primes produces `x ∈ 𝔭` lying in none of them, hence a
nonzerodivisor on `M`, and `depth_𝔪(M/xM) + 1 = depth_𝔪(M)` (Stacks 090R) feeds the inductive
hypothesis to `M/xM`, whose sequence `x` extends.

Localizing at `𝔭` then costs nothing: the image of such a sequence under `R → R_𝔭` is a weakly
`M_𝔭`-regular sequence of the same length with all terms in `𝔭R_𝔭`, because localization is
flat, so `r ≤ depth_{𝔭R_𝔭}(M_𝔭)` by the description of the depth as a supremum over *weakly*
regular sequences (Stacks 0AUI). Since a bound valid for every natural number below `depth_𝔪(M)`
is a bound on `depth_𝔪(M)` itself, this finishes the proof.

## Main results

* `Stacks.Depth.LocalizedCoheightBound.solution`: the tagged statement.

## Implementation notes

The source's induction replaces `M` by `M/xM` on both sides of the inequality at once, which
would require identifying `(M/xM)_𝔭` with `M_𝔭/xM_𝔭`. That identification is avoided here: only
the left-hand side is used in the induction, whose output is a regular sequence in `𝔭`, and the
localization is performed once, at the end, on that sequence. This is also why the source's
hypothesis `M_𝔭 ≠ 0`, needed to make `depth(M_𝔭/xM_𝔭) = depth(M_𝔭) - 1` meaningful, plays no
role, and why the degenerate case `M = 0` needs no separate treatment: the depth of `M_𝔭` is
bounded below through weakly regular sequences, which is insensitive to the vanishing of the
quotients, and `ENat.forall_natCast_le_iff_le` covers `depth_𝔪(M) = ∞` along with the rest.

Facts about `Module.depth` (Stacks 00LI) that Mathlib does not state for lack of the definition
are proved here as private lemmas: that a weakly regular sequence in `I` has length at most
`depth_I(M)`, which is one half of Stacks 0AUI; that Stacks 090R(1) lowers a lower bound on the
depth by one when one divides by a nonzerodivisor; and that the depth of a localization is at
least the length of a localized weakly regular sequence, which is the second half of the proof.

The identification `dim(R/𝔭) = coheight 𝔭` in `Spec(R)` is `ringKrullDim_quotient` together with
`V(𝔭) = Set.Ici 𝔭`, which holds by definition; the same bridge is proved privately in the
companion statements Stacks 0BK4 and Stacks 0BUS, Mathlib having no lemma for it.

## References

* [StacksProject 0FCC](https://stacks.math.columbia.edu/tag/0FCC)
-/

@[expose] public section

namespace Stacks.Depth.LocalizedCoheightBound

-- The `universe` command above is scoped to a section that has already been closed.
universe u v

open Ideal IsLocalRing Module Order RingTheory.Sequence

section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **Prime avoidance for the associated primes.** An ideal contained in no associated prime of a
finite module over a Noetherian ring contains a nonzerodivisor on that module. -/
private theorem exists_mem_isSMulRegular_of_forall_not_le [IsNoetherianRing R] [Module.Finite R M]
    {I : Ideal R} (h : ∀ q ∈ associatedPrimes R M, ¬ I ≤ q) : ∃ x ∈ I, IsSMulRegular M x := by
  have hns : ¬ ((I : Set R) ⊆ ⋃ q ∈ associatedPrimes R M, (q : Set R)) := fun hsub => by
    obtain ⟨q, hq, hle⟩ := (I.subset_union_prime_finite (associatedPrimes.finite R M) (f := id)
      0 0 fun _ hq _ _ ↦ hq.isPrime).1 (by simpa only [id] using hsub)
    exact h q hq hle
  rw [biUnion_associatedPrimes_eq_compl_regular] at hns
  obtain ⟨x, hxI, hx⟩ := Set.not_subset.mp hns
  exact ⟨x, hxI, by simpa using hx⟩

/-- **Stacks 0BK4 in coheights, at a smaller prime.** If an associated prime of `M` contains a
prime `𝔭`, then `depth_𝔪(M) ≤ coheight 𝔭`: the associated prime bounds the depth by the
dimension of its own quotient, and a larger prime has a smaller coheight. -/
private theorem depth_le_coheight_of_le_of_mem_associatedPrimes [IsNoetherianRing R]
    [IsLocalRing R] [Module.Finite R M] (p : Ideal R) [hp : p.IsPrime] {q : Ideal R}
    (hq : q ∈ associatedPrimes R M) (hpq : p ≤ q) :
    stacksDepth R (maximalIdeal R) M ≤ coheight (⟨p, hp⟩ : PrimeSpectrum R) := by
  have hqp : q.IsPrime := hq.isPrime
  have h : (stacksDepth R (maximalIdeal R) M : WithBot ℕ∞) ≤
      (coheight (⟨q, hqp⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by
    rw [coheight_eq_ringKrullDim_quotient ⟨q, hqp⟩]
    exact Module.stacks_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes hq
  exact (WithBot.coe_le_coe.mp h).trans
    (coheight_anti ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hpq))

end

/-- **The induction of Stacks 0FCC, over a fixed ring.** If `n ≤ depth_𝔪(M)`, then there is a
weakly `M`-regular sequence with all terms in `𝔭` whose length `r` satisfies
`n ≤ r + coheight 𝔭`. The module varies along the induction, `M` being replaced by `M/xM`, so it
is quantified over inside, while the ring stays fixed. -/
private theorem exists_isWeaklyRegular_length_add_coheight {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (p : Ideal R) [hp : p.IsPrime] (n : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
      (n : ℕ∞) ≤ stacksDepth R (maximalIdeal R) M →
      ∃ rs : List R, (∀ r ∈ rs, r ∈ p) ∧ IsWeaklyRegular M rs ∧
        (n : ℕ∞) ≤ (rs.length : ℕ∞) + coheight (⟨p, hp⟩ : PrimeSpectrum R) := by
  induction n with
  | zero =>
    intro M _ _ _ _
    exact ⟨[], by simp, IsWeaklyRegular.nil R M, by simp⟩
  | succ n ih =>
    intro M _ _ _ hd
    by_cases hle : ((n + 1 : ℕ) : ℕ∞) ≤ coheight (⟨p, hp⟩ : PrimeSpectrum R)
    · exact ⟨[], by simp, IsWeaklyRegular.nil R M, by simpa using hle⟩
    · -- `𝔭` is contained in no associated prime of `M`, so it contains a nonzerodivisor.
      obtain ⟨x, hxp, hxreg⟩ := exists_mem_isSMulRegular_of_forall_not_le (I := p)
        fun q hq hpq => hle (hd.trans (depth_le_coheight_of_le_of_mem_associatedPrimes p hq hpq))
      obtain ⟨rs, hmem, hreg, hlen⟩ := ih (QuotSMulTop x M)
        (Stacks.Depth.LocalizedInfimum.le_depth_quotSMulTop _ (le_maximalIdeal hp.ne_top hxp) hxreg
          hd)
      refine ⟨x :: rs, List.forall_mem_cons.mpr ⟨hxp, hmem⟩,
        (isWeaklyRegular_cons_iff M x rs).mpr ⟨hxreg, hreg⟩, ?_⟩
      calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; ring
        _ ≤ ((rs.length : ℕ∞) + coheight (⟨p, hp⟩ : PrimeSpectrum R)) + 1 := by gcongr
        _ = ((x :: rs).length : ℕ∞) + coheight (⟨p, hp⟩ : PrimeSpectrum R) := by
            push_cast [List.length_cons]; ring

/-- For `(R, 𝔪)` a Noetherian local ring, `M` a finite `R`-module and `𝔭` a prime ideal of `R`,
`depth_𝔪(M) ≤ depth_{𝔭R_𝔭}(M_𝔭) + dim(R/𝔭)`, both sides read in `WithBot ℕ∞`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] (p : Ideal R) [p.IsPrime]
    (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
    (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule p.primeCompl f] :
    (stacksDepth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) ≤
      (stacksDepth Rₚ (IsLocalRing.maximalIdeal Rₚ) Mₚ : WithBot ℕ∞) + ringKrullDim (R ⧸ p) := by
  rw [← coheight_eq_ringKrullDim_quotient ⟨p, inferInstance⟩, ← WithBot.coe_add, WithBot.coe_le_coe,
    ← ENat.forall_natCast_le_iff_le]
  intro n hn
  obtain ⟨rs, hmem, hreg, hlen⟩ := exists_isWeaklyRegular_length_add_coheight p n M hn
  exact hlen.trans (add_le_add
    (Stacks.Depth.LocalizedInfimum.length_le_depth_localized_of_isWeaklyRegular p Rₚ f hmem hreg)
    le_rfl)

end Stacks.Depth.LocalizedCoheightBound

end

/-!
# Depth drops by at most `dim(R/𝔭)` under localization at `𝔭`

Let `(R, 𝔪)` be a Noetherian local ring, let `M` be a finite `R`-module and let `𝔭 ⊆ R` be a
prime ideal. Writing `depth(M) = depth_𝔪(M)` for the depth of `M` along the maximal ideal and
`depth(M_𝔭) = depth_{𝔭R_𝔭}(M_𝔭)` for the depth of the localization `M_𝔭` as a module over the
local ring `R_𝔭`, we have
`depth(M) ≤ depth(M_𝔭) + dim(R/𝔭)`,
that is, localizing at `𝔭` costs at most `dim(R/𝔭)` of the depth. The three extreme cases are
instructive: for `𝔭 = 𝔪` the inequality is the equality `depth(M) = depth(M)`; for `M_𝔭 = 0`
it holds because `depth(0) = ∞`; and for `R` a discrete valuation ring, `M = R` and `𝔭 = (0)`
it is the equality `1 = 0 + 1`, the middle term being the depth of the fraction field over
itself, whose maximal ideal is `(0)`.

The reason is an induction on `depth(M)`. If `depth(M) ≤ dim(R/𝔭)` there is nothing to prove,
and if `M_𝔭 = 0` then `depth(M_𝔭) = ∞`. Otherwise `depth(M) > dim(R/𝔭)`, so `𝔭` is contained
in no associated prime `𝔮` of `M`, since `depth(M) ≤ dim(R/𝔮)` for such `𝔮` (Tag 0BK4). As
`Ass(M)` is finite (Tag 05BZ) prime avoidance produces `x ∈ 𝔭` lying in no associated prime of
`M`, hence a nonzerodivisor on `M` (Tag 00LD), and also a nonzerodivisor on `M_𝔭` when the
latter is nonzero. Then `depth(M/xM) = depth(M) - 1` and
`depth(M_𝔭/xM_𝔭) = depth(M_𝔭) - 1` (Tag 090R), and `(M/xM)_𝔭 = M_𝔭/xM_𝔭`, so the induction
hypothesis applies to `M/xM`.

## Main results

* `Module.depth_le_depth_localized_add_ringKrullDim_quotient`:
  `depth_𝔪(M) ≤ depth_{𝔪 R_𝔭}(M_𝔭) + dim(R/𝔭)` for `R` Noetherian local and `M` finite.

## Implementation notes

Faithfulness to [StackProject 0FCC]:

1. No dead hypothesis: `IsNoetherianRing R`, `IsLocalRing R` and `Module.Finite R M` are the
   source's and all three are used (Noetherian and finite for the finiteness of `Ass(M)` that
   drives the induction, locality because `depth(M)` on the left means depth along `𝔪`); the
   data `Rₚ`, `Mₚ` and `f` are what the term `depth(M_𝔭)` refers to, and `𝔭` occurs in both
   summands on the right.
2. The scalars are the source's: `depth(M)` is formed over `R` along `IsLocalRing.maximalIdeal
   R`, `depth(M_𝔭)` over `R_𝔭` along `IsLocalRing.maximalIdeal Rₚ` — not over `R` along `𝔭` —
   and `dim(R/𝔭)` is a Krull dimension of a quotient of `R` itself.
3. The canonical maps are pinned, not merely assumed to exist: `IsLocalization.AtPrime Rₚ p`
   pins `Rₚ` as `R_𝔭` together with its structure map `algebraMap R Rₚ`, and
   `IsLocalizedModule p.primeCompl f` pins the given `R`-linear `f : M →ₗ[R] Mₚ` as the
   localization map `M → M_𝔭`; `IsScalarTower R Rₚ Mₚ` is what makes the `Rₚ`-module structure
   used by the depth on the right the one transported along `f`.
4. Not degenerate: for `R` a discrete valuation ring with maximal ideal `𝔪`, `M = R` and
   `𝔭 = (0)`, the three terms are `1`, `0` and `1` and the inequality is the attained
   `1 ≤ 0 + 1`; the same `R` with `M = R ⧸ 𝔪` and `𝔭 = (0)` gives `0 ≤ ∞ + 1`, since
   `M_𝔭 = 0`; and `𝔭 = 𝔪`, `M = R` gives `1 ≤ 1 + 0`. So each of the three terms varies with
   the data and none is inert.

Three departures from the source's form, none of them weakening it.

The localization is presented abstractly: rather than fixing the models
`Localization.AtPrime 𝔭` and `LocalizedModule 𝔭.primeCompl M`, the statement quantifies over
any `Rₚ` with `IsLocalization.AtPrime Rₚ p` and any `Mₚ` with `IsLocalizedModule p.primeCompl
f`, in arbitrary universes. Every such pair is uniquely isomorphic to those models, so this is
the same statement for each choice and saves every user from transporting along the
isomorphism.

`IsLocalRing Rₚ` is listed as an instance although it follows from `IsLocalization.AtPrime Rₚ
p` by `IsLocalization.AtPrime.isLocalRing`, which is a theorem rather than an instance; it is
needed for `IsLocalRing.maximalIdeal Rₚ` to be available to the elaborator.

`Module.depth` takes values in `ℕ∞` and `ringKrullDim` in `WithBot ℕ∞`, the value `⊥` being
reserved for the trivial ring; the inequality is therefore read in `WithBot ℕ∞`, as in
`Module.depth_le_supportDim` (Tag 00LK). No summand is `⊥`: `R ⧸ 𝔭` is a nonzero ring. The
source writes the inequality as `depth(M_𝔭) + dim(R/𝔭) ≥ depth(M)`; it is stated here with the
smaller quantity on the left, as Mathlib does. The term `dim(R/𝔭)` is spelled
`ringKrullDim (R ⧸ 𝔭)`, which for a prime `𝔭` is also the coheight of `𝔭` in
`PrimeSpectrum R`, i.e. the dimension of the closed subset `V(𝔭)`.

## References

* [StackProject 0FCC](https://stacks.math.columbia.edu/tag/0FCC)

## Tags

depth, localization, dimension, Noetherian local ring
-/

@[expose] public section

namespace Module

/-- **Depth drops by at most `dim(R/𝔭)` under localization.** Let `(R, 𝔪)` be a Noetherian
local ring, `M` a finite `R`-module and `𝔭 ⊆ R` a prime ideal. Then
`depth_𝔪(M) ≤ depth_{𝔭R_𝔭}(M_𝔭) + dim(R/𝔭)`. The localization is presented abstractly: `Rₚ`
is any localization of `R` at `𝔭` and `f : M →ₗ[R] Mₚ` any localization of `M` at `𝔭`. The
inequality is read in `WithBot ℕ∞`, where `ringKrullDim` lives. -/
@[stacks 0FCC "Stated in `WithBot ℕ∞` with the smaller side on the left, for `Module.depth`
(Tag 00LI) along the maximal ideals of `R` and of `Rₚ`, and with the localizations presented by
`IsLocalization.AtPrime` and `IsLocalizedModule`. See the module docstring."]
public theorem depth_le_depth_localized_add_ringKrullDim_quotient {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] (Mₚ : Type*) [AddCommGroup Mₚ]
    [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ)
    [IsLocalizedModule p.primeCompl f] :
    (stacksDepth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) ≤
      (stacksDepth Rₚ (IsLocalRing.maximalIdeal Rₚ) Mₚ : WithBot ℕ∞) + ringKrullDim (R ⧸ p) :=
    by exact Stacks.Depth.LocalizedCoheightBound.solution M p Rₚ Mₚ f

end Module

end
