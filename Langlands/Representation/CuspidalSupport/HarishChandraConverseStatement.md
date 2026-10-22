# Compact coefficients imply product-Levi quasicuspidality

Author: Worker 180.

`Langlands.CuspidalSupport.LeviHarishChandraConverseTheorem.{uF,uV}`
is a `Prop`-valued definition of a future proof target. It states the
(4) ⇒ (1) direction of Bernstein–Zelevinsky (1976), Theorem 3.21,
with the elementary rank-zero extension explained below. It does not
prove or postulate the implication.

## Exact statement and conventions

All quantifiers are internal. They range over every `p : ℕ` with
`Fact p.Prime`, actual `F : PadicField.{uF} p`, compatible
`T : F.TopologicalData`, `n : ℕ`, `B : BlockShape n`, and, after
installing `T.topology`, every actual smooth complex representation
`A : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)`. The field universe `uF`
and representation carrier universe `uV` are independent. The quantifier
prefix is identical to that of the imported `LeviHarishChandraTheorem`.

Writing `G = B.Levi F.Carrier`, `G° = determinantUnitSubgroup T B`, and
`ρ₀ = determinantUnitRestriction T B A.representation`, the assertion is
exactly

\[
 \operatorname{HasCompactSmoothDualCoefficients}(\rho_0)
 \quad\Longrightarrow\quad
 \operatorname{IsLeviQuasicuspidal}(B,A.\mathrm{representation}).
\]

The antecedent means that for every vector `v : A` and algebraic linear
functional `ℓ : Module.Dual ℂ A`, smoothness `IsSmoothVector ρ₀.dual ℓ`
implies `HasCompactSupport (matrixCoefficient ρ₀ ℓ v)`. Smoothness is
that of the **restricted dual action**, and compact support means
compactness of the closure of the nonzero locus in the subgroup topology
on `G°`. This subgroup requires determinant absolute value one separately
in every Levi block. The restriction is the actual action through its
inclusion into `G` and retains the carrier of `A`.

The consequent means that for every `S : BlockRefinement B` with
`refinedParabolic F.Carrier B S ≠ ⊤`, the actual quotient
`Jacquet.Coinvariants A.representation (refinedUnipotent F.Carrier B S)`
is a subsingleton. This is vanishing of every proper standard refined
unipotent coinvariant module. Normalizing the residual Jacquet action
does not change this quotient or its vanishing.

There is no admissibility, irreducibility, finite length, finite dimension,
semisimplicity, central character, nonzero-carrier, or positive-rank
hypothesis. Smoothness is supplied by the bundled object `A`. In particular,
no theorem-valued input is used to assume the desired implication.

## Original source and future proof obligations

The registered original is I. N. Bernshtein and A. V. Zelevinskii,
*Representations of the group GL(n,F) where F is a non-Archimedean local
field*, Russian Mathematical Surveys **31**:3 (1976), 1–68, English
translation (BZ76).

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- PDF SHA256: `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Retained original: `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
- Directly read for this pair: §§2.39–2.40, printed/PDF p.26, and
  §§3.18, 3.20–3.23, printed/PDF pp.34–35. No corresponding errata note
  was present in the current Library.

Section 3.18 defines quasicuspidality by vanishing of the Jacquet modules
for proper standard refinements of a product group. Section 3.20 defines
its open determinant-unit subgroup `G°`. Condition (4) of Theorem 3.21
says that restriction to `G°` is finite in the sense of §2.40(a): all
coefficients against smooth contragredient vectors have compact support.
Here “finite” does not mean finite-dimensional. The actual p-adic fields
with compatible topology in this target specialize the nonarchimedean
local fields of the source.

The source's §2.39 coefficient is `g ↦ ℓ (ρ₀ g⁻¹ v)`, whereas the
Library uses `g ↦ ℓ (ρ₀ g v)`. Inversion is a homeomorphism of `G°`,
so these coefficients have compact support simultaneously. For a smooth
representation the coefficients are locally constant, making their
nonzero loci closed and agreeing with the source's support convention.
The proposition uses the restricted smooth dual directly; no identification
with the smooth dual for the original group is an extra hypothesis.

The source proves this implication by (4) ⇒ (2) ⇒ (1). The following
steps describe future obligations; none is implemented or supplied as
an assumption by this statement pair.

1. Apply the compact averaged-orbit criterion of §2.40 to the restricted
   representation: for a vector `v` and a compact open congruence subgroup
   `N` contained in `G°`, compact coefficients imply compactness of the
   set of `g ∈ G°` for which `e_N ρ(g⁻¹)v ≠ 0`, where `e_N` denotes
   normalized averaging. This requires the full smooth-dual separation
   argument of §2.40, with no finite-dimensional or admissibility
   assumption on the original representation.
2. Pass to the corresponding set in `G`. Section 3.20 gives finite
   `G/(G° Z)`, where `Z` is the center. Finitely many coset representatives
   and the resulting finitely many transformed vectors reduce this set
   to central translates of compact sets in `G°`; central operators
   commute with averaging and preserve nonvanishing. This yields condition
   (2), compactness modulo `Z`, without requiring a scalar central character.
3. Use the Cartan and gap argument of §3.23 to derive the eventual
   vanishing condition in Lemma 3.22(2) for every proper refinement and
   every vector. The converse direction of Lemma 3.22 is essential:
   choose a congruence subgroup fixing the vector, use its decomposition
   relative to the refinement and a sufficiently contracting block-central
   element, and turn the assumed vanishing of the conjugated average
   into vanishing of an average over a compact subgroup of the refined
   unipotent radical. The unipotent averaging criterion then puts the
   vector in the span of the differences `ρ(u)w - w`. Every vector thus
   has zero class in the corresponding coinvariant quotient, giving (1).

This description separates compactness modulo the center, the averaged-orbit
criterion, and the converse of Lemma 3.22 as mathematical work still needed
for a proof of this target. The forward gap-decay direction and the full
Harish-Chandra equivalence are not asserted as proved here.

## Rank zero and imported dependencies

For `n = 0`, positivity of all block sizes and their sum being zero force
`B` to be empty. Its Levi and determinant-unit subgroup are one-element
groups. Every refined parabolic is the whole group, so the consequent has
no proper-refinement cases. Every coefficient on the one-element subgroup
also has compact support, independently of the carrier dimension. This is
an elementary internal extension of the positive-rank source statement;
this pair supplies no proof even of that boundary case.

The sole direct import is the published
`Langlands.Representation.CuspidalSupport.HarishChandraStatement`.
It supplies the accepted full equivalence target and imports the accepted
`LeviDefinitions`, `DeterminantUnit`, and `CompactCoefficient.Classes`
interfaces used here. All imported Lean/Markdown pairs and the existing
full target remain unchanged. The new proposition isolates one direction
for a separately reviewed proof and subsequent assembly of the equivalence.
There are no new axioms or placeholder theorems.
