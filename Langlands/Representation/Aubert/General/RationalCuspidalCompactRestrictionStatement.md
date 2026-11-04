# Renard VI.2.1, (a) implies (c), on the actual rational-point group

`Langlands.Aubert.General.RationalPointFamily.RationalCuspidalCompactRestrictionStatement`
is a closed `Prop`. It states one implication from the theorem of VI.2.1 in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026,
printed pp.137–139 / PDF pp.143–145. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The implication is
(a) ⇒ (c): a smooth representation that is supercuspidal, tested on proper standard
parabolics, has compact restriction to `⁰G`. This module proves nothing. It records the
statement and the structural inputs that it assumes.

## The statement

The two universe parameters are independent: `u` for the field and `v` for the
representation carrier. The statement quantifies over the following data, in this order.

1. A field `F : Type u` with `Field`, `ValuativeRel`, `TopologicalSpace` and
   `IsNonarchimedeanLocalField`. This covers both equal and mixed characteristic.
2. An actual `G : GroupScheme (Spec (CommRingCat.of F))` with
   `hG : IsConnectedReductive G`, an actual commutative group scheme `S`,
   `i : S.toGrp ⟶ G`, and `hi : IsMaximalSplitTorus i`. Three instances are installed
   from these hypotheses: `hG.isAffineHom`, `IsAffine G.X.left` (through
   `isAffine_of_isAffineHom`) and the monomorphism `hi.isSplitSubtorus.mono`. No split,
   quasi-split or rank hypothesis is added.
3. The topology on `RationalPoint F G.X` is bound with `letI` to
   `rationalPointTopology F G.X`. `rationalPoints G` is the same carrier with the same
   topology, by reducible unfolding. The structural predicates below install this same
   topology internally.
4. Instance binders `[LocallyCompactSpace]`, `[NonarchimedeanGroup]` and `[T2Space]` for
   this canonical topology. They are hypotheses only in form. The Library already proves
   them for nonarchimedean local fields: `rationalPoint_locallyCompactSpace` and
   `rationalPoint_t2Space` in `Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups`,
   and `Plancherel.rationalPoints_nonarchimedeanGroup` in
   `Langlands.Representation.Plancherel.RationalTwistStabilizer`.
5. `ν : cocharacterLattice S` with `hν : IsGenericCocharacter i ν`.
6. `hStandard : StandardCocharacterStatement.{u}` (ledger item S15) and
   `hRoots : HasRelativeRootSystem i` (ledger item S09).
7. `hU : ∀ I, IsClosed (unipotent i ν I)`, which makes the normalized Jacquet
   restrictions available. The Library already proves this as
   `isClosed_unipotent_of_isNonarchimedeanLocalField` in
   `Langlands.Representation.Aubert.General.StandardFamilyStructure`. The binder is kept
   in the form used by the published neighbouring statement
   `RationalCuspidalInertiaDecompositionStatement`.
8. `D : KPApartmentData i (localFieldOrder F)`, a point `x : D.Apartment`, and the
   hypothesis `D.IsSpecialApartmentVertex x`. The statement then sets
   `K0 := D.specialCompactSubgroup x` with `let`. The three structural hypotheses below
   all refer to this same `K0`:
   - `SpecialCompactProperties F i ν K0`;
   - `SimultaneousStandardBasisAt i ν K0`;
   - `FiniteCartanCovering F i ν K0`.
9. The statement then installs the root index `simpleRelativeRootFintype i hRoots
   hi.isSplitSubtorus.1 ν` and sets
   `h := isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν`.
   This is the semidirect decomposition of every actual standard parabolic
   `parabolic i ν I = levi i ν I ⋉ unipotent i ν I`.
10. The conclusion: for every `A : SmoothRep.{0, u, v} ℂ (RationalPoint F G.X)`,

    ```text
    IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A →
      HasCompactSmoothDualCoefficients
        (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) A).representation
    ```

`FiniteCartanCovering F i ν K0` is a local abbreviation. It is exactly the following
formula and contains no other law:

```text
∃ F0 : Finset (centralizerPoints i), ∀ g : rationalPoints G,
  ∃ k₁ k₂ f a, k₁ ∈ K0 ∧ k₂ ∈ K0 ∧ f ∈ F0 ∧
    a ∈ CocharacterUniformizer.CAplus F S (simpleRelativeRoots i ν) ∧
    g = k₁ * (f : rationalPoints G) * rationalPoints.map i a * k₂
```

## Hypothesis and conclusion conventions

**Supercuspidality.** `IsCuspidal` is the existing convention in
`Langlands.Representation.Aubert.General.SupportCategory`. The normalized Jacquet module
`jacquetFunctor (h I) (hU I)` of `A` must be a subsingleton for every
`I : Finset (simpleRelativeRoots i ν)` with `I ≠ Finset.univ`. Only the full set is
excluded, so the empty subset counts whenever the root set is nonempty. If there are no
simple roots, there is no proper subset and the hypothesis holds vacuously. This matches
Remark 1 after the definition in VI.2.1: supercuspidality can be tested on proper
**standard** parabolics only. The source definition quantifies over all proper
parabolics, and reducing to standard ones uses conjugacy (V.3.9). That reduction is not
part of this statement.

**Compactness of the restriction.** Renard defines a compact representation in IV.1.3,
printed p.89 / PDF p.95, through the functions `f_{K,v}`. The theorem there shows this is
equivalent to compact support of every matrix coefficient against the smooth
contragredient. This statement uses the coefficient form, through the existing
`HasCompactSmoothDualCoefficients` in `Langlands.Representation.CompactCoefficient.Classes`.
For every vector `v` and every algebraic dual functional `ℓ` that is smooth for the dual
of the **restricted** action, the coefficient `g ↦ ℓ (ρ g v)` must have compact support.
The coefficient is a function on the subgroup `rationalCommonNormKernel G`, with its
inherited subspace topology. The predicate quantifies over the entire smooth dual of the
restricted representation, not only over restrictions of ambient smooth functionals.
The norm kernel is open (`Plancherel.isOpen_rationalCommonNormKernel`), and the Library
proves that the two smooth duals agree
(`Plancherel.isSmoothVector_dual_rationalNormKernel_iff`). That comparison is a proof
tool for later; the statement does not use it.

**The group `⁰G`.** `Plancherel.rationalCommonNormKernel G` is the intersection of the
kernels of the normalized norms `|χ|_F` of all actual rational characters `χ` of `G`.
This is Renard's `⁰G` from V.2.3, printed p.105 / PDF p.111.

**Generality.** The statement covers all of the following, as the source does:
- every smooth complex representation, with no admissibility, irreducibility, finite
  length or finite-dimensionality condition;
- the zero representation;
- every connected reductive group, including nonsplit and non-quasi-split ones;
- relative rank zero and empty root sets.

## Structural antecedents and source locations

The ledger `notes/renard/chapter-v-structural-inputs.md` fixes which Chapter V inputs
count as structural (S-items) and which must be derived (D-items). This statement uses
only the following.

| Hypothesis | Source | Ledger |
| --- | --- | --- |
| `StandardCocharacterStatement.{u}` | V.4.2, printed p.118 / PDF p.124, standard parabolics as subsets of `Δ_∅` | S15 |
| `HasRelativeRootSystem i` | V.3.7, printed p.111 / PDF p.117, the reduced relative roots of a minimal parabolic form a root system | S09 |
| `SpecialCompactProperties F i ν K0` | V.5.1(2),(3), printed p.122 / PDF p.128 (Weyl representatives in `K0`; `K0 ∩ P = (K0 ∩ M)(K0 ∩ N)`), plus maximality of `K0` as a compact open and as a bounded open subgroup (Kaletha–Prasad 4.2.15(1)) | S19 |
| `SimultaneousStandardBasisAt i ν K0` | V.5.2(i)–(iv), printed p.123 / PDF p.129, citing [24] §2.1: a basis of compact open subgroups normal in `K0`, inherited by every standard Levi; for every standard parabolic, a compatible split component chosen before the basis, and for every basis member the Iwahori intersection decomposition and the contraction and cofinality clauses | S20–S23 |
| `FiniteCartanCovering F i ν K0` | V.5.1(4), printed p.122 / PDF p.128, covering clause only | S19(4) |

V.5 says its results are proved in [14].

`D.specialCompactSubgroup x` is the existing geometric special compact subgroup of a
special vertex. The statement assumes the three properties for this particular `K0`. It
does not claim that every `KPApartmentData` has a special vertex, or that the properties
hold for an arbitrary special vertex. Those are tasks of the shared KP program.

**The covering clause.** V.5.1(4) says
`G = ⊔_{a ∈ C̃_∅^+} K0 a K0 = ⊔_{a ∈ C_∅^+, f ∈ F_∅} K0 a f K0`, with notation from V.3.23,
printed p.117 / PDF p.123. The objects correspond to the Library as follows.
- `C_∅^+ = C_∅ ∩ M_∅^+`. For points of `A_∅` this is the set `|α(a)|_F ≤ 1` for
  `α ∈ Δ_∅` (V.3.21, printed p.116 / PDF p.122).
- `C_∅ = C_{A_∅}` is the lift `c ↦ c(ϖ)` of `X_*(A_∅)` into `A_∅` (V.2.5, printed
  pp.106–107 / PDF pp.112–113). It is the existing `CocharacterUniformizer.CA F S`, the
  range of `latticeSection` at the chosen order-one uniformizer.
- `CAplus F S R` adds the condition `characterNorm F S α a ≤ 1` for `α ∈ R`. Here `R` is
  `simpleRelativeRoots i ν`.
- `F_∅` is a finite subset of `M_∅ = Z_G(A_∅)`. It corresponds to
  `F0 : Finset (centralizerPoints i)`.
- `a ∈ A_∅(F)` enters `G(F)` as `rationalPoints.map i a`.

The order matters only formally. `f` lies in the actual torus centralizer, so it
commutes with the image of `a`, and `k₁ f a k₂` agrees with the source's `K0 a f K0`. The
source proof of (a) ⇒ (b) writes the decomposition as `G = K0 F_∅ C_∅^+ K0`.

The abbreviation keeps only coverage. It omits:
- disjointness of the double cosets;
- the requirement `F_∅ ⊆ M_∅^+`;
- the lattice-lifting law `C̃_∅ = C_∅ F_∅` with its unique representatives;
- any valuation inverse or lattice basis.

Each of these omissions weakens the hypothesis relative to the source. Once `simpleRelativeRoots i ν` is identified with `Δ_∅` (see the next section), the source's V.5.1(4) implies `FiniteCartanCovering`. The existence and uniqueness laws of the V.3.23 lifting remain D05 obligations.

No other in-book conclusion is assumed. In particular, the statement does not use:
- `JointSpecialCompactBasisExistenceStatement`, `SpecialCompactRenardComparison`,
  `DominantCentralizerLatticeConclusions` or `HasSpecialCompactCartanCoverage`;
- compactness of `⁰G ∩ Z(G)`, or bijectivity of character evaluation;
- admissibility, compact coefficients, or Jacquet–Cartan estimates.

## Actual simple roots and the source's `Δ_∅`

`simpleRelativeRoots i ν`
(`Langlands.GroupScheme.Rational.StandardParabolic`) is the set of actual relative roots
that pair positively with `ν` and are not the sum of two such roots. Here `relativeRoots
i` means the nonzero `S`-weights with a nonzero weight space, which may form a nonreduced
system. Renard's `Δ_∅` is defined in V.3.4 and V.3.12, printed pp.110,112 / PDF
pp.116,118. Let `Σ'(A_∅)` be the roots of `A_∅` in `Lie(G)`, and `Σ(A_∅)` its reduced
roots `α` (those with `α/n ∉ Σ'(A_∅)` for `n ≥ 2`). Then `Σ_∅^+ = Σ(P_∅)` is the set of
reduced roots positive for `P_∅`, and `Δ_∅` is its set of simple roots.

The Library proves one direction of the comparison. From `hRoots`, splitness of `S` and
`hν`, `HasRelativeRootSystem.linearIndependent_simpleRelativeRoots` gives linear
independence of the actual simple roots. `simpleRelativeRoot_mem_indivisiblePositiveRoots`
then shows that every actual simple root is indivisible and `ν`-positive. The following
remain explicit comparison obligations of the general framework:
- the converse inclusion (every simple root of the indivisible positive system is an
  actual simple root);
- the identification of `relativeRoots i` with `Σ'(A_∅)`;
- the identification of the `ν`-positive system with the roots of a minimal parabolic
  `P_∅`.

These obligations determine how far the cuspidality hypothesis (indexed by subsets of
`simpleRelativeRoots i ν`) and the set `CAplus` match the source's standard parabolics
and `C_∅^+`. The statement uses the existing actual objects, not a separate Renard root
theory. It does not claim independence from the choice of `(S, ν, x)`.

## Proof obligations left to the proof successor

The source proves (a) ⇒ (c) through (b), compactness modulo the center
(PDF pp.144–145):

1. **(a) ⇒ (b), by contraposition.** Take a coefficient whose support is not compact
   modulo the center. The Cartan covering gives `f ∈ F_∅` and distinct `t_n ∈ C_∅^+`
   with `K0 f t_n K0` meeting the support, and some `α ∈ Δ_∅` with `|α(t_n)|_F → 0`.
   Let `K` be the basis member normal in `K0` with an Iwahori factorization along
   `P_α`. Finiteness of `[K0 : K]` and contraction of `K_N` then give
   `V_{N_α} ≠ 0`.
2. **(b) ⇒ (c).** This uses compactness of `⁰G ∩ Z(G)` (V.2.6) and [32], Theorem 2.6.

The following steps are not assumed and remain proof obligations:
- the D02/D05 facts used along the way: compactness of the center intersection,
  split/central/derived comparisons, the section and finite-lattice arguments, and
  extraction of a contracted wall;
- the simple-root comparison above;
- the smooth-dual comparison for the open subgroup.

A proof may also go directly to `⁰G` without passing through (b). The successor must
prove this implication unchanged, with no theorem-valued premises added.

## Scope

Not stated here:
- the converse (c) ⇒ (a) and the full equivalence;
- condition (b);
- the remarks after the theorem and the corollary of VI.2.1;
- reduction from all parabolics to standard ones;
- every categorical consequence, including the VI.3.3.1 decomposition, whose actual
  statements are in `Langlands.Representation.CuspidalSupport.RationalInertiaDecompositionStatement`.

That module's intermediate target takes compact restriction to
`rationalCommonNormKernel G` as its hypothesis. This statement supplies that hypothesis
from proper-standard cuspidality, conditionally on the structural antecedents above.
