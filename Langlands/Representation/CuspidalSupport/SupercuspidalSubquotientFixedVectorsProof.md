# Fixed vectors of supercuspidal subquotients (Renard VI.6.3, Proposition): proof

Module `Langlands.Representation.CuspidalSupport.SupercuspidalSubquotientFixedVectorsProof`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `u, v`.

The theorem `Langlands.CuspidalSupport.supercuspidalSubquotientFixedVectors` proves the
published proposition
`Langlands.CuspidalSupport.SupercuspidalSubquotientFixedVectorsStatement.{u, v}`
(module `SupercuspidalSubquotientFixedVectorsStatement`). Its type is exactly that
proposition, at both universe parameters, with no further hypothesis. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.
[Statement](SupercuspidalSubquotientFixedVectorsStatement.md)

## What is proved

Let `k` be a nonarchimedean local field (`T2Space`), `G` a connected reductive group
scheme over `k`, and give `G(k)` the represented point topology
`Aubert.General.RationalPointFamily.pointTopology`, with the statement's
`LocallyCompactSpace` and `NonarchimedeanGroup` binders. For every compact open
subgroup `K` of `G(k)` and every smooth complex representation `V` such that every
subrepresentation containing `V^K` is all of `V`, every subquotient `D` of `V`
(`SmoothRep.IsSubquotient`) that is nontrivial and supercuspidal (the represented
predicate `Aubert.General.RepresentedParabolic.IsSupercuspidal`) satisfies
`fixedVectors D K ≠ ⊥`.

This is Renard VI.6.3, Proposition (David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, printed pp.178–179 / PDF
pp.184–185), for every compact open `K`, as the statement's Markdown explains; the
source assumes in addition that `K` is contained and normal in `K₀`.

## Proof

The route agrees with Renard's in its first and last steps: decompose `V` along the
inertia class of an irreducible supercuspidal subquotient `τ` by (VI.3.3.1), and
finish with the exactness of `K`-fixed vectors (III.1.5). Renard deduces `τ^K ≠ 0` from
the description of the restriction of the block summand `V(τ)` to `⁰G` as a sum of
copies of the compact components of `τ|_{⁰G}` (VI.3.2). The Lean proof replaces that
step by an argument on irreducible constituents: some constituent of `V(τ)` has a
nonzero `K`-fixed vector, it is an unramified twist of `τ`, and unramified characters
are trivial on the compact subgroup `K`.

1. **An irreducible supercuspidal subquotient.**
   `SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial` gives an irreducible
   subquotient `τ` of `D`. It is supercuspidal by
   `Aubert.General.RepresentedParabolic.IsSupercuspidal.of_isSubquotient`, and a
   subquotient of `V` by `smoothSubquotientTransitivity`.
2. **Compactness on `⁰G` (VI.2.1 (a) ⇒ (c)).**
   `Aubert.General.RepresentedParabolic.compactRestriction_of_isSupercuspidal` shows
   that the restriction of `τ` to the common norm kernel
   `Plancherel.rationalCommonNormKernel G` (Renard's `⁰G`) has compact smooth-dual
   coefficients. Its four structural premises are supplied by the theorems
   `parabolicDynamic`, `standardCocharacter`, `relativeRootSystem` and
   `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`.
3. **The inertia decomposition (VI.3.3.1).**
   `rationalCompactRestrictionInertiaDecomposition` applies to the irreducible `τ`,
   compact on `⁰G`, and gives `IsRationalInertiaCategoryDecomposition G τ`. Its first
   clause at the object `V` gives a coproduct cofan `j : Y b ⟶ V` (`b : Bool`), where
   every irreducible subquotient of `Y true` is inertia-related to `τ`
   (`IsRationalInertiaRelated G τ`) and no irreducible subquotient of `Y false` is.
4. **The block summand has a nonzero `K`-fixed vector.** Suppose
   `(Y true)^K = 0`. Let `p : V ⟶ Y true` be induced by `𝟙` on `Y true` and `0` on
   `Y false`. By `fixedVectorsMap`, `p` sends `V^K` into `(Y true)^K = 0`, so the
   kernel of `p` is a subrepresentation containing `V^K`; by the generation
   hypothesis it is all of `V`, and `p = 0`. Since `j true ≫ p = 𝟙`, the identity of
   `Y true` is zero and `j true = 0`. Then the map `q : V ⟶ Y false` induced by `0`
   and `𝟙` is inverse to `j false`, so `V ≅ Y false`. This is the argument of
   `no_supercuspidal_subquotient_of_splitting`. Now `τ` is an irreducible
   subquotient of `Y false` inertia-related to itself
   (`IsRationalInertiaRelated.refl`), which is excluded by step 3.
5. **A constituent with a fixed vector.**
   `SmoothRep.hasFixedVectorConstituent_of_nontrivial` gives an irreducible
   subquotient `σ` of `Y true` with nonzero `K`-fixed vectors. By step 3, `σ` is
   inertia-related to `τ`: it is isomorphic to `rationalUnramifiedTwist G χ τ` for an
   unramified character `χ`.
6. **Transfer to `τ`.** `nontrivial_fixedVectors_iff_of_rationalInertiaRelated`
   (module `Langlands.Representation.Jacquet.RationalInertiaFixedVectors`) states
   that, for a compact subgroup, nontriviality of fixed vectors is the same for
   inertia-related representations: an unramified character is trivial on the common
   norm kernel, which contains every compact subgroup, so an unramified twist has the
   same `K`-fixed vectors. Applied to `σ` and `τ` it gives `τ^K ≠ 0`.
7. **Exactness (III.1.5).** `SmoothRep.nontrivial_fixedVectors_of_isSubquotient`
   lifts nontrivial `K`-fixed vectors from the subquotient `τ` of `D` to `D`, and
   `Submodule.nontrivial_iff_ne_bot` gives `fixedVectors D K ≠ ⊥`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.SupercuspidalSubquotientFixedVectorsStatement` | the target statement |
| `Langlands.Representation.CuspidalSupport.RationalCompactRestrictionInertiaDecompositionProof` | `rationalCompactRestrictionInertiaDecomposition` (VI.3.3.1) |
| `Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal` | `compactRestriction_of_isSupercuspidal` (VI.2.1 (a) ⇒ (c)) |
| `Langlands.Representation.Exponents.RepresentedCuspidalProjection` | `IsSupercuspidal.of_isSubquotient` |
| `Langlands.Representation.Category.FixedVectorConstituent` | `hasFixedVectorConstituent_of_nontrivial`; through its import `Langlands.Representation.Category.IrreducibleSubquotientExistence`, `exists_isIrreducible_isSubquotient_of_nontrivial` |
| `Langlands.Representation.Jacquet.IrreducibleFixedVectorGeneration` | `nontrivial_fixedVectors_of_isSubquotient` |
| `Langlands.Representation.Jacquet.RationalInertiaFixedVectors` | `nontrivial_fixedVectors_iff_of_rationalInertiaRelated` |
| `Langlands.Representation.Filtration.SubquotientAlgebraProof` | `smoothSubquotientTransitivity` |
| `Langlands.GroupScheme.Absolute.ParabolicDynamicProof` | `parabolicDynamic` |
| `Langlands.GroupScheme.Rational.StandardCocharacterProof` | `standardCocharacter` |
| `Langlands.GroupScheme.Rational.RelativeRootSystemProof` | `relativeRootSystem` |
| `Langlands.BruhatTits.SpecialCompact.JointBasisProof` | `jointSpecialCompactBasisExistence` |
