# Certified local pole comparisons for witnessed relative pairs

This module declares the **statement**
`Langlands.Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement`,
with universe parameters `uF uW uP`. It is a proposition definition, and the
file contains no proof of it. It is part of the Henniart global-input program
(H3, task `34b81620-20d7-4059-9b08-6bedd1c1c029`). It is the universal form of
the published hypothesis `RelativeCertifiedPoleComparisons`, which is the input
of the proved `relativePolePairing` theorem and of the statement targets
`RelativeIsometryOperationStatement`, `RelativeIsometryFactorStatement` and
`HenniartCompositeMapStatement`. Its source is Henniart (2000), Corollaire 2.4
and Lemme 2.8. It adapts them to the finite-relative, witnessed setting of the
Library, so its provenance is *derived*. The section "Source correspondence"
below lists the differences.

## 1. The statement

For

- number fields `F` and `E` in a common universe `uF`, with `E/F` Galois;
- the compact adele quotient instance `CompactSpace (AdeleQuotient F)`;
- a fundamental class family `c` with `RelativeWeilGroup.IsArithmeticClassFamily c`;
- a finite place `v` of `F`;
- a nontrivial additive character `ψ` of the completion `F_v`;

the proposition `RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ` holds.

The compactness instance is a binder because the published definitions need
it. It is proved in the Library (`Langlands/Global/AdeleQuotientCompactProof.lean`),
so it restricts nothing. All four quantified objects are universal. In
particular the statement holds for **every** nontrivial `ψ`, not for a chosen
one.

## 2. What `RelativeCertifiedPoleComparisons` asserts

The definition is published in
`Langlands/Global/Factors/RelativePolePairingStatement.lean`. Its index type is
`WitnessedGenerator.{uF, uW, uP} F E c v`
(`Langlands/VirtualRepresentation/Global/RelativeImages.lean`). A witnessed
generator `d` consists of the following data:

- an irreducible unitary finite-dimensional representation `d.weil` of the
  relative Weil group `W_{E/F}` of `c`, with carrier universe `uW`;
- a cuspidal operator realization `d.cuspidal` of `GL_{n}` over `F`, where
  `n = d.rankIndex + 1`, with a spectral presentation in universe `uP`;
- weak association of `d.weil` with that presentation;
- a place `w` of `E` above `v`, a reciprocity candidate for `E_w`, and a local
  map `W_{F_v} → W_{E/F}` satisfying `IsLocalRelativeWeilMap`;
- irreducibility and admissibility of the local component `Π_v` at `v`;
- an effective element `d.weilElement` of the local unitary Weil lattice that is
  the exact expansion of the restriction of `d.weil` along the local map;
- an element `d.automorphicElement` of the local unitary supercuspidal lattice
  that is the unitary supercuspidal support of `Π_v`.

Both lattices have the isomorphism classes of irreducible unitary objects as an
orthonormal basis. The pairings are the published `LocalWeil.unitaryPairing`
and `PadicSupercuspidal.unitaryPairing`.

The proposition `RelativeCertifiedPoleComparisons F E c v ψ` says:

1. a Haar measure `ν` on `F_v` that is self-dual for `ψ` exists;
2. for **every** such self-dual `ν` there is a `RelativePairFactorData` `D`
   consisting of:
   - for each generator `e`, a smooth dual class of its local component
     (`IsSmoothDual`);
   - for each pair `(d, e)`, a polynomial with
     `IsAutomorphicPairLPolynomial ψ ν` for the local component of `d` and the
     dual class of `e`. This is the actual Langlands-quotient Rankin–Selberg
     L-polynomial, so `1/P(q^{-s}) = L(s, Π_{d,v} × Π_{e,v}^∨)`;
   - finite sets of omitted finite places, omitted local functions and
     boundary functions, separately for the two sides.

   These data must satisfy three conditions:
   - `RegularPairComparisonsAt D.comparison 0`. For every pair `(d, e)`, both
     distinguished functions are meromorphic at `0`. The omitted local
     functions and the boundary functions are analytic and nonzero at `0`.
     The two completed products agree on a punctured neighbourhood of `0`.
   - `RealizesPairingAtZero (fun j => j.weilElement) D.comparison.left`. The
     arithmetic function of `(d, e)` is the arithmetic pair L-factor
     `L(s, S_{d,v} ⊗ S_{e,v}^∨)` of the restricted representations, evaluated
     at `X = q^{-s}`. Its `meromorphicOrderAt` at `0` equals
     `-⟨d.weilElement, e.weilElement⟩`.
   - `RealizesPairingAtZero (fun j => j.automorphicElement) D.comparison.right`.
     The automorphic function `1/P(q^{-s})` has order at `0` equal to
     `-⟨d.automorphicElement, e.automorphicElement⟩`.

The existence of a self-dual measure, of the dual classes and of the
L-polynomials is **asserted**, not assumed. So the statement cannot be made true
by an empty supply of factor or measure witnesses. The omitted and boundary data
are existentially quantified. This is the only flexibility, and it is the one
the published definition provides. The statement does not assert that any
witnessed generator exists. If there are none, the comparison conditions hold
trivially, and the downstream isometry concerns the zero span.

## 3. Source correspondence

The source is G. Henniart, *Une preuve simple des conjectures de Langlands pour
GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), 439–455
(`henniart-2000-simple-proof`). PDF page = printed page − 438.

- **§2.2, p.444 (PDF 6).** `S` and `P` are associated if `L(S_w, s) = L(P_w, s)`
  at almost all finite unramified places `w`. Here this is the published weak
  association `RelativeWeilGroup.IsWeaklyAssociated`.
- **Théorème 2.4 and its Corollaire, p.445 (PDF 7).** Take irreducible unitary
  `S`, `S'` of `W_F` and unitary cuspidal `P`, `P'`, with `S` associated to `P`
  and `S'` associated to `P'`. Then at every finite place `v`,
  `L(P_v × P'_v, s) = L(S_v ⊗ S'_v, s)`; the same holds for the contragredients,
  and `ε` agrees for every nontrivial additive character. Théorème 2.4 says that
  `P_v` is parabolically induced from unitary supercuspidal representations.
- **§2.5, pp.445–446 (PDF 7–8).** `G(F)` is the set of such associated pairs.
  `φ_G(S, P)` is the class of `S_0` in `R_G(F_0)`. `φ_A(S, P)` is the sum of the
  classes of the unitary supercuspidal `π_i` with `P_0 = π_1 × ⋯ × π_r`. Both
  lattices have orthonormal bases (§2.6, p.446). Here `φ_G` and `φ_A` are
  `weilElement` and `automorphicElement`, and Henniart's place `0` is `v`.
- **Lemme 2.8 and its proof, pp.447–448 (PDF 9–10).** The Lemma says
  `⟨σ, σ'⟩_G = ⟨π, π'⟩_A`. The proof has three steps:
  1. Since `S_0` and `S'_0` are semisimple, `⟨σ, σ'⟩_G` is the order of the pole
     at `s = 0` of `L(σ ⊗ σ'^∨, s)`. This is the arithmetic pole formula
     `RealizesPairingAtZero` for `weilElement`. Mathlib's `meromorphicOrderAt`
     gives a pole a negative order, hence the sign.
  2. `π_0` and `π'_0` are induced from unitary supercuspidals. By [JPSS,
     Prop. 8.1 et 8.4], `⟨π, π'⟩_A` is the order of the pole at `s = 0` of
     `L(π × π'^∨, s)`. This is the automorphic pole formula for
     `automorphicElement`. The printed proof cites "Théorème 2.3" for the
     induction property; that property is the content of Théorème 2.4.
  3. The Lemma follows from Corollaire 2.4. In the present form, Corollaire 2.4
     applied to the pairs `(S, P)` and `(S'^∨, P'^∨)` makes the two
     distinguished factors equal rational functions of `q^{-s}`. Then
     `RegularPairComparisonsAt` holds with empty omitted sets and constant
     boundary functions `1`. (This application is our reading; the printed
     proof only says that the Lemma follows from Corollaire 2.4.)

So the statement asserts, for every witnessed pair, the three facts that the
proof of Lemme 2.8 combines, in the form that `relativePolePairing` consumes.
Lemme 2.8's own conclusion, equality of the pairings, is the first conclusion
of the published `RelativePolePairingStatement` (proved as `relativePolePairing`).

### Differences from the source

- Henniart's `S` is a representation of the absolute Weil group `W_F`. Here it
  is a representation of the finite-relative group `W_{E/F}` of an arithmetic
  class family. Its inflation to `W_F` is Henniart's object, and the statement
  is quantified over every finite Galois `E/F`.
- Henniart restricts along a fixed embedding at the place `0`. Each witnessed
  generator here carries its own place `w` above `v`, reciprocity candidate and
  characterized local map. The arithmetic factor of `(d, e)` uses the local map
  of `d` for `d.weil` and the local map of `e` for the dual of `e.weil`. The
  statement therefore also asserts the comparison when the two maps differ.
  The expected reason is that characterized local maps at the same `v` are
  conjugate in `W_{E/F}`: for a fixed `w` two such maps differ by a 1-cocycle
  of the decomposition group with values in the idele class group of `E`, and
  that cohomology group vanishes. Conjugate maps give isomorphic restrictions.
  The statement does not state this fact separately; it is listed in §5.
- Henniart takes `P` unitary cuspidal. Here `P` is an actual cuspidal operator
  realization, and `WitnessedGenerator` does not assume its central character
  unitary. Weak association with the unitary `S` is expected to supply this:
  the central character agrees with `det S` at almost all places, and `det S`
  is unitary. This is also listed in §5.
- Henniart fixes a global additive character. Here `ψ` is any nontrivial
  character of `F_v`. Only the choice of the automorphic L-polynomial certificate
  depends on `ψ` and `ν`, and Rankin–Selberg L-factors do not depend on them.

## 4. Relation to other Library units

- `Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCuspidalFactorStatement`
  (`Langlands/Automorphic/AssociatedFactorStatement.lean`) is Henniart's
  Corollaire 2.4 for actual cuspidal classes and a single local map. It does not
  contain the pole formulas, the lattices or the witnessed generators. The
  present statement does not duplicate it; the expected proof uses it.
- `AssociatedSupercuspidalInductionStatement` (same file) is Théorème 2.4, which
  step 2 needs.
- `Langlands.RankinSelberg.TemperedLFactorStatement`, proved as
  `temperedLFactor`, gives the product decomposition of L-polynomials of block
  inductions. It is one of the results that step 2 needs. The pole of
  `L(s, ρ × ρ'^∨)` at `0` for unitary supercuspidal `ρ`, `ρ'` (JPSS Prop. 8.1)
  is a further local input.
- `RelativePolePairingStatement`, proved as `relativePolePairing`, derives from
  `RelativeCertifiedPoleComparisons` the pairing equality, the equality of
  relation kernels and the unique generated isometry.

## 5. Proof obligations

These belong to a future proof task; this unit proves none of them.

- Corollaire 2.4 at the place `v`, through `AssociatedCuspidalFactorStatement`.
  It needs an additive character of the adeles whose component at `v` is
  related to `ψ`, or the independence of L-factors from the additive character.
- Théorème 2.4 (`AssociatedSupercuspidalInductionStatement`).
- The JPSS pole formula for unitary supercuspidal pairs. Multiplicativity of
  the L-polynomial over the support is in `temperedLFactor`.
- Semisimplicity of the restricted unitary Weil representations, and the
  arithmetic pole formula: the multiplicity of the eigenvalue `1` of geometric
  Frobenius on inertia invariants equals the intertwining number.
- Conjugacy of characterized local maps, giving independence of the restriction
  from the map.
- Unitarity of the central character of each witnessed cuspidal realization,
  from weak association with a unitary representation (needed for the
  hypothesis `HasUnitaryCentralCharacter` of the two statements above).
- Meromorphy at `0` of both distinguished factors. They are rational functions
  of `q^{-s}` with nonzero denominators, so this is routine.
