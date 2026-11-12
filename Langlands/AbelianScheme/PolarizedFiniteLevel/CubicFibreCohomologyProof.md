# Proof of the cubic-fibre cohomology theorem

`cubicFibreCohomology` proves the published target
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyStatement`.
Let `a` be a datum over an algebraically closed field `K`. Then the cubic
diagonal bundle `a.cubicBundle` has no cohomology in positive degrees, and its
global sections have dimension `6^g*d`.

The module first proves the theorem from three geometric inputs, given as
explicit hypotheses. It then discharges each input with a published Library
theorem. The inputs are:

- `Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingStatement`:
  an ample line bundle on an abelian variety over an algebraically closed
  field has no higher cohomology (Mumford, Fogarty and Kirwan, *Geometric
  Invariant Theory*, third edition, Proposition 6.13 (i)).
- `Langlands.GroupScheme.FieldSymmetricMultiplicationPullbackStatement`:
  `[k]^* N ≅ N^(k*k)` for a symmetric line bundle `N` and `k > 0` (Milne,
  *Abelian Varieties*, Corollary 6.6).
- `Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement`:
  if the Mumford map of an ample `L` is finite and flat, then `χ(L)^2` is
  its native degree (Milne, Theorem 13.3 (a); GIT, Proposition 6.13 (iii)).

The first two inputs follow from the balanced cube identity
`Langlands.GroupScheme.FieldCubePullbackStatement`, through the published
conditional theorems `ampleLineBundleHigherCohomologyVanishing_of_cube` and
`fieldSymmetricMultiplicationPullbackOfCube`. The cube identity is the
published `Langlands.GroupScheme.fieldCubePullback`
(`Langlands.AbelianScheme.FieldCubePullbackProof`). The third input is the
published `Langlands.AbelianScheme.algClosedFieldAmpleMumfordEulerSquare`
(`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleMumfordEulerSquareProof`).

## Declarations

`multiplication_isIsogeny_finrank_of_symmetricMultiplication` assumes the
symmetric multiplication formula. Let `A` be an abelian scheme of relative
dimension `g` over an algebraically closed field, with an ample line bundle
`H`, and let `k > 0`. Then multiplication by `k` is an isogeny, and its
native rank `Scheme.Hom.finrank` is `k ^ (2 * g)` at every point. This holds
in every characteristic, including when the characteristic divides `k`.

1. The proof applies the formula to the symmetric ample bundle
   `N = H ⊗ [-1]^* H`. This uses `symmetrization`, `symmetrization_symmetric`
   and `isAmple_symmetrization` from `MultiplicationDegree`.
2. The published `fieldAmpleMultiplicationKernel` then makes the kernel of
   `[k]` finite.
3. The published `fieldFiniteKernelIsogeny` makes `[k]` finite, flat and
   surjective.
4. The published `polarizedFiniteFlatRank`, applied to `[k]^* N ≅ N^(k*k)`,
   gives rank `(k*k)^g = k^(2*g)`.

`groupHom_nsmul_id_eq_multiplication` identifies the natural multiple
`k • 𝟙 A` in the additive group of abelian-scheme endomorphisms with the
published `GroupScheme.multiplication A.toGrp k`. Both are the `k`-th power
of the identity.

`Datum.sixfoldPolarization_degree_of_symmetricMultiplication` assumes the
symmetric multiplication formula. For a datum `a` over an algebraically
closed field, it shows that `6 • a.polarization` is finite and flat, with
constant native rank `6 ^ (2 * g) * d ^ 2`. The proof applies the previous
theorem with `k = 6` to the ample bundle `a.cubicBundle`
(`Datum.cubicBundle_isAmple`). It transports the result along
`groupHom_nsmul_id_eq_multiplication` and passes it to the published
`sixfoldPolarizationDegreeReduction`.

`cubicFibreCohomology_of_inputs` derives `CubicFibreCohomologyStatement`
from the three inputs. Let `a` be a datum over an algebraically closed `K`.

1. Vanishing: by the published `Datum.cubicBundle_isAmple` and the vanishing
   input, `H^i(A, a.cubicBundle) = 0` for `i > 0`.
2. The published `Datum.cubicBundle_hasFiniteCohomology` gives finite
   cohomology. The published
   `Datum.cubicBundle_finrank_of_vanishing_of_eulerSquare` reduces the
   dimension claim to `χ(a.cubicBundle)^2 = 6^(2g) d^2` in `ℤ`.
3. The published `cubicBundleMumford` supplies normalization data under which
   the Mumford map of `a.cubicBundle` is the parameter map of
   `6 • a.polarization`.
4. Apply the Euler-square input at the image `y` of the unit point under
   that map. It gives `χ^2 = finrank_y`. By step 3 and
   `Datum.sixfoldPolarization_degree_of_symmetricMultiplication`, this rank
   is `6^(2g) d^2`.

`cubicFibreCohomology_of_cube` supplies the first two inputs from the
balanced cube identity, using the two published conditional theorems named
above.

`cubicFibreCohomology_of_eulerSquare` applies `cubicFibreCohomology_of_cube`
to the published `fieldCubePullback`. Its only hypothesis is the
Euler-square input.

`cubicFibreCohomology` applies `cubicFibreCohomology_of_eulerSquare` to the
published `algClosedFieldAmpleMumfordEulerSquare`. It has no hypotheses. Its
axioms are `propext`, `Classical.choice` and `Quot.sound`.

The hypothesis `0 < d` of the target is not used, and the level `n` plays no
role.

## Provenance

This is internal derived content that composes published Library theorems.
The mathematical route is the one in the target's Markdown: GIT
Proposition 6.13 (i) and (iii) on printed pp.123–124, the footnote to
Definition 7.5 on printed p.130, and Milne, *Abelian Varieties*, Theorems 8.2
and 13.3. The degree of `[6]` follows Milne's Theorem 8.2, p.13, except that
the published `polarizedFiniteFlatRank` replaces Milne's comparison of
intersection numbers.
