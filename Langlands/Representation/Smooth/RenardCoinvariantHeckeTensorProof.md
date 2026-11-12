# Diagonal coinvariants and the original Hecke tensor product

Author: Worker 139. The theorem `Langlands.Renard.Smooth.coinvariantHeckeTensor`
proves exactly `CoinvariantHeckeTensorStatement`. It constructs an additive
equivalence on the published objects with the required value on every pure
tensor. The group and carrier universes remain independent, and the statement
and its imports are unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, III.1.15, printed p.69 / PDF p.75, using III.1.4 and the checked
right action of II.3.12 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
Renard identifies the diagonal coinvariants with the balanced Hecke tensor
by the equivalence of smooth representations and nondegenerate Hecke modules.
The implementation proves the identification directly from the two universal
quotient properties. Its internal helper lemmas justify that route.

The operator lemmas in `CoinvariantTensor` first show:

- Applying the check action of the left translate of f by a is applying the
  check action of f after ρ(a⁻¹). Scalar evaluation by `CheckAction.dual` reduces
  this to left invariance of the original measure.
- The normalized indicator of a compact-open subgroup K fixes every K-fixed
  vector for the check action. Inversion preserves the subgroup indicator,
  and μ.inv(K) = μ(K), so the published integrated subgroup-indicator formula
  gives the claim. No unimodularity is needed.

Two bilinear lemmas compare the relations. For a complex bilinear map b,
`balanced_of_invariant` turns diagonal invariance into Hecke balancing. Apply
an arbitrary algebraic linear functional to the output and use the scalar
integral formulas for the check action and the positive integrated action.
Diagonal invariance changes `b(ρ(g⁻¹)x,y)` to `b(x,σ(g)y)`, so the integrals
agree; algebraic dual separation proves the vector equality.

Conversely, `invariant_of_balanced` chooses one compact-open K fixing x and y.
Put e = e_K and let f be its left translate by g. Balancing evaluated at
`(ρ(g)x,y)` becomes `b(x,y) = b(ρ(g)x,σ(g)y)` by the two operator lemmas and the
published positive left-translation and fixed-vector formulas. This proves
that Hecke balancing implies diagonal invariance.

The published `NonUnitalModuleTensor.Tensor` is an integer tensor quotient.
The proof therefore explicitly supplies the complex scalar structure needed
to map out of the complex tensor product. It uses
`NondegenerateTensorScalars.compatibleModule`: multiply the left-module factor
by the complex scalar. The integrated action on that factor commutes with
complex scalars. For the right factor, `right_scalar` follows from the exact
check-action predicate and linearity of integration. A compact-open right
local unit fixing x then proves `scalar_tmul`, moving scalars from x to the
left-module factor through the actual balancing relation. Thus the published
pure-tensor map is complex bilinear (`pureBilinear`). These are local scalar
structures on the existing tensor carrier, without changing either factor's
given complex module or additive group.

`tensorProjection` lifts that bilinear map from the complex tensor. The
balancing-to-invariance lemma makes it diagonal-invariant, so
`fromCoinvariants` descends it through `Representation.Coinvariants.lift`.
For the reverse map, `classBilinear` sends (x,y) to the coinvariant class of
x ⊗ y. This map is diagonally invariant by the definition of coinvariants.
The invariance-to-balancing lemma lets `NonUnitalModuleTensor.lift` descend
its underlying biadditive map through the original integer balancing quotient,
giving `toCoinvariants`.

The maps are inverse: on the coinvariant side use surjectivity of the quotient
map and induction over complex tensors; on the Hecke side use the published
pure-tensor extensionality theorem. Both composites are identity on every pure
tensor and preserve sums. `CoinvariantTensor.equivalence` bundles these maps;
the final theorem installs the exact specified right structure and published
integrated left structure. The helper proofs allow independent carrier sizes,
while the final theorem specializes to the single carrier universe required
by the published statement. Neither representation is assumed admissible or
finite-dimensional.
