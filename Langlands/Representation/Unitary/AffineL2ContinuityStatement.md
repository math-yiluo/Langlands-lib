# Joint continuity of the actual normalized affine L² action: statement

Authors: Worker 452 (statement and original description) and Worker 971
(independent inspection and description edits).

This module defines the proposition
`Langlands.AffineL2.JointContinuity F T` for the published construction in
`Langlands.Representation.Unitary.AffineL2`. It states an analytic target;
this module supplies no proof of the proposition. The target is internal,
derived from that construction and Mathlib's `Continuous`, product topology
and `Lp` interfaces. It does not transcribe a separately numbered result
from external literature.

## Binders and topologies

For every prime `p` with `[Fact p.Prime]`, every `F : PadicField.{u} p` and
every supplied `T : F.TopologicalData`, the proposition first installs
`T.topology`, `T.valuativeRel` and `T.localField` as local instances, before
the dependent Borel and Haar binders. It then quantifies over

- every `n : ℕ`, including `n = 0`;
- every measurable structure on `V = Fin n → F.Carrier` with
  `[BorelSpace V]` for the finite product topology induced by `T.topology`;
- every measure `μ : Measure V` with `[Measure.IsAddHaarMeasure μ]`.

No normalization of the additive Haar measure is chosen. All topologies are
the inherited Mathlib ones built from `T.topology`:

- `GeneralLinear n F.Carrier`, Mathlib's units of the matrix ring, carries
  the units topology over the entrywise matrix topology (induced through
  the matrix and its inverse);
- `Fin n → F.Carrier` carries the finite product topology;
- `GeneralLinear.mirabolic n F.Carrier`, the published subgroup of
  `GeneralLinear (n + 1) F.Carrier` with last row `(0, …, 0, 1)`, carries the
  subspace topology of that units topology;
- `Lp ℂ 2 μ`, Mathlib's actual almost-everywhere quotient, carries its norm
  topology;
- the parameter-vector spaces carry the product topologies.

## Conclusion

The proposition is the conjunction of

```text
Continuous (fun zf : (GeneralLinear n F.Carrier × (Fin n → F.Carrier)) × Lp ℂ 2 μ =>
  operator F T μ zf.1.1 zf.1.2 zf.2)
Continuous (fun gf : GeneralLinear.mirabolic n F.Carrier × Lp ℂ 2 μ =>
  mirabolicRepresentation F T μ gf.1 gf.2)
```

that is, joint continuity of `((A,v),f) ↦ operator F T μ A v f` and of
`(g,f) ↦ mirabolicRepresentation F T μ g f`. Both maps use the constructed
operator and representation on the actual carrier `Lp ℂ 2 μ`, with the
supplied measure and topology.

By the published `coeFn_operator`, `operator F T μ A v f` is represented
`μ`-almost everywhere by

```text
x ↦ NormalizedL2Pullback.normalization (T.determinantNorm n A : ℝ≥0) •
      f ((A⁻¹).val.mulVec (x - v)),
```

that is, `x ↦ |det A|^(-1/2) f(A⁻¹(x-v))`. Here `T.determinantNorm n A`
is the residue-normalized absolute determinant of the supplied data, and
`NormalizedL2Pullback.normalization c = ((NNReal.sqrt c : ℝ) : ℂ)⁻¹` is the
positive inverse square root. By the published
`coeFn_mirabolicRepresentation`, the mirabolic action has the same
representative with `A = GeneralLinear.Mirabolic.linearPart g` and
`v = GeneralLinear.Mirabolic.columnPart g`, the actual leading block and
final column of `g`. Their multiplication is the affine
law `(A,v)(B,w) = (A*B, v + A.val.mulVec w)` inherited from matrix
multiplication. These are almost-everywhere identities of representatives,
not pointwise formulas.

## Scope

The proposition assumes only the stated field, topological, Borel and Haar
data. It imposes no continuity, local constancy, measure-scaling,
generic-continuity or extra regularity premise. Joint continuity concerns
the parameter and the vector simultaneously. Continuity of a fixed-vector
orbit map would follow by composition, but no such corollary is stated
here. Operator-norm continuity is not claimed.

A prospective proof can combine joint continuity of inverse-affine
evaluation, local constancy obtained from the open kernel of the determinant
norm, and joint continuity of normalized pullback. The mirabolic part can
then use the continuous actual coordinate maps. These are proof obligations;
no generic continuity proposition or proof is an input to this statement.

Fourier/Plancherel, coefficient completion, quotient transport, induced
Hilbert models, general semidirect induction and irreducibility remain
separate obligations. In particular, this statement neither proves
continuity nor settles normalized-induction irreducibility.
