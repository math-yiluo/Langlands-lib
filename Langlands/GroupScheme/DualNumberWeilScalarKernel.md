# Scalar kernels on the actual dual-number Weil group

This derived supporting construction extends the epsilon calculation in
`DualNumberWeilKernel` to every scalar `c : DualNumber k`, over every field
`k` in arbitrary universe and characteristic. The group remains the actual
affine Weil restriction of the additive line from `k[ε]` to `k`.

For every scheme `S` over `Spec k`, `scalarElement` extends the two base-field
coefficients of `c` to the relative global sections of `S`. Its pullback
compatibility is `scalarElement_comp`. Conjugating additive multiplication by
this element through the previously constructed natural coordinates gives
`scalarPoints`. Its naturality recovers the actual scheme homomorphism
`scalarMap k c` through `homOfPoints`. Its action on every test scheme is
`coordinates_scalarMap`, and `scalarMap_epsilon` identifies the epsilon
specialization with the previously constructed `epsilonMap`.

Write `c = a + εb` and a test coordinate as `z = x + εy`. The underlying
coefficient identity is

```text
c z = a x + ε(a y + b x).
```

The two coefficient lemmas prove the following alternatives on every
commutative coefficient algebra, including nonreduced and trivial algebras.
Nonzero field coefficients are cancelled by their mapped inverses; the
proof does not assume that a test algebra is a field.

| Base scalar | Annihilator condition on `z` | Kernel dimension |
| --- | --- | --- |
| `a ≠ 0` | `x = y = 0` | `0` |
| `a = 0`, `b ≠ 0` | `x = 0` | `1` |
| `a = b = 0` | no condition | `2` |

The kernels throughout are the published scheme-theoretic pullbacks along
the target unit. `kernelPointsEquiv` identifies their scheme points with the
pointwise kernels. The three cases construct the following actual natural
coordinate equivalences:

- `unitScalarKernelCoordinates` gives the unique function on `Fin 0`;
  `scalarMap_eq_one_iff_of_fst_ne_zero` supplies its inverse identity.
- `nilpotentScalarKernelCoordinates` reads the epsilon coefficient with
  inverse `y ↦ εy`. Its naturality follows from the coefficient formula for
  pullback of the original Weil coordinates.
- `zeroScalarKernelCoordinates` retains both dual-number coefficients.
  The inverse is the original coordinate equivalence, since multiplication
  by zero imposes no equation. `dualVectorEquiv` then turns the two
  coefficients into a function on `Fin 2`.

The same `dualVectorEquiv` gives `isVectorGroup` and the actual isomorphism
`vectorIso` between the entire Weil restriction and the standard vector group
of dimension two. In each kernel case the proofs verify naturality on
arbitrary scheme tests. They establish `unitScalarKernel_isVectorGroup`,
`nilpotentScalarKernel_isVectorGroup` and
`zeroScalarKernel_isVectorGroup`, respectively.

`scalarKernelDimension` selects the dimension in the table. Case analysis
combines the three constructions into `scalarKernel_isVectorGroup`.
The published natural-vector-coordinate API then constructs the actual
group-scheme isomorphism

```text
scalarKernelIso :
  kernel (scalarMap k c) ≅
    VectorGroup.groupScheme (CommRingCat.of k) (scalarKernelDimension k c).
```

`scalarKernel_smooth`, `scalarKernel_connected` and
`scalarKernel_unipotent` apply the published vector-group geometry and
all-coefficient unipotence results. These conclusions include dimension zero
and have no perfectness or characteristic restriction.

The provenance is derived from the final scalar calculation in the proof of
Kaletha–Prasad Lemma C.4.4, printed pp.701–702 / PDF pp.732–733 of the
2023 book, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
There the special-fibre coordinate map is multiplication by a power of the
ramified uniformizer in the dual-number algebra. A positive power beyond
the first is zero and has the whole restricted additive group as kernel;
the first power has the additive line as restricted kernel. The present
construction includes these scalar cases and the equality case, and
generalizes them to all base dual numbers by the coefficient calculation
above. It does not identify the ramified special-fibre algebra with these
dual numbers, construct the unitary models `X_{r,s}`, compare their
transitions with `scalarMap`, or prove the full C.4.4 or C.5.3 assertion.
Those comparisons remain obligations of the consuming root-depth proof.
