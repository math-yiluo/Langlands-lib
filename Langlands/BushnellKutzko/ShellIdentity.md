# The shell identity from a monomial functional equation

## Setting

`K` is a `p`-adic field (`PadicField p`) with its canonical topology, valuation and local-field
structure; `T = K.canonicalTopologicalData`, `q = T.residueCardinality`, and `T.ord` is the
canonical order of `K`. `GeneralLinear (n + 1) K.Carrier` carries its Borel measurable structure
and the Library Haar measure `RankinSelberg.generalLinearHaar K.Carrier n`. For a complex number
`t`, `spectralPoint q t = q^{-t}` (Library `RankinSelberg.spectralPoint`), and
`GodementJacquet.jpssShift n = n/2`.

`σ` is a complex representation of `GL_{n+1}(K)` on `V`, `ψ` a Library
`UnitaryAdditiveCharacter K.Carrier` and `ν` an `AdditiveHaarMeasure K.Carrier`. The hypothesis
`GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ 1 1 c a` is the Library
form of the Godement–Jacquet functional equation of `σ` with both Euler polynomials equal to `1`,
unit `c` and exponent `a`. The Library theorem
`GodementJacquet.Padic.exists_supercuspidalMatrixFunctionalEquationData` provides such data for
every irreducible supercuspidal representation of rank at least two.

## Declarations

- `spectralPoint_mul_spectralPoint_one_sub`: for `0 < q`, `q^{-t} q^{-(1-t)} = q^{-1}`.
- `continuous_ord_det`: `g ↦ ord(det g)` is continuous on `GL_{n+1}(K)` (with the discrete
  topology on `ℤ`).
- `measurableSet_ord_det_eq`: each determinant shell `{g | ord(det g) = j}` is measurable.
- `setIntegral_ord_det_eq_of_functionalEquation` (the shell identity): assume the
  functional-equation data above; let `Φ` be a `GodementJacquet.MatrixTestFunction n K.Carrier`
  such that `ord(det g) ≥ j₀` whenever the Fourier transform
  `rectangularFourierIntegral ψ ν Φ` is nonzero at the matrix of `g ∈ GL_{n+1}(K)`; let `f` be an
  element of `GodementJacquet.biSmoothMatrixCoefficients σ` such that
  `GodementJacquet.HasShiftedRationalValue` holds for `Φ`, `f` and the constant rational function
  `r` (with the residue cardinality, the normalized absolute value and `generalLinearHaar`). Then

  `∫_{ord(det g) = -a} Φ̂(g) f^ι(g) dg = c r (q^{-1} q^{-n/2})^a`,

  where `Φ̂ = rectangularFourierIntegral ψ ν Φ` and `f^ι = GodementJacquet.coefficientIota f`
  (the coefficient `g ↦ f(g^{-T})`).
- `exists_ord_det_eq_of_functionalEquation`: under the same hypotheses, if `r ≠ 0` then some
  `g ∈ GL_{n+1}(K)` has `ord(det g) = -a`, `Φ̂(g) ≠ 0` and `f^ι(g) ≠ 0`.

## Provenance

The shell identity is an internal step in the determinant-shell proof of T2. It extracts a
single coefficient of the dual zeta integral using the Library theorem
`RankinSelberg.HighlyRamified.shell_integral_eq_of_const`
(module `Langlands.Representation.RankinSelberg.HighlyRamified.ShellExpansion`).

## Proof

From the functional-equation data take the Fourier partner `Φ̂` of `Φ` (it agrees pointwise with
`rectangularFourierIntegral ψ ν Φ`), and from the data for the dual side a rational function
`RDual` with `HasShiftedRationalValue` for `Φ̂` and `f^ι`. The functional equation, with
`R = C r` and both Euler polynomials `1`, says that for `Re t` large the dual integral at
`t + n/2` equals `c r q^{-a(1-t)}` (`RankinSelberg.epsilonMonomial`).

Write `Ψ(g) = Φ̂(g) f^ι(g) |det g|^{n/2}` and `D(g) = ord(det g) + a`. By the Library lemma
`GodementJacquet.Padic.determinantWeight_shift_spectral`, the dual integrand at `t + n/2` is
`Ψ(g) (q^{-t})^{ord(det g)}`, so `Ψ(g) (q^{-t})^{D(g)}` integrates to
`c r q^{-a(1-t)} q^{-ta} = c r (q^{-1})^a` (`spectralPoint_mul_spectralPoint_one_sub`), a constant,
on a right half-plane. Integrability at one real point comes from the convergence part of
`HasShiftedRationalValue` for the dual side. The fibres of `D` are measurable shells
(`measurableSet_ord_det_eq`), and `Ψ(g) ≠ 0` forces `D(g) ≥ j₀ + a` by the support hypothesis.
`shell_integral_eq_of_const` then gives `∫_{D = 0} Ψ = c r (q^{-1})^a`. On the shell
`D = 0`, that is `ord(det g) = -a`, the weight `|det g|^{n/2}` is the constant `(q^{-n/2})^{-a}`
(`RankinSelberg.normalizedDeterminantWeight_eq_spectralPoint_zpow`); dividing by it gives the
identity.

For `exists_ord_det_eq_of_functionalEquation`: the right side is nonzero (`c` is a unit, `r ≠ 0`,
and `q^{-t} ≠ 0`). If the integrand vanished at every point of the shell, the integral would be
`0` (`setIntegral_eq_zero_of_forall_eq_zero`).
