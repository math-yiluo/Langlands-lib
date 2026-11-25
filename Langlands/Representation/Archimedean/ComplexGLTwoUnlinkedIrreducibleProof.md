# Proof: principal series of `GL_2(ℂ)` with unlinked characters are irreducible

Lean module: `Langlands.Representation.Archimedean.ComplexGLTwoUnlinkedIrreducibleProof`.

## Statement proved

`Langlands.Archimedean.complexGLTwoUnlinkedIrreducible : ComplexGLTwoUnlinkedIrreducibleStatement`
(Library module `ComplexGLTwoUnlinkedIrreducible`). For complex characters `d`, `e` that are not
linked (`¬ IsComplexLinked d e`), the `(𝔤𝔩_2(ℂ), U(2))`-module of `U(2)`-finite functions of the
standard module of `[d, e]` is irreducible. This is Tadić 2009, p. 11, after Jacquet–Langlands:
`δ_d × δ_e` is irreducible unless `δ_d δ_e⁻¹ = z^p z̄^q` with integers `p q > 0`.

## Proof

Put `m = l_e - l_d` and `A = (t_e - t_d - 1) + m/2`, and `B = A - m`. A function of the standard
module is `Φ(det g) H(r)` with `H` homogeneous of type `z^A z̄^B` in the bottom row `r`.
`GLTwoUnlinked.setup` verifies the hypotheses of `GLTwoCore.Setup [d, e] (Phi d) A m`:

* `hΦ`, `hΦ0`: `Phi d = unitChar l_d (t_d + 1/2)` is real differentiable and nonzero on `ℂˣ`
  (`differentiableAt_unitChar`, `unitChar_ne_zero`);
* `hF1`: `GLTwoKFinite.exists_isRealized`;
* `hup`: if `s_j = A - (m⁺ + j) = 0`, then `p = -(A + 1) = -(m⁺ + j + 1)` and
  `q = p + m = -(m⁻ + j + 1)` are both negative. With `x = t + l/2` and `y = t - l/2`,
  `x_d - x_e = -(A + 1) = p` and `y_d - y_e = -(A + 1) + m = q` (`x_sub`, `y_sub`), so `d`, `e` would
  be linked (`linked_of`);
* `hdown`: if `A + (m⁻ + j) + 1 = 0` with `j ≥ 1`, then `p = m⁻ + j ≥ 1` and `q = p + m = m⁺ + j ≥ 1`,
  and again `d`, `e` would be linked.

`Setup.isIrreducible` (module `ComplexGLTwoIrreducibleCore`) then gives irreducibility. The
nontriviality of the `U(2)`-finite functions is the Library theorem `complexStandardNontrivial`.
The proof uses no swap, criterion or Langlands-quotient statement: only the modules
`ComplexGLTwoPolynomial`, `ComplexGLTwoModel`, `ComplexGLTwoIrreducibleCore`,
`ComplexGLTwoKFinite` and the Library.
