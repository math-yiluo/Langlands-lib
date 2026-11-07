# Valuation layers and the degree of a full-residue subfield

This internal development proves a dimension bound from the actual valuation,
actual residue quotient, and finite integer lattice already constructed in
`LocalDivisionValuation`, `LocalDivisionResidueSubfield`, and
`LocalDivisionIntegerLattice`. It does not assume a ramification formula or a
maximal-subfield theorem.

Let `K : Type u` be a nonarchimedean local field and `D : Type u` a
finite-dimensional central division algebra over `K`. There is no restriction
on characteristic. Put

\[
 n=\operatorname{reducedDegree}_K(D),\qquad
 v=\texttt{localReducedNormValuation K D},\qquad
 w=\texttt{localReducedNormIntValuation K D}.
\]

Here `w` is `v` followed by the existing ordered multiplicative isomorphism from
the original base value group to `WithZero (Multiplicative ℤ)`.
The notation `exp(j)` below denotes its integer-value element, with
`exp(j+k)=exp(j)exp(k)`. The actual integer lattice is
`A = {x : D | v(x) ≤ 1}`, as a module over the original base integer ring
`𝒪[K]`. Its finiteness and its full `K`-span are imported results.

For an arbitrary independent universe `uL`, let `L : Type uL` be a field and
`ι : L →ₐ[K] D` an embedding. The hypothesis throughout the subfield argument is
surjectivity of `localDivisionSubfieldResidueMap K D ι`: the actual residue
quotient of the restricted valuation on `L` maps onto the actual residue quotient
of `D`. No finiteness or separability assumption on `L/K` is added.

`localDivisionSubfieldLeftModule` is the original left action
`c • x = ι(c)x`. It is a `Module L D`, not a central `Algebra L D` structure.
The original `K`-action is compatible with this module structure because `ι`
is a `K`-algebra homomorphism. The integer scalar actions and towers in the
proof are the composites of the original inclusions through `K`.

## Original layer representatives and a base scalar

`localDivisionValuationLayerRepresentative K D i` chooses an original element
with value `w(x)=exp(-i)` when this value is attained, and is zero otherwise.
`localDivisionValuationLayerRepresentative_value` proves the required equality
under the explicit attainment hypothesis. The private adjacent-layer comparison
uses discreteness of the integer group:

\[
 a<\exp(-i)\quad\Longleftrightarrow\quad a\leq\exp(-(i+1)).
\]

`exists_localDivision_scalar_valuation_step` constructs a nonzero
`p : 𝒪[K]` in the Jacobson radical of the zero ideal such that

\[
 w(\operatorname{algebraMap}_{K,D}(p))=\exp(-n).
\]

Surjectivity of the original base valuation gives a base element with
integer-normalized value `exp(-1)`. Its value is strictly less than one, so it
is an integer and a nonunit. The local-ring description of the Jacobson radical
puts it in that radical. The imported reduced-norm scalar formula raises this
base value to the power `n`, giving the displayed value in `D`.

## Approximation from full actual residue

`exists_localDivisionSubfield_valuation_improvement` says that for original
elements `x,t : D` with `t ≠ 0` and `v(x)=v(t)`, some `c : L` satisfies

\[
 v(x-\iota(c)t)<v(t).
\]

Indeed, `xt⁻¹` is integral. Residue surjectivity and the surjectivity of reduction
in the restricted field supply an integral `c` with the same actual residue.
Equality in the actual residue quotient means that `xt⁻¹-ι(c)` has value less
than one. Multiplication on the right by `t` gives the inequality.
`exists_localDivisionSubfield_intValuation_improvement` transports this result
through the ordered value-group isomorphism.

`exists_localDivisionSubfield_layer_approximation` removes one layer from any
`x` with `w(x) ≤ exp(-i)` by an element of a given `L`-submodule containing the
chosen `i`-th representative. If equality holds, that value is attained and
the previous improvement applies. If equality fails, zero suffices by the
adjacent-layer comparison.

`exists_localDivisionSubfield_finite_layer_approximation` iterates this argument.
If `N` contains the representatives for `i < m`, then every original integral
element `x` admits `s ∈ N` with

\[
 w(x-s)\leq\exp(-m).
\]

The proof is a finite induction, adding the successive subfield-span corrections.

## Spanning by at most the reduced degree many elements

`localDivisionSubfield_layer_span_eq_top` proves

\[
 \operatorname{span}_L\{t_i\mid i\in\operatorname{Fin}(n)\}=D,
\]

where `t_i` are the original layer representatives. Let `N` be this span,
and let `I=(p)` for the base integer constructed above. Finite-layer
approximation gives, for every `x ∈ A`, an element `s ∈ N` whose remainder
has value at most `exp(-n)`. Consequently

\[
 y=\operatorname{algebraMap}(p)^{-1}(x-s)\in A,\qquad x-s=p\mathbin{\bullet}y.
\]

As submodules for the original `𝒪[K]`-action, this proves
`A ≤ N.restrictScalars 𝒪[K] ⊔ I • A`. The ideal `I` is contained in the
Jacobson radical and `A` is finitely generated. Mathlib's
`Submodule.le_of_le_smul_of_le_jacobson_bot`, a form of Nakayama's lemma, gives
`A ≤ N.restrictScalars 𝒪[K]`. Since the original `K`-span of `A` is `D`,
and the original `K`-action factors through the embedded field action, `N=D`.

`localDivisionSubfield_finrank_le` applies the finite spanning-family bound:

\[
 \dim_L D\leq n.
\]

Finally, `reducedDegree_le_localDivisionSubfield_finrank` proves

\[
 n\leq\dim_K L.
\]

The embedding makes `L` finite-dimensional over `K`, and the original scalar
tower makes `D` finite-dimensional over `L`. The tower dimension formula and
the imported square-dimension identity give

\[
 (\dim_K L)(\dim_L D)=\dim_K D=n^2.
\]

Together with `dim_L D ≤ n` and `n>0`, this implies the asserted lower bound.

These results do not yet identify the degree of any selected generator, prove
that the actual residue degree equals `n`, prove local SK1, or prove the full
local Kneser–Tits proposition.
