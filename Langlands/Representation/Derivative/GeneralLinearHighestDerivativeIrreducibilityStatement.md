# Irreducibility of the highest actual general-linear derivative

Worker 596. The Prop-valued definition
`Langlands.Derivative.GeneralLinearHighestDerivativeIrreducibility.{uF, uV} F T`
states the first assertion of Zelevinsky 1980, Theorem 8.1. It proves nothing.

For any p-adic field `F : PadicField.{uF} p`, supplied topological data `T`,
positive rank `N`, nontrivial unitary additive character `ψ` and irreducible
actual smooth complex representation `π` of `GL_N(F)`, every highest-order
datum `hd` has an irreducible derivative
`(generalLinearDerivative T ψ N hd.order hd.le_rank).obj π`.
Carriers lie in `Type (max uF uV)` with independent universes `uF` and `uV`.
No unitarity, admissibility, homogeneity, label, finite-length or socle
assumption is imposed on `π`.

The existing `GeneralLinearHighestDerivativeOrderData` records a positive
order at most `N`, nonzero derivative at that order, and vanishing at every
higher feasible order. Such data exist for every nonzero smooth `π` of
positive rank by the Library's
`chooseGeneralLinearHighestDerivativeOrder`. Thus quantification over `hd`
is the actual highest derivative, not a supplied irreducibility certificate.
The derivative is the Library's normalized Bernstein-Zelevinsky functor:
restriction to `P_N`, followed by `hd.order - 1` applications of `Φ⁻` and
one `Ψ⁻`. The output is a representation of `GL_(N - hd.order)`, including
`GL_0` when the highest order equals `N`.
`Representation.IsIrreducible` asserts that the actual lattice of invariant
subspaces is simple.

Source: A. V. Zelevinsky, *Induced representations of reductive p-adic
groups II. On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13
(1980), Theorem 8.1, printed p.195, PDF page 32 (zero-based index 31). Registered source
`zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
at
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
The original rendered page and its proof were read. No corresponding errata
entry was found in the public notes.

The source asserts irreducibility of the highest derivative and then
identifies its multisegment label. This statement retains the first
assertion only. It does not claim the label formula. The source fixes a
character when defining derivatives; the assertion applies to every
nontrivial unitary choice quantified here. The definitions of highest
order and normalized derivative agree with the convention used by the
shifted highest-derivative statement in `Classification.BernsteinUnitaryStatement`.

The published proof uses a nondegenerate pairing between highest derivatives,
finite length, the unique irreducible submodule and quotient of the same
label, and its multiplicity one. The existing Library label-step result
only produces an irreducible subquotient and does not prove this statement.
All of the irreducibility argument remains a proof obligation.
