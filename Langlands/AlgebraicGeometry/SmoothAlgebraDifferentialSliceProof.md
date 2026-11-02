# Proof of the algebraic differential slicing criterion

The proof is an internal derivation from Mathlib's cotangent complex API. It
proves `SmoothAlgebraDifferentialSliceStatement`, with no additional hypotheses.

The classes of the chosen equations generate the conormal module `I/I²`.
Their images under the cotangent map are precisely the prescribed basis of
`S ⊗[P.Ring] Ω[P.Ring/R]`. A linear map which sends a spanning family to a
basis is bijective. Exactness of the cotangent sequence then makes `Ω[S/R]`
zero. Its kernel is also zero; because the source algebra is formally smooth,
Mathlib identifies this kernel with `H¹(L[S/R])`. These two vanishings give
formal etaleness.

The finite set of equations generates the kernel, so the quotient of the
finitely presented smooth algebra is finitely presented. This upgrades formal
etaleness to etaleness. The auxiliary theorem
`formallyEtale_of_cotangentComplex_bijective` isolates the exactness argument.
No scheme slicing or existence of transverse equations is asserted here.

The auxiliary theorem `exists_notMem_basis_kaehlerDifferential` extends a
prescribed differential basis at a prime to a principal open neighborhood.
It forms the linear map from the finite free module on the chosen functions
to the module of differentials. Localization at the prime identifies this
map with the given basis isomorphism. Finite presentation extends its
bijectivity to a principal open, where the same functions give the new basis.
This argument follows Mathlib's proof of
`Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`, retaining the prescribed
functions instead of choosing new ones.

`etale_quotient_span_of_basis_kaehlerDifferential` applies the main criterion to
the quotient by the chosen functions: scalar extension carries their
differential basis to the required basis along the quotient.
`exists_notMem_etale_quotient_span` combines this with the neighborhood lemma.
It supplies an etale quotient on a principal open from a differential basis at
one prime. The statements do not require that the equations vanish at that
prime; applications can impose that separate condition to ensure that the
closed slice contains it.

The final two auxiliary theorems choose finitely many equations from an
arbitrary allowed set. If their differentials generate the localized module
of differentials, Mathlib's finite flat local module theorem extracts a
basis, and the preceding result applies. Generation on the cotangent fiber
also suffices: Nakayama's lemma lifts this generation to the localized module.
Thus the allowed set can later be chosen to consist of pullbacks of functions
vanishing at the point of the desired scheme slice.
