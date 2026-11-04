# Symmetries of character forms induced from an ambient form

This internal construction continues `AmbientCharacterForm`. It proves
naturality of that construction under specified commuting automorphisms.
It then constructs local positive forms from the single actual ambient
relative Weyl invariant form and proves their invariance under ambient
normalizer points which preserve the specified subtorus inclusion.

For a finite-dimensional real vector space `V` with a specified symmetric
strictly positive form `B` and a surjective linear map `q : V → W`,
`eq_orthogonalLift_of_mem` proves uniqueness of a lift in the orthogonal
complement of `ker q`. The proof uses injectivity of the previously
constructed equivalence from that complement to `W`.

Suppose `a` and `b` are linear automorphisms of `V` and `W` such that
`q (a v) = b (q v)`, and `a` preserves `B` in both variables.
The inverse image under `a` of any vector in `ker q` is again in `ker q`,
by the commuting identity and injectivity of `b`. Ambient invariance
therefore implies that `a` takes an orthogonal lift to an orthogonal
vector. Its image under `q` is prescribed by the commuting identity,
so uniqueness proves `orthogonalLift_equivariant`. Substitution into
the pullback definition proves `quotientForm_invariant`.

The actual-torus comparison uses `characterRealAut`, the published real
extension of inverse precomposition on actual characters. For an actual
morphism `f : A → T` and automorphisms `s` of `A` and `t` of `T`, the
commuting square is `f ≫ t.hom = s.hom ≫ f`. Composing with both inverses
gives `s.inv ≫ f = f ≫ t.inv`. Tensor induction and this identity prove
`restrict_characterRealAut` for actual real character restriction.
For split tori and a monomorphic underlying scheme map, the preceding
linear-algebra laws then give equivariance of the actual orthogonal lift
and invariance of the actual induced form whenever `t` preserves the
specified ambient form.

Finally, let `i : T → G` be an actual monomorphism into an actual group
scheme, and assume explicitly that its actual normalizer/centralizer
quotient has a `Fintype` instance. The published
`relativeWeylInvariantForm i hT` is the one ambient form used to define
`weylInducedCharacterForm` and `weylCharacterRestrictionLift` for every
specified monomorphism `A → T` of split tori. Symmetry, strict positivity
on nonzero vectors, and the exact `CompatibleCharacterForms` condition
follow from the previous construction.

For an actual normalizer point `n`, suppose a specified actual
automorphism `s` of `A` satisfies
`f ≫ (normalizingAut i n).hom = s.hom ≫ f`.
The ambient form is invariant under the quotient class of `n`.
The actual-torus comparison therefore proves
`weylInducedCharacterForm_normalizer_invariant`: the resulting
`characterRealAut s` preserves the induced local form in both variables.
The local form and the ambient form are constructed, rather than
independently chosen forms whose compatibility or positivity is assumed.

The field has arbitrary universe and characteristic. The full actual
real character spaces are used, including central directions and rank
zero. Actual splitness and both underlying monomorphisms are explicit
where needed, as is finiteness of the ambient quotient. No assertion is
made that an arbitrary ambient normalizer point preserves `A`, that an
unspecified local Weyl group has been compared to the ambient quotient,
or that any unspecified Levi split component or root set has been
identified. Unramified-character realization, intertwining convergence,
rationality and Plancherel remain separate obligations. The provenance
is the proved orthogonal construction, actual character functoriality
and the proved ambient finite-Weyl-sum invariance.
