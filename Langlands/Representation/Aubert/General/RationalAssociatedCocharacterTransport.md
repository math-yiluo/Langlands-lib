# Actual associated-opposite cocharacter transport

This is a derived supporting unit for the rational rank-one self-association
argument. It proves cocharacter and point identities; it makes no assertion
about scalar characters, admissibility, Jacquet modules or self-association.

`isStandardCocharacter_associatedOpposite_of_pointRootSigns` uses the supplied
actual point Coxeter system, its root-length and positive-simple-reflection
comparisons, minimality and associated-subset laws. For any standard cocharacter
`ζ` of a finite simple-root subset `J` and every specified normalizer lift `n` of
`longestRep cs J`, the cocharacter
`associatedOppositeCocharacter i ((normalizerEquiv i hN).symm n) ζ` is standard
for `associatedSubset cs J`. The remaining explicit inputs are a split torus,
a relative root system and the generic original cocharacter. Finiteness and
monomorphism assumptions are the displayed Lean assumptions. No full scheme
Coxeter realization is assumed.

`associatedOppositeStandardCocharacter` constructs this cocharacter together
with its standardness certificate. Its domain is the subtype of standard
cocharacters for `J`, and its codomain is the subtype of standard cocharacters
for `associatedSubset cs J`. It uses the same explicit inputs and the chosen
normalizer lift as the theorem. Its underlying cocharacter is the literal
associated-opposite cocharacter above, without any further choice.

The proof first identifies the actual character image of the associated subset
with the original root set. Pairing invariance gives zero on the associated
subset. A positive simple root outside that subset has negative longest image,
by the supplied length comparison. Its negative is a positive relative root.
If that root belonged to the additive closure of the original selected roots,
its inverse image would have nonnegative pairing with the original generic
cocharacter, contradicting positivity of the simple root. The published standard
cocharacter closure criterion then gives the required strict positive pairing.
This adapts the argument in
`GroupScheme.isStandardCocharacter_associatedOppositeCocharacter` to the supplied
point-root comparisons of the consumer target.

Over a nonarchimedean local field, `uniformizerPowers_cocharacterAut` says that
evaluating the actual normalizer action on a cocharacter at the common chosen
uniformizer gives literal conjugation of its original point. It evaluates the
published scheme identity `groupHom_cocharacterAut_comp`, exposes the underlying
scheme composites, and applies `comp_innerIso_hom` at the identity test scheme.
The normalization and uniformizer are exactly those of `uniformizerPowers` and
`CocharacterUniformizer.latticeSection`.

`uniformizerPowers_associatedOpposite_conj` specializes this identity to the
associated-opposite cocharacter. Literal conjugation by the same normalizer
point gives the inverse original uniformizer point. The proof uses the defining
inverse linear action and the inverse law of the uniformizer homomorphism.
These two point identities require neither a split-torus hypothesis nor a
Coxeter system.

All content is an internal deduction from the cited published Lean definitions
and transport lemmas. No additional external mathematical assertion is used.
