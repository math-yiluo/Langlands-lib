# Intrinsic transport on actual finite and local determinant images

This internal construction extends `FiniteLocalDeterminantTwist`. The number
field `F : Type u` has arbitrary universe, every natural rank `n` is allowed,
coefficients are complex, and `χ` is a finite-order continuous Hecke character.
Both source and target are the existing actual invariant subspaces of
automorphic forms, with multiplication `Mχ f(a) = χ(det a) f(a)`.

In both `FiniteRealization` and `LocalRealization`,
`determinantTwistSubrepresentationOrderIso` constructs an order equivalence
between all subrepresentations of the source action and all
subrepresentations of its actual multiplied-image action. Its forward map
is submodule image under the existing multiplication equivalence. Its inverse
is submodule preimage under that same equivalence. The displayed
`determinantTwistSubrepresentationOrderIso_toSubmodule` identity identifies
the forward map explicitly.

The private scalar-covariance helper proves that these image and preimage
submodules are invariant. For the forward direction it uses
`R(g) Mχ = χ(det g) Mχ R(g)` and closure under complex scalar multiplication.
For the inverse direction it multiplies this equation by the inverse unit
`χ(det g)⁻¹`. The existing submodule map/comap order equivalence supplies
the two inverse laws and the order equivalence. Thus invariance is proved
in both directions, without an extra preservation hypothesis.
`determinantTwist_isIrreducible_iff` follows by transporting simple order
through this constructed equivalence. In the local case this concerns
irreducibility under the specified completed-local group; in the finite
case it concerns the whole finite adelic action.

`determinantTwist_hasCentralCharacter_iff` proves, for any continuous
Hecke character `ω`, that the actual image has embedded central character
`χ^n * ω` exactly when the source has embedded central character `ω`.
The forward construction is also exposed as
`determinantTwist_hasCentralCharacter`. These are the existing conditions
on all embedded adelic functions, including for a local realization;
they are not a claim about central characters of arbitrary equivalent
embeddings or solely about the local group center.

The central-character forward proof applies the existing ambient multiplier
formula to each source vector. Reflection applies the inverse-character
formula to a multiplied vector, cancels `(χ⁻¹)^n * χ^n`, and uses the actual
inverse multiplier law. The image membership argument uses the actual
submodule image; it does not assume a target realization.

With the existing explicit `CompactSpace (AdeleQuotient F)` premise,
`determinantTwist_isCuspidal_iff` preserves and reflects the existing
embedded cuspidality condition in both namespaces. It applies the published
constant-term multiplier formula and its cuspidality biconditional to
each actual image vector. This is vanishing of the existing normalized
maximal-block constant terms, not the local Jacquet-vanishing definition of
supercuspidality.

Provenance is internal: these order equivalences and condition transports
are derived from the existing actual multiplier covariance, actual
finite/local image construction, ambient central-character formula and
constant-term formula, together with Mathlib's submodule order equivalence
and simple-order characterization of representation irreducibility. No
new original-literature identification is claimed. No occurrence,
admissibility, tensor factorization, spectral or weak-association
compatibility is asserted.
