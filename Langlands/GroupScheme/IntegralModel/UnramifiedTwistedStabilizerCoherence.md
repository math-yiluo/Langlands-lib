# Coherence for actual unramified twisted stabilizer models

This internal construction specializes `InnerSemilinearCoherence` and
`UnramifiedTwistedStabilizer` to the actual inertia integers of a
nonarchimedean local field. All coefficient types and schemes have arbitrary
common universe `u`; the finite cover index has type `Type`.

Let `F` be the local field, `K = inertiaFixedField F` its actual inertia fixed
field, and `R = fixedFieldIntegers F`. Let `G` be an affine group scheme over
`F`, `B` supplied building data for its specified scalar extension to `K`, and
`A` supplied semilinear apartment data. The actual rational points `c σ`
satisfy

`c (σ * τ) = c σ * rationalConjugate F K G σ (c τ)`.

The point `y` is fixed by every associated twisted building permutation.
The supplied smooth integral model `P` over `R` has integral-point image
exactly `B.oneStabilizer y`, the full character-valuation-kernel point
stabilizer. This hypothesis retains the full stabilizer rather than identifying
it with a neutral parahoric.

The theorem `Descent.FiniteUnramified.fixedIntegerBaseAut_mul` proves the
actual scheme-map composition identity

`fixedIntegerBaseAut F (σ * τ) =
  fixedIntegerBaseAut F σ ≫ fixedIntegerBaseAut F τ`.

The proof uses contravariance of `Spec` and equality of the restricted ring
homomorphisms. After taking underlying elements of `R`, the remaining identity
is the defining composition law of field automorphisms.

For every coefficient automorphism, `twistedStabilizerModelIso` already gives
the integral extension of coefficient comparison followed by inner conjugation
by `c σ`. The theorem `twistedStabilizerModelIso_tower` proves their integral
tower law, including the canonical iterated-pullback comparison:

`comparison ≪≫ twist(σ * τ) =
  baseChange(fixedIntegerBaseAut F σ)(twist(τ)) ≪≫ twist(σ)`.

Its proof applies `semilinear_tower_of_generic` to these actual integral maps.
The integer-map composition theorem, the coefficient-map composition theorem,
and the three actual generic compatibility squares supply its integral and
generic comparison data. The generic tower law is
`innerGaloisDescentIso_tower`, specialized using the displayed cocycle identity.
Generic rigidity then identifies the integral maps.
The helper `twistedStabilizerModelIso_tower_of_eq` transports this equality to
any index `ρ` with a specified equality `ρ = σ * τ` and a specified integral
base-map composition proof.

For a supplied map `p : Spec R ⟶ S`, assume a finite family of maps `q i`
to its actual overlap. Their first projections are the identity, their second
projections are `fixedIntegerBaseAut F (σ i)`, and their coproduct
`Sigma.desc q` is an isomorphism. The first-projection isomorphism instances
are explicit. A supplied multiplication index `m` satisfies
`σ (m i j) = σ i * σ j`.

The definition `datumOfTwistedStabilizerModel` applies
`SemilinearComponents.datumOfSemilinear` to this cover and the proved integral
tower laws. Its output is an actual `Descent.Datum p P.group`, consisting of
an overlap group-scheme isomorphism with its triple-overlap cocycle.
The theorem `pullIso_datumOfTwistedStabilizerModel` identifies its pullback
along every normalized `q i` with `semilinearComponent` of the corresponding
constructed integral twist. That component uses the inverse twist to orient
the overlap map from the first projection to the second.

The supplied smooth model, its exact full-stabilizer identification, and the
finite normalized overlap cover remain premises. In particular, no existence
of such a finite cover for the entire maximal-unramified extension is claimed.
Effective descent, the finite-field quotient, Frobenius compatibility, and the
chamber witnesses remain separate obligations of the statement this module
serves.
