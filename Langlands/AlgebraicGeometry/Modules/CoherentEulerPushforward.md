# Actual coherent Euler polynomials under affine pushforward

This internal construction compares actual coefficient sheaves and their Euler
sequences. For schemes in an arbitrary common universe, a morphism `j : Y ⟶ X`,
an actual module sheaf `M` on `Y`, a line bundle `L` on `X`, and every natural
number `n`, `coherentTwistPushforwardIso` constructs the sheaf isomorphism

`(j_* M) ⊗ L^n ≅ j_* (M ⊗ (j^* L)^n)`.

There are no geometric hypotheses on `j` for this construction, and exponent
zero is included. The construction composes the actual tensor commutator,
the published line-bundle projection isomorphism applied to `L^n`, and the
published isomorphism identifying pullback of a tensor power with the power of
the pullback. All tensors and pushforwards are the actual scheme module functors.

`HasFiniteAffineSections.pushforward` proves that a finite morphism preserves
finite generation on every affine open. It requires no quasi-coherence
assumption. For an affine open `U` of `X`, its inverse image is affine and
`Γ(Y,j⁻¹U)` is finite over `Γ(X,U)`. By hypothesis, the coefficient sections are
finite over the former ring. Transitivity of finite generation applies to the
actual scalar restriction defining pushforward sections.

For a proper morphism `f : X ⟶ Spec K` over a field, an affine `j : Y ⟶ X`
with `j ≫ f` proper, a quasi-coherent `M`, and finite affine sections for both
`M` and `j_*M`, `coherentEulerSequence_pushforward` identifies their twisted
Euler sequences:

`coherentEulerSequence f (j_*M) L = coherentEulerSequence (j ≫ f) M (j^*L)`.

The finite-generation witnesses are suppressed only in this displayed formula.
Proper coherent cohomology supplies actual finite-cohomology witnesses for the
two twisted sheaves. The published affine-pushforward cohomology comparison
identifies the Euler characteristic of the twisted sheaf on `Y` with that of
its pushforward on `X`. The projection isomorphism above and isomorphism
invariance identify this latter characteristic with that of `(j_*M) ⊗ L^n`.
Casting the integer characteristics to rational numbers gives equality at every
natural `n`.

`coherentEulerPolynomial_pushforward` then identifies their coherent Euler
polynomials at any common natural truncation `d`, by applying the defining
finite Newton transform to the equal sequences. This equality requires no
support bound, no noetherianity, and no separatedness hypothesis beyond the
stated proper structure maps. It does not assert reconstruction of the sequence
without the support bound required by the existing evaluation theorem.

The `_finite_pushforward` corollaries supply finite affine sections internally
and infer properness of the composite for finite `j`. They apply in particular
to closed immersions. The quasi-coherence of the pushforward is supplied by the
published affine-pushforward closure theorem through a local instance in each
conclusion.

The provenance is internal: the construction and proofs derive from the
published actual tensor, pullback, line-bundle projection, coherent Euler
sequence, coherent Euler polynomial, and affine-pushforward Euler
characteristic modules, together with finite-morphism affine algebra. No
polynomiality, positivity, or support-comparison certificate is assumed. The
positive-dimensional ample leading-term argument remains separate.
