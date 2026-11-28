# Discrete infinitesimal characters at a compact open level

`TwistedLeviDiscreteSupportFixedLevelStatement` uses the cyclic field-extension
hypotheses, Levi product topology and arbitrary Haar measures of
`TwistedLeviDiscretePaleyWienerStatement`. For a block shape `B`, write
`M_B = B.Levi E = ∏ᵢ GL_{Bᵢ}(E)` with the entrywise action `leviAut σ B`.
In Rogawski's setting one can view `M_B` as the group of `F`-points of the
product of the restrictions of scalars from `E` to `F`. The finite-order
automorphism preserves its standard minimal parabolic and all standard block
parabolics.

## Discreteness and infinitesimal character

`IsLeviSigmaDiscrete` asks for an irreducible admissible representation and a
`σ`-intertwining equivalence whose twisted character has nonzero class modulo
`leviProperInducedSpan`. This is the distribution formulation of the
discreteness condition in Rogawski §9. The twisted character vanishes on the
classes with cyclically permuted inequivalent constituents from Rogawski §2,
and twisted characters of inequivalent `σ`-stable irreducibles are linearly
independent. By Schur's lemma, any other intertwining equivalence rescales
the character by a nonzero scalar. The `l`-th power of the intertwiner is a
nonzero scalar as well, so rescaling gives an extension to the cyclic
semidirect product with the same nonvanishing criterion.

`HasLeviSigmaDiscreteSupport` includes the discrete representations directly.
It also includes a representation `π` when `π` and some discrete `ρ` are both
subquotients of the unnormalized smooth induction from a common irreducible
cuspidal representation of `M_C`, where `C.parabolic E ≤ B.parabolic E`.
The predicate `CuspidalSupport.IsLeviCuspidal` requires admissibility and
vanishing of the proper standard Jacquet modules, as in
Bernstein–Zelevinsky §2.4. The relative parabolic and inflation map are
`relParabolic` and `relProjection`. Each
subquotient is given by a surjective intertwiner from a subrepresentation of
the induction. For irreducibles this common datum expresses equality of
infinitesimal characters, by the description in Rogawski §10 and the cuspidal
induction comparison of Bernstein–Zelevinsky §2.9.

Writing `δ_P` for the parabolic modulus in the normalized covariance convention
of Rogawski §3, normalized induction of `Ξ` is unnormalized induction of
`δ_P^(1/2) ⊗ Ξ`. Conversely, unnormalized induction of `Ξ` is normalized
induction of `δ_P^(-1/2) ⊗ Ξ`. These twists are smooth characters on the Levi
and preserve irreducibility and cuspidality. The half modulus is invariant
under `σ`, since `σ` preserves the parabolic and conjugates the Levi actions
on its unipotent radical. Conjugate automorphisms scale Haar measure by the
same factor. The same change of inducing data therefore applies to twisted
induction and to the proper-induced span.

`leviDiscreteSupportSpan` takes the complex span of the twisted characters of
all irreducible admissible `σ`-pairs whose underlying representations satisfy
`HasLeviSigmaDiscreteSupport`. This is the distribution space corresponding
to the span used for descent and interpolation in the proof of Rogawski
Proposition 11.2. The field universes and representation-carrier universe are
independent. With fields in `Type u` and `Type v`, the target, the discrete
witness, and the inducing data for the common induction and for the
proper-induced span all have carriers in `Type z`. The induced function model
has carrier in `Type (max v z)`.

## Fixed-level finiteness

For each compact open subgroup `K` of `M_B`, the statement gives a finite set
of irreducible admissible `σ`-stable representatives with nonzero `K`-fixed
vectors. Every irreducible admissible `σ`-stable representation with
`K`-fixed vectors and discrete infinitesimal character is isomorphic to a
twist of one of these representatives. `IsUnramifiedTwistOf` requires the
twisting character of `M_B` to be unramified and invariant under `σ`.

Rogawski's Proposition 10.1 gives finitely many orbits of discrete
infinitesimal characters in each Bernstein component under this group of
invariant unramified characters. Lemma 11.1 limits the components meeting a
fixed compact open subgroup to a finite set. Each chosen infinitesimal
character has finitely many irreducibles in its fiber, since one cuspidal
induction realizes the fiber and has finite length. Twisting commutes with
induction after restriction of the character to the inducing Levi. The
invariance of the twist preserves `σ`-stability and its triviality on `K`
preserves the space of `K`-fixed vectors. Thus the fibers give a finite
cover by representation orbits with representatives at the prescribed level.

## Sources

- J. D. Rogawski, *Trace Paley–Wiener theorem in the twisted case*,
  Trans. Amer. Math. Soc. 309 (1988), 215–229. See §§1–6 (printed
  pp. 216–219), §§9–10 and Proposition 10.1 (pp. 223–224), Lemma 11.1(a)
  and the proof of Proposition 11.2 (pp. 228–229). Literature ID
  `rogawski-1988-twisted-trace-paley-wiener`, SHA-256
  `86fbe930fc1db80a3a0f279db5d83af85b7e37dc7e041d813ebc9f5fdcb7c274`.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
  reductive p-adic groups I*, Ann. Sci. Éc. Norm. Supér. (4) 10 (1977),
  441–472. See §§2.4–2.5 and 2.8–2.9 (printed pp. 446–448). Literature ID
  `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
