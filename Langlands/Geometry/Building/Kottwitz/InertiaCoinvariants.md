# Inertia coinvariants and their residual Galois action

This internal construction supplies the Galois modules used in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Chapter 11, especially §11.1,
Construction 11.3.1, Definition 11.3.2 and Lemma 11.5.1 (printed pp. 420–430,
PDF pp. 451–461).

For a tower of fields `k ⊆ K ⊆ E` with `K/k` normal,
`relativeInertia k K E` is the kernel of the actual restriction
`Aut_k(E) → Aut_k(K)`. If `E/k` is also normal, restriction is surjective and
`residualGaloisEquiv` is its first-isomorphism-theorem identification
`Aut_k(E)/relativeInertia ≃ Aut_k(K)`.

For an integral representation `ρ` of `Aut_k(E)`, `inertiaCoinvariants`
is Mathlib's quotient by the integral span of the elements `ρ(σ)x − x`
for `σ` in this kernel. `inertiaProjection` is the quotient map.
`inertiaGammaRepresentation` descends the original action and transports
it along `residualGaloisEquiv`; consequently it is an action of the actual
group `Aut_k(K)`. The implemented `inertiaGammaRepresentation_restrict`
law follows by the inverse-equivalence identity and the definition of the
action on quotient classes. In the local-field application, `k = F`,
`E = F^sep` and `K = UnramifiedClosure F`, so the kernel is precisely
inertia and the residual group is `Γ = Gal(K/F)`.

`inertiaInvariants` is the fixed submodule for this action.
`invariantTorsion` is the ordinary torsion subgroup of that fixed group,
with `Multiplicative` only changing the notation for the group law.
It identifies `(A_tor)^Γ` as a subgroup of `A^Γ`, since an element of a
subgroup has finite order exactly when its image does. No invariants of
`A/A_tor` are used in this definition.

For a commutative group scheme `T/k`, `geometricCocharacters` uses the
Library's actual cocharacters of `T_E`. `torusInertiaCoinvariants` and
`torusGammaRepresentation` specialize the constructions above to the
Library's Galois representation on these cocharacters. The construction
itself does not require `T` to be a torus.

These are concrete quotient and action definitions, with no chosen
Kottwitz homomorphism or asserted kernel. Their provenance is internal:
they assemble the published lattice action with Mathlib's coinvariant
and quotient-action constructions. This pair does not state or prove
Kottwitz existence or any of the four principal targets.
