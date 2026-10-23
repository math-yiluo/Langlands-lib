# Finite local actions on actual automorphic forms

For a number field `K : Type u`, any natural rank `n`, and a finite place `v`,
`automorphicLocalRightAction K n v` is the complex representation of the actual
group `GL_n(K_v)` on the existing space `AutomorphicForms K n`. It composes
`automorphicFiniteRightAction` with `FiniteAdelicGL.localInclusion`. The latter
inserts the local matrix and its inverse at `v` and the identity matrix at every
other finite place. The action-type abbreviations only name these representation
types; they introduce no alternate carrier or scalar structure.

The action is smooth. The proof applies the existing continuous-pullback theorem:
an open subgroup fixing a form in the finite adelic action pulls back along the
continuous local inclusion to an open subgroup fixing it locally. No topology
on the complex representation space is needed.

The underlying continuous function satisfies precisely

\[
 (R_v(g)f)(x)
   = f\bigl(x\,\operatorname{ofFinite}(\operatorname{localInclusion}_v(g))\bigr).
\]

There is no inverse in this right-translation formula. Actions at distinct finite
places commute, because the actual inserted matrices commute and the finite
adelic action is a monoid homomorphism into complex linear endomorphisms. This
does not assert commutativity at a single place.

`mem_automorphicLocalFixedVectors` identifies local fixed-vector membership with
invariance of the actual continuous function under all locally inserted elements
of the given subgroup. Injectivity of `automorphicToContinuous` proves the
reverse implication. A vector fixed by the global standard integral subgroup is
fixed by every local integral subgroup; the proof uses the exact preimage
identity from `LocalFactor`. No converse or density argument is claimed here.

For every ambient subrepresentation `S` of the actual continuous right action,
`restrictedAutomorphicLocalRightAction` constructs the same local restriction on
`RestrictedAutomorphicForms K n S`. Smoothness, the function formula and
distinct-place commutation hold on this space as well.
`restrictedAutomorphicLocalInclusion` is the existing inclusion into all forms,
now bundled as an injective local intertwiner. The named specializations give
the actions on forms with specified central character, on cusp forms, and on
cusp forms with specified central character. The cuspidal specializations retain
the existing `[CompactSpace (AdeleQuotient K)]` parameter of their carriers. Their
character convention and constant terms are unchanged from `CuspidalForms`.

This is an internal construction from `Forms`, `CuspidalForms`,
`FiniteAdelicGL.LocalFactor`, and `Smooth.Transfer.PullbackProof`. Its proofs
are composition, the published smooth pullback argument, injectivity of the
existing function realization, and the actual local insertion identities. No
additional external-literature theorem is asserted. Rank zero is allowed.

These are restrictions of whole form spaces to local groups. They are not
irreducible local components of an automorphic representation. The module
asserts neither admissibility nor finite length, and does not construct a
restricted tensor factorization or an isomorphism class of local constituents.
