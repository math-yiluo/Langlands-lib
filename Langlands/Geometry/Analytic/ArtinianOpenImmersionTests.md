# Artinian tests for affine open immersions

For a finite-type algebra over a field, a quotient by a positive power of a
maximal ideal is finite dimensional and local. Finiteness follows from the
finite residue field and the nilpotent kernel of the residue map. Every prime
of the quotient contracts to a prime containing the original maximal ideal.

Let `g : A →ₐ[K] B` be a map of finite-type algebras over a field, with `Spec g`
a monomorphism. For each maximal ideal `m` of `B`, its contraction `p` in `A` is
maximal by Zariski's lemma. For every positive `n`, `truncationMap g (p ^ n)`
is the canonical map from `A / p ^ n` to `B / (p ^ n)B`.

The scheme map of this quotient comparison is an affine, locally finite
type monomorphism over an Artinian base. It is quasi-finite and hence finite.
The corresponding ring map is a finite epimorphism, so it is surjective.
If all these comparison maps are injective, the first quotient identifies
`p B` with `m`. The higher quotient isomorphisms give flatness at `m` by
the adic completion comparison. Flatness at all maximal ideals gives
flatness of `Spec g`, and the flat, locally finitely presented monomorphism
is an open immersion.

This criterion combines the Library's affine quotient pullbacks and truncated
comparison for flatness with Mathlib's finite-monomorphism and open-immersion
criteria. It provides the algebraic step for reflecting open immersions using
finite Artinian tests.
