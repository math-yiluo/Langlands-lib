# Standard Hecke scalars determine spherical irreducible representations (proof)

`Langlands.Unramified.sphericalHeckeSpectrumDetermination` proves
`SphericalHeckeSpectrumDeterminationStatement.{uF, uV, uW}` (module
`Langlands.Representation.Unramified.SphericalHeckeSpectrumDeterminationStatement`).
Two actual irreducible admissible spherical objects `A` and `B` of `GL_{r+1}(F)`,
with independent carrier universes, are equivalent when every standard
double-coset operator `T_i` (`0 ≤ i ≤ r + 1`) acts on both nonzero
`GL_{r+1}(O_F)`-fixed spaces by `standardHeckeScalar F s i` for one common
`s : Eigenvalues (r + 1)`.

## Proof

The theorem applies `sphericalHeckeSpectrumDetermination_of` (module
`Langlands.Representation.Unramified.SphericalHeckeDetermination`) to
`sphericalHeckeGeneration.{uF}`, the published proof of
`SphericalHeckeGenerationStatement` (module
`Langlands.Representation.Unramified.SphericalHeckeGenerationProof`).

That module carries the argument. By generation, every element `f` of the
spherical corner satisfies `T_n^m f ∈ Algebra.adjoin ℂ {T_0, …, T_n}` for some `m`.
Elements of the adjoined subalgebra act on both fixed spaces by one common scalar,
and `T_n` acts by the nonzero scalar `standardHeckeScalar F s n`. So every corner
element acts on `A^K` and `B^K` by a common scalar. Then for nonzero fixed vectors
`a` and `b`, a corner element kills `a` exactly when it kills `b`. The annihilator
form of Bernstein–Zelevinsky 2.10(b),
`Langlands.Hecke.nonempty_equiv_of_cornerAction_eq_zero_iff` (module
`Langlands.Representation.Hecke.CornerDetermination`), gives the equivalence.

## Provenance

Borel, *Automorphic L-functions* (1979), 7.1–7.2, printed pages 38–39 (source
`borel-1979-automorphic-l-functions`): the class-1 representation is determined by
its spherical Hecke character. Gross, *On the Satake isomorphism* (1998),
section 6 (source `gross-1998-satake-isomorphism`), states this through the Satake
isomorphism. This proof avoids the Satake transform; it uses the generation
statement and the corner annihilator comparison instead.
