# Realized dominant characters span the full character space

This internal prerequisite for the corrected reduction argument concerns a supplied
split pinning of an actual affine connected reductive group over any field.
`realizedDominantCharacters` consists of actual integral torus characters that
are both dominant and realized by normalized covariant coordinates, in the sense
of the published `IsRealizedWeight`. The realizing functions are left covariant
for the negative Borel subgroup, right invariant under the positive unipotent
subgroup, and have counit one. These are algebraic statements over the original
field; algebraic closure, semisimplicity and simple connectedness are not assumed.

The module proves that the quotient of the full integral character lattice by
the integral span of these characters is finite, and that their rational span
is the full rational character space. Central-character directions are included.
This is the spanning input used after obtaining two-sided dominant-character
bounds in Godement's reduction argument. The module does not prove adelic height
estimates, compact overlap, or the final compactness theorem.

The implemented proof first applies the published simple-dual construction to
the flipped based integral root pairing. Summing the resulting characters gives
an integral character strictly positive on every simple coroot. For any character
`lam`, an explicitly bounded integral multiple of this character makes both
`lam` plus that multiple and the multiple itself dominant. Thus every integral
character is a difference of two dominant characters. This also covers a root
system with empty index and all characters orthogonal to the coroots.

The published `exists_pos_nsmul_isRealizedWeight` gives positive realized
multiples of each of the two dominant characters, without changing the field.
Multiplying the two positive integers puts a positive multiple of `lam` into the
integral span of `realizedDominantCharacters`. The quotient is therefore torsion;
finite generation of the actual split-torus character lattice makes it finite.
The rational-span result maps the integral span into the rationalization and
divides by the nonzero integer, then uses tensor induction.

The root-pairing decomposition and the two elementary span consequences are
internal derived results. Their provenance is the Cartan-adjugate simple-dual
proof in `Reductive.DominantMultipleRootData`, positive-multiple realization in
`Rational.DominantHighestWeightProof`, and the finitely generated torsion abelian
group theorem in Mathlib. The surrounding reduction-theory motivation is
Godement, *Domaines fondamentaux des groupes arithmétiques*, Bourbaki exposé 257,
§10, Lemma 2, printed pp. 217–218; the argument formalized here is the explicit
algebraic spanning step, not its analytic estimates.
