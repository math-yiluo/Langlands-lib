# Stabilizers of irreducible classes of a normal subgroup

This internal module works with a topological group `G`, a normal subgroup
`N` and the Library's classes `OpenKernelIrreducibleClasses N` of
finite-dimensional irreducible complex representations of `N` with open
kernel. `G` acts on these classes by the published
`normalConjugationMulAction` (module
`Langlands.Weil.Representation.NormalConjugacyClasses`): `g • [A]` is the
class of `n ↦ A (g⁻¹ n g)`, the representative
`conjugateOpenKernelIrreducible N g A`.

## Definitions and facts

- `WildObj N` is the subtype of representations satisfying
  `OpenKernelIrreducibleProperty N`, with carriers in `Type uW`, and
  `wildClass A` is the class of such an object. `wildClass_eq_iff` says that
  two objects have the same class exactly when their representations are
  equivalent, and `smul_wildClass` identifies `g • wildClass A` with the class
  of the conjugate representative.
- `le_stabilizer`: the stabilizer of every class contains `N`. This is the
  published `openKernelClass_inner_smul`: an element of `N` conjugates a
  representation of `N` into an equivalent one.
- `conjugateEquiv`: if `θ` is a representation of a subgroup `H ⊇ N` whose
  restriction to `N` is equivalent to `A`, then the restriction of `θ` along
  the conjugated inclusion `n ↦ x n x⁻¹` (the Library's
  `Weil.InductionSemisimplicity.conjugateInclusion`) is equivalent to the
  conjugate representative of `x⁻¹ • [A]`, by the same linear map.
- `conjugatesDisjoint_of_stabilizer`: if `θ` and `θ'` are representations of
  the stabilizer `H` of `[A]` whose restrictions to `N` are both equivalent to
  `A`, then `ConjugatesDisjoint H N _ θ θ'` holds (module
  `Langlands.Representation.Clifford.Coinduction`). A nonzero intertwiner from
  a conjugate by `x ∉ H` would give a nonzero intertwiner between the
  irreducible representations `x⁻¹ • A` and `A`, hence an equivalence, and so
  `x⁻¹` and `x` would stabilize `[A]`.

These are the inputs for Mackey's criterion in the case of the inertia group
of a class; compare J.-P. Serre, *Linear Representations of Finite Groups*
(1977), registered as `serre-1977-linear-representations`, the proof of §8.2,
Proposition 25 (a) (printed p. 63), where the subgroup `G_i` is the stabilizer
of a character of the normal subgroup.
