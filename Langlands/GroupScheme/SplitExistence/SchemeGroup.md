# The torus and the root groups as homomorphisms into `GL_n`

Module `Langlands.GroupScheme.SplitExistence.SchemeGroup`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). For Chevalley data `D` (module `ChevalleyData`)
and a field `k`, it turns the point-level formulas of `Points` into actual group-scheme
homomorphisms over `Spec k`. This follows the classical construction of a Chevalley group
inside `GL(V)`, where the torus acts on the weight basis through characters and the root
groups act by divided-power exponentials (Steinberg, *Lectures on Chevalley Groups*, §§2–3;
Milne, *Algebraic Groups* (2017), proof of Theorem 23.72).

## Declarations

- `torusHom_map f χ`, `x_map f j s`: extension of scalars along a ring map `f : A →+* B`
  commutes with the torus formula `χ ↦ diag(χ(wt c))` and the root formula `s ↦ x_j(s)`.
- `torusHom_injective`: over any commutative ring, `χ ↦ diag(χ(wt c))` is injective. Two
  characters that agree on all weights `wt c` agree on the subgroup they generate, which is
  `X` (field `closure_range_wt`).
- `GLk k`: the Library `GeneralLinear.groupScheme (Fin D.n)` over `Spec k`.
- `Tk k`: the Library diagonalizable group `Diagonalizable.groupScheme (CommRingCat.of k) X`.
  This is the split torus with character lattice `X`, since `X` is a lattice.
- `isTorsionFree_weight P`: the weight lattice of a root datum is torsion-free. If
  `r • x = r • y` with `r ≠ 0`, pairing with every coweight and cancelling `r` in `ℤ` gives
  equal functionals, so `x = y` by perfectness of the pairing.
- `isSplitTorus_Tk P`: for a root datum on a finitely generated `X`, the module `X` is free.
  A basis identifies `X` with `ℤ^I`, so `Tk k` is a split torus (Library
  `Diagonalizable.isSplitTorus`).
- `torusPointsEquiv k T`: the Library identification of the `T`-points of `Tk k` with group
  homomorphisms `Multiplicative X →* Γ(T, ⊤)ˣ`, via its corepresentation.
- `torusPointsHom k T`: on `T`-points, a character `χ` goes to the invertible matrix
  `D.torusHom χ`, through the Library identification `GeneralLinear.pointsEquiv` of the
  points of `GL_n` with `GL (Fin n) Γ(T, ⊤)`.
- `torusPointsHom_naturality`: compatibility with every morphism of test schemes. It follows
  from `torusHom_map` and naturality of the two points equivalences.
- `torusToGL k`: the homomorphism `Tk k ⟶ GLk k` obtained by the Library `homOfPoints` from
  these natural point maps.
- `pointsEquiv_torusToGL k T x`: on every test scheme `T`, the matrix of the image of a point
  `x` is `D.torusHom` of its character.
- `mono_torusToGL`, `isClosedSubgroup_torusToGL k hT`: by `torusHom_injective`, the torus
  homomorphism is a monomorphism on all test schemes. For a split torus (hypothesis `hT`),
  it is therefore a closed subgroup embedding, by the Library's
  `HomImage.isClosedSubgroup_of_mono` (a monic homomorphism from a smooth connected affine
  group is closed).
- `Gak k`: the additive group, the Library `VectorGroup.groupScheme (CommRingCat.of k) 1`.
- `gaCoord k T`: the coordinate of a `T`-point of `Gak k`, a global section of `T`, written
  multiplicatively.
- `rootPointsHom k j T`, `rootPointsHom_naturality`, `rootToGL k j`: the same construction for
  the root map `s ↦ D.x j s`. Naturality follows from `x_map` and
  `VectorGroup.coordinates_comp`. `pointsEquiv_rootToGL` records the matrix of the image of
  a point.

All statements hold on every test scheme over `Spec k`, including nonreduced ones. No
hypothesis on `k` is used.
