# The split group attached to Chevalley data

Module `Langlands.GroupScheme.SplitExistence.Assembly`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). It assembles the properties of a Chevalley group
proved in the other modules, following Milne, *Algebraic groups*, Thm. 23.72.

## Declarations

- `ChevGroup.isConnectedReductive` (`J` finite, `P` reduced): **every Chevalley group `G` for
  `D` is connected reductive over `k`** in the Library's sense (`IsConnectedReductive`). It is
  smooth, affine and connected (fields of a stage, module `Generation`). Its base change to the
  algebraic closure has trivial unipotent radical (`hasTrivialUnipotentRadical`, module
  `Reductive`).
- `exists_split_of_chevalleyData k D` (`J` finite, `X` finitely generated, `P` reduced): for
  Chevalley data `D` on a base `b` of `P`, there are a connected reductive group `G` over `k`,
  a commutative group scheme `T`, and a homomorphism `i : T ⟶ G` such that:
  - `T` is a split torus;
  - `i` is a maximal torus;
  - some root datum `Q` on the character and cocharacter lattices of `T` satisfies
    `IsRootDatumOf i Q` and is isomorphic to `P` as a root pairing.

  This is the body of the Library's `SplitReductiveExistenceStatement`. Take a Chevalley group
  (`nonempty_chevGroup`), `T = D(X)` (`isSplitTorus_Tk`), `i = t` (`isMaximalTorus`, module
  `Maximal`), and `Q = chevDatum k P` (`isRootDatumOf` and `chevDatumEquiv`, module
  `RootDatumOf`). `X` is free because it is finitely generated and torsion-free
  (`isTorsionFree_weight`).
