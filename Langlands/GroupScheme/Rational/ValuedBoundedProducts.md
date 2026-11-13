# Products of algebraically bounded sets over an arbitrary valued field

This module proves closure properties of KP algebraic boundedness
(`IsAlgebraicallyBounded`, KP Definition 2.2.1) over an arbitrary field `F` with a
valuative relation. It uses no topology, completeness or local compactness. The Library's
`IsAlgebraicallyBounded.mul`, `IsAlgebraicallyBounded.smul_set` and related lemmas in
`Langlands.BruhatTits.RationalPoints.BoundedSetOperations` assume a local field and argue by
compactness, so they do not apply over the maximal unramified extension. Source: Kaletha--Prasad, *Bruhat--Tits
Theory: A New Approach* (registered as `kaletha-prasad-2023-bruhat-tits-new-approach`),
Lemma 2.2.6, the "if" direction for products. The proof here goes through matrix
entries rather than KP's argument through the multiplication morphism. This is a derived
supporting result, not a new definition.

## Matrix representations (`Langlands.GroupScheme.MatrixRepresentation`)

Here `G` is a group scheme over `Spec F` with affine underlying scheme, and `ρ` is a
matrix representation of `G` with finite index type `n`.

- `exists_entry_regularFunction`: for each pair of indices `i j`, some global regular
  function `f` on `G` has value `ρ(x) i j` at every rational point `x`, and some `g` has
  value `ρ(x)⁻¹ i j`. These are the pullbacks under `ρ` of the general linear entry
  and inverse-entry coordinates.
- `inverseEntries_bounded_of_isAlgebraicallyBounded`: on an algebraically bounded set,
  every inverse-matrix entry of `ρ` is bounded by one nonzero constant. The analogous
  statement for entries is the existing Library lemma
  `MatrixRepresentation.hasBoundedRationalEntries_of_isAlgebraicallyBounded`.
- `matrix_mul_entries_bounded`: take two families `M p`, `N p` of `n × n` matrices over
  `F`, indexed by any type, each with uniformly bounded entries. Then the product
  family `M p * N p` has uniformly bounded entries. Each entry is a finite sum of products
  of bounded functions, and bounded functions form the subalgebra
  `boundedEvaluationSubalgebra`.
- `isAlgebraicallyBounded_mul`: let `ρ` be a closed embedding (`IsClosedSubgroup ρ`) and
  `S`, `T` algebraically bounded subsets of `G(F)`. Then `S * T` is algebraically
  bounded. The entries of `ρ(st)` and of `ρ(st)⁻¹ = ρ(t)⁻¹ρ(s)⁻¹` are bounded by
  `matrix_mul_entries_bounded`. The Library's `isAlgebraicallyBounded_of_entries_and_inverse`
  turns bounds on entries and inverse entries into boundedness of every regular function.

## Groups of finite type

Here `G` is a group scheme over `Spec F` with `IsAffineHom G.X.hom` and
`LocallyOfFiniteType G.X.hom`.

- `isAlgebraicallyBounded_mul_of_finiteType`: if `S` and `T` are algebraically bounded
  subsets of `G(F)`, so is `S * T`. A closed linear embedding exists by the Library
  theorem `affineLinearEmbeddingStatement` (Milne, Theorem 4.9 / Corollary 4.10), and
  then `isAlgebraicallyBounded_mul` applies.
- `isAlgebraicallyBounded_smul_set_of_finiteType`: every left translate `g • S` of a
  bounded set is bounded. It is contained in `{g} * S`, and singletons are bounded
  (`isAlgebraicallyBounded_singleton`).
- `isAlgebraicallyBounded_conj_of_finiteType`: every conjugate `{g} * S * {g⁻¹}` of a
  bounded set is bounded.
- `isAlgebraicallyBounded_range_orderedProduct_of_finiteType`: take finitely many
  subgroups `H 0, …, H (m-1)` of `G(F)`, each algebraically bounded. Then the range of
  their ordered product map `RelativeRoot.CentralExtension.orderedProduct` (the set
  of all products `h_0 h_1 ⋯ h_{m-1}` with `h_j ∈ H j`) is algebraically bounded. The
  proof is by induction on `m`. The empty product is `{1}`, and the product for `m + 1`
  lies in `H 0 * (range for the remaining m)`.
