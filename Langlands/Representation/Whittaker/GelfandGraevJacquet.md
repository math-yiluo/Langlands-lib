# The Jacquet module of the Gelfand–Graev representation (assembly)

Draft by Worker 1832 for task `d7c75f29-8641-4f6e-9a08-aaa69f1db69c`. This module reduces
`RankinSelberg.SupercuspidalCompleteness.GelfandGraevJacquetStatement` to the identification of
the open orbit piece, `GelfandGraevOpenPieceStatement` (module
`GelfandGraevJacquetOpenStatement`). It also proves two small auxiliary facts about the unipotent
radical of a standard block parabolic and about smooth characters.

## Setting

`F` is a `p`-adic field with its canonical topology, `G = GL_(n+1)(F)`, `N` is the upper
unipotent subgroup, `B` is a block shape of `n + 1` and `P = B.parabolic F.Carrier` is the upper
block parabolic with Levi `M = B.Levi F.Carrier` and unipotent radical
`U = B.unipotentRadical F.Carrier`. `ψ` is a unitary additive character and `ψ_N` is the
Gelfand–Graev character `gelfandGraevCharacterRepresentation ψ n` of `N`.

## Results

- `unipotentRadical_val_mem_upperUnipotent`: over any commutative ring, every element of the
  unipotent radical of a standard block parabolic is an upper unitriangular matrix, that is, it
  lies in `upperUnipotent n R`.
- `unipotentRadical_compactContainment`: over a `p`-adic field with its canonical topology,
  every compact subset of `U` lies in a compact open subgroup of `U`.
- `isSmooth_characterRepresentation_of_isOpen_ker`: a character `θ : H →* ℂˣ` of a topological
  group whose kernel is open defines a smooth one-dimensional representation
  `characterRepresentation θ`.
- `gelfandGraevJacquet_of_openPiece`: `GelfandGraevOpenPieceStatement` implies
  `GelfandGraevJacquetStatement`. That is, if for every `p`, `F`, `ψ`, `n` and `B` the normalized
  Jacquet module of the open orbit piece is equivalent to `leviGelfandGraev B ψ.complex`, then for
  every such data `T.normalizedJacquet B (gelfandGraev ψ n)` is equivalent, as a representation
  of `M`, to `leviGelfandGraev B ψ.complex`.

## Proofs

- `unipotentRadical_val_mem_upperUnipotent`: write the row and column indices as
  `B.index i a` and `B.index j b`. Below the diagonal, either the column block `j` comes before
  the row block `i`, where the entry vanishes because `g ∈ P`; or `i = j` and `b < a`, where the
  entry is the identity entry `0` because `g ∈ U` (`B.mem_unipotentRadical_iff`). The case `i < j` cannot
  occur below the diagonal by `BlockShape.index_lt_index_of_block_lt`. Diagonal entries are `1`
  by the same characterization of `U`.
- `unipotentRadical_compactContainment`: the inclusion `ι : U → N` of the previous result is a
  continuous homomorphism. For compact `C ⊆ U`, the Library result
  `upperUnipotentCompactContainment` gives a compact open subgroup `K` of `N` containing
  `ι(C)`. Its preimage `ι⁻¹(K)` is an open subgroup of `U` containing `C`. It is compact because
  it is the preimage of the compact set `K ⊆ GL_(n+1)(F)` under the closed embedding
  `U → P → GL_(n+1)(F)` (`B.isClosed_unipotentRadical`, `B.isClosed_parabolic`).
- `isSmooth_characterRepresentation_of_isOpen_ker`: every vector is fixed by the open subgroup
  `ker θ`.
- `gelfandGraevJacquet_of_openPiece`:
  1. `ψ_N` is smooth: the standard character is continuous, so its kernel is open
     (`isOpen_ker_of_continuous_complex_character`).
  2. `gelfandGraevOrbitData` (module `GelfandGraevJacquetOrbits`) gives an ordering `s` of the
     `m` double cosets `N \ G / P` and an index `j` whose representative is the block-reversal
     matrix `w = B.reverseMatrix F.Carrier`. The piece of index `i` belongs to the double coset
     `N r_i⁻¹ P` of its representative `r_i`, so the piece of `j` is that of the open double coset
     `N w⁻¹ P`. Every other index `i` has a witness `x` in the
     stabilizer with `x ∈ U` and `ψ_N(stabilizerToInducing x) ≠ 1`.
  3. The restriction of `c-Ind_N^G ψ_N` to `P` carries the support filtration of `s`
     (`OrderedDoubleCosets.supportFiltration`). Packaged as an `ObjectRepFiltration`, its graded
     pieces are equivalent to the Mackey pieces `c-Ind_{H_i}^P (ψ_N ∘ stabilizerToInducing)` by
     `Geometric.closedSubgroupMackeyFiltration`. Here `H_i = orbitStabilizer N P r_i`, and
     `N` and `P` are closed.
  4. For `i ≠ j`, the witness `x` acts on the inducing character by the scalar
     `ψ_N(stabilizerToInducing x) ≠ 1`. So the `U`-coinvariants of the Mackey piece vanish by
     `subsingleton_coinvariants_compactInduced_of_scalar` (module
     `GelfandGraevJacquetVanishing`), using the compact containment above. The vanishing
     transfers to the graded piece through the equivalence
     (`subsingleton_coinvariants_of_equiv`).
  5. The restriction of the ambient representation to `U` is smooth, and every finite subset of
     `U` lies in a compact open subgroup. So `coinvariantsFiltrationEquiv` (module
     `GelfandGraevJacquetCollapse`) identifies the normalized Jacquet action of the ambient
     representation with that of the graded piece `j`. The action is over the subgroup `⊤` of
     `P` with the modulus `B.topModulus (T.leviModulus B)`.
  6. `normalizedEquivOfModulus` carries the equivalence of step 3 for `j` to the normalized
     Jacquet actions. Composing with `B.leviToTop` (`representationEquivComp`) turns both steps
     into equivalences of representations of `M`. By definition, the source is
     `T.normalizedJacquet B (gelfandGraev ψ n)` and the target is `parabolicNormalizedJacquet T B`
     of the Mackey piece `j`.
  7. The representative of `j` equals `B.reverseMatrix F.Carrier`. After substituting it, the
     hypothesis `GelfandGraevOpenPieceStatement` identifies this piece with
     `leviGelfandGraev B ψ.complex`.

## Provenance

The computation follows the classical one: the Mackey (Bruhat) filtration of `c-Ind_N^G ψ`
restricted to `P`, vanishing of the Jacquet module on every non-open double coset because
`ψ` is nontrivial on `U` there, and identification of the open piece. See Bernstein–Zelevinsky's
geometric lemma and Bushnell–Henniart's treatment of Whittaker models. The reduction to
`GelfandGraevOpenPieceStatement`, the compact containment for `U` and the smoothness lemma are
internal. The Library only provides finite containment for `U`
(`Parabolic.unipotentFiniteContainment`), so the compact version is derived here from the
upper unipotent one.
