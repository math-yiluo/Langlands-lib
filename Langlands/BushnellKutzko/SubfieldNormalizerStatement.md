# Subfields normalizing a hereditary order (Bushnell–Kutzko 1993, (1.2.1), p. 24)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
Proposition (1.2.1), printed pp. 24–25 (statement p. 24, proof pp. 24–25; PDF pp. 36–37; PDF
page = printed page + 12).

`SubfieldNormalizerStatement : Prop` is an unproved statement. A later `lean.proof@1` task will
prove it. It uses `Langlands.BushnellKutzko.LatticeChain`, `...UnitFiltration` and
`...SubfieldIntegers`.

## Quantifiers

For every nonarchimedean local field `F : Type u`, every `F`-vector space `V : Type v`, every
field `E : Type w` with `[Algebra F E] [Module E V] [IsScalarTower F E V]`, and every
`𝔬_F`-lattice chain `𝓛 : LatticeChain 𝒪[F] F V`. The three universes are independent.

`E` stands for BK93's subfield `E/F` of `A = End_F(V)` acting on `V` through the inclusion
`E → A` (see `SubfieldIntegers.md`). Since `𝓛` exists, `V` is nonzero and finite-dimensional
over `F`. So `E → A` (`subfieldEmbedding`) is injective, `E` is isomorphic to a subfield of `A`
containing `F`, and `E/F` is finite. Every subfield of `A` containing `F`, including `F[β]`
when it is a field, arises this way. The ring `𝔬_E = subfieldIntegers F E` is the integral
closure of `𝔬_F` in `E`. The ideal `𝔭_E = subfieldMaximalIdeal F E` is its Jacobson radical,
which is the maximal ideal of the discrete valuation ring `𝔬_E`.

## Statement

The following are equivalent.

- (i) **`E^× ⊆ 𝔎(𝔄)`**: `subfieldUnits F E V a ∈ 𝓛.stabilizer` for every `a ∈ E^×`, where
  `𝔎(𝔄) = 𝓛.stabilizer` and `subfieldUnits` is the map `E^× → G`.
- (ii) **Every `L_i` is an `𝔬_E`-module, and `𝔭_E L_i = L_{i+e'}` for some integer `e'` and
  all `i`.** Formally:
  - for every `i`, every `a ∈ 𝔬_E` and every `w ∈ L_i`, `a • w ∈ L_i`; and
  - there is `e' : ℤ` such that for every `i` the `𝒪[F]`-span of the vectors `a • w`, with
    `a ∈ 𝔭_E` and `w ∈ L_i`, equals `L_{i+e'}`.

## Comparison with BK93

BK93's (ii) reads "each `L_i` is an `𝔬_E`-lattice and there is an integer `e'` such that
`𝔭_E L_i = L_{i+e'}` for all `i` (i.e. `𝓛` is an `𝔬_E`-lattice chain in the `E`-vector space
`V`)". The formal version differs in two ways, neither of which changes the meaning.

- **"`𝔬_E`-module" instead of "`𝔬_E`-lattice".** An `𝔬_E`-stable `𝔬_F`-lattice is
  automatically an `𝔬_E`-lattice: it is finitely generated over `𝔬_F ⊆ 𝔬_E`, and its `F`-span,
  hence its `E`-span, is `V`.
- **`𝔭_E L_i` as an `𝒪[F]`-span.** When `L_i` is `𝔬_E`-stable, the `𝒪[F]`-span of
  `{a w : a ∈ 𝔭_E, w ∈ L_i}` is already an `𝔬_E`-submodule, because `𝔭_E` is an ideal of
  `𝔬_E`. It is then the product `𝔭_E L_i` in BK93's sense.

BK93's condition (i) is written `E^× ⊆ 𝔎(𝔄)` ("i.e. `E` normalises `𝔄`"). The formal (i) is
the literal inclusion, through the embedding `E^× → G`.

This statement does not build the `𝔬_E`-lattice chain that (ii) describes as an object of type
`LatticeChain 𝔬_E E V`. `SubfieldOrderStatement` asserts that it exists, under (i).
