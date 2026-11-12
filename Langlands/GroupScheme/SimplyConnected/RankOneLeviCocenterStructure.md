# The derived group of the standard Levi subgroup of a simple relative root

Authors: Worker 183. The construction is copied from the proof of
`rankOneLeviFactorDichotomy` by Worker 180.

The module `Langlands.GroupScheme.SimplyConnected.RankOneLeviCocenterStructure` proves one
theorem, `Langlands.GroupScheme.rankOneLeviFactor_derivedRetraction`, using only the standard
axioms.

## Statement

Let `k` be a field, `G` a simply connected group over `k` with affine structure morphism,
`i : S ⟶ G` a maximal split torus, `ν` a generic cocharacter, `j : M ⟶ G` a representative of
the dynamic centralizer of `ν`, `α` a simple relative root, `a : A ⟶ G` a rank-one Levi
factor for `α` (`IsRankOneLeviFactor i α a`), and `d : D ⟶ M` with `IsDerivedSubgroup d`.
Then there exist:

- a cocharacter `ζ` with `IsStandardCocharacter i ν {α} ζ`;
- `l : L ⟶ G` representing the dynamic centralizer of `ζ`, with `IsClosedSubgroup l` and
  `IsConnectedReductive L`;
- `jL : M ⟶ L` with `jL ≫ l = j`;
- `e : E ⟶ L` with `IsDerivedSubgroup e`;
- `aE : A ⟶ E` with `aE ≫ e ≫ l = a`, and `pA : E ⟶ A` with `aE ≫ pA = 𝟙 A`;
- the kernel condition: every point `y` of `E` (on any test scheme) with `y ≫ pA = 1` maps
  into the range of `d ≫ j`;
- `δ : D ⟶ E` with `δ ≫ e ≫ l = d ≫ j`.

## Implemented proof

The proof repeats steps 1–7 of the published proof of `rankOneLeviFactorDichotomy` (module
`SimplyConnected.RankOneLeviFactorDichotomyProof`), whose Lean proof is a single tactic block.
Only the final assembly is new.

1. The published `standardCocharacter` gives `ζ` and identifies `standardLevi i ν {α}` with the
   dynamic centralizer of `ζ`. That centralizer is in turn the common centralizer of all
   cocharacters orthogonal to `α` (`standardLevi_eq_cocharacterAnnihilatorCentralizer`).
   `l` is the affine representative `Dynamic.Affine.centralizerHom`; it is closed, and `L` is
   connected reductive by `dynamicCentralizerReductive`.
2. `derivedSubgroupRepresentability` gives `e : E ⟶ L`. Since `L` is the centralizer of a split
   subtorus, `splitTorusCentralizerDerivedSimplyConnected` makes `E` simply connected.
3. `A` lies in `L` (condition 6 of `IsRankOneLeviFactor`) and is perfect, so it factors as
   `aE : A ⟶ E`. Condition 7 makes its image normal in `E`.
4. `semisimpleNormalIsogenyComplement` gives a complement `κ : K ⟶ E` commuting with `A` such
   that multiplication `A ⊗ K ⟶ E` is a central isogeny. Simple connectedness of `E` makes it an
   isomorphism.
5. A rational point `n` of `A` normalizing `S` acts on `α` by `-α`.
6. Using `n`, every point of `K` commutes with every value of `2ν`, so `K` lies in `M`.
7. `K` is perfect, so it factors through `d` as `κD : K ⟶ D`. `D` maps to `E` by `δ`, with
   `δ ≫ e ≫ l = d ≫ j` (`mem_derivedSubgroup_comp`).

Assembly: `pA` is the published `commutingFactorRetraction aE κ hc`, and
`comp_commutingFactorRetraction` gives `aE ≫ pA = 𝟙 A`. For the kernel condition,
`comp_commutingFactorRetraction_eq_one_iff` writes a point `y` with `y ≫ pA = 1` as `n ≫ κ`.
Its image in `G` is `n ≫ κD ≫ d ≫ j`, by the factorizations of step 7.

## Relation to the literature

As in the dichotomy proof: Prasad–Raghunathan, *On the Kneser–Tits problem* (1985), proof of
Theorem A, printed p.110 (registered as `prasad-raghunathan-1985-kneser-tits`). The derived
group of the Levi subgroup of `α` is the product of the rank-one factor and anisotropic factors
contained in the minimal Levi. The complement comes from Milne, *Algebraic Groups* (2022),
Theorem 21.51, in the Library as `semisimpleNormalIsogenyComplement`.
