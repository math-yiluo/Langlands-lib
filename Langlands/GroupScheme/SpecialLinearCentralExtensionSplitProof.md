# Proof that central extensions of `SL₂` by separated commutative groups split uniquely

Worker 65, with Worker 794.

`Langlands.GroupScheme.specialLinearCentralExtensionSplit` proves the published proposition
`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement.{u}` exactly, in every
universe `u`, with no added hypothesis. The statement's Lean/Markdown pair is unchanged. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

Source: Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014, Proposition 4.3.1 (due to Gabber), proof pp. 126–131.
It is registered as `conrad-2014-reductive-group-schemes`. The implemented proof follows
Conrad's construction of the section. It replaces his schematic density arguments by
fppf-local computations with units, except in one step (commutativity of `D′`), where a
relative density argument by Worker 794 is used. Its uniqueness argument differs from Conrad's:
it uses the Library's relative fppf perfectness of `SL₂`.

## Declarations in this module

Namespace `Langlands.GroupScheme.SL2CentralExtension`:

- `postcomp q T : (T ⟶ G.X) →* (T ⟶ H.X)`: composition with a homomorphism of group schemes
  `q : G ⟶ H`, as a homomorphism of point groups.
- `toExt E z q hz hker hlift : Ext S` turns the data of the target statement into the
  point-level structure `Ext` of the helper module `Setup`. Its components are:
  - `E` is the middle term.
  - `Q T` is `q` on `T`-points followed by `slEquiv T`, the identification of `T`-points of
    `SL₂` with determinant-one matrices over `Γ(T, 𝒪_T)` from `Points`. `Q_nat` is
    `slEquiv_naturality`.
  - `central`: if `Q e = 1`, then `e ≫ q = 1`. Exactness puts `e` in the range of `z`, and
    centrality of `z` makes `e` commute with every point.
  - `lift`: the fppf cover of hypothesis 4 of the statement, read through `Loc.of_cover`
    (module `Local`), gives fppf-local lifts of every matrix.
  - `sep`: matrices that agree fppf-locally are equal, by `Loc.ext` applied to the
    corresponding points of `SL₂`.
- `Ext.sigma_slEquiv_nat`: the homomorphisms `sigma hD T` of `Cell`, composed with `slEquiv`,
  are natural in `T`.
- `Ext.section_ hD : sl2 S ⟶ X.E`: these homomorphisms on points assemble to a homomorphism
  of group schemes by the Library's `homOfPoints` (`Langlands.GroupScheme.Multiplicative`).
  `Ext.Q_section`: `Q (x ≫ section_) = slEquiv x` for every point `x` of `SL₂`, by
  `comp_homOfPoints` and `Q_sigma`.

Namespace `Langlands.GroupScheme`:

- `specialLinearCentralExtensionSplit : SpecialLinearCentralExtensionSplitStatement.{u}`.

## Route of the main theorem

Fix `S`, a separated commutative group scheme `Z`, the group scheme `E`, and `z`, `q` with
the four hypotheses of the statement. Let `X = toExt E z q hz hker hlift`.

1. **Kernel factorization.** `hi`: a point `e` of `E` with `Q e = 1` factors as `c ≫ z`, by
   injectivity of `slEquiv` and exactness (`SubgroupFunctor.mem_range`).
2. **Commutativity of `D′`.** `hD : X.DComm` is `dComm_of_separated` (module `DComm`). It
   uses `hi`, the monomorphism hypothesis on `z` and separatedness of `Z`. This is the only use
   of separatedness. `DComm` builds from the commutators of lifts of diagonal matrices a natural
   bimultiplicative pairing of units with values in `Z`. Worker 794's `UnitPairing.eq_one`
   shows that such a pairing into a separated commutative group scheme is trivial.
3. **Existence.** `s = X.section_ hD`. The point-level section `sigma` of `Cell` is Conrad's
   section `y′(a) h′(t) x′(b)` on the open cell. It is translated fppf-locally into the cell by
   `x(r)` and glued. Its ingredients, in order, are:
   - `Unipotent`: lifts of matrices in one root group commute;
   - `Splitting`: the homomorphic lifts `x′`, `y′` of the root groups;
   - `Torus`: `h′`, and Conrad's relation (4.3.1) under `DComm`;
   - `Cell`: the gluing and the multiplicativity of `sigma`.
   `Q_section` gives `slEquiv (x ≫ s ≫ q) = slEquiv x` for every point `x`. Hence `s ≫ q = 𝟙`
   by the Library's `hom_ext_points` and injectivity of `slEquiv`.
4. **Uniqueness.** Worker 794's `binarySpecialLinear_section_unique` (module `Uniqueness`)
   shows that any two sections of `q` are equal. It uses only centrality of `z` and the
   kernel hypothesis. Two sections differ by a central homomorphism, which kills commutators.
   By the Library's relative fppf perfectness of `SL₂`, every point of `SL₂` is fppf-locally a
   product of commutators. Conrad instead shows directly that every homomorphism `SL₂ → Z` is
   trivial.

The conclusion `∃! s, s ≫ q = 𝟙 (sl2 S)` follows. Here `sl2 S` (module `Points`) and Worker
794's `binarySpecialLinear S` are by definition the statement's
`(GroupScheme.baseChange (Gm.toSpecZ S)).obj (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of (ULift.{u} ℤ)))`.

## Helper modules

All under `Langlands/GroupScheme/SL2CentralExtension/`, each with its own Markdown file.

By Worker 65 (part of this candidate):

- `Local`: fppf-local truth of properties of points (`Loc`), gluing and descent of equalities.
- `Covers`: fppf covers from nowhere degenerate polynomials (local unit values and roots).
- `Matrices`: matrix identities in `SL₂` over a commutative ring.
- `Points`: `sl2 S` and `slEquiv`.
- `Setup`: the structure `Ext`, commutators of local lifts.
- `Unipotent`, `Splitting`, `Torus`, `Cell`: the existence construction described above.
- `DComm`: commutativity of `D′` for separated kernels.

By Worker 794 (published separately; imported, not part of this candidate): `Density`,
`TorsionDensity`, `UnitPairing` and `Uniqueness`.
