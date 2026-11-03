# Jacquet–Cartan data on the rational points of reductive groups

Module `Langlands.Representation.Aubert.General.RationalJacquetCartanDatum`.

This module derives the target statement
`Langlands.Aubert.General.RationalPointsJacquetCartanDatumStatement` (module
`Langlands.Representation.Aubert.General.JacquetCartanDatumStatement`) from three
published statements that the Library does not yet prove. It is therefore a
conditional result, not a proof of the target. The construction follows the
realization described in the Markdown of the target statement: the standard
parabolic, Levi and unipotent subgroups of a maximal split torus with a generic
cocharacter, the Iwasawa and Cartan decompositions of D. Renard,
*Représentations des groupes réductifs p-adiques* (French version dated 9 July
2026, source id `renard-2026-representations-groupes-reductifs-padiques`),
Théorème V.5.1 (1), (4), (5) (printed p. 122), and the wall contraction derived
from V.5.2 (iii) (printed p. 123).

The module has two declarations: the definition
`rationalStandardParabolicSystem`, which builds the `StandardParabolicSystem` of
`G(F)` from explicit data, and the theorem `rationalPointsJacquetCartanDatum_of`,
which obtains that data from the three statements.

## `Langlands.Aubert.General.rationalStandardParabolicSystem`

```
def rationalStandardParabolicSystem (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    (hstd : StandardCocharacterStatement.{u}) (hord : StandardParabolicOrderStatement.{u})
    (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
    {j : Z ⟶ G} {s : S.toGrp ⟶ Z} {h : Function.Bijective (restrictionEvaluation s)}
    (hrep : (torusCentralizer i).IsRepresentedBy j) (hsj : s ≫ j = i)
    (hsc : SpecialCompactProperties F i ν (D.specialCompactSubgroup x))
    (hP : Langlands.BruhatTits.Iwasawa.ParabolicPointProductFamily i ν
      (D.specialCompactSubgroup x))
    (hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j)
    (hbasis : SimultaneousStandardBasisAt i ν (D.specialCompactSubgroup x))
    {F0 : Set (rationalPoints Z)} (hF0 : IsFiniteLatticeTransversal s F0) :
    StandardParabolicSystem.{u, u} (RationalPoint F G.X)
```

Here `F` is a nonarchimedean local field, `G` and `Z` are group schemes over
`F`, `i : S → G` is a homomorphism from a commutative group scheme `S` with
`Mono i.hom.hom.left` and `IsAffineHom G.X.hom` as instances. `G(F)` carries the
rational-point topology `rationalPointTopology F G.X`. Write
`K₀ = D.specialCompactSubgroup x`.

The data are those produced by the published statement
`JointSpecialCompactBasisExistenceStatement` for a maximal split torus `i` with
a generic cocharacter `ν`. They are: apartment data `D` with a vertex `x`, the
special compact properties `hsc` of `K₀`, the Iwasawa product family `hP` at
`K₀`, the same-`K₀` standard Levi compatibility `hcompat`, the simultaneous
Renard V.5.2 basis `hbasis`, and a represented torus centralizer `j : Z → G`
with `s ≫ j = i`. The bijectivity proof `h` belongs to the same data. To these
it adds a finite lattice transversal `F₀ ⊆ Z(F)` (`hF0`). It also takes the
statements `hstd` and `hord`.

The system has the following fields:

- simple-root type `Δ = SimpleRoot i ν`, with classical decidable equality;
- `parabolic I`, `levi I`, `unipotent I`: the families `parabolic i ν`,
  `levi i ν` and `unipotent i ν` of
  `Langlands.Representation.Aubert.General.RationalPointFamily`;
- `parabolic_mono`: `parabolic_mono` with `hord`;
- `levi_mul_unipotent`: `exists_mul_of_mem_parabolic` with `hstd`;
- `levi_le_normalizer`: `RationalPointFamily.levi_le_normalizer`;
- `isClosed_levi`: `isClosed_levi_of_isNonarchimedeanLocalField`;
- `top`, `unipotent_top`: the index chosen from `exists_unipotent_eq_bot`, a
  finite set containing every simple root, with `unipotent i ν top = ⊥`;
- `unipotent_descent`: `exists_mul_of_mem_unipotent` with `hstd` and `hord`;
- `iwasawa`: `hasCompactCosetCover_parabolic_empty_of_specialCompactProperties`
  with `hsc` and `hP` (Renard V.5.1 (1), `G = P_∅ K₀`);
- `cartanCompact I = K₀ ∩ M_I`, compact by `isCompact_inf_levi` from the
  compactness of `K₀` in `hsc`, and contained in `M_I`;
- `cartanSet = rationalCartanSet i ν j s h F₀`, countable by
  `countable_image_tildeC0Plus` and contained in every `M_I` by
  `image_tildeC0Plus_subset_levi`;
- `cartan`: `exists_cartan_levi` (Renard V.5.1 (4), (5), covering part);
- `contraction`: `IsCartanLatticeModel.hasWallContraction` (module
  `Langlands.Representation.Aubert.General.CartanLatticeContraction`) applied to
  `isCartanLatticeModel_rational` (module
  `Langlands.Representation.Aubert.General.RationalCartanLatticeModel`). That
  lemma needs further inputs. The simple roots are finite (`finite_simpleRoot`).
  `hstd` gives a standard cocharacter for every set of simple roots. The
  uniformizer valuation formula
  `centralizerValuation s h (s(c(ϖ))) = 1 ⊗ c` is the first conjunct of the
  `DominantCentralizerLatticeConclusions` that `hcompat` gives at the empty set
  of simple roots. The remaining inputs are `hrep`, `hsj`, `hbasis` and the
  finiteness of `F₀`.

The definition is internal: `StandardParabolicSystem` is a Lean packaging (module
`Langlands.Representation.Aubert.General.JacquetCartanAssembly`), and this
definition fills it with the standard family of `G(F)` and Renard's Iwasawa and
Cartan data.

## `Langlands.Aubert.General.rationalPointsJacquetCartanDatum_of`

```
theorem rationalPointsJacquetCartanDatum_of
    (hjoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hstd : StandardCocharacterStatement.{u})
    (hord : StandardParabolicOrderStatement.{u}) :
    RationalPointsJacquetCartanDatumStatement.{u}
```

The three hypotheses are the published Prop-valued statements

- `Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisStatement`): for a
  maximal split torus `i : S → G` of a connected reductive group over a
  nonarchimedean local field and a generic cocharacter `ν`, there are apartment
  data `D`, a special vertex `x`, a represented torus centralizer `j : Z → G`
  with `s ≫ j = i`, and the bijectivity `h` of the restriction-evaluation map,
  such that `K₀ = D.specialCompactSubgroup x` has the special compact properties,
  the Iwasawa products, the same-`K₀` standard Levi compatibility and a
  simultaneous Renard V.5.2 basis;
- `Langlands.GroupScheme.StandardCocharacterStatement` (module
  `Langlands.GroupScheme.Rational.StandardCocharacterStatement`): standard
  cocharacters exist, and the standard subgroups agree with the dynamic
  subgroups of every standard cocharacter;
- `Langlands.GroupScheme.StandardParabolicOrderStatement` (module
  `Langlands.GroupScheme.Rational.StandardParabolicOrderStatement`): the
  standard parabolic, Levi and unipotent subgroups are monotone in the set of
  simple roots.

The conclusion is the target statement itself: for every nonarchimedean local
field `F` and every connected reductive `G` over `F`, the rational points
`G(F)` with the point topology carry a `JacquetCartanDatum` whose index and wall
types lie in the universe of `F`. Once the three statements are proved, applying
this theorem to their proofs proves the target.

### The proof

Fix `F` and `G`, and equip `G(F)` with the rational-point topology.

1. **Torus.** Choose a maximal split torus `i : S → G` with a generic
   cocharacter `ν` (`exists_maximalSplitTorus_genericCocharacter`).
2. **Joint witness.** Apply `hjoint` to obtain `D`, `x`, `Z`, `j`, `s`, `h`
   with `hrep`, `hsj`, `hsc`, `hP`, `hcompat` and `hbasis`; the other conjuncts
   are not used.
3. **Lattice transversal.** `exists_isFiniteLatticeTransversal` gives a finite
   lattice transversal `F₀` of `Z(F)` from `hcompat`.
4. **Conclusion.** `rationalStandardParabolicSystem` with these data, `hstd`
   and `hord` is a `StandardParabolicSystem` of `G(F)`, and
   `StandardParabolicSystem.nonempty_jacquetCartanDatum` turns it into a
   `JacquetCartanDatum`. Its index type is `Finset (SimpleRoot i ν)` and its
   wall types are subtypes of it, all in the universe of `F`.

The lemmas `exists_maximalSplitTorus_genericCocharacter`, `finite_simpleRoot`,
`exists_unipotent_eq_bot`, `parabolic_mono`, `exists_mul_of_mem_parabolic` and
`exists_mul_of_mem_unipotent` are in
`Langlands.Representation.Aubert.General.StandardFamilyStructure`. The Iwasawa and
Cartan lemmas `hasCompactCosetCover_parabolic_empty_of_specialCompactProperties`,
`isCompact_inf_levi`, `countable_image_tildeC0Plus`,
`image_tildeC0Plus_subset_levi`, `exists_isFiniteLatticeTransversal` and
`exists_cartan_levi` are in
`Langlands.Representation.Aubert.General.RationalIwasawaCartan`.

## Status

The theorem does not prove `RationalPointsJacquetCartanDatumStatement`: its
three hypotheses are published statements without proofs in the Library. The
definition `rationalStandardParabolicSystem` likewise assumes `hstd`, `hord` and
the joint special compact data as arguments.
