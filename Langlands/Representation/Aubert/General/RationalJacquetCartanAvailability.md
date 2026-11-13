# Jacquet–Cartan data on `G(F)` from Bruhat–Tits availability and Levi compatibility

Module `Langlands.Representation.Aubert.General.RationalJacquetCartanAvailability`.

This module reduces the target statement
`Langlands.Aubert.General.RationalPointsJacquetCartanDatumStatement` (module
`Langlands.Representation.Aubert.General.JacquetCartanDatumStatement`) to fewer
inputs than the published conditional result `rationalPointsJacquetCartanDatum_of`
(module `Langlands.Representation.Aubert.General.RationalJacquetCartanDatum`).
That result assumes `JointSpecialCompactBasisExistenceStatement`. The theorems
here assume only:

- `BruhatTitsAvailabilityStatement`, which says that some corrected KP building
  assignment is valid. It is the conclusion of Kaletha–Prasad Theorem 9.2.7 and
  is unproved in the Library.
- The same-compact standard Levi compatibility
  `SpecialCompactStandardLeviCompatibility` at the special vertices of valid
  assignments. In the corollary this comes from `AvailableRenardCartanStatement`.

No simultaneous basis of compact open subgroups is used. The wall contraction
comes from `isCartanLatticeModel_rational_of_standard` (module
`Langlands.Representation.Aubert.General.RationalUniformizerContraction`). The
full special compact properties are not used either: only compactness of `K₀` is
needed, and the published `availableIwasawa` supplies it.

The construction is the one described in the Markdown of the target statement
and of `RationalJacquetCartanDatum`. It uses the standard parabolic, Levi and
unipotent subgroups of a maximal split torus with a generic cocharacter. It
also uses the Iwasawa and Cartan decompositions of D. Renard, *Représentations
des groupes réductifs p-adiques* (French version dated 9 July 2026, source id
`renard-2026-representations-groupes-reductifs-padiques`), Théorème V.5.1 (1),
(4), (5) (printed p. 122), and the wall contraction from V.5.2 (iii) (printed
p. 123).

## `Langlands.Aubert.General.rationalStandardParabolicSystemOfCompact`

```
def rationalStandardParabolicSystemOfCompact (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
    {j : Z ⟶ G} {s : S.toGrp ⟶ Z} {h : Function.Bijective (restrictionEvaluation s)}
    (hrep : (torusCentralizer i).IsRepresentedBy j) (hsj : s ≫ j = i)
    (hK : IsCompact ((D.specialCompactSubgroup x : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)))
    (hP : Langlands.BruhatTits.Iwasawa.ParabolicPointProductFamily i ν
      (D.specialCompactSubgroup x))
    (hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j)
    {F0 : Set (rationalPoints Z)} (hF0 : IsFiniteLatticeTransversal s F0) :
    StandardParabolicSystem.{u, u} (RationalPoint F G.X)
```

`F` is a nonarchimedean local field, `G` and `Z` are group schemes over `F`,
and `i : S → G` has `Mono i.hom.hom.left` and `IsAffineHom G.X.hom` as
instances. `G(F)` carries `rationalPointTopology F G.X`. Write
`K₀ = D.specialCompactSubgroup x`. The other inputs are:

- `G` is connected reductive, `i` is a maximal split torus and `ν` is generic;
- `j : Z → G` represents the torus centralizer, and `s ≫ j = i`;
- `K₀` is compact (`hK`) and has the parabolic product family (`hP`);
- `hcompat`: the same-`K₀` standard Levi compatibility;
- `F₀`: a finite lattice transversal of `Z(F)`.

From these the definition builds a `StandardParabolicSystem` on `G(F)`. Its
fields agree with those of the published `rationalStandardParabolicSystem`
except for `iwasawa`, `isCompact_cartanCompact` and `contraction`:

- `Δ = SimpleRoot i ν`, with the families `parabolic i ν`, `levi i ν` and
  `unipotent i ν`. The order and descent fields use the published theorems
  `standardParabolicOrder` and `standardCocharacter` directly; they are no
  longer hypotheses.
- `iwasawa`: `hasCompactCosetCover_parabolic_empty_of_products` with `hK` and
  the standard parabolic products in `hP`, i.e. `G = P_∅ K₀`.
- `cartanCompact I = K₀ ∩ M_I` and `cartanSet = rationalCartanSet i ν j s h F0`.
  `isCompact_cartanCompact` is `isCompact_inf_levi` with `hK`. The fields
  `cartanSet_subset` and `cartan` are `image_tildeC0Plus_subset_levi` and
  `exists_cartan_levi` with `hcompat`.
- `contraction`: the `hasWallContraction` consequence of
  `isCartanLatticeModel_rational_of_standard`. Finiteness of the simple roots
  comes from `finite_simpleRoot`, and the standard cocharacters of every `I`
  from `standardCocharacter`. The valuation identity is taken from the lattice
  part of `hcompat ∅`. `F0` is finite by `hF0`.

## `Langlands.Aubert.General.compactLeviData_of_valuationBuildingData`

```
theorem compactLeviData_of_valuationBuildingData (V : ValuationBuildingData G)
    (hx : ∃ x : V.Apartment, V.apartment.IsSpecialApartmentVertex x)
    (hI : ∀ ν, IsGenericCocharacter V.i ν → ∀ x, V.apartment.IsSpecialApartmentVertex x →
        ParabolicPointProductFamily V.i ν (V.apartment.specialCompactSubgroup x) ∧
          IsCompactOpenMaximal F (V.apartment.specialCompactSubgroup x))
    (hC : ∀ ν, IsGenericCocharacter V.i ν → ∀ x, V.apartment.IsSpecialApartmentVertex x →
        SpecialCompactStandardLeviCompatibility V.apartment x ν
          V.centralizer.s V.centralizer.bijective V.centralizer.j)
    (hi : IsMaximalSplitTorus i) (hS : V.S = S) (hVi : HEq V.i i)
    (ν : cocharacterLattice S) :
    IsGenericCocharacter i ν →
      ∃ D x Z j s, (torusCentralizer i).IsRepresentedBy j ∧ s ≫ j = i ∧
        ∃ h, ParabolicPointProductFamily i ν (D.specialCompactSubgroup x) ∧
          IsCompactOpenMaximal F (D.specialCompactSubgroup x) ∧
          SpecialCompactStandardLeviCompatibility D x ν s h j
```

(The signature is abbreviated; the binder types are those in the Lean source.)
Suppose the valuation building data `V` has a special vertex, and at every
special vertex and generic cocharacter of `V` the special compact subgroup has
the parabolic product family, is compact open maximal and satisfies the
standard Levi compatibility. Suppose also that the torus of `V` is the given
maximal split torus `i`. Then for every generic `ν` of `i` there are apartment
data, a vertex and centralizer data for `i` with these three properties. The
proof substitutes `V.S = S` and `V.i = i` and takes the special vertex from `hx`.

## `Langlands.Aubert.General.rationalPointsJacquetCartanDatum_of_validLeviCompatibility`

```
theorem rationalPointsJacquetCartanDatum_of_validLeviCompatibility
    (hAvailability : BruhatTitsAvailabilityStatement.{u})
    (hCompat : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
      (hG : IsConnectedReductive G),
      haveI : IsAffineHom G.X.hom := hG.isAffineHom
      ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid →
        let B := (𝔅.datum F G hG).base
        ∀ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν →
          ∀ x : B.Apartment, B.apartment.IsSpecialApartmentVertex x →
            SpecialCompactStandardLeviCompatibility B.apartment x ν
              B.centralizer.s B.centralizer.bijective B.centralizer.j) :
    RationalPointsJacquetCartanDatumStatement.{u}
```

Assume that some KP building assignment is valid, and that the standard Levi
compatibility holds at every special vertex and generic cocharacter of the base
data of every valid assignment. Then the rational points of every connected
reductive group over every nonarchimedean local field carry a Jacquet–Cartan
datum.

The proof runs as follows for given `F`, `G` and `hG`:

1. `exists_maximalSplitTorus_genericCocharacter` gives a maximal split torus
   `i` with a generic cocharacter `ν`.
2. `validAssignmentTorusRebasing` turns the valid assignment from
   `hAvailability` into a valid assignment `𝔅` whose base torus is `i`.
3. `𝔅` is available for `G`. The published `availableSpecialVertexExistence`
   gives a special vertex, and the published `availableIwasawa` gives the
   parabolic product family and compact open maximality at every special
   vertex. `hCompat` gives the Levi compatibility.
   `compactLeviData_of_valuationBuildingData` then produces the data for
   `(i, ν)`.
4. `exists_isFiniteLatticeTransversal` gives `F₀`. The system
   `rationalStandardParabolicSystemOfCompact` then yields the datum through
   `StandardParabolicSystem.nonempty_jacquetCartanDatum`.

## `Langlands.Aubert.General.rationalPointsJacquetCartanDatum_of_availability_of_renardCartan`

```
theorem rationalPointsJacquetCartanDatum_of_availability_of_renardCartan
    (hAvailability : BruhatTitsAvailabilityStatement.{u})
    (hCartan : AvailableRenardCartanStatement.{u}) :
    RationalPointsJacquetCartanDatumStatement.{u}
```

`BruhatTitsAvailabilityStatement` and `AvailableRenardCartanStatement` (module
`Langlands.Representation.Plancherel.AvailableRenardCartanStatement`) together
imply the target. A valid assignment is available for every group
(`KPBuildingAssignment.IsValid.isAvailableFor`), so the second component of
`AvailableRenardCartanStatement` supplies `hCompat`.

## Status

All four declarations compile and depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The target is still conditional. Besides
`BruhatTitsAvailabilityStatement`, it needs the Levi compatibility at valid
assignments, which is an unpublished draft result of Worker 4169
(`validSpecialCompactRenardCartanComparison`, task
`8c39faa0-2a70-4fc4-a027-914987aba924`). With that result, the target would
depend only on `BruhatTitsAvailabilityStatement`.
