# Finite index and uniformizer realization of the split-component valuation image

Author: Worker 4160 (Task 4160, `1c86ad12-dbcb-464d-9590-4e553687ba3c`).
The reduction it applies was written by Worker 1503.

`Langlands.Plancherel.RenardCartan.splitComponentLattice` proves exactly the
published proposition
`Langlands.Plancherel.RenardCartan.SplitComponentLatticeStatement.{u}`
(module [`RenardLatticeComparisonStatement`](RenardLatticeComparisonStatement.md)),
at every universe `u`, with no added hypotheses.

## Statement

For every nonarchimedean local field `F : Type u` (with the Library's field,
`ValuativeRel`, topology and `IsNonarchimedeanLocalField` instances, of either
characteristic), every actual connected reductive group scheme `Z` over
`Spec F`, every actual commutative group scheme `T` and every
`s : T.toGrp ⟶ Z` with `IsSplitComponent s`:

1. `(splitValuationImage s).FiniteIndex`: the subgroup of
   `rationalCharacterValuationImage Z` formed by the valuations of the actual
   points `s(t)`, `t ∈ T(F)`, has finite index in the actual valuation image
   of `Z(F)`;
2. `Set.BijOn (rationalCharacterValuation Z).rangeRestrict (C0 T s)
   (splitValuationImage s)`: the valuation maps the uniformizer subgroup
   `C0 T s` (cocharacters of `T` evaluated at the Library's order-one
   uniformizer, then mapped by `s`) injectively onto that same subgroup.

## Implemented proof

The Lean proof is the single application

`splitComponentLatticeStatement_of_characterRestriction Langlands.GroupScheme.characterRestriction`.

- `Langlands.GroupScheme.characterRestriction`, from
  [`CharacterRestrictionProof`](../../GroupScheme/Rational/CharacterRestrictionProof.md),
  is the published unconditional proof of
  `Langlands.GroupScheme.CharacterRestrictionStatement.{u}`: over every field,
  for every split component `i : A.toGrp ⟶ G` of a connected reductive group,
  `characterRestrict i` is injective and its range has finite index. Here it is
  used for `F`, `Z` and `s`.
- `splitComponentLatticeStatement_of_characterRestriction`, from
  [`SplitComponentLatticeBridge`](SplitComponentLatticeBridge.md), has type
  `CharacterRestrictionStatement.{u} → SplitComponentLatticeStatement.{u}`.
  For each `F`, `Z`, `T`, `s` it applies `splitComponentLattice_of_injective`
  to the injectivity conjunct of the character restriction statement.

The bridge module's Markdown gives the details. In outline, it realizes the
integral lattice information by actual field points as follows.

- For a cocharacter `c` of the split torus `T` and a rational character `χ`
  of `Z`, the `χ`-coordinate of the valuation of `s(c(ϖ))` is the pairing
  `⟨r(χ), c⟩` of the restricted character `r(χ) = characterRestrict s χ` with
  `c` (`rationalCharacterValuation_map_uniformizerSection`).
- Surjectivity of `C0 T s` onto `splitValuationImage s`: every `t ∈ T(F)` is
  a uniformizer point `c(ϖ)` times an element of the norm kernel of `T`
  (`CocharacterUniformizer.isUniformizerLatticeSection`), so `s(t)` and
  `s(c(ϖ))` have the same valuation.
- Injectivity on `C0 T s`: the range of `r` has finite index `N`, so `N • α`
  is a restricted character for every `α ∈ X^*(T)`. Equal valuations of
  `s(c(ϖ))` and `s(d(ϖ))` give `N⟨α, c⟩ = N⟨α, d⟩`, hence `c = d` by the
  perfect pairing of characters and cocharacters of the split torus.
- Finite index: for `y` in the actual valuation image, injectivity of `r`
  lets one define the integer functional `α ↦ y(r⁻¹(N • α))` on `X^*(T)`.
  The perfect pairing represents it by a cocharacter `c`, and `s(c(ϖ))` has
  valuation `y^N`. So `y^N ∈ splitValuationImage s` for every `y`. The actual
  valuation image is a finitely generated abelian group, because `X^*(Z)_F` is
  finitely generated (published `rationalCharacterLattice`). Hence
  `CharacterRestrictionFiniteIndex.finiteIndex_of_nsmul_mem` gives finite
  index.

No integral image realization, finite index of the valuation image,
rational-point surjectivity of a central isogeny, or replacement lattice is
assumed: the only external input is the proved character restriction
statement.

## Relation to the literature

The statement corresponds to Renard, *Représentations des groupes réductifs
p-adiques*, V.2.5–V.2.6 (printed pages 107–108), as recorded in the
statement's Markdown. The implemented route goes through injectivity and
finite index of restriction of rational characters to the split component
(Renard V.2.6, Waldspurger I.1), proved in the Library over arbitrary fields.

## Scope

This proves only `SplitComponentLatticeStatement`. It does not prove the
kernel statement `SplitComponentKernelStatement` or the full representative
statement `FullLatticeRepresentativeStatement`. It also does not show that the
centralizer of a chosen maximal split torus is connected reductive with that
torus as its split component.
