# The simultaneous basis at every special vertex of valid corrected KP data

`Langlands.BruhatTits.SpecialCompact.availableSimultaneousStandardBasis` proves
exactly `AvailableSimultaneousStandardBasisStatement.{u}` (module
`Langlands.BruhatTits.SpecialCompact.AvailableBasisStatement`) for an arbitrary
universe `u`. This is the target of Task 5310
(`8d4643b8-dcf9-476e-a86f-04b62b8d738f`).

The theorem covers every nonarchimedean local field `F` in universe `u`, every
connected reductive group scheme `G` over `F`, and every `KPBuildingAssignment`
`𝔅` with `𝔅.IsValid`. Write `D := (𝔅.datum F G hG).base`. For every generic
cocharacter `ν` of `D.S` and every special apartment vertex `x`, the theorem
gives the three conjuncts of the target. All three are about the same datum,
torus, cocharacter, vertex and geometric compact stabilizer
`D.apartment.specialCompactSubgroup x`:

1. `SpecialCompactProperties F D.i ν (D.apartment.specialCompactSubgroup x)`;
2. `SpecialLeviInheritance F D.isMaximalSplitTorus ν D.apartment x`;
3. `SimultaneousStandardBasisAt D.i ν (D.apartment.specialCompactSubgroup x)`.

The only building premise is `𝔅.IsValid`. The proof adds no other premise: no
split, quasi-split, tame or residue-characteristic condition, no centralizer
filtration, and no unproved proposition. In particular it does not use
`CentralizerFiltrationDoubleRootExistenceStatement`. The proof uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The proof introduces the data of the statement. It installs the instance
`IsAffineHom G.X.hom` from `hG.isAffineHom`, the same instance the statement
installs with `haveI`. It then unfolds the `let D := …` binder with
`dsimp only`. Each conjunct is then one published theorem.

- **Conjuncts 1 and 2.** The apartment of `D` is Ω-compatible with the
  centralizer datum of `D`: this is the structure field `D.isOmegaCompatible`.
  The published theorems
  `availableSpecialCompactProperties_of_omegaCompatibleApartment` and
  `availableSpecialLeviInheritance_of_omegaCompatibleApartment`, from
  `Langlands.BruhatTits.SpecialCompact.CompatibleApartmentProperties`, are
  applied to
  `hG, 𝔅, h𝔅, D.i, D.isMaximalSplitTorus, D.centralizer, D.apartment,
  D.isOmegaCompatible, ν, hν, x, hx`. They give conjuncts 1 and 2 exactly.
  Their own proofs get boundedness, compactness, maximality and Weyl
  representatives from `availableCompactCore_of_omegaCompatibleApartment`. They
  get the factorization `K0 ∩ P_J = (K0 ∩ M_J)(K0 ∩ U_J)` from
  `hasParabolicFactorization_of_maximal_compact_levis`, and the Levi
  inheritance from the restricted Levi apartment and its special vertex.

- **Conjunct 3.** `KPBuildingAssignment.IsValid.isAvailableFor`
  (`Langlands.Geometry.Building.FullValidity.Assignment`) turns `h𝔅` into
  `𝔅.IsAvailableFor F G hG`. The published theorem
  `CongruenceGL.available_simultaneousStandardBasisAt`, from
  `Langlands.BruhatTits.SpecialCompact.CongruenceBasis.Assembly`, is applied
  to `𝔅, hG, h𝔅.isAvailableFor, ν, hν, x, hx`. It gives
  `SimultaneousStandardBasisAt D.i ν (D.apartment.specialCompactSubgroup x)`
  exactly. Its proof writes `specialCompactSubgroup x` as the integral points
  of the KP full model at `x` (`exists_specialVertexModel`). It takes the
  congruence subgroups of that model as the compact open normal subgroups,
  and proves their Iwahori decomposition and weak contraction for every
  standard parabolic. Its paired Markdown and helper modules describe that
  construction.

The three terms are combined into the target's conjunction with an anonymous
constructor.

## Provenance

The statement formalizes Renard, *Représentations des groupes réductifs
p-adiques*, V.5.1 and V.5.2(i)–(iv), on valid corrected KP data. Its Markdown
gives the details. This proof is an internal composition of published Library
theorems. Its route for conjunct 3 uses the congruence tower of an integral
model, not Renard's own argument. The conjunct-3 theorem and its helper modules
are by Worker 55 (Task 4169). Worker 55 also wrote this assembly; Worker 5310
earlier found the conjunct-1 and conjunct-2 lemmas.
