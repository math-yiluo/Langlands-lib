# Proof of the ordered fixer factorization in the unramified open cell

Module `Langlands.BruhatTits.IntegralModels.OrderedFixerFactorizationProof`.

## What is proved

`Langlands.BruhatTits.IntegralModels.unramifiedOrderedFixerFactorization` has type exactly
`UnramifiedOrderedFixerFactorizationStatement.{u}` (module
`Langlands.BruhatTits.IntegralModels.OrderedFixerFactorizationStatement`). No hypothesis is
added or changed. `lean_check` reports only `propext`, `Classical.choice` and `Quot.sound`.

For every non-archimedean local field `F`, affine group `G` over `K = inertiaFixedField F`,
supplied `C : MaximalUnramified.BuildingData F G` and zero datum `E` with
`(torusCentralizer C.i).IsRepresentedBy E.i`, generic cocharacter `ν`, injective complete
enumerations `aneg`, `apos` of the indivisible roots positive on `-ν` and on `ν`, and subsets
`Ω`, `Ω'` of the apartment, it proves
`OrderedFixerFactorization C E (TorusRootModelFamilyData.orderedIntegralIndex aneg apos) Ω Ω'`.
The proof does not use the hypotheses that `Ω'` is nonempty and affine bounded.

## The implemented proof

Helpers in the namespace `OrderedFixerFactorizationProof`:

- `list_prod_ofFn_eq`: for `h : Fin (nneg + (npos + 1)) → M` in a monoid,
  `(List.ofFn h).prod` is the product of the first `nneg` values, then the value at
  `Fin.natAdd nneg 0`, then the remaining `npos` values (`List.ofFn_add`, `List.ofFn_succ`).
- `orderedIntegralIndex_castAdd`, `orderedIntegralIndex_natAdd_zero`,
  `orderedIntegralIndex_natAdd_succ`: `orderedIntegralIndex aneg apos` takes the values
  `some (aneg j)`, `none` and `some (apos j)` on the three blocks (`simp` on `Fin.addCases` and
  `Fin.cases`).
- `exists_normalizer_of_mem_torusIwahori`: let `s ∈ E.torusIwahori`. Factor `E.i` through the
  centralizer datum of `C`
  (`SubgroupFunctor.IsRepresentedBy.factorHom` with `hrep.2.le`) as `cz` with
  `cz ≫ C.centralizer.j = E.i`. The point `z = cz(s)` lies in the character valuation kernel of
  `C.centralizer.Z`: `E.torusIwahori_le_integerCharacterValuationKernel` and
  `map_characterValuationKernel_le`. Then `tn = C.centralizer.toNormalizer z` has underlying
  point `E.i(s)`. It acts trivially on characters (`weylAction_centralizerToNormalizer`) and
  fixes every apartment point by V 6 (`C.isOmegaCompatible.smul_eq_self`).

Main argument. Let `h` have root slots `h j ∈ U_{a_j,Ω,0} ⊆ U_{a_j}(K)` and torus slot
`E.i(s)` with `s ∈ T(K)⁰`. Suppose the ordered product lies in
`E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω')`. Fix `x ∈ Ω'`. The product fixes
`C.apartmentMap x`. By `list_prod_ofFn_eq` it is `(∏ negative slots) · tn · (∏ positive slots)`.
The helper theorem
`KPApartmentData.mem_filtration_of_orderedProduct_mul_smul_apartmentMap_eq` (module
`Langlands.Geometry.Building.GenericOppositeUnipotentFixer`) applies to `C.apartment`. Its
inputs are the enumerations `fun j => (aneg j : characterLattice C.S)` and
`fun j => (apos j : characterLattice C.S)`, which are injective because `aneg`, `apos` are
injective and `Subtype.val` is injective, the given range equalities, and `t = tn`. It puts
every negative factor in `C.apartment.filtration x (aneg j) 0` and every positive factor in
`C.apartment.filtration x (apos j) 0`. Since `x ∈ Ω'` was arbitrary, `mem_rootFixer` gives
`h j ∈ C.rootFixer (a_j) Ω'` for every root slot. The torus slot condition is the same for `Ω`
and `Ω'`, so the hypothesis gives it. The final case split on the slot index uses
`Fin.addCases` and `Fin.cases`.

The mathematical content is in the helper module. There, an Iwasawa-fold induction on Coxeter
length, together with the fact that a `U(ν)`-orbit meets the apartment at most once, shows
the following without apartment axioms: if `u⁻ ∈ U(-ν)(K)`, `u⁺ ∈ U(ν)(K)` and `u⁻ u⁺` fixes
an apartment point, then `u⁻` and `u⁺` fix it. The published single-sign theorem
`mem_filtration_of_orderedProduct_smul_apartmentMap_eq` then places the individual factors.
See `Langlands/Geometry/Building/GenericOppositeUnipotentFixer.md`.

## Provenance

The target is the corrected display in the proof of Kaletha–Prasad, *Bruhat–Tits theory: a new
approach* (2023), Proposition 8.4.15 (printed p. 307 / PDF p. 338), as recorded in the
statement's Markdown. The implemented route is internal. It is described in the helper
module's Markdown, which relates its steps to Bruhat–Tits (1972), Proposition 7.3.3 and
Lemma 7.3.6.
