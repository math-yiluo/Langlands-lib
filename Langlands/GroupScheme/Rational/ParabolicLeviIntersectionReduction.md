# Levi intersections along a common maximal split torus from the dynamic description

This internal reduction proves the published
`RepresentedParabolicLeviIntersectionStatement` from two separately owned
open propositions:

- `ParabolicDynamicStatement`: every parabolic subgroup of a connected
  reductive group is a dynamic parabolic;
- `DynamicCentralizerReductiveStatement`: dynamic centralizers in a
  connected reductive group are connected reductive.

It does not prove either proposition, so it is not an unconditional proof of
`RepresentedParabolicLeviIntersectionStatement`.

## Universal reduction

`RepresentedParabolicLeviIntersectionFromDynamicStatement` is the
Prop-valued implication

`ParabolicDynamicStatement.{u} → DynamicCentralizerReductiveStatement.{u} →
RepresentedParabolicLeviIntersectionStatement.{u}`.

All three propositions use the same universe `u`.
`representedParabolicLeviIntersection_of_dynamic` proves the implication. It
introduces the data of the target unchanged and applies
`RepresentedParabolicLeviIntersection.exists_leviIntersection_of_commonMaximalSplitTorus`.
It does not use the target's multiplication hypothesis `_hmulQ` on `Q`.
No unproved proposition is used other than the two premises.

## Main theorem

`RepresentedParabolicLeviIntersection.exists_leviIntersection_of_commonMaximalSplitTorus`
takes `hPD`, `hDCR` and the target's data: a connected reductive `G` over a
field `k`, a parabolic `p : P ⟶ G` with rational Levi subgroup `l : M ⟶ P`,
and a parabolic `q : Q ⟶ G` with rational Levi subgroup `lQ : L ⟶ Q` and
geometric unipotent radical `rQ : U ⟶ Q`. It also takes a maximal split
torus `i : T.toGrp ⟶ G` with factorizations `tM ≫ l ≫ p = i` and
`tL ≫ lQ ≫ q = i`. Its conclusion is the target's conclusion together with a
factorization `t ≫ l' ≫ p' ≫ l ≫ p = i` of the torus through `M'`. The
wrapper discards that last factorization. The proof proceeds in these steps:

1. `dynamicGeometricUnipotentRadical_of_centralizer hDCR` gives the dynamic
   geometric-radical statement. `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi`
   then gives cocharacters `ψP` and `ψQ` of `G` with
   `range (l ≫ p) = Z_G(ψP)`, `range q = P_G(ψQ)` and
   `range (lQ ≫ q) = Z_G(ψQ)`.
2. `T` lies in both centralizers, because it factors through `M` and through
   `L`. The helper `exists_factor_of_range_le_centralizer` uses
   `Dynamic.commute_cocharacter_of_mem_centralizer` and
   `IsMaximalSplitTorus.exists_factor_of_commute`. It factors both
   cocharacters through `T` as `α ≫ i = ψP` and `β ≫ i = ψQ`.
3. `l ≫ p` represents `Z_G(α ≫ i)`. `Dynamic.intersectionCocharacter i α β`
   gives a cocharacter `χM` of `M` lifting `β ≫ i`.
   `Dynamic.intersection_dynamic_eq_comap` identifies `P_M(χM)`, `Z_M(χM)`
   and `U_M(χM)` with the preimages under `l ≫ p` of `P_G(ψQ)`, `Z_G(ψQ)`
   and `U_G(ψQ)`.
4. `Dynamic.affineDecompositionModel χM` supplies closed models `P'`, `M'`
   and `N'` of these dynamic subgroups of the affine group `M`. It also
   supplies compatible inclusions and an isomorphic multiplication.
5. The three structural properties are proved as follows:
   - `P'` is parabolic in `M` by `hPD` applied to the connected reductive
     group `M`.
   - `N'` is a geometric unipotent radical by the dynamic geometric-radical
     statement, upgraded by
     `IsGeometricUnipotentRadical.leviSubgroup_of_unipotentFieldExtension`
     with the proved `unipotentFieldExtensionStatement`.
   - `M'` is a rational Levi subgroup by `hDCR`, which makes it connected
     reductive, together with the model's closed inclusion and its
     decomposition.
6. The helper `range_comp_eq_inf_of_range_eq_comap` turns each preimage
   identity into an equality `range (_ ≫ l ≫ p) = range (l ≫ p) ⊓ _`.
   `Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer`
   identifies `range (rQ ≫ q)` with `U_G(ψQ)`. This uses that `L` is
   connected reductive and `rQ` is a geometric unipotent radical.
7. `i` lands in `range (l ≫ p) ⊓ range (lQ ≫ q)`, which `M'` represents.
   `IsRepresentedBy.factorHom` therefore gives the factorization `t`.

The equalities are equalities of subgroup functors of `G` on every
`k`-scheme, so they identify scheme-theoretic intersections, not only
rational points.

## Elementary helpers

- `range_comp_eq_map`: the range of a composite is the image of the range
  of its first factor.
- `range_comp_le`: the range of a composite lies in the range of its last
  factor.
- `range_comp_eq_inf_of_range_eq_comap`: if the range of `f` is the
  preimage of `F` under `j`, then the range of `f ≫ j` is
  `range j ⊓ F`.
- `mono_of_isClosedSubgroup`: a closed subgroup inclusion is a monomorphism.

## Provenance

This is a derived internal implication between Library propositions. It
composes published theorems and introduces no new external assertion, so it
adds no citation. Its route is the dynamic description recorded in the
section *Provenance of the hypothesis form* of
`RepresentedParabolicLeviIntersectionStatement`, whose Markdown gives the
sources. With `S` the common torus, that description writes
`P = P_G(λ)`, `M = Z_G(λ)`, `Q = P_G(μ)`, `L = Z_G(μ)` and `U = U_G(μ)` for
cocharacters `λ`, `μ` of `S`, and obtains `M ∩ Q = P_M(μ)`,
`M ∩ L = Z_M(μ)` and `M ∩ U = U_M(μ)`. The two premises supply the
cocharacters (step 1) and the structure of the dynamic subgroups of `M`
(step 5). The route does not follow Renard's root-system
argument for V.4.6 (ii) and V.4.7, which goes through the bijection of V.4.2.

The monicity wrapper reuses `IsClosedSubgroup.mono_overHom` from `GroupScheme.ClosedSubgroupMonomorphism`.
