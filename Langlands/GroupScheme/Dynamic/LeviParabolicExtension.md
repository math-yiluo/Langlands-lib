# Inverse image and exact extension for a represented dynamic centralizer

Author: Worker 1116. The hypothesis interface `hfwd`, `hsurj` was proposed by
Worker 1236.

This module proves the elementary all-test algebra behind the parabolic
correspondence of
`Langlands.GroupScheme.DynamicLeviParabolicCorrespondenceStatement`, together
with a conditional assembly of that correspondence. It does not prove the
structural facts the correspondence needs; those are explicit hypotheses of the
assembly theorem.

Throughout, `j : L ⟶ G` represents `Dynamic.centralizer χ` in the sense of
`SubgroupFunctor.IsRepresentedBy`: `j` is a monomorphism and its all-test
range is the centralizer. For a subgroup functor `F` of `L`,
`extendFromCentralizer χ j hj F` is the exact pointwise product `j(F) U(χ)`
from `Dynamic/LeviParabolicDefinitions`. All statements hold on every test
scheme `T` over the base, including nonreduced ones. No closedness of `j` is
used.

## Generic lemmas over any base scheme

- `unipotent_le_extendFromCentralizer`: `U(χ) ≤ j(F) U(χ)`, taking the factor
  `l = 1`.
- `map_le_extendFromCentralizer`: `F.map j ≤ j(F) U(χ)`, taking the factor
  `n = 1`.

The remaining lemmas assume `[IsSeparated G.X.hom]`. This is what makes limits
of orbit maps unique, so that `HasLimit.unique` from `Dynamic/Uniqueness`
applies.

- `comap_extendFromCentralizer`: `(j(F) U(χ)).comap j = F`. If
  `x ≫ j = (l ≫ j) * n` with `l ∈ F(T)` and `n ∈ U(χ)(T)`, then
  `n = (l⁻¹ * x) ≫ j` lies in the range of `j`, which is the centralizer. A
  point in both the centralizer and `U(χ)` is `1`
  (`eq_one_of_mem_centralizer_of_mem_unipotent`, with uniqueness of limits
  supplied by `HasLimit.unique`). Hence `x ≫ j = l ≫ j`, and since `j` is a
  monomorphism, `x = l ∈ F(T)`. The reverse inclusion takes `n = 1`.
- `extendFromCentralizer_comap`: if `U(χ) ≤ Q ≤ P(χ)` then
  `j(Q.comap j) U(χ) = Q`. The image of `Q.comap j` is `range j ⊓ Q`
  (`SubgroupFunctor.map_comap`), so the product lies in `Q` by
  `normalizedProduct_le`. Conversely, `q ∈ Q(T)` lies in `P(χ)(T)`, so it has
  a limit `l` (`exists_hasLimit`). That limit lies in the centralizer
  (`HasLimit.mem_centralizer`), so `l = y ≫ j` for some point `y` of `L`. Also
  `l⁻¹ * q` has limit `1`, so it lies in `U(χ)(T)`. Finally `y` lies in
  `Q.comap j` because `l = q (l⁻¹ q)⁻¹` and `U(χ) ≤ Q`. So
  `q = (y ≫ j) * (l⁻¹ * q)` is in the product.
- `extendFromCentralizer_le_iff`: `j(F) U(χ) ≤ j(F') U(χ) ↔ F ≤ F'`. The
  forward direction applies `comap j` and `comap_extendFromCentralizer`; the
  reverse is the published `extendFromCentralizer_mono`.

## Conditional order isomorphism over a field

The section `Field` fixes a field `k` in an arbitrary universe, group schemes
`G` and `L` over `Spec k` with `[IsSeparated G.X.hom]`, a cocharacter `χ`, and
a representative `j` with proof `hj`. The definition
`extendFromCentralizerOrderIso χ j hj hfwd hsurj` takes two hypotheses:

- `hfwd`: for every actual parabolic functor `F` of `L`,
  `extendFromCentralizer χ j hj F` is an actual parabolic functor of `G`;
- `hsurj`: every actual parabolic functor `Q` of `G` with
  `Q ≤ Dynamic.parabolic χ` equals `extendFromCentralizer χ j hj F` for some
  actual parabolic functor `F` of `L`.

It is an order isomorphism
`ParabolicFunctor L ≃o ParabolicFunctorBelow (Dynamic.parabolic χ)`. The
forward map sends `F` to its extension, which is parabolic by `hfwd` and lies
below `P(χ)` by the published `extendFromCentralizer_le_parabolic`. The
inverse sends `Q` to `Q.comap j`. It is parabolic because `hsurj` writes `Q`
as the extension of a parabolic `F`, and then `Q.comap j = F` by
`comap_extendFromCentralizer`. The same lemma gives `e.symm (e F) = F`.
Rewriting `Q` as the extension of `F` gives `e (e.symm Q) = Q`. Order
reflection is `extendFromCentralizer_le_iff`. The simp lemmas
`extendFromCentralizerOrderIso_apply_coe` and
`extendFromCentralizerOrderIso_symm_apply_coe` record, by definition, that the
underlying functors are `extendFromCentralizer χ j hj F.val` and
`Q.val.comap j`.

`exists_parabolicFunctor_orderIso_of_forward_of_surjective` then takes a
connected reductive `G`, together with `χ`, `j`, `hj`, `hfwd` and `hsurj`. It
concludes exactly the body of `DynamicLeviParabolicCorrespondenceStatement`:
there is `e : ParabolicFunctor L ≃o ParabolicFunctorBelow (Dynamic.parabolic χ)`
with `(e F).val = extendFromCentralizer χ j hj F.val` and
`(e.symm Q).val = Q.val.comap j`. Separatedness of `G.X.hom` comes from
`hG.isAffineHom`, and `e` is `extendFromCentralizerOrderIso`. The closedness of
`j` that the statement also supplies is not needed.

`hfwd` and `hsurj` are structural facts that this module does not prove. One
expected route derives them from
`ParabolicDynamicStatement`, `DynamicCentralizerReductiveStatement` and a
descent statement for parabolics contained in `P(χ)`. Until such proofs are
available, the assembly theorem is a reduction, not a proof of the target.

## Provenance

Internal. The lemmas are elementary consequences of the published definitions
of the exact product, the dynamic subgroup functors and uniqueness of limits
over a separated base, and the order isomorphism is a direct construction from them
and the two stated hypotheses. No literature is cited.
