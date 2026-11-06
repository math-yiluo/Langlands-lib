# Levi subgroups of proper parabolics containing a maximal Levi

`Langlands.GroupScheme.MaximalLeviContainmentStatement.{u}` is a Prop-valued
definition. This module states it and proves nothing.

## Source

Renard, Représentations des groupes réductifs p-adiques (2026 version), VII.1.3,
proof of the theorem (printed p.224, PDF p.230). There `M` is a maximal standard
Levi, and the geometric lemma VI.5.3 is applied to `r_Q^G(π)` for the proper
standard parabolics `Q`. Renard concludes that "the only contributions come from the
parabolic subgroups `P` and `P'`". Proposition VI.5.3 makes `r_Q^G i_P^G ρ` vanish
unless the Levi `L` of `Q` contains a conjugate `w·M` of `M`. The step used
implicitly is that such an `L` then equals `w·M`. Renard defines maximal Levi
subgroups in V.4.8 (printed p.122, PDF p.128): they are the Levi factors of maximal
proper parabolics, the standard ones corresponding to `Θ = Δ∅ \ {α}`. On PDF p.231
he uses that `A_M / A_G` has dimension one. This statement isolates the structural
step for actual rational parabolics, applied to a conjugate of `M`.

The source proof of the step goes as follows. `A_L` centralizes `M ⊆ L`, so it
lies in the centre of `M` and hence in `A_M`. Also `A_G ⊆ A_L`, and `A_L ≠ A_G`
because `L = Z_G(A_L)` and `Q ≠ G`. Since `dim A_M = dim A_G + 1`, this forces
`A_L = A_M`, and then `L = Z_G(A_L) = Z_G(A_M) = M`. These arguments are
explanation only; the module records just the statement.

## The proposition

It quantifies, in this order:

- an arbitrary field `k : Type u`;
- a group scheme `G` over `Spec k` with `IsConnectedReductive G`;
- group schemes `P, M, Q, L` over `Spec k`, and maps `p : P ⟶ G`, `l : M ⟶ P`,
  `q : Q ⟶ G` and `lQ : L ⟶ Q`.

It assumes:

1. `IsParabolicSubgroup p`, `IsRationalLeviSubgroup l` and `¬ IsIso p`. So `P` is an
   actual proper rational parabolic with rational Levi `M`.
2. Maximality, in the same form as in the published
   `MaximalLeviSupercuspidalUnitarizableConstituentStatement`. For every rational
   parabolic `q' : Q' ⟶ G` and every `j : P ⟶ Q'` with `j ≫ q' = p`, either `j` or
   `q'` is an isomorphism.
3. `IsParabolicSubgroup q`, `IsRationalLeviSubgroup lQ` and `¬ IsIso q`. So `Q` is an
   actual proper rational parabolic with rational Levi `L`.
4. `SubgroupFunctor.range (l ≫ p) ≤ SubgroupFunctor.range (lQ ≫ q)`. The image of
   `M` in `G` is contained in the image of `L` on every test scheme.

It concludes `SubgroupFunctor.range (l ≫ p) = SubgroupFunctor.range (lQ ≫ q)`: the
two Levi subgroups of `G` coincide as subgroup functors. Both maps are closed
immersions, so the published `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`
(as in `IsRationalLeviSubgroup.isoOfRangeLe`) then gives an isomorphism `M ≅ L`
compatible with the inclusions into `G`.

## Scope

The field is arbitrary: the Borel–Tits structure theory behind the source argument
holds over every field. There is no topology or valuation. Conjugation does not
appear. In the application, `q` is replaced by `q ≫ (G.innerIso z).hom`, which is
again a proper rational parabolic. The statement does not assume, and does not
assert, that a parabolic with Levi `M` is maximal or that `Q` contains `P`. No
existence of standard parabolics or root presentations is used or asserted.
