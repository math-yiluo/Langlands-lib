# Parabolicity transfer along a represented dynamic Levi

This internal helper reduces `DynamicLeviParabolicCorrespondenceStatement` to
seven published structure statements. Fix a field `k` in an arbitrary universe
`u`, a connected reductive group `G` over `Spec k`, a cocharacter
`χ : Gm ⟶ G`, and a closed subgroup `j : L ⟶ G` that represents the dynamic
centralizer `Dynamic.centralizer χ` (witness `hj`). Write `P(χ)`, `U(χ)` for
`Dynamic.parabolic χ`, `Dynamic.unipotent χ`. Parabolicity means the published
predicate `IsParabolicFunctor`: the subgroup functor is the range of an actual
parabolic subgroup (`IsParabolicSubgroup`).

Every result here is conditional. The structure statements it uses are
explicit hypotheses:

- `hPD : ParabolicDynamicStatement`;
- `hCR : DynamicCentralizerReductiveStatement`;
- `hReal : DynamicLeviCocharacterRealizationStatement`;
- `hconj : SmoothMaximalSplitTorusConjugacyStatement`;
- `hconn : DynamicConnectedStatement`;
- `hRS : RelativeRootSignInclusionsStatement`;
- `hNeg : RelativeRootNegationStatement`.

This file proves none of them. Every statement input is taken in the universe
`u` of `k`.

The order isomorphism itself comes from Worker 1116's published definition
`Dynamic.extendFromCentralizerOrderIso` (module
`Langlands.GroupScheme.Dynamic.LeviParabolicExtension`). That definition takes
two parabolicity transfers, `hfwd` and `hsurj`, which this file supplies.

## Conjugation by a centralizer point

`Dynamic.comp_innerIso_hom_of_mem_centralizer` works over any base scheme `S`.
If a point `z` of `G` over `S` lies in `Dynamic.centralizer χ`, then
`χ ≫ (G.innerIso z).hom = χ`. The proof rewrites the centralizer as
`torusCentralizer χ` by `torusCentralizer_gm_eq_dynamicCentralizer`. It then
checks the equality on points (`hom_ext_points`). On points, `z` commutes with
every point of the image of `χ`, so conjugation by `z` fixes that image.

## Root-sign step

`unipotent_le_parabolic_of_parabolic_le` assumes `hRS` and `hNeg`. Let
`i : T ⟶ G` be a maximal split torus and let `ζ, ξ` be cocharacters of `T`. If
`P(ζ ≫ i) ≤ P(ξ ≫ i)`, then `U(ξ ≫ i) ≤ P(ζ ≫ i)`. Here `ζ ≫ i` abbreviates
`CommGroupScheme.groupHom ζ ≫ i`, and similarly for `ξ`.

1. Positive implies positive: if `α` is an actual relative root with
   `⟨α, ξ⟩ > 0`, then `⟨α, ζ⟩ > 0`. Otherwise `-α` is a root by `hNeg`, with
   `⟨-α, ζ⟩ ≥ 0`. The parabolic half of `hRS`, applied to the hypothesis
   `P(ζ ≫ i) ≤ P(ξ ≫ i)`, then gives `⟨-α, ξ⟩ ≥ 0`, a contradiction.
2. The set of relative roots is finite (`IsSplitTorus.finite_relativeRoots`).
   So there is a bound `M` with `⟨α, ξ⟩ ≤ M` for every root. Put
   `N = max M 0 + 1` and `η = N • ζ + ξ`.
3. The unipotent half of `hRS` gives `U(ξ ≫ i) ≤ U(η ≫ i)`. If
   `⟨α, ξ⟩ > 0`, then `⟨α, ζ⟩ > 0` by step 1. Hence
   `⟨α, η⟩ = N⟨α, ζ⟩ + ⟨α, ξ⟩ > 0`.
4. The parabolic half of `hRS` gives `P(η ≫ i) ≤ P(ζ ≫ i)`. If
   `⟨α, η⟩ ≥ 0` but `⟨α, ζ⟩ ≤ -1`, then
   `⟨α, η⟩ ≤ -N + M < 0`, a contradiction.
5. Finally `U(ξ ≫ i) ≤ U(η ≫ i) ≤ P(η ≫ i) ≤ P(ζ ≫ i)`, using
   `Dynamic.unipotent_le_parabolic`.

## Descent of dynamic parabolics

`Dynamic.exists_parabolic_eq_extendFromCentralizer_of_parabolic_le` assumes
`hconj`, `hconn`, `hRS` and `hNeg`. For every cocharacter `ψ : Gm ⟶ G` with
`P(ψ) ≤ P(χ)`, it gives a cocharacter `ν : Gm ⟶ L` with
`P(ψ) = Dynamic.extendFromCentralizer χ j hj (P(ν))`. The proof:

1. The published theorem `cocharacterMaximalSplitTorus` writes `ψ` as
   `ν₁ ≫ i` for a maximal split torus `i : T ⟶ G` and a cocharacter `ν₁` of
   `T`.
2. The published conditional lemma
   `exists_mem_parabolic_innerIso_comp_eq_cocharacter` uses `hconj`, `hconn`
   and the proved smoothness statement `dynamicSmooth`. It gives a rational
   point `g ∈ P(χ)(k)` and a cocharacter `ξ` of `T` with
   `χ ≫ Int(g) = ξ ≫ i`, where `Int(g)` is `(G.innerIso g).hom`.
3. `RationalPoint.existsUnique_unipotent_mul_levi` writes `g = u * z` with
   `u ∈ U(χ)(k)` and `z` in the dynamic Levi of `χ`. Since `Int(u * z)` is
   `Int(z) ≫ Int(u)` (`innerIso_mul_hom`), the conjugation lemma above gives
   `χ ≫ Int(u) = ξ ≫ i`.
4. Transport along `Int(u)` (`parabolic_eq_comap_of_iso`,
   `unipotent_eq_comap_of_iso`, `SubgroupFunctor.eq_comap_iso_iff`) gives
   `P(ξ ≫ i)` and `U(ξ ≫ i)` as the inverse images of `P(χ)` and `U(χ)` under
   `Int(u⁻¹)`. Conjugation by `u⁻¹`, a point of `U(χ) ≤ P(χ)`, preserves both
   subgroup functors (`SubgroupFunctor.comap_innerIso_hom_eq_of_mem`). Hence
   `P(χ) = P(ξ ≫ i)` and `U(χ) = U(ξ ≫ i)`.
5. The root-sign step, applied to `P(ν₁ ≫ i) ≤ P(χ) = P(ξ ≫ i)`, gives
   `U(χ) = U(ξ ≫ i) ≤ P(ψ)`.
6. Conjugating by `u` gives `P(ψ ≫ Int(u)⁻¹) = P(ψ)`, because `u` lies in
   `U(χ) ≤ P(ψ)`. Also `χ = ξ ≫ i ≫ Int(u)⁻¹`. So `j` also represents the
   centralizer of `ξ ≫ (i ≫ Int(u)⁻¹)`. The published `torusFactor` then
   factors the torus `i ≫ Int(u)⁻¹` through `j` (`torusFactor_comp`). Put
   `ν = ν₁ ≫ torusFactor (i ≫ Int(u)⁻¹) ξ _`, so that
   `ν ≫ j = ψ ≫ Int(u)⁻¹`.
7. Since `j` is a closed subgroup, `parabolic_eq_comap_of_isClosedSubgroup`
   gives `P(ν) = P(ν ≫ j).comap j = P(ψ).comap j`. Worker 1116's
   `extendFromCentralizer_comap`, applied to `U(χ) ≤ P(ψ) ≤ P(χ)`, gives
   `Dynamic.extendFromCentralizer χ j hj (P(ψ).comap j) = P(ψ)`.

## Forward and inverse transfers

`Dynamic.isParabolicFunctor_extendFromCentralizer_of_structural_statements`
assumes `hPD`, `hCR` and `hReal`. It states that if `F` is an actual parabolic
of `L`, then `Dynamic.extendFromCentralizer χ j hj F` is an actual parabolic of
`G`. By `hCR` the group `L` is connected reductive. The published lemma
`IsParabolicFunctor.exists_dynamicCocharacter` uses `hPD` for `L` to write `F`
as `P(ν)` for some `ν : Gm ⟶ L`. `hReal` gives `ψ : Gm ⟶ G` with
`P(ψ) = Dynamic.extendFromCentralizer χ j hj (P(ν))`; its centralizer and
unipotent equalities are not used. The published lemma
`isParabolicFunctor_dynamic_of_parabolicDynamic` for `G` shows that `P(ψ)` is
an actual parabolic.

`Dynamic.exists_isParabolicFunctor_extendFromCentralizer_eq_of_descent` assumes
`hPD`, `hCR` and a descent input `hdesc` for this `χ` and `j`, of the form
proved in the previous section. It states that every actual parabolic `Q` of
`G` with `Q ≤ P(χ)` equals `Dynamic.extendFromCentralizer χ j hj F` for some
actual parabolic `F` of `L`. The proof writes `Q = P(ψ)` by
`IsParabolicFunctor.exists_dynamicCocharacter` for `G`, applies `hdesc` to `ψ`,
and takes `F = P(ν)`. This `F` is an actual parabolic of `L` by
`isParabolicFunctor_dynamic_of_parabolicDynamic`, since `L` is connected
reductive by `hCR`.

## The conditional order isomorphism

The entry definition `Dynamic.extendFromCentralizerOrderIsoOfStructuralStatements`
takes the seven hypotheses, `hG : IsConnectedReductive G`, `χ`, `j`,
`hjc : IsClosedSubgroup j` and `hj`. Its value has type
`ParabolicFunctor L ≃o ParabolicFunctorBelow (Dynamic.parabolic χ)`. It is
`Dynamic.extendFromCentralizerOrderIso χ j hj hfwd hsurj`. The separatedness
instance comes from `hG.isSeparated`. `hfwd` is the forward transfer, and
`hsurj` is the inverse transfer with `hdesc` given by the descent theorem. So
the isomorphism sends `F` to `Dynamic.extendFromCentralizer χ j hj F`, and its
inverse sends `Q` to `Q.comap j`. Both equalities hold by `rfl`.

`dynamicLeviParabolicCorrespondenceStatement_of_structural_statements` states
that `DynamicLeviParabolicCorrespondenceStatement.{u}` follows from the seven
hypotheses. For each instance, it gives the entry definition as the
isomorphism, together with the two `rfl` equalities.

## Provenance and scope

This file states no new external theorem. It is a derived combination of the
published definitions and lemmas named above with the seven named statement
inputs. The geometric content of those inputs is neither proved nor asserted
here; each records its sources in its own statement file. The descent step is
the dynamic form of the classical fact that a parabolic of `G` contained in
`P(χ)` comes from a parabolic of the Levi. Classically this is Borel–Tits,
*Groupes réductifs* (Publ. Math. IHÉS 27, 1965), Proposition 4.4(c)
(printed p.86), a geometric statement, together with the rationality results
of Proposition 4.7 (printed p.88). The proof here does not follow Borel–Tits.
It uses rational conjugacy into a maximal split torus and the root-sign
comparison described above.

All results allow an arbitrary field in an arbitrary universe `u`, with no
splitness, perfectness or characteristic assumption. They hold for every
closed representative `j` of the dynamic centralizer.
