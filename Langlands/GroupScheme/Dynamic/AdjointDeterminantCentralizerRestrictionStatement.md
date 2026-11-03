# Restriction of the adjoint determinant character from the parabolic to the Levi

This module states, without proof, that restricting the algebraic character
`det(Ad | Lie U)` from the parabolic `P(χ)` to its Levi factor `M = Z(χ)`
gives the determinant of the conjugation action of `M` on `Lie(U)`.

The only declaration is the Prop-valued definition
`Langlands.GroupScheme.Dynamic.AdjointDeterminantCentralizerRestrictionStatement`,
at a single universe level `u`.

## Setting

The statement quantifies over the following data.

- A commutative ring `R : CommRingCat.{u}`, a group scheme `G` over
  `Spec R`, and an actual cocharacter `χ : (Gm (Spec R)).toGrp ⟶ G`.
- Representations of the three published dynamic subgroup functors:
  - `hP : (parabolic χ).IsRepresentedBy iP` with `iP : P ⟶ G`,
  - `hZ : (centralizer χ).IsRepresentedBy iZ` with `iZ : Z ⟶ G`,
  - `hU : (unipotent χ).IsRepresentedBy iU` with `iU : U ⟶ G`.
- The finiteness and affineness hypotheses that the determinant characters
  need: `IsAffineHom U.X.hom`, `IsAffine P.X.left` and `IsAffine Z.X.left`.
- Finite coordinates `c : Lie.FiniteCoordinates U d` of `Lie(U)`, from
  `Langlands.GroupScheme.Lie.FiniteAction`. These are
  natural `A`-linear isomorphisms `Lie(U)(A) ≅ A^d` over all commutative
  `R`-algebras `A`.

No separatedness of `G` is assumed. The published
`Dynamic.centralizerToParabolic` and `Dynamic.centralizerToParabolic_comp`
take no separatedness hypothesis. No field, reductivity, connectedness or
smoothness hypothesis is made. The
characteristic is arbitrary, and `χ` may be trivial.

## The statement

`characterRestrict (centralizerToParabolic hP hZ)
    (adjointDeterminantCharacter hP hU c) =
  (centralizerAdjointAction hZ hU).determinantCharacter c`.

The ingredients are the following.

- `centralizerToParabolic hP hZ : Z ⟶ P` is the published inclusion of the
  represented centralizer into the represented parabolic. It satisfies
  `centralizerToParabolic hP hZ ≫ iP = iZ`
  (`Dynamic.centralizerToParabolic_comp`).
- `characterRestrict f` is the published restriction of rational characters
  along `f`, namely `χ ↦ f ≫ χ`.
- `adjointDeterminantCharacter hP hU c : rationalCharacters P` is the
  determinant character of the conjugation action
  `parabolicAdjointAction hP hU` of `P` on `U` in the coordinates `c`. Both
  are from `Langlands.GroupScheme.Dynamic.AdjointDeterminant`.
- `centralizerAdjointAction hZ hU : AutomorphicAction Z U` is the action of
  `Z` on `U` by conjugation, from
  `Langlands.GroupScheme.Dynamic.CentralizerAdjointAction`.
  `AutomorphicAction.determinantCharacter`, from
  `Langlands.GroupScheme.Lie.ActionDeterminant`, is the determinant of the
  differential of an action, read in the given coordinates. The right side
  uses the same coordinates `c` as the left side.

Characters are written additively: `rationalCharacters H` is the additive
group of homomorphisms `H ⟶ G_m`.

## Conjugation orientation

Both actions are normalized conjugation with `p` as the left factor:
`u ↦ p u p⁻¹` on `P` and `u ↦ m u m⁻¹` on `Z`. For the parabolic this is
`Dynamic.parabolicAdjointAction_act_comp`, and for the centralizer it is
`Dynamic.centralizerAdjointAction_act_comp`.

## Scope

The statement uses the actual `P(χ)`, `Z(χ)`, `U(χ)` and the actual
inclusion of `Z(χ)` into `P(χ)`. Both sides are the constructed determinant
characters, not abstract characters supplied as hypotheses. The coordinates
`c` are arbitrary; their existence is a separate structural target. The
statement does not say that the result is independent of the models or the
coordinates (`AdjointDeterminantModelIndependenceStatement`). It does not
compute the character on a torus
(`AdjointDeterminantTorusRestrictionStatement`).

## Provenance

The packaging is internal and derived. Renard, *Représentations des groupes
réductifs p-adiques* (version of 9 July 2026), §V.5.4, printed pp.126–127 /
PDF pp.132–133, evaluates the modulus of a parabolic `P = MN` at points
`m ∈ M` of the Levi factor. Its Lemma gives, for all `m ∈ M`,
`δ_{P\G}(m) = δ_G(m)/δ_P(m) = δ_P(m)⁻¹`, where `δ_P` is Renard's modular
function of `P`. The same Lemma gives
`δ_P(a) = ∏_{γ∈Σ(P)} |γ(a)^{-(m_γ+2m_{2γ})}|_F` for `a` in the split
component `A`. So Renard's `δ_P` is the inverse of the absolute value of the
character studied here. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra* (2003), §I.1, printed pp.238–241 / PDF pp.4–7, uses
`δ_P(m)` for `m` in the Levi factor `M`. The decomposition of the measure
there is `∫_G f = ∫_{U×M×K} f(umk) δ_P(m)⁻¹`. It is registered as
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

In both sources the Levi restriction of the modulus is the restriction of a
function on `P`. Here it is an identity of algebraic characters over any
commutative ring. The expected proof follows: the restriction of
`parabolicAdjointAction hP hU` along `centralizerToParabolic hP hZ` is
`centralizerAdjointAction hZ hU`, and the determinant character commutes with
restricting the acting group. Absolute values, Haar measures and the analytic
modulus are not part of this statement.
