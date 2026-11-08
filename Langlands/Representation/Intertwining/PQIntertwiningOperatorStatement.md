# The intertwining operator of a `PQ`-regular representation (Renard VII.3.4)

Author: Worker 6. Module `Langlands.Representation.Intertwining.PQIntertwiningOperatorStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. The module contains one **statement**: the closed `Prop`-valued definition `PQIntertwiningOperatorStatement` (universe parameters `u, v`). It proves nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated **9 July 2026**:

- VII.3.4, the construction of `K_{Q|P}(σ)` and `J_{Q|P}(σ)`, the explicit formula for `K_{Q|P}`, the Proposition and its proof, printed pp.235–236 / PDF pp.241–242;
- VII.3.2–VII.3.3, the support subspaces, the identification `F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(E) ≃ E`, the ideals `I_σ`, `I^{PQ}_σ` and `PQ`-regularity, printed pp.232–235 / PDF pp.238–241;
- III.2.5, Frobenius reciprocity, which the proof of the Proposition uses.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Worker 6 read PDF pages 238–242.

Renard's construction is as follows. Let `P = MN` and `Q = MU` be parabolic subgroups with the same Levi factor `M`, and `(σ, E)` a smooth representation of `M`. There is an inclusion `i_σ : E ≃ F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(E) ↪ (r_Q^G ∘ i_P^G / F^{≤1̄}_{PQ})(E)`. When `σ` is `PQ`-regular, `i_σ` has a retraction `r_σ`, given by the action of an element `ε_σ ∈ I^{PQ}_σ` with `1 ∈ ε_σ + I_σ`. The composite `K_{Q|P}(σ) : r_Q^G ∘ i_P^G(E) → (r_Q^G ∘ i_P^G / F^{≤1̄}_{PQ})(E) → E` (projection, then `r_σ`) is a nonzero element of `Hom_M(r_Q^G ∘ i_P^G(σ), σ)`. Frobenius reciprocity turns it into a nonzero intertwining operator `J_{Q|P}(σ) ∈ Hom_G(i_P^G(σ), i_Q^G(σ))`. The identification `F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(E) ≃ E` is induced by `F̃^{<1̄}_{PQ} → E`, `f ↦ ∫_{N̄∩U} f(u) du`.

The Proposition reads: "Soient `P = MN` et `Q = MU` deux sous-groupes paraboliques semi-standards de `G` et `(σ, E)` une représentation lisse de `M` que l'on suppose `PQ`-régulière. Alors l'opérateur d'entrelacement `J_{Q|P}(σ)` est l'unique élément de `Hom_G(i^G_P(σ), i^G_Q(σ))` vérifiant `(∀ f ∈ F̃^{<1̄}_{PQ}(E)), J_{Q|P}(σ)(f)(1_G) = ∫_{N̄∩U} f(u) du`."

## Published objects used

From [PQRegularity](PQRegularity.md) (module `Langlands.Representation.Intertwining.PQRegularity`):

- `identityParabolicDoubleCoset p q`, Renard's `1̄`, the double coset `P(F) Q(F)`;
- `boundaryVanishingSubfunctor p l r hp hr hl hmul q (identityParabolicDoubleCoset p q)`, Renard's `F̃^{<1̄}_{PQ}`: the functions in `i_P^G(-)` that vanish on `closure (P(F) Q(F)) \ P(F) Q(F)`;
- `boundarySupportImage … (identityParabolicDoubleCoset p q)` and `closureSupportImage … (identityParabolicDoubleCoset p q)`, Renard's `F^{<1̄}_{PQ}` and `F^{≤1̄}_{PQ}`: the images in `r_Q^G ∘ i_P^G(-)` of the subfunctors of functions vanishing on the boundary and on the closure of `P(F) Q(F)`;
- `IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ`, condition (i) of the VII.3.3 Lemma, `I_σ + I^{PQ}_σ = ℂ[A_M]`;
- through it, `leviInductionFunctor`, Renard's normalized `i_P^G` and `i_Q^G` on representations of `M(F)`, and `leviJacquetInductionFunctor`, Renard's `r_Q^G ∘ i_P^G`.

From [Definitions](../Filtration/Definitions.md) (module `Langlands.Representation.Filtration.Definitions`): for subfunctors `S` and `T`, `S.quotientObj T X` is the quotient of `T(X)` by `S(X) ∩ T(X)`, and `S.quotientProjection T X : T(X) → S.quotientObj T X` is the projection.

The Jacquet quotient map `Jacquet.Localization.mk π (pointImage (rQ ≫ q)) 1`, the evaluation `Induction.eval`, the inducing representation `inducingRepresentation … (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm σ)` of `Q(F)` and the Levi-point identification `leviPointsEquiv` are the published ones. They appear in the same form in the published [LeviFrobeniusReciprocityStatement](../Exponents/LeviFrobeniusReciprocityStatement.md).

From Mathlib: `Representation.IntertwiningMap` and `Representation.Equiv`, the linear maps and linear equivalences that commute with the group actions.

## Lean statement

`PQIntertwiningOperatorStatement` quantifies over:

- a nonarchimedean local field `k : Type u` and a connected reductive `G` over `Spec k`, with the canonical topology on `G(F)`, and `[LocallyCompactSpace (rationalPoints G)]`, `[NonarchimedeanGroup (rationalPoints G)]`;
- represented parabolics `P = MN` (`p`, `l`, `r` with `hp`, `hl`, `hr`, `hmul`) and `Q = MU` (`q`, `lQ`, `rQ` with `hq`, `hlQ`, `hrQ`, `hmulQ`) that share the Levi scheme `M`, and a proof of `l ≫ p = lQ ≫ q`, so the two embeddings of `M` in `G` agree;
- a commutative group scheme `A` with `a : A.toGrp ⟶ M` and a proof of `IsSplitComponent a`, so `A` is Renard's `A_M`. The topology on `M(F)` is `leviPointTopology l hl`;
- a smooth representation `σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` with `IsPQRegular … a σ`;
- an `M(F)`-equivariant linear equivalence `e` from `(closureSupportImage … 1̄).quotientObj (boundarySupportImage … 1̄) σ` to `σ`. This quotient is `F^{<1̄}_{PQ}(σ)/(F^{≤1̄}_{PQ}(σ) ∩ F^{<1̄}_{PQ}(σ))`, Renard's `F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(E)`.

The conclusion is that there is exactly one intertwining map `J` from `i_P^G(σ)` to `i_Q^G(σ)` such that, for every `f ∈ i_P^G(σ)` with `f ∈ F̃^{<1̄}_{PQ}(σ)`, every `y` in `r_Q^G ∘ i_P^G(σ)` and every proof `hy` that `y` lies in `F^{<1̄}_{PQ}(σ)`: if `y` is the image `Jacquet.Localization.mk … 1 f` of `f`, then

`Induction.eval (pointImage q) (inducingRepresentation …) (J f) 1 = e (quotientProjection ⟨y, hy⟩)`.

The left side is `J(f)(1_G)`. The right side is `e` applied to the class of the image `f̄` of `f`. Renard writes `f̄` for that image in the proof of the Proposition. The variable `y` with the equation `y = mk … f` names `f̄` as an element of the Jacquet module together with its membership in `F^{<1̄}_{PQ}(σ)`. That membership always holds, since `F^{<1̄}_{PQ}` is defined as the image of `F̃^{<1̄}_{PQ}`, so the quantification over `y` and `hy` adds no condition.

## Provenance and departures from the source

The provenance is derived. The statement is Renard's Proposition with the integral replaced by an arbitrary identification `e`.

- **The integral.** Renard's `J_{Q|P}(σ)` is the operator for the particular `e` induced by `f ↦ ∫_{N̄∩U} f(u) du`. The module does not construct that integral. Doing so needs the opposite unipotent radical `N̄` of `P` and a Haar measure on `N̄ ∩ U`, and the resulting operator depends on the normalization of that measure. The statement holds for every equivariant identification `e`, so it applies to Renard's `e` once that identification is formalized.
- **Why the statement holds for every `e`.** This is how Renard's proof goes. Take `ε ∈ I^{PQ}_σ` with `1 - ε ∈ I_σ`, which exists by `PQ`-regularity. `A_M` is central in `M`, so `ε` acts on `r_Q^G ∘ i_P^G(σ)` by an `M(F)`-equivariant map. `ε` kills the quotient by `F^{<1̄}_{PQ}(σ)` and acts as the identity on `σ`. Then `K(x) = e([ε x])` is an `M(F)`-equivariant map `r_Q^G ∘ i_P^G(σ) → σ`, and `K(f̄) = e([f̄])` for `f ∈ F̃^{<1̄}_{PQ}(σ)`. Two such maps differ by an equivariant map `D` that vanishes on `F^{<1̄}_{PQ}(σ)`. Then `D(x) = ε D(x) = D(ε x) = 0`, so `K` is unique. Frobenius reciprocity (Renard III.2.5; the published `LeviFrobeniusReciprocityStatement` applied to `Q`, `π = i_P^G(σ)` and `σ`) identifies `Hom_G(i_P^G(σ), i_Q^G(σ))` with `Hom_M(r_Q^G ∘ i_P^G(σ), σ)` through `J(f)(1_G) = K(f̄)`. This transfers existence and uniqueness to `J`. The argument is a justification of the statement and is not formalized here.
- **Identification of the subquotient with `σ`.** Renard uses a natural isomorphism `F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(E) ≃ E`. Here `e` is a hypothesis. If no such `e` exists, the statement says nothing about `σ`. The VII.3.2 statement asserts that such an identification exists.
- **The quotient.** `quotientObj` divides `F^{<1̄}_{PQ}(σ)` by `F^{≤1̄}_{PQ}(σ) ∩ F^{<1̄}_{PQ}(σ)`. Renard divides by `F^{≤1̄}_{PQ}(σ)`. The two agree because `F^{≤1̄}_{PQ} ⊂ F^{<1̄}_{PQ}`, an inclusion asserted in the VII.3.2 statement and not used here.
- **Nonvanishing.** Renard notes that `K_{Q|P}(σ)` and `J_{Q|P}(σ)` are nonzero. The statement does not assert this. When `σ ≠ 0` it follows from the characterization, because `f ↦ [f̄]` maps `F̃^{<1̄}_{PQ}(σ)` onto the quotient, so some `f` has `e([f̄]) ≠ 0`.
- **Double cosets.** `1̄` is the actual double coset `P(F) Q(F)`, and the support subspaces use the closure relation on actual double cosets of [PQRegularity](PQRegularity.md), not `W_M \ W_G / W_M`.
- **Semi-standard parabolics.** Renard takes `P` and `Q` semi-standard. The statement does not assume this.
- **`PQ`-regularity.** `IsPQRegular` is condition (i) of the VII.3.3 Lemma. Renard defines `PQ`-regularity as "(i) or (ii)", and the Lemma proves the two conditions equivalent.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Intertwining.PQRegularity` | `identityParabolicDoubleCoset`, `boundaryVanishingSubfunctor`, `boundarySupportImage`, `closureSupportImage`, `IsPQRegular`; through it, `leviInductionFunctor`, `leviJacquetInductionFunctor`, `quotientObj`, `quotientProjection`, `Jacquet.Localization.mk`, `Induction.eval`, `inducingRepresentation`, `leviPointsEquiv` and `IsSplitComponent` |
| `Langlands.Representation.Category.Basic` | `SmoothRep` |
