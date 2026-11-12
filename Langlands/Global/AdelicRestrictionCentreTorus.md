# The Getz–Hahn split centre: the greatest `ℚ`-split torus of `Res_{F/ℚ} Z_G`

Author: Worker 3659.

Getz–Hahn (2.20), printed p. 68, define `A_G < G(F_∞) < G(𝔸_F)` for a number field `F` as
"the neutral component of the `ℝ`-points of the greatest `ℚ`-split torus in
`Res_{F/ℚ} Z_G`". The published module `AdelicRestrictionSplitCentreCanonical` builds
`[G] = A_G G(F) \ G(𝔸_F)` from a different object: a *split component* of `Res_{F/ℚ} G`
(the published `IsSplitComponent`), that is, a central split torus of `Res_{F/ℚ} G` that
admits no proper factorization through another central split torus. Its subgroup
`canonicalSubgroup F G` is the image in `G(𝔸_F)` of the positive real points of the chosen
component. That module does not show that this is the Getz–Hahn group.

This module defines the Getz–Hahn torus literally and proves that it is the same object. More
precisely, it:

1. defines when a homomorphism `j : S → Res_{F/ℚ} G` takes values in `Res_{F/ℚ} Z_G`
   (`IsRestrictionCentreValued`), using the Library's centre `center G` of `G` and the
   published Weil restriction `AffineWeil.groupScheme ℚ F G`;
2. defines when `j` is the greatest `ℚ`-split torus of `Res_{F/ℚ} Z_G`
   (`IsGreatestRestrictionCentreSplitTorus`);
3. proves that such a `j` exists, that it is exactly a split component of `Res_{F/ℚ} G`, and
   that its subgroup of `G(𝔸_F)` is `canonicalSubgroup F G`;
4. proves that this subgroup is the image in `G(𝔸_F)` of the identity component of the real
   points of the torus, as in (2.20).

So the published quotient `CanonicalQuotient F G` and its measure `canonicalMeasure F G` are
built from exactly the Getz–Hahn `A_G`. No reductivity is assumed anywhere in the module.

## Data

- `F : Type` is a number field, as in the published `RestrictionSplitCentre` namespace.
- `G` is a group scheme over `Spec F` with `IsAffine G.X.left` and
  `LocallyOfFiniteType G.X.hom`.
- `S` is a commutative group scheme over `Spec ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G` a homomorphism into the published Weil
  restriction `Res_{F/ℚ} G`. Its points over a `ℚ`-algebra `C` are identified with
  `G(F ⊗_ℚ C)` by the published multiplicative equivalence `AffineWeil.pointsEquiv ℚ F G C`.

## The centre on algebra points

`Langlands.GroupScheme.mem_center_algSpec_iff` holds for any affine group scheme `G` over any
`Spec R`, any `R`-algebra `A` and any point `g ∈ G(A)`. It states that `g` lies in the
Library's centre `(center G).carrier (Spec A)` if and only if, for every `A`-algebra `D`
(an `R`-algebra `D` with an algebra map `φ : A → D`) and every `y ∈ G(D)`, the image of `g`
in `G(D)` commutes with `y`.

The Library's `center G` tests commutation over every scheme over the given one. The theorem
shows that, for affine `G`, testing over affine schemes, that is over algebras, suffices.
This is the functorial description of the centre in Milne, Proposition 1.92 and the
following paragraph: `C_G(H)(R)` consists of the `g ∈ G(R)` centralizing `H(R')` for all
`R`-algebras `R'`, and `Z(G) = C_G(G)`.

## Values in `Res_{F/ℚ} Z_G`

`RestrictionSplitCentre.IsRestrictionCentreValued F G j` is a definition returning `Prop`.
It says: for every `ℚ`-algebra `C : Type` and every point `s ∈ S(C)`, the point
`AffineWeil.pointsEquiv ℚ F G C (s ≫ j)` of `G(F ⊗_ℚ C)` lies in the Library's centre
`(center G).carrier (Spec (F ⊗_ℚ C))`.

This is the statement that `j` factors through `Res_{F/ℚ} Z_G`. By Milne 2.55 the Weil
restriction of an algebraic group `H` over `F` is the group with
`(Res_{F/ℚ} H)(C) = H(F ⊗_ℚ C)`, and `Res_{F/ℚ} Z_G` is the subgroup with
`(Res_{F/ℚ} Z_G)(C) = Z_G(F ⊗_ℚ C)`. Since `S` is tested on all algebra points, `j` takes
values in that subgroup exactly when the condition above holds.

## The greatest split torus

`RestrictionSplitCentre.IsGreatestRestrictionCentreSplitTorus F G j` is a definition
returning `Prop`, the conjunction of:

- `IsSplitSubtorus j`: `S` is a split torus over `ℚ` and `j` is a closed subgroup (the
  published predicate);
- `IsRestrictionCentreValued F G j`;
- every `j' : S' ⟶ Res_{F/ℚ} G` with `IsSplitSubtorus j'` and `IsRestrictionCentreValued F G j'`
  factors as `f ≫ j = j'` for some homomorphism `f : S' ⟶ S`.

The first two clauses say that `j` is a `ℚ`-split torus in `Res_{F/ℚ} Z_G`. The third says
that it contains every other one, which is "greatest" in (2.20).

## Results

All in namespace `Langlands.Global.RestrictionSplitCentre`.

- `tensorRightHom φ`: for a `ℚ`-algebra `C`, an `F`-algebra `D` and an `F`-algebra map
  `φ : F ⊗_ℚ C → D`, the `ℚ`-algebra map `C → D`, `c ↦ φ(1 ⊗ c)`, into `D` viewed as a
  `ℚ`-algebra through `F` (the published `AffineWeil.restrictScalars`).
  `tensorRightHom_apply` records the formula.
- `tensorMap_tensorRightHom_multiplication`: tensoring `tensorRightHom φ` with `F` and then
  applying the published multiplication map `F ⊗_ℚ D → D` gives `φ`.
- `isRestrictionCentreValued_of_isCentral`: every `j` that is central in `Res_{F/ℚ} G` (the
  published `IsCentral`) takes values in `Res_{F/ℚ} Z_G`. No hypothesis on `S`.
- `isCentral_of_isRestrictionCentreValued`: if `S` is a split torus and `j` takes values in
  `Res_{F/ℚ} Z_G`, then `j` is central in `Res_{F/ℚ} G`.
- `isRestrictionCentreValued_iff_isCentral`: for split `S`, the two conditions are equivalent.
  In other words, a split torus lies in the centre of `Res_{F/ℚ} G` exactly when it lies in
  `Res_{F/ℚ} Z_G`.
- `isGreatestRestrictionCentreSplitTorus_iff_isSplitComponent`: `j` is the greatest `ℚ`-split
  torus of `Res_{F/ℚ} Z_G` if and only if it is a split component of `Res_{F/ℚ} G`.
- `exists_isGreatestRestrictionCentreSplitTorus F G`: such a `j` exists.
- `subgroup_eq_canonicalSubgroup_of_isGreatest`: for such a `j`, the published subgroup
  `subgroup F G S j` equals `canonicalSubgroup F G`.
- `coe_subgroup_eq_image_connectedComponent`: for split `S`, `subgroup F G S j` is, as a set,
  the image of the identity component `connectedComponent 1` of the real points
  `Lie.AffinePoints S.toGrp ℝ` under
  `a ↦ AdelicGroupPoints.ofInfinite F G (realPointsEquiv F G (pointMap ℚ S.toGrp _ ℝ j a))`.
  This is the composite `S(ℝ) → (Res_{F/ℚ} G)(ℝ) = G(F ⊗_ℚ ℝ) = G(F_∞) ⊆ G(𝔸_F)`, the last map
  with finite component `1`. The topology on `S(ℝ)` is the published regular-function
  evaluation topology `GroupScheme.affinePointsTopologicalSpace`.
- `coe_canonicalSubgroup_eq_image_connectedComponent`: combining the last two, for the greatest
  `ℚ`-split torus `j` of `Res_{F/ℚ} Z_G`, `canonicalSubgroup F G` is the image in `G(𝔸_F)` of
  the identity component of its real points. This is (2.20) word for word.

## Proofs

**`mem_center_algSpec_iff`.** The forward direction applies the definition of `center G` to
the scheme map `Spec D → Spec A`. For the converse, let `T'` be any scheme over `Spec R`, with
`a : T' → Spec A` and `y ∈ G(T')`. The published coordinate model of `G`
(`AffineCoordinates.groupSchemeIso`) is a corepresented group scheme, and the published
`Corepresented.pointsEquiv` identifies its points over `T'` with its points over the algebra
`D = Γ(T')` of relative global sections. Under this identification, `a ≫ g` becomes the image
of `g` along `ψ = (A ≅ Γ(Spec A)) ≫ Γ(a) : A → D`. This uses the published
`Corepresented.pointsEquiv_naturality`, `Corepresented.pointsEquiv_eq_affinePointsEquiv` and
`SplitComponent.coordinatePointsEquiv_naturality`. The hypothesis for `D`, `ψ` and the point of
`G(D)` corresponding to `y` gives the commutation, and it transfers back along the
multiplicative equivalences.

**`isRestrictionCentreValued_of_isCentral`.** Fix `C`, `s ∈ S(C)` and use
`mem_center_algSpec_iff`: let `D` be an `F ⊗_ℚ C`-algebra, given as an `F`-algebra `D` with an
`F`-algebra map `φ : F ⊗_ℚ C → D`, and let `y ∈ G(D)`. Since `F/ℚ` is finite separable, it is
formally unramified (`Algebra.FormallyUnramified.of_isSeparable`), and the published
`AffineWeil.exists_affinePointMap_multiplication_eq` lifts `y` along the multiplication
`F ⊗_ℚ D → D`. That is, `y` is the image of some point of `G(F ⊗_ℚ D) = (Res_{F/ℚ} G)(D)`.
Centrality of `j`, applied over `Spec D` with the map `ψ = tensorRightHom φ : C → D`, makes the
image of `j(s)` in `(Res_{F/ℚ} G)(D)` commute with that point. Transport through
`AffineWeil.pointsEquiv` and its naturality (`AffineWeil.pointsEquiv_naturality`), then apply
the multiplication map. By `tensorMap_tensorRightHom_multiplication` the image of `j(s)` is
then the image of `AffineWeil.pointsEquiv ℚ F G C (s ≫ j)` along `φ`.

**`tensorMap_tensorRightHom_multiplication`.** On a pure tensor `b ⊗ c` the left side is
`b · φ(1 ⊗ c) = φ(b ⊗ 1) φ(1 ⊗ c) = φ(b ⊗ c)` (published `multiplication_tensorMap_tmul`). Both
sides are additive, and pure tensors span.

**`isCentral_of_isRestrictionCentreValued`.** Choose a splitting `e : S ≅ splitTorus I`. Compose
with the published isomorphism `torusIso` from the lattice torus of `FreeAbelianGroup I`.
This turns `j` into a homomorphism between two corepresented group schemes: the lattice torus
and the Weil restriction, which the Library builds as `Corepresented.groupScheme` of its
point functor. By the published `groupSchemeMap_natOfHom` this homomorphism is induced by its
point transformation `natOfHom`. By the published `isCentral_groupSchemeMap` it suffices that
each value of that transformation, over each `ℚ`-algebra `C`, commutes with every point of
`G(F ⊗_ℚ C)`. Each value is `AffineWeil.pointsEquiv ℚ F G C (s ≫ j)` for a point `s ∈ S(C)`, so
the hypothesis and `commute_of_mem_center` give this. Finally `j` is the composite of an
isomorphism with this central homomorphism, and `IsCentral.comp` applies.

**`isGreatestRestrictionCentreSplitTorus_iff_isSplitComponent`.** If `j` is greatest, it is a
central split torus by `isCentral_of_isRestrictionCentreValued`. Given a factorization
`f ≫ i' = j` through a central split torus `i'`, the greatest property, applied to `i'` (which
takes values in `Res_{F/ℚ} Z_G` by `isRestrictionCentreValued_of_isCentral`), gives `g` with
`g ≫ j = i'`. Then `(f ≫ g) ≫ j = j` and `(g ≫ f) ≫ i' = i'`. Closed subgroups are
monomorphisms and can be cancelled (a private lemma, the same argument as the private
`cancel_of_isClosedSubgroup` of `AdelicRestrictionSplitCentreCanonical`). So `f` and `g` are
inverse and `f` is an isomorphism. Conversely, a split component is a central split subtorus,
hence `Res_{F/ℚ} Z_G`-valued. Every split subtorus `j'` with values in `Res_{F/ℚ} Z_G` is central
by `isCentral_of_isRestrictionCentreValued`. The published
`IsSplitComponent.exists_comp_eq_of_isCentral` then factors it through `j`. Its finite-type
hypothesis is the published `finiteType_coordinateAlgebra` for the affine, locally finite type
Weil restriction.

**`exists_isGreatestRestrictionCentreSplitTorus`.** Apply the previous equivalence to the
published chosen split component `canonicalRestrictionComponent F G`
(`isSplitComponent_canonicalRestrictionComponent`).

**`subgroup_eq_canonicalSubgroup_of_isGreatest`.** The previous equivalence and the published
`subgroup_eq_canonicalSubgroup`.

**`coe_subgroup_eq_image_connectedComponent`.** The published `subgroup F G S j` is the range of
`positiveImageHom`, the same composite map restricted to `orderedCoefficientPositiveSubgroup ℚ S ℝ`,
the real points on which every rational character is positive. For a split torus the published
`connectedComponent_one_eq_orderedCoefficientPositiveSubgroup` identifies that subgroup with
the identity component, and the two sets agree element by element.

**`coe_canonicalSubgroup_eq_image_connectedComponent`.** Rewrite with
`subgroup_eq_canonicalSubgroup_of_isGreatest` and apply the previous theorem, using that the
greatest torus is a split torus.

## Scope

- The module treats number fields `F : Type` only, matching the published
  `RestrictionSplitCentre` constructions. The function-field `A_G` of (2.20) is not treated.
- No reductivity, smoothness or connectedness of `G` is used. Getz–Hahn state (2.20) for any
  affine algebraic group `G`.
- The module changes no published definition. `canonicalSubgroup`, `CanonicalQuotient`,
  `canonicalMeasure` and their properties are unchanged. It proves that their subgroup is the
  Getz–Hahn `A_G`.

## Sources

- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, Graduate Texts in
  Mathematics 300, Springer, 2024, registered as `getz-hahn-2024-automorphic-representations`,
  SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. Used: §2.6,
  (2.20), printed p. 68 (PDF p. 85), the definition of `A_G` for a number field, and (2.21),
  printed p. 69 (PDF p. 86), the quotient `[G]`. The October 2026 author errata
  (`getz-hahn-2024-errata-2026-10`) have no Chapter 2 entry.
- J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over a Field*,
  Cambridge University Press, 2017, registered as `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Used: Proposition 1.92
  and the definition of the centre `Z(G) = C_G(G)` after it, printed pp. 33–34 (PDF pp. 49–50);
  2.55, printed p. 57 (PDF p. 73), the Weil restriction `(Res G)(R) = G(A ⊗ R)`. The registered
  errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02` has no entry for these
  passages.
