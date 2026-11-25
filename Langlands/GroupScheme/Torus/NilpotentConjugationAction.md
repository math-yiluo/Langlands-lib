# Nilpotent centrality for multiplicative-type sources and arbitrary targets

This internal module proves the affine-base case of SGA 3, IX, Corollaire 3.9, with no
condition on the target group. It asserts nothing attributed to external literature. The
route is the one SGA 3 uses for Corollaire 3.9: apply the rigidity of actions of
diagonalizable groups (Proposition 3.8) to the conjugation action
`(g, h) ↦ u(g) h u(g)⁻¹` of the source on the target. Here that rigidity is only applied on
affine open charts of the target, where it is the Library's affine character-action result.

All declarations lie in `Langlands.GroupScheme.NilpotentConjugation`. Throughout, `R` is a
commutative ring and `I ⊆ R` an ideal, and the hypothesis `hc` says that the base change of
the homomorphism along `Spec (R ⧸ I) ⟶ Spec R` is central (`IsCentral`, from
[`Rational.Characters`](../Rational/Characters.md)). Groups over `Spec R` are
`GroupScheme (Spec R) = Grp (Over (Spec R))`, and `algSpec R` sends an `R`-algebra `C` to
`Spec C` as an object over `Spec R`.

## Main results

- `isCentral_of_isMultiplicativeType`: let `G, H` be group schemes over `Spec R` with
  `RelativeMultiplicativeType.IsMultiplicativeType G`, let `i : G ⟶ H` be a homomorphism,
  and let `I` be nilpotent. If the base change of `i` to `Spec (R ⧸ I)` is central, then `i`
  is central. `H` is arbitrary: no affineness, separatedness or finite-presentation
  hypothesis is made on it. This generalises the Library theorem
  `MultiplicativeTypeAffineInfinitesimalCentrality.isCentral_of_isMultiplicativeType`
  ([`Torus.MultiplicativeTypeAffineInfinitesimalCentrality`](MultiplicativeTypeAffineInfinitesimalCentrality.md)),
  which assumes `IsAffine H.X.left`.
- `isCentral`: the same conclusion for a homomorphism
  `u : (Diagonalizable.groupScheme R N).toGrp ⟶ H` out of the standard diagonalizable group
  `D(N)` of an arbitrary abelian group `N` in universe `u`.
- `isCentral_of_isDiagonalizable`: the same conclusion when the source is diagonalizable
  (`RelativeMultiplicativeType.IsDiagonalizable`).

## Conjugation and the reduction modulo `I`

Fix `u : D(N) ⟶ H`.

- `conj u x h` is the Library conjugation action `(AutomorphicAction.conjugation u).act x h`
  ([`AutomorphicAction`](../AutomorphicAction.md)) of a point `x` of `D(N)` on a point `h` of
  `H`, both over the same test object `T` over `Spec R`. `conj_eq` unfolds it to
  `u(x) * h * u(x)⁻¹`, and `conj_eq_self_iff` says `conj u x h = h` iff `u(x)` commutes with
  `h`.
- `commute_of_quotient`: if `Y` is an `R`-algebra in which `I` maps to zero, then `u(x)`
  commutes with `h` for all points `x, h` with values in `Spec Y`. The proof views `Spec Y`
  as a scheme over `Spec (R ⧸ I)`, transports `x` and `h` through the Library bijection
  `baseChangePointsEquiv` between points of a base change and points over the original
  base, applies `hc` there, and transports back.
- `conj_left_apply`: if `I` is nilpotent, then for every `R`-algebra `C` and points `x`, `p`
  with values in `Spec C`, the underlying maps of topological spaces of `conj u x p` and `p`
  agree. Write `J = I C`. The quotient map `C ⟶ C ⧸ J` induces a surjection
  `Spec (C ⧸ J) ⟶ Spec C` on points, because `J` lies in the nilradical
  (`PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical`). After composing with
  `Spec (C ⧸ J) ⟶ Spec C`, naturality of the action and `commute_of_quotient` make the two
  morphisms equal.

## Affine charts of the target

Let `φ : Spec B ⟶ H.X` be a morphism over `Spec R` from the spectrum of an `R`-algebra `B`
whose underlying scheme morphism is an open immersion.

- `chartPoint φ y` is the point `Spec C ⟶ Spec B ⟶ H.X` determined by an `R`-algebra map
  `y : B ⟶ C`. `chartPoint_injective` shows it is injective in `y`. `exists_chartPoint` shows
  that every point `Spec C ⟶ H.X` whose image lies in the image of `φ` has this form
  (`IsOpenImmersion.lift` and full faithfulness of `algSpec R`).
- `range_conj_subset`: by `conj_left_apply`, conjugation keeps a chart point inside the image
  of `φ`.
- `chartAct` therefore defines, for a character `t : Multiplicative N →* Cˣ` and a chart point
  `y`, the unique `chartAct t y : B ⟶ C` with
  `chartPoint φ (chartAct t y) = conj u (characterPoint t) (chartPoint φ y)`
  (`chartPoint_chartAct`). Here `CharacterAction.characterPoint t` is the point of `D(N)` given by
  `t` ([`Torus.AffineCharacterAction`](AffineCharacterAction.md)).
- `chartAction` packages `chartAct` as a `CharacterAction.Action` on `B`
  ([`Torus.CharacterActionGrading`](CharacterActionGrading.md)): an action of characters on
  `R`-algebra maps out of `B` that is unital, multiplicative and natural in `C`. Each law is
  checked after the injective map `chartPoint φ`, where it is the corresponding law of the
  Library conjugation action.
- `conj_chartPoint`: if `I` is nilpotent, then `chartAction` fixes every point, so
  conjugation fixes every chart point. Over algebras in which `I` maps to zero it fixes
  every point by `commute_of_quotient`. The Library theorem
  `CharacterAction.act_eq_of_nilpotent_quotient`
  ([`Torus.CharacterActionNilpotentRigidity`](CharacterActionNilpotentRigidity.md)) then
  shows that it fixes every point over every algebra.

## From charts to all points

- `hom_ext_of_affine`: two morphisms `f g : T ⟶ Y` over `Spec R` are equal if every point
  `z` of `T` has an open neighbourhood `U` such that `w ≫ f = w ≫ g` for all `R`-algebras `C`
  and all `w : Spec C ⟶ T` over `Spec R` with image in `U`. The proof chooses an affine open
  `W ⊆ U` containing `z`, gives `Γ(T, W)` the `R`-algebra structure of the composite
  `Spec Γ(T, W) ⟶ T ⟶ Spec R`, tests on `W.fromSpec`, and concludes with Mathlib's
  `Scheme.hom_ext_of_forall`.
- `conj_eq_of_range_subset`: conjugation fixes every point `p : Spec C ⟶ H.X` whose image lies
  in an affine open `V` of `H`. The chart is `V.fromSpec`, with the `R`-algebra structure on
  `Γ(H, V)` obtained in the same way. `p` is a chart point by `exists_chartPoint`, and every
  point of `D(N)` with values in `Spec C` is `characterPoint t` for some character `t`
  (`Corepresented.affinePointsEquiv`).
- `isCentral`: centrality of `u` says that, for every `x : T ⟶ D(N)`, every `a : T' ⟶ T` and
  every `h : T' ⟶ H.X`, the point `u(a ≫ x)` commutes with `h`. Equivalently,
  `conj u (a ≫ x) h = h`. This is checked with `hom_ext_of_affine`: near a point `z` of `T'`
  take the preimage under `h` of an affine open `V` of `H` containing `h(z)`. By naturality
  of the action, an affine test point `w` with image in that preimage gives the equation
  `conj u (w ≫ a ≫ x) (w ≫ h) = w ≫ h`, which is `conj_eq_of_range_subset` for `V`.

## Diagonalizable and multiplicative-type sources

- `isCentral_of_isDiagonalizable` transports `isCentral` through an isomorphism
  `d : D(L) ≅ G`. `IsDiagonalizable G` gives `G ≅ diagonalizable (Spec R) L`, the base change
  of the diagonalizable group over `ℤ`, and the Library's `Diagonalizable.baseChangeIso`
  identifies that base change with `Diagonalizable.groupScheme R L`. Centrality is preserved
  by precomposition with any homomorphism (`IsCentral.comp`). It is used for the reduced
  hypothesis of `d.hom ≫ i` and for `i = d.inv ≫ d.hom ≫ i`.
- `isCentral_baseChange_of_isDiagonalizable` and `isCentral_affineChart_of_isDiagonalizable`
  apply it after base change to an affine chart `Spec B ⟶ Spec R` over which the source is
  diagonalizable, with the nilpotent ideal `I B` (Library `isNilpotent_map`). The Library
  `isCentral_quotient_baseChange` supplies the reduced hypothesis. The two theorems have the
  same proofs as the Library theorems of the same names in
  `MultiplicativeTypeAffineInfinitesimalCentrality`, with the affine-target theorem replaced
  by `isCentral_of_isDiagonalizable`.
- `isCentral_of_isMultiplicativeType` has the same proof as the Library affine-target
  theorem. It chooses an fppf cover over which `G` is diagonalizable, then an affine open
  cover of each member. It proves centrality on each affine chart with the previous theorem,
  and descends it by two applications of `IsCentral.of_flatCover`.

## Scope

The base is affine and the thickening is `Spec (R ⧸ I) ⟶ Spec R` for a nilpotent ideal `I`.
The proof uses no finite-presentation hypothesis on the target. The general base, a closed
immersion with locally nilpotent ideal, is handled in
[`Torus.MultiplicativeTypeInfinitesimalCentralityProof`](MultiplicativeTypeInfinitesimalCentralityProof.md).
The module does not state SGA 3, IX, Proposition 3.8 for actions on arbitrary schemes. It
only uses the conjugation action of the source on the target.
