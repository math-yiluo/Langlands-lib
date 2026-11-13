# Characters and homomorphisms of diagonalizable groups: proof

Worker 158.

`Langlands.GroupScheme.diagonalizableCharacter` proves
`Langlands.GroupScheme.DiagonalizableCharacterStatement.{u}`
(module `Langlands.GroupScheme.Torus.DiagonalizableCharacterStatement`) for every
universe `u`. It adds no hypotheses. The auxiliary declarations are in the
namespace `Langlands.GroupScheme.DiagonalizableCharacter`.

The statement follows Milne, *Algebraic Groups* (2017), Lemma 12.4 with the
sentence after it ("X(D(M)) ≃ M; the character attached to m is f ↦ f(m)") and
Theorem 12.9(a) (full faithfulness of M ⇝ D(M)). The statement's Markdown gives the
quotations. As in Milne, the key fact is that the group-like elements of `k[Λ]` are
exactly the monomials `m ∈ Λ`. The finite generation hypotheses `AddGroup.FG Λ` and
`AddGroup.FG Λ'` are not used: the proof works for every abelian group `Λ`.

Notation: `R` is a commutative ring, `D(Λ) = Diagonalizable.groupScheme R Λ`, and
`P U = Diagonalizable.characterPointsEquiv R Λ U` identifies points
`x : U ⟶ D(Λ).X` over a test scheme `U → Spec R` with characters
`Multiplicative Λ →* Γ(U, ⊤)ˣ`. Write `t(m)` for `t (Multiplicative.ofAdd m)`.

## Step 1: the evaluation character (Part 1, existence)

`evalPoints R Λ m U` sends a point `x` to the point of `𝔾_m` whose unit is
`P U x (ofAdd m)`, that is, `(Gm.pointsEquiv _ U).symm (P U x (ofAdd m))`. It is a
group homomorphism because `P U` and `Gm.pointsEquiv` are multiplicative
equivalences. `evalPoints_naturality` shows that it is natural in `U`, using
`Gm.pointsEquiv_naturality` and `Diagonalizable.characterPointsEquiv_naturality`.
So `homOfPoints` turns it into a homomorphism `D(Λ) ⟶ 𝔾_m`, which is the
character `evalCharacter R Λ m`. `evalCharacter_apply` is the identity required in
Part 1(a). It follows from `comp_homOfPoints`.

## Step 2: natural families of units and their universal value

The structure `NaturalUnits R Λ` packages what the remaining parts need. It is a
family of homomorphisms `app U : (U ⟶ D(Λ).X) →* Γ(U, ⊤)ˣ` that is natural in `U`:
`app U' (a ≫ x) = Units.map a.left.appTop (app U x)`.

- `NaturalUnits.ofCharacter χ` uses the values of a character χ,
  `x ↦ Gm.pointsEquiv _ U (x ≫ χ)`. It is multiplicative by `MonObj.one_comp` and
  `MonObj.mul_comp` (the homomorphism `CommGroupScheme.groupHom χ` is a monoid
  morphism) and natural by `Gm.pointsEquiv_naturality`.
- `NaturalUnits.ofHom f m'` uses the `m'`-th coordinate of a homomorphism
  `f : D(Λ) ⟶ D(Λ')`, `x ↦ P' U (x ≫ f)(m')`. It is multiplicative for the same
  reason and natural by `Diagonalizable.characterPointsEquiv_naturality`.

**Classifying maps.** `sectionsIso R Λ` is `Corepresented.affineSectionsIso` for
`R[Λ]`, the isomorphism `Γ(D(Λ)) ≅ R[Λ]`. `lift_characterPointsEquiv` shows that
`Diagonalizable.lift R Λ (P U x) = sectionsIso.inv ≫ Γ(x)`. In words, the algebra
map `R[Λ] → Γ(U)` that sends `single m 1` to `P U x (ofAdd m)` is the map on global
sections induced by `x`. The proof combines
`Corepresented.pointsEquiv_eq_affinePointsEquiv` at the identity of `R[Λ]`,
`Corepresented.affinePointsEquiv_map`, `Corepresented.pointsEquiv_naturality` and
`CorepresentableBy.homEquiv_comp` for `Diagonalizable.corepresentation`.
`lift_map` shows that changing coefficients along `g : B ⟶ C` composes `lift` with
`g`. It is proved with `AddMonoidAlgebra.algHom_ext` and `Diagonalizable.lift_single`.

**Value formula.** The universal value `c.value ∈ R[Λ]` is the image under
`sectionsIso.hom` of `c.app D(Λ).X (𝟙 _)`. `NaturalUnits.app_eq` states that
`c.app U x = lift (P U x) (c.value)` for every point `x`. The proof applies
naturality to `x = x ≫ 𝟙` and then uses `lift_characterPointsEquiv`.

**Multiplicativity of evaluation.** For an `R`-algebra `B` and a character
`s : Multiplicative Λ →* Bˣ`, `affinePoint B s` is the point of `D(Λ)` over
`Spec B` corresponding to `s`, transported along `toSections B`
(`Corepresented.affineSectionsIso B` inverted). It is multiplicative in `s`
(`affinePoint_mul`, `affinePoint_one`). The value formula gives `toSections_lift`:
`toSections B (lift s c.value) = c.app (Spec B) (affinePoint B s)`. Since
`toSections B` is injective (`toSections_injective`) and `c.app` is a homomorphism,
`NaturalUnits.lift_mul` and `NaturalUnits.lift_one` follow:
`lift (s * s') c.value = lift s c.value * lift s' c.value`, and
`lift 1 c.value = 1`.

## Step 3: the universal value is grouplike, hence a monomial over a field

`evaluate_eq_lift` identifies `CharacterAction.evaluate x t` with
`Diagonalizable.lift R Λ t` when the coefficient algebra is `R` itself (`baseAlg R`).
The proof is by induction on the element using `CharacterAction.evaluate_single`,
`Diagonalizable.lift_single`, and the fact that `x` is an `R`-algebra map.

`NaturalUnits.isGrouplike_value` shows that `c.value` satisfies
`CharacterAction.IsGrouplike` (in `Torus/Grouplike`):

- *Comultiplication.* Apply `lift_mul` over `B = R[Λ][Λ]` (`CharacterAction.algebra`
  twice) to the two characters `CharacterAction.universal` and
  `CharacterAction.mapCharacter constant (CharacterAction.universal)`. Each side
  becomes a `CharacterAction.evaluate` by `evaluate_eq_lift`. The product side is
  `CharacterAction.diagonalMap`. The other factors are
  `CharacterAction.constant` (by `CharacterAction.evaluate_comp` and
  `CharacterAction.evaluate_constant_universal`) and
  `CharacterAction.coefficientMap CharacterAction.constant` (by definition). This
  is the identity `Δ v = v ⊗ v`, up to commuting the factors.
- *Counit.* `lift_one` over `baseAlg R` gives `ε v = 1`.

`eq_single_of_isGrouplike` shows that over a field `k` a grouplike `v ∈ k[Λ]` is
`single m 1` for some `m`. By `CharacterAction.IsGrouplike.isIdempotentElem_coeff`
each coefficient is idempotent, so it is `0` or `1`
(`IsIdempotentElem.iff_eq_zero_or_one`). By
`CharacterAction.IsGrouplike.sum_coeff` the coefficients sum to `1`, so some
coefficient `v_m` is nonzero and equals `1`. By
`CharacterAction.IsGrouplike.coeff_mul_coeff_of_ne`, `v_n v_m = 0` for `n ≠ m`, so
every other coefficient vanishes.

## Step 4: core lemma

`characterPointsEquiv_val` writes `P U x (ofAdd m)` as `lift (P U x) (single m 1)`.
`lift_characterPointsEquiv_id` shows that `lift (P _ (𝟙 _)) = sectionsIso.inv`.
Together with the value formula they give `NaturalUnits.app_eq_iff`:
`c.app U x = P U x (ofAdd m)` holds for all `U` and `x` if and only if
`c.value = single m 1`. For the forward direction, evaluate at the universal point
and apply `sectionsIso.hom`.

`NaturalUnits.existsUnique` (over a field `k`) says that exactly one `m ∈ Λ`
satisfies `c.app U x = P U x (ofAdd m)` for all `U` and `x`. Existence follows from
Step 3 and `app_eq_iff`. For uniqueness, two such `m` give the same monomial
`single m 1`, and `AddMonoidAlgebra.single_left_injective` (with `1 ≠ 0` in `k`)
gives equality.

## Step 5: Part 1(b) and Part 2

**Part 1(b).** For a character χ, `(NaturalUnits.ofCharacter χ).existsUnique` is
the required unique existence.

**Part 2** (`restrictMap_bijective`). By
`Diagonalizable.pointsEquiv_restrictMap`, on points `restrictMap g` composes a
character with `g`: `P' U (x ≫ restrictMap g)(m') = P U x (ofAdd (g m'))`.

- *Injectivity.* If `restrictMap g₁ = restrictMap g₂`, then for each `l' ∈ Λ'` the
  family `NaturalUnits.ofHom (restrictMap g₁) l'` is evaluation at both `g₁ l'`
  and `g₂ l'`. The uniqueness in `existsUnique` gives `g₁ l' = g₂ l'`.
- *Surjectivity.* For `f : D(Λ) ⟶ D(Λ')`, `existsUnique` applied to
  `NaturalUnits.ofHom f m'` chooses `g m' ∈ Λ` for each `m' ∈ Λ'`. The map `g` is
  additive: the family for `a + b` is the product of the families for `a` and `b`,
  so by uniqueness `g (a + b) = g a + g b`. Then `restrictMap g` and `f` agree on
  all points: for each `T` and `x`, both characters `P' T (x ≫ _)` agree at every
  `l'`, and `P' T` is injective. So `hom_ext_points` gives `restrictMap g = f`.

The main theorem combines `evalCharacter`/`evalCharacter_apply`,
`NaturalUnits.ofCharacter`/`existsUnique` and `restrictMap_bijective`.

The module sets `backward.isDefEq.respectTransparency false` and
`maxHeartbeats 800000`.

## Published inputs

Library declarations used, with their modules:

- `Langlands.GroupScheme.Torus.Diagonalizable`: `Diagonalizable.groupScheme`,
  `Diagonalizable.algebra`, `Diagonalizable.functor`,
  `Diagonalizable.corepresentation`, `Diagonalizable.grpCorepresentation`,
  `Diagonalizable.lift`, and the theorem `Diagonalizable.lift_single`.
- `Langlands.GroupScheme.Torus.KernelDiagonalizable`:
  `Diagonalizable.characterPointsEquiv` and the theorem
  `Diagonalizable.characterPointsEquiv_naturality`.
- `Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat`:
  `Diagonalizable.restrictMap` and the theorem
  `Diagonalizable.pointsEquiv_restrictMap`.
- `Langlands.GroupScheme.Corepresented`: the theorem
  `Corepresented.affinePointsEquiv_map`.
- `Langlands.GroupScheme.CorepresentedPoints`: the theorem
  `Corepresented.pointsEquiv_naturality`.
- `Langlands.GroupScheme.CorepresentedAffineComparison`:
  `Corepresented.affineSectionsIso` and the theorem
  `Corepresented.pointsEquiv_eq_affinePointsEquiv`.
- `Langlands.GroupScheme.Multiplicative`: `Gm`, `Gm.pointsEquiv`, `homOfPoints`,
  and the theorems `Gm.pointsEquiv_naturality`, `comp_homOfPoints` and
  `hom_ext_points`.
- `Langlands.GroupScheme.Torus.Lattice`: `characterLattice`.
- `Langlands.AbelianScheme.GroupScheme`: `Langlands.CommGroupScheme.groupHom`.
- `Langlands.GroupScheme.Torus.CharacterActionGrading`:
  `CharacterAction.algebra`, `CharacterAction.constant`,
  `CharacterAction.universal`, `CharacterAction.mapCharacter`,
  `CharacterAction.evaluate`, `CharacterAction.coefficientMap`,
  `CharacterAction.diagonalMap`, and the theorem `CharacterAction.evaluate_single`.
- `Langlands.GroupScheme.Torus.Grouplike`: `CharacterAction.IsGrouplike` and the
  theorems `CharacterAction.evaluate_comp`,
  `CharacterAction.evaluate_constant_universal`,
  `CharacterAction.IsGrouplike.isIdempotentElem_coeff`,
  `CharacterAction.IsGrouplike.coeff_mul_coeff_of_ne` and
  `CharacterAction.IsGrouplike.sum_coeff`.

Except for `Langlands.CommGroupScheme.groupHom`, all of these are in the namespace
`Langlands.GroupScheme`. The proof also uses the Mathlib facts
`CategoryTheory.MonObj.one_comp`, `CategoryTheory.MonObj.mul_comp`,
`CategoryTheory.Functor.CorepresentableBy.homEquiv_comp`,
`AddMonoidAlgebra.algHom_ext`, `AddMonoidAlgebra.induction_linear`,
`AddMonoidAlgebra.single_left_injective` and `IsIdempotentElem.iff_eq_zero_or_one`.
The module imports the statement module, `Langlands.GroupScheme.Torus.Grouplike`
and `Langlands.GroupScheme.CorepresentedAffineComparison`.
