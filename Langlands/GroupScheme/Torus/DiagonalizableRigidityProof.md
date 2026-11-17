# Rigidity of families of homomorphisms between diagonalizable groups: proof

Worker 383.

`Langlands.GroupScheme.diagonalizableRigidity` proves
`Langlands.GroupScheme.DiagonalizableRigidityStatement.{u}` (module
[`Torus.DiagonalizableRigidityStatement`](DiagonalizableRigidityStatement.md); Milne,
*Algebraic Groups* (2017), Theorem 12.36) for every universe `u`. It adds no hypotheses.
The auxiliary declarations are in the namespace
`Langlands.GroupScheme.DiagonalizableRigidity`.

The proof uses fewer hypotheses than the statement provides. It does not use that `k` is a
field, the finite generation of `Λ` and `Λ'`, or that `X` is of finite type
(`LocallyOfFiniteType`, `QuasiCompact`). It does not use that `x₀` is a `k`-point, except to
form the constant `T`-point `toUnit T ≫ x₀`. The core theorem `eq_of_connected` holds over any
commutative ring `R`, for any abelian groups `Λ`, `Λ'` and any `X` over `Spec R` whose
underlying space is connected. Its conclusion is that `φ(x, g) = φ(x', g)` for any two
`T`-points `x`, `x'` of `X`. The proof does not follow Milne's route through finite subgroups
and density. Instead, each coordinate of the family is a natural family of units, and the
Library's group-like criterion applies to it on affine charts.

Notation: `P U = Diagonalizable.characterPointsEquiv R Λ U` identifies the points
`U ⟶ D(Λ).X` over a test scheme `U → Spec R` with characters
`Multiplicative Λ →* Γ(U, ⊤)ˣ`. `P'` is the same for `Λ'`. Write `χ(m)` for
`χ (Multiplicative.ofAdd m)`.

## Step 0: tools

- `eq_of_cover`: two global sections `a b : Γ(Y, ⊤)` are equal if their pullbacks along every
  member of an open cover of `Y` are equal. The proof views a section as a morphism
  `Y ⟶ 𝔸¹_ℤ` through `AffineSpace.toSpecMvPolyIntEquiv PUnit`. Morphisms that agree on an
  open cover are equal (`Scheme.Cover.hom_ext`), and
  `AffineSpace.toSpecMvPolyIntEquiv_comp` turns composition into pullback of sections.
- `resChar t χ` restricts a character `χ : Multiplicative Λ →* Γ(Y, ⊤)ˣ` along
  `t : Y' ⟶ Y`, by composing with `Units.map t.appTop`. `characterPointsEquiv_comp` states
  `P U' (a ≫ x) = resChar a.left (P U x)`. It is
  `Diagonalizable.characterPointsEquiv_naturality` (module
  [`Torus.KernelDiagonalizable`](KernelDiagonalizable.md)) for each `m`.

## Step 1: families of characters (`CharFamily`)

`CharFamily X Λ`, for a scheme `X` with no base, is a family of homomorphisms
`D(Λ) → 𝔾_m` parametrized by `X`, recorded on points. For each scheme `Y` and each
`y : Y ⟶ X` it has a monoid homomorphism
`app y : (Multiplicative Λ →* Γ(Y, ⊤)ˣ) →* Γ(Y, ⊤)ˣ` from the `Y`-points of `D(Λ)`
(as characters) to the units of `Γ(Y, ⊤)`. Naturality in `Y` says
`app (t ≫ y) (resChar t χ) = Units.map t.appTop (app y χ)`.

**Charts.** For a morphism `ρ : Spec A ⟶ X`, `chartUnits c ρ : NaturalUnits A Λ` is the
family `U ↦ c.app (U.hom ≫ ρ) ∘ P U` over `Spec A`. `NaturalUnits` is the structure of
[`Torus.DiagonalizableCharacterProof`](DiagonalizableCharacterProof.md). Naturality follows
from `characterPointsEquiv_comp`, `Over.w` and the naturality of `c`. By
`chartUnits_app_symm`, `chartUnits c ρ` evaluated at `P⁻¹ χ` is `c.app (U.hom ≫ ρ) χ`. The
Library gives the universal value `v = (chartUnits c ρ).value ∈ A[Λ]`. It is group-like
(`NaturalUnits.isGrouplike_value`), and `NaturalUnits.app_eq` expresses every value through
`v`. By `IsGrouplike.isIdempotentElem_coeff`, `IsGrouplike.coeff_mul_coeff_of_ne` and
`IsGrouplike.sum_coeff` (module [`Torus.Grouplike`](Grouplike.md)), the coefficients `vₙ` are
orthogonal idempotents with sum `1`.

**Acting by a character.** `ActsBy c m y` means that `c.app (t ≫ y) χ = χ(m)` for every
`t : Y' ⟶ Y` and every `χ`. In words, over `y` the family is evaluation at `m`.

- `actsBy_iff_value`: `ActsBy c m ρ ↔ v = single m 1`. This is the Library's
  `NaturalUnits.app_eq_iff`, after translating between points over `Spec A` and pairs
  `(t, χ)` with `chartUnits_app_symm`.
- `app_eq_sum` (expansion): for `t : Y ⟶ Spec A`,
  `c.app (t ≫ ρ) χ = ∑ₙ sectionMap t (vₙ) · χ(n)`. Here `sectionMap t : A →+* Γ(Y, ⊤)` is
  `(ΓSpecIso A).inv ≫ t.appTop`. The proof is `NaturalUnits.app_eq` followed by
  `AddMonoidAlgebra.lift_apply'`.
- `actsBy_of_sectionMap`: if `sectionMap t (vₘ) = 1`, then `ActsBy c m (t ≫ ρ)`. For `n ≠ m`,
  orthogonality gives `vₙ vₘ = 0`, so `sectionMap t (vₙ) = 0`. Pulling back further along
  `t'` composes `sectionMap` with `t'.appTop`. So the expansion reduces to its `m`-th term
  (`Finsupp.sum_eq_single`), which is `χ(m)`.
- `exists_coeff_notMem`: for every prime `p` of `A` some `vₘ` is not in `p`, because the
  coefficients sum to `1`.

## Step 2: the locus of a character is open and closed

`Locus c m : Set X` is the set of points `x` with
`ActsBy c m (X.fromSpecResidueField x)`.

- `mem_locus_of_chart`: let `ρ : Spec A ⟶ X` be an open immersion and `p` a prime with
  `vₘ ∉ p`. Then `ρ p ∈ Locus c m`. The morphism `X.fromSpecResidueField (ρ p)` has range
  `{ρ p}` (`Scheme.range_fromSpecResidueField`), so it factors through `ρ`
  (`IsOpenImmersion.lift`) as `Spec.map β` for some ring map `β : A ⟶ κ(ρ p)`. The closed
  point of `Spec κ(ρ p)` maps to `p`, by `Scheme.fromSpecResidueField_apply` and injectivity
  of `ρ`. So `β(vₘ) ≠ 0`. Since `β(vₘ)` is an idempotent of a field, `β(vₘ) = 1`. By
  `Scheme.ΓSpecIso_inv_naturality`, `sectionMap (Spec.map β) = β`, and
  `actsBy_of_sectionMap` gives the claim.
- `eq_of_mem_locus` (disjointness): if `x ∈ Locus c m ∩ Locus c n`, then
  `actsBy_iff_value` over the chart `Spec κ(x) ⟶ X` gives `single m 1 = single n 1` in
  `κ(x)[Λ]`. So `m = n` (`AddMonoidAlgebra.single_left_injective`).
- `exists_mem_locus` (cover): every point lies in the image of a chart of
  `X.affineOpenCover`, and some coefficient is outside the corresponding prime.
- `isOpen_locus`: let `x ∈ Locus c m`, and write `x = ρ p` for a chart `ρ` of
  `X.affineOpenCover`. Some `vₙ ∉ p`, so `x ∈ Locus c n`, and disjointness gives `n = m`. The
  image under `ρ` of the basic open set `D(vₘ)` is an open neighbourhood of `x`
  (`IsOpenEmbedding.isOpenMap`). It lies in `Locus c m` by `mem_locus_of_chart`.
- `isClosed_locus`: the complement of `Locus c m` is a union of the other loci, which are
  open. This uses the cover and disjointness.

## Step 3: rigidity for one family of characters

- `actsBy_of_locus`: suppose `Locus c m` is all of `X`, and let `ρ : Spec A ⟶ X` be an open
  immersion. Then `vₘ` is a unit. Otherwise it lies in a maximal ideal `P`. Some `vₙ ∉ P`,
  so `ρ P ∈ Locus c n`, and disjointness gives `n = m`, a contradiction. An idempotent unit
  is `1`, so `actsBy_of_sectionMap` with `t = 𝟙` gives `ActsBy c m ρ`.
- `app_eq_of_locus`: if `Locus c m` is all of `X`, then `c.app y χ = χ(m)` for every
  `y : Y ⟶ X`. Pull `X.affineOpenCover` back along `y`. On the `j`-th piece, naturality of
  `c` (with `Scheme.Cover.pullbackHom_map`) and `actsBy_of_locus` for the chart
  `X.affineOpenCover.f j` give the equality after restriction. `eq_of_cover` concludes.
- `CharFamily.exists_app_eq`: if `X` is connected, there is one `m ∈ Λ` with
  `c.app y χ = χ(m)` for all `y` and `χ`. `X` is nonempty, and a point `x` lies in some
  `Locus c m`. This locus is open, closed and nonempty, so it is all of `X`
  (`IsClopen.eq_univ`). Then `app_eq_of_locus` applies.

## Step 4: from `φ : X ⊗ G.X ⟶ H.X` to families of characters

Fix isomorphisms `eG : G ≅ D(Λ)` and `eH : H ≅ D(Λ')`, obtained from the `Nonempty`
hypotheses.

- `pointHom eG eH φ hφ x`: for `x : T ⟶ X` this is the homomorphism
  `(T ⟶ D(Λ).X) →* (T ⟶ D(Λ').X)` given by `g ↦ lift x (g ≫ eG⁻¹) ≫ φ ≫ eH`. It is
  multiplicative by `hφ` and `MonObj.mul_comp`, since `eG⁻¹` and `eH` are morphisms of group
  objects. `pointHom_comp` states `pointHom (a ≫ x) (a ≫ g) = a ≫ pointHom x g`, by
  `comp_lift`.
- `family eG eH φ hφ l : CharFamily X.left Λ`, for `l ∈ Λ'`, is the `l`-th coordinate. A
  morphism `y : Y ⟶ X.left` makes `Y` a scheme over `Spec R` through `y ≫ X.hom`, and the
  family sends `χ` to `P'(pointHom (Over.homMk y) (P⁻¹ χ))(l)`. It is multiplicative because
  `P`, `P'` and `pointHom` are. Naturality follows from `pointHom_comp` and
  `Diagonalizable.characterPointsEquiv_naturality`.
- `family_app`: for `x : T ⟶ X` and `g : T ⟶ G.X`,
  `P'_T(lift x g ≫ φ ≫ eH)(l) = (family l).app x.left (P_T(g ≫ eG))`. The proof factors `x`
  through `Over.homMk x.left` by the identity of `T.left`, and then uses `pointHom_comp` and
  `eG.hom_inv_id`.

## Step 5: conclusion

- `eq_of_connected`: assume `[ConnectedSpace X.left]`, and let `x x' : T ⟶ X` and
  `g : T ⟶ G.X`. Then `lift x g ≫ φ = lift x' g ≫ φ`. For each `l ∈ Λ'`,
  `CharFamily.exists_app_eq` gives `m` with `(family l).app y χ = χ(m)` for all `y` and `χ`.
  By `family_app`, the `l`-th coordinates of `P'_T(φ(x, g) ≫ eH)` and
  `P'_T(φ(x', g) ≫ eH)` are both `P_T(g ≫ eG)(m)`. Since `P'_T` is injective,
  `φ(x, g) ≫ eH = φ(x', g) ≫ eH`. Composing with `eH⁻¹` (`eH.hom_inv_id`) gives the claim.
- `diagonalizableRigidity`: given the data of the statement, take the isomorphisms from
  `hG` and `hH`, and apply `eq_of_connected` with `R = CommRingCat.of k` and
  `x' = toUnit T ≫ x₀`.

## Related Library results

- [`Torus.HomFamilyRigidity`](HomFamilyRigidity.md) proves a similar rigidity for split tori.
  Families there are given on points. Its proof also uses idempotent coefficients on a
  connected base.
- [`Torus.DiagonalizableCharacterProof`](DiagonalizableCharacterProof.md) supplies
  `NaturalUnits`, its universal value and the criterion `NaturalUnits.app_eq_iff`.
