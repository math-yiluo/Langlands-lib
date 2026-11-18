# Local rigidity of characters of a diagonalizable group

Namespace: `Langlands.GroupScheme.Cartier.DiagonalizableCharacters`.

Let `S : Scheme.{u}` be any scheme and `M : Type u` any additive commutative
group. No finiteness hypothesis on `M` is used, and no hypothesis on `S`. For a
test scheme `T : Over S`, this module shows that every Cartier character `χ` of
the diagonalizable model `model S M = D_S(M)` over `T` is, Zariski-locally on
`T.left`, an evaluation character `evalChar _ m`. The exponent `m` is uniquely
determined near each point. This attaches to `χ` a locally constant function
`T.left → M`. The module builds on
`Langlands.GroupScheme.Cartier.DiagonalizablePoints`, which supplies `act`,
`evalChar` and their basic laws.

## Homomorphisms out of `ℤ`

- `zpowEquiv G : G ≃* (Multiplicative (ULift ℤ) →* G)` for a commutative group
  `G` sends `u` to `n ↦ u ^ n`. Built from Mathlib's `zpowersMulHom`.
- `zpowEquiv_apply_one`, `zpowEquiv_symm_apply`: the inverse evaluates at the
  generator `ofAdd (up 1)`.
- `multiplicativeULiftInt_hom_ext`: two homomorphisms out of
  `Multiplicative (ULift ℤ)` that agree on the generator are equal.
- `zpowEquiv_naturality`: compatibility with group homomorphisms.
- `addGroupFG_uliftInt`: `ULift ℤ` is a finitely generated additive group. It is
  a lemma, not a global instance, and is used locally.

## `𝔾_m` as `D(ℤ)`

For any scheme `X`:

- `gmDiagPoints X V` and `gmDiag X : (Gm X).toGrp ⟶ diagonalizable X (ULift ℤ)`
  form the homomorphism of group schemes that sends a unit `u` to the character
  `n ↦ u ^ n`. It is built with `homOfPoints`.
- `pointsEquiv_gmDiagPoints`, `gmDiagPoints_naturality`, `comp_gmDiag` describe
  it on points.

## A character as a homomorphism of diagonalizable groups

For `T : Over S` and a character `χ` over `T`:

- `testPointsEquiv_baseChangeIso_inv` relates `testPointsEquiv` to
  `RelativeMultiplicativeType.pointsEquiv` over `T.left` through the Library's
  isomorphism `diagonalizableBaseChangeIso T.hom M`.
- `toDiag χ : diagonalizable T.left M ⟶ diagonalizable T.left (ULift ℤ)` is
  `χ` transported along `diagonalizableBaseChangeIso` and
  `Gm.baseChangeIso`, followed by `gmDiag`.
- `pointsEquiv_toDiag`: on a point `s`, `toDiag χ` gives
  `zpowEquiv _ (act χ V (pointsEquiv T.left M V s))`.
- `act_eq_of_actsBy`: if `toDiag χ` acts on the points over `V` by
  precomposition with `g : ULift ℤ →+ M` (the Library predicate `ActsBy`),
  then `act χ V t = t (ofAdd (g (up 1)))` for every `t`.
- `zmulHom m : ULift ℤ →+ M` is `n ↦ n • m`. `zmulHom_apply_one` evaluates it at
  `up 1`.
- `toDiag_evalChar`: `toDiag (evalChar T m) = diagonalizableMap T.left (zmulHom m)`.
- `evalChar_injective`: if `T.left` is nonempty, then `m ↦ evalChar T m` is
  injective. The proof uses the Library's `diagonalizableMap_injective`.
  Residue-field points could not prove this, because of `p`-torsion in
  characteristic `p`.

## Open subschemes and local evaluation

For an open `U` of `T.left`:

- `opensOver T U := Over.mk (U.ι ≫ T.hom)`, the open subscheme as a scheme over
  `S`, and `opensι T U : opensOver T U ⟶ T := Over.homMk U.ι`.
- `opensLE T h` is the inclusion for `W ≤ U`. `opensLE_comp_opensι` says that
  composing it with `opensι T U` gives `opensι T W`.
- `IsEvalOn χ U m` (a `Prop`) means
  `(characters (model S M)).map (opensι T U).op χ = evalChar (opensOver T U) m`:
  the Cartier restriction of `χ` to `U` is the evaluation character at `m`.
- `isEvalOn_iff_act`: `IsEvalOn χ U m` holds if and only if
  `act χ ((Over.map U.ι).obj V) t = t (ofAdd m)` for every scheme `V` over `U`
  and every `t`.
- `act_of_isEvalOn`: if `IsEvalOn χ U m` holds, then
  `act χ V t = t (ofAdd m)` for every scheme `V` over `T.left` whose structure
  map has image in `U`.
- `IsEvalOn.mono` (shrinking the open), `IsEvalOn.restrict` (Cartier restriction
  along `a : T' ⟶ T` gives `IsEvalOn _ (a.left ⁻¹ᵁ U) m`), `IsEvalOn.add`,
  `isEvalOn_zero`, `isEvalOn_evalChar`.
- `IsEvalOn.unique` (**uniqueness**): if `IsEvalOn χ U m` and
  `IsEvalOn χ U' m'` hold and `x ∈ U ∩ U'`, then `m = m'`. The proof restricts
  to the nonempty open `U ⊓ U'` and applies `evalChar_injective`.
- `exists_isEvalOn` (**local existence**): every point `x` of `T.left` has an
  open neighbourhood `U` and an `m` with `IsEvalOn χ U m`. The proof applies
  the Library's local rigidity theorem `exists_opens_baseChange_map_eq` to
  `toDiag χ`, with target character group `ULift ℤ`. That theorem needs only the
  target to be finitely generated. Then `actsBy_of_transport` and
  `act_eq_of_actsBy` finish the argument.

## The locally constant function of a character

- `charValue χ x : M` is the exponent of `χ` near `x`, chosen from
  `exists_isEvalOn`.
- `charValue_spec`, `charValue_eq_of_isEvalOn`, and `charValue_eq_iff` give the
  local characterization:
  `charValue χ x = m ↔ ∃ U : T.left.Opens, x ∈ U ∧ IsEvalOn χ U m`.
- `isLocallyConstant_charValue` and `toLocallyConstant χ : LocallyConstant T.left M`,
  with `toLocallyConstant_apply`.
- `toLocallyConstant_add`, `toLocallyConstant_zero`: additivity.
- `toLocallyConstant_evalChar`: `toLocallyConstant (evalChar T m)` is the
  constant function `LocallyConstant.const T.left m`.
- `toLocallyConstant_restrict`: for `a : T' ⟶ T`, the function of the Cartier
  restriction of `χ` is `x ↦ toLocallyConstant χ (a.left x)`.

## Provenance

The mathematical statement is SGA 3, Exposé VIII, Corollary 1.3 (Gille–Polo
edition, version 1.1, pp. 3–4). For an arbitrary base `S` and an arbitrary
abelian group `M`, a character of `D_S(M)` is given by a unique locally
constant section of the constant sheaf `M_S`, so it is Zariski-locally a
monomial evaluation. This module proves that statement for the Library's model
of `D_S(M)`, with no finiteness hypothesis on `M` and no hypothesis on `S`.

The proof specializes the Library's local rigidity theorem
`exists_opens_baseChange_map_eq`, for homomorphisms `D_X(Λ) → D_X(Λ')`, to
the case `Λ' = ULift ℤ`. That theorem requires the character group `Λ'` of the
target to be finitely generated (`addGroupFG_uliftInt`). The source group `Λ`
may be arbitrary. No more general comparison is claimed here. In particular,
SGA 3, Exposé VIII, Corollary 1.5(a) identifies homomorphisms
`D_S(M) → D_S(N)` with locally constant functions to `Hom(N, M)` only when `N`
is finitely generated. In the character case `N = ℤ`.

The transport through `gmDiag`, the uniqueness argument via
`diagonalizableMap_injective`, and the packaging as `IsEvalOn`, `charValue`
and `toLocallyConstant` are internal to this development.
