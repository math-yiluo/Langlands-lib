# The character presheaf of a diagonalizable group is the constant presheaf

Namespace: `Langlands.GroupScheme.Cartier.DiagonalizableCharacters`.

For every scheme `S : Scheme.{u}` and every additive commutative group
`M : Type u`, in every universe `u`, this module constructs the canonical
natural isomorphism

```lean
charactersIso S M :
  characters (model S M) ≅ EtaleLocalSystem.constant S (AddCommGrpCat.of M)
```

Here:

- `model S M` is the abbreviation for the actual commutative diagonalizable model
  `(CommGroupScheme.baseChange (Gm.toSpecZ S)).obj
  (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) M)`. Its underlying
  group scheme is definitionally `RelativeMultiplicativeType.diagonalizable S M`.
- `characters (model S M)` is the Library's Cartier character presheaf on all
  schemes over `S`, with its actual pullback restriction maps.
- `EtaleLocalSystem.constant S (AddCommGrpCat.of M)` is the Library's constant
  abelian presheaf. Its sections over `T` are the locally constant functions
  `T.left → M`, through `EtaleLocalSystem.constantSections`.

No hypothesis on `S` is used: no connectedness, nonemptiness, reducedness,
normality, affineness or noetherian condition. Torsion in `M` and arbitrary
characteristic are allowed. The task is stated for finitely generated `M`, but
the construction needs no finiteness hypothesis on `M`, so the module states it
for every additive commutative group.

## Ingredients

- `Langlands.GroupScheme.Cartier.DiagonalizablePoints` provides the action
  `act` of characters on character-valued points, the evaluation characters
  `evalChar T m` (base changes of the monomial evaluation character
  `DiagonalizableCharacter.evalCharacter`), and `ofAct`.
- `Langlands.GroupScheme.Cartier.DiagonalizableRigidity` provides
  `toLocallyConstant χ : LocallyConstant T.left M`. Its value at `x` is the
  unique `m` such that `χ` restricts to `evalChar _ m` on some open
  neighbourhood of `x` (`IsEvalOn`, `charValue_eq_iff`).
- `Langlands.GroupScheme.Cartier.DiagonalizableGlue` provides
  `ofLocallyConstant f`. This is the character that acts on a point `t` over
  `V` by the unit glued from the units `t(f(v))`, using
  `Langlands.AlgebraicGeometry.LocallyConstantUnitPower.lcPow`.

## The two constructions are inverse

- `toLocallyConstant_ofLocallyConstant`: `toLocallyConstant (ofLocallyConstant f) = f`.
  At `x`, the restriction of `ofLocallyConstant f` to the open fibre
  `{y | f y = f x}` is `evalChar _ (f x)`, by
  `restrict_ofLocallyConstant_eq_evalChar`. Then `charValue_eq_iff` applies.
- `ofLocallyConstant_toLocallyConstant`: `ofLocallyConstant (toLocallyConstant χ) = χ`.
  By `act_ext`, it suffices to compare the actions on a point `t` over
  `V → T.left`. For `y ∈ V`, choose an open `U ∋ V.hom y` with
  `IsEvalOn χ U (charValue χ (V.hom y))`. On the open `V.hom ⁻¹ᵁ U` of `V`,
  `act_naturality` and `act_of_isEvalOn` show that `act χ V t` restricts to
  `t (ofAdd (charValue χ (V.hom y)))`. Then `eq_lcPow_of_cover` identifies
  `act χ V t` with the glued unit.

## The comparison

- `charactersEquiv M T : (characters (model S M)).obj (op T) ≃+ LocallyConstant T.left M`
  has forward map `toLocallyConstant` and inverse `ofLocallyConstant`
  (`charactersEquiv_apply`, `charactersEquiv_symm_apply`).
- `charactersIso S M` is `NatIso.ofComponents` of `charactersEquiv` composed
  with the inverse of `EtaleLocalSystem.constantSections`. Naturality is
  `toLocallyConstant_restrict` together with `EtaleLocalSystem.constantSections_map`.

## Component formulas

For `T : Over S`, `χ : (characters (model S M)).obj (op T)` and `m : M`:

- `constantSections_charactersIso_hom`:
  `constantSections S (AddCommGrpCat.of M) T ((charactersIso S M).hom.app (op T) χ) = toLocallyConstant χ`.
- `charactersIso_inv_app`: the inverse component sends a section `s` to
  `ofLocallyConstant (constantSections S (AddCommGrpCat.of M) T s)`.
- **Normalization**, `constantSections_charactersIso_hom_evalChar`: the
  evaluation character `evalChar T m` goes to the constant function
  `LocallyConstant.const T.left m`. Conversely, `charactersIso_inv_app_const`
  says the inverse sends the constant section `m` to `evalChar T m`.
- `constantSections_charactersIso_hom_eq_const_iff`: `χ` goes to the constant
  function `m` if and only if `χ = evalChar T m`.
- **Local characterization**, `constantSections_charactersIso_hom_apply_eq_iff`:
  the value at `x : T.left` of the function attached to `χ` is `m` if and only
  if there is an open `U ∋ x` with
  `(characters (model S M)).map (opensι T U).op χ = evalChar (opensOver T U) m`.
  Here `opensOver T U = Over.mk (U.ι ≫ T.hom)` and `opensι T U = Over.homMk U.ι`.
- **Restriction-compatible characterization**, `restrict_eq_evalChar_iff`: for
  `a : T' ⟶ T` over `S`,
  `(characters (model S M)).map a.op χ = evalChar T' m` holds if and only if
  `constantSections S (AddCommGrpCat.of M) T ((charactersIso S M).hom.app (op T) χ) (a.left x) = m`
  for every `x : T'.left`.

## Provenance

This is the classical identification of the character group of a
diagonalizable group: characters of `D_S(M)` over `T` are the locally constant
functions `T → M` (SGA 3, Exposé VIII, §1). The normalization sends the
monomial character `m` to the constant function `m`. The Lean route through
`act`, local rigidity and gluing of units is internal to this development.
