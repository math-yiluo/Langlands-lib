# Field coordinates on the quotient of a multipliable root group

Let `G` be a connected reductive group over a field `k`, with `f ≫ j : S → T → G` where `S` is
a split torus and `j : T → G` is a maximal torus split by a finite Galois extension `L/k`. Let
`a` be a nonzero character of `S` such that no `n • a` with `n ≥ 3` is a relative root of
`f ≫ j`. Let `C` be a commutator pairing of the root group `U_a` with quotient
`V = C.V = U_a / U_{2a}`. Let `β` be an absolute root of `j_L` whose Galois orbit is the
restriction fiber of `a` (hypothesis `horbit`), and let `E_β = rootOrbitField k L j β`.

This module identifies `V(k)` with `E_β`, `k`-linearly through the Lie algebra, such that
conjugation by `z ∈ T(k)` becomes multiplication by the root value `β(z)`. These are the data
`first` and `first_act`, and the linearity hypothesis `hfirst` of
`HeisenbergNormalForm.form_smul_left_of_lie`, that the field data of `HeisenbergUnitaryData`
(`Langlands.Geometry.Building.RootUnitaryHeisenbergAssembly`) and its separation variant
require.

Provenance: internal. The module composes two published comparisons:
`rootOrbitFieldWeightSpaceLinearEquiv` (`E_β ≃ₗ[k] 𝔤_a`,
`Langlands.GroupScheme.Lie.RootOrbitCharacterAction`) and
`DoubleRootCommutatorPairing.rootQuotientPointLieEquiv` (`V(k) ≃+ 𝔤_a`,
`Langlands.GroupScheme.Rational.RootQuotientLieEquiv`). The equivariance proof follows the
published R1 lemma `conjugation_rootPointLieEquiv_symm`
(`Langlands.Geometry.Building.RootFieldCoordinatesOfTorus`), with the quotient `V` in place of
the root group.

All declarations live in namespace `Langlands.Geometry.Building`. Throughout, `G.X → Spec k`
is affine, locally of finite type and smooth, `L/k` is finite Galois, and the representative
`U` of `U_a` and the quotient `V` are affine over `Spec k` (instance arguments; the Library's
`C.isAffineHom_V` supplies the one for `V`). The arguments are `hG` (connected reductive), `hj` (`j` a maximal
torus), `hS` (`S` split), `hT` (`T_L` split), `ha : a ≠ 0`, `hhigh` and `horbit`.

## Definition

- `quotientFieldEquiv k L f j C hG hj hS hT ha hhigh β horbit :
  Multiplicative E_β ≃* V(k)`. It is the additive equivalence
  `rootOrbitFieldWeightSpaceLinearEquiv … β horbit : E_β ≃ₗ[k] 𝔤_a` followed by the inverse of
  `C.rootQuotientPointLieEquiv hS ha hhigh : Additive V(k) ≃+ 𝔤_a`, turned into a
  multiplicative equivalence by `AddEquiv.toMultiplicativeLeft`. Here `𝔤_a` is
  `weightSpace (f ≫ j) a`.

## Theorems

- `rootQuotientPointLieEquiv_quotientFieldEquiv … x`: the comparison
  `C.rootQuotientPointLieEquiv` sends the point with field coordinate `x` to
  `rootOrbitFieldWeightSpaceLinearEquiv … x`.

  Proof. By definition the point is the image of that weight vector under the inverse
  comparison.

- `quotientFieldEquiv_smul … c x`: for `c ∈ k`, the weight vector (as an element of the Lie
  algebra of `G`) of the point with coordinate `c • x` is `c` times that of the point with
  coordinate `x`.

  Proof. By the previous theorem both sides are values of the `k`-linear map
  `rootOrbitFieldWeightSpaceLinearEquiv`.

- `quotientFieldEquiv_act … hfix z x`. Let `T.toGrp.X → Spec k` be affine, and let `hfix` say
  that conjugation by points of `T` fixes `f ≫ j`. Then for `z ∈ T(k)` and `x ∈ E_β`, the action
  of `z` on `V` by conjugation (`C.torusQuotientAction (AutomorphicAction.conjugation j) hfix`)
  sends the point with coordinate `x` to the point with coordinate
  `rootOrbitCharacterValue k L j β z' * x`. Here
  `z' = GaloisPointComparison.rationalCoeffEquiv k T.toGrp z`.

  Proof. `C.rootQuotientPointLieEquiv_act` says that the comparison `V(k) ≃+ 𝔤_a` carries the
  action of `z` to the differential of conjugation by `z`. By
  `conjugation_differential_rootOrbitFieldWeightSpaceEquiv`, that differential acts on the field
  coordinates as multiplication by `rootOrbitCharacterValue k L j β z'`. Both sides then have
  the same image under the injective comparison.

- `quotientFieldEquiv_act_character … hfix z x`: the same statement, now also assuming
  `T.toGrp.X.left` affine, with the root value written as
  `rationalCharacterEval (rootOrbitCharacter k L j β)
  (GaloisPointComparison.rationalExtend k E_β T.toGrp z)`. This is the form of the field
  `first_act` of `HeisenbergUnitaryData` for the character `rootOrbitCharacter k L j β`.

  Proof. Rewrite with `rationalCharacterEval_rootOrbitCharacter`.
