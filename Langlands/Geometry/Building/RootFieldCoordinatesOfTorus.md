# Root field coordinates when a maximal torus is the centralizer

This internal unit constructs the published structure
`RootFieldCoordinates i j s a` of the R1 statement
`QuasiSplitR1RootFieldCoordinatesStatement` in one case: the representative
`j` of the centralizer of the maximal split torus is itself a maximal torus
`T` of `G`, given as a commutative group scheme. The construction takes
two explicit structural inputs: a root datum of the split base change and the
absence of higher multiples of the root. It does not prove the R1 statement.

## Setting

Let `k` be a field, `L/k` a finite Galois extension, `G` an affine group
scheme over `k`, locally of finite type and smooth, `T` and `S` commutative
group schemes, `j : T.toGrp -> G` and `f : S -> T`. Write `i` for the
composite `CommGroupScheme.groupHom f ≫ j`.

## Conjugation by the centralizer

`conjugation_act_of_torusCentralizer` states that if `j` represents the
published all-test centralizer `torusCentralizer i`, conjugation along `j` by
every point of `T`, on every test scheme, fixes every point of `S` mapped
through `i`. The proof uses the published formula
`AutomorphicAction.conjugation_act` and the commutation in the definition of
the centralizer. This is the torus-fixing hypothesis of the published
`RelativeRoot.rootPointLieEquiv_act`.

`conjugation_rootPointLieEquiv_symm` assumes that `G` is connected reductive,
`j` is a maximal torus, `S` is split, `j` represents the centralizer, `T_L` is
split, `a` is a relative root with no higher multiples
(`RelativeRoot.HasNoHigherRoots`), and the Galois orbit of an actual root `β`
of `T_L` is the whole restriction fiber of `a`. Let `x` be in the root-orbit
field `E_β = rootOrbitField k L j β`. Map `x` to an original relative-weight
vector by the published `rootOrbitFieldWeightSpaceLinearEquiv`, and then to a
rational root point by the inverse of the published
`RelativeRoot.rootPointLieEquiv`. The theorem states that conjugation by
`j(z)`, for a rational point `z` of `T`, sends this root point to the root
point with coordinate `β(z_L) · x`. Here `β(z_L)` is the published
`rootOrbitCharacterValue`. The proof combines `rootPointLieEquiv_act` for the
conjugation action with the published
`conjugation_differential_rootOrbitFieldWeightSpaceEquiv`, and uses
injectivity of both equivalences.

## The coordinates

`rootFieldCoordinatesOfOrbit` builds `RootFieldCoordinates i j
(CommGroupScheme.groupHom f) a` under the hypotheses above, for a root `β` in
the restriction fiber of `a` whose orbit is that fiber. It also assumes that
`T` and `S` are affine. Its fields are as follows.

- The extension is `E_β`. It is finite over `k`, and separable because it
  lies in the Galois extension `L`.
- The coordinate isomorphism is the composite additive equivalence above,
  reinterpreted by `AddEquiv.toMultiplicativeLeft` as
  `Multiplicative E_β ≃* rootGroupPoints i a`.
- The character is the published `rootOrbitCharacter k L j β`. Its restriction
  property is `characterRestrict_rootOrbitCharacter`.
- The conjugation property is `conjugation_rootPointLieEquiv_symm`, after
  `rationalCharacterEval_rootOrbitCharacter` identifies the value of the
  character at `z_E` with `β(z_L)`.

`rootFieldCoordinatesOfTorus` removes the choice of root and of orbit
equality. In addition to the hypotheses above, it assumes that `T` is affine
and locally of finite type over `k`, `j` is a closed subgroup, `i` is a
maximal split torus, and `IsRootDatumOf j_L P` holds for some finite root
datum `P` of `T_L`. It chooses a root in the fiber from the published
`rootRestrictionFiber_nonempty`. It proves that its orbit is the whole fiber by
the published `rootOrbit_eq_restrictionFiber_of_torusCentralizer`. Affineness
of `S` follows from splitness.

## Scope

The centralizer representative is the maximal torus `T` itself, with its
commutative structure. Transport to an arbitrary representative `Z`, existence
of such a torus in a quasi-split group, existence of the root datum, and the
absence of higher multiples for indivisible roots with `2a` not a root are
separate obligations. All results are uniform in the universe and the
characteristic.
