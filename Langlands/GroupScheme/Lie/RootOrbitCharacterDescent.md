# Actual root characters over root-orbit fields

This internal unit descends a split root to an actual character over its
root-orbit field. Let `L/k` be a field extension, `T` a commutative group
scheme over `k` and `β` an actual root of the split base change `T_L` for
`j : T -> G`. The unit builds an actual rational character of the base change
of `T` to the published stabilizer field `rootOrbitField k L j β`, written
`E_β`. Its base change to `L` is `β`. The unit gives its values at rational
points and its restriction along a homomorphism `S -> T`. It applies the
tower descent `AffineCharacterTowerDescent.fixedDescend` to the root, viewed
as a character of the base change.

## Base-changed characters

`baseChangedCharacter k L T χ` is a character `χ` of the commutative group
scheme `T_L`, regarded as a rational character of the group scheme
`GaloisPointComparison.baseChanged k L T.toGrp`, by the published identity
`rationalCharacters.equivCharacterLattice`.

`affineBaseChangeEquiv_pointE` states that for an `L`-algebra `D`, the
published `Lie.affineBaseChangeEquiv` undoes the coefficient comparison
`pointE` from points of `T` over `D` to points of the base change.
`valueE_baseChangedCharacter` states that the value `valueE` of
`baseChangedCharacter k L T χ` at a point `y` is the actual character value
`Lie.characterValue χ` at `pointE y`. This holds by definition.
`rationalCharacterEval_baseChangedCharacter` states that at the extension
`z_L` of a rational point `z` of `T`, the rational value of the base-changed
character is `χ` evaluated at the published `rationalBaseChangePoint` of `z`.

## Galois transport of universal tensor values

Let `k -> E -> L` be a scalar tower of fields and assume `T` is affine.
`tensorConjTest T E σ` is the published coefficient action
`AffineCharacterTowerDescent.tensorConj` of `σ` in `Aut(L/E)` on
`L ⊗[k] Coord T`. It is regarded as an `L`-algebra map into the published
Galois-twisted test algebra `Lie.GaloisTestAlgebra` of `σ`, viewed as an
automorphism over `k`. `tensorValue_baseChangedCharacter` states that the
universal tensor value of a base-changed character is its actual value at the
universal tensor point. This holds by definition.

`affineMap_tensorConjTest` states that the coefficient action carries the
universal point of the base change to its twisted test point
`Lie.galoisTestPoint`. The proof is injectivity of `Lie.affineBaseChangeEquiv`.
Over the original base, both sides are the universal tensor point
`tensorPoint`, because the coefficient action fixes `1 ⊗ a`.

`tensorConj_tensorValue_baseChangedCharacter` states that the coefficient
action of `σ` sends the universal tensor value of `χ` to the universal tensor
value of the canonical Galois transport
`characterLattice.galoisRepresentation k L T σ χ`. The proof combines the
naturality `CoordinateWeights.characterValue_affineMap` along
`tensorConjTest`, the previous point equality, and the published
`Lie.characterValue_galoisRepresentation`.

## The root-orbit character

Now let `j : T.toGrp -> G` be an actual homomorphism into an affine group
scheme, with `L/k` finite. `galoisRepresentation_rootOrbitField` states that
every automorphism of `L` over `E_β` fixes `β` under the canonical Galois
transport. The proof uses Mathlib's
`IntermediateField.fixingSubgroup_fixedField`: the fixing subgroup of the
fixed field of the stabilizer of `β` is that stabilizer. If `T` is affine,
`tensorConj_tensorValue_root` therefore states that the universal tensor value
of `β` is fixed by `Aut(L/E_β)`.

Assume further that `L/k` is Galois. Then `L/E_β` is Galois.
`rootOrbitCharacter k L j β` is the published `fixedDescend` of the
base-changed root. It is an actual rational character of
`GaloisPointComparison.baseChanged k E_β T.toGrp`.

- `valueE_rootOrbitCharacter` states that at a point `y` of `T` over `L`, its
  value is `β` at `pointE y`.
- `rationalCharacterEval_rootOrbitCharacter` states that at the extension to
  `E_β` of a rational point `z` of `T`, its rational value is the published
  field element `rootOrbitCharacterValue k L j β` at
  `GaloisPointComparison.rationalCoeffEquiv k T.toGrp z`, which is `β(z_L)`.
- `characterRestrict_rootOrbitCharacter` states that if `β` lies in the
  published `rootRestrictionFiber k L j f a` of a homomorphism `f : S -> T` of
  commutative group schemes and an original character `a` of `S`, and `S` is
  affine, then its restriction along the base change of `f` to `E_β` is the
  base change of `a`. The proof applies `characterRestrict_fixedDescend`. The
  fiber equation over `L` is the needed restriction identity.
- `characterNormOrder_rootOrbitCharacter` applies the published
  `IntegerValuation.characterNormOrder_eq_eval` to this restriction. For a
  valuation `v` of `k` with values in `ℤₘ₀`, assume that the published
  `Cartan.restrictionEvaluation` along `f` is bijective. Then the
  degree-normalized order of the norm of the root-orbit character at a
  rational point `z` of `T` is the pairing of `a` with the published integer
  centralizer valuation of `z`.

The value lemma over `L` sets `maxRecDepth` to `4000` for elaboration.

## Scope

The unit gives no further construction for multipliable roots. It does not
identify the torus with the centralizer used in the R1 statement, and it gives
no root-group point coordinates. The R1 and R2 assemblies and apartment
existence remain separate obligations. All results are uniform in the
universe and the characteristic.
