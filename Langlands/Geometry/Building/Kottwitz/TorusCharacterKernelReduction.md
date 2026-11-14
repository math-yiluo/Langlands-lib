# Reduction of the torus character-kernel theorem to the norm law

This module is a derived supporting construction for Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Lemma 11.1.3, printed p. 422,
PDF p. 453. It uses the norm characterization of the torus Kottwitz
homomorphism in Proposition 11.1.1, printed p. 421, PDF p. 452. The November
2024 corrections do not change these assertions.

## The reduction

`TorusCharacterKernelInputs` is the conjunction of two unconditional
propositions that must be proved separately:

- `TorusKottwitzExistenceStatement`, the Library form of KP Proposition 11.1.1
  for the torus Kottwitz homomorphisms;
- `NormalizedIntermediateValuationStatement`, the existence and uniqueness of
  the surjective integer normalization of the valuation on every finite
  extension `L` of `UnramifiedClosure F` inside `SeparableClosure F`.

The theorem `TorusCharacterKernelInputs.torusCharacterKernel` proves the exact
existing `TorusCharacterKernelStatement` from this conjunction. The module is a
conditional reduction. It proves neither the target unconditionally nor either
of the two inputs. The proof uses only two consequences of the inputs: that
`torusKottwitz F F T hT` satisfies the norm law `IsTorusKottwitzHom`, and that a
normalized valuation exists on the chosen splitting field. It needs neither
norm surjectivity, nor uniqueness, nor Galois equivariance.

## Route

KP prove the lemma from the split case and the maximal split quotient. The Lean
proof takes a different, more direct route, which needs the norm law at only one
splitting field. Let `K = UnramifiedClosure F`. Choose a finite Galois
extension `L/K` inside `SeparableClosure F` that splits `T`, and set
`n = |Gal(L/K)|`. For `t ∈ T(F)`, the relative norm from `L` to `K` of the
extension of `t` is `t^n`. The norm law at `L` therefore gives
`κ(t)^n = π(e(ω_L(t)))`, where `ω_L` is the split valuation for the normalized
valuation on `L`, `e` extends cocharacters of `T_L` to geometric cocharacters,
and `π` is the projection to the inertia coinvariants. Since `n > 0`, `κ(t)` is
torsion exactly when `π(e(ω_L(t)))` is torsion.

- If `t` lies in the character-valuation kernel, then `ω_L(t) = 0`, so `κ(t)^n = 1`.
- If `π(e(ω_L(t)))` is torsion, then for each rational character `χ` of `T`,
  the base change of `χ` to `SeparableClosure F` is inertia invariant. So its
  pairing with `e(ω_L(t))` vanishes, because that pairing factors through the
  torsion-free group `ℤ`. That pairing is the normalized order of `χ(t)` in `L`,
  so `χ(t)` has valuation one.

## Lemmas

The generic section proves `characterRestrict_baseChange_comp`. For base maps
`b`, `c` and `d` with `c ≫ b = d`, it says that restricting the base change
along `d` of a rational character, along any compatible group comparison, gives
the iterated base change. It rests on `compTestHom`, the identity comparison of
test objects, and `characterEval_comp_of_left_eq_id`. The lemma is proved over
variable morphisms and then instantiated, which keeps kernel conversion checks
between test objects cheap.

The tower section instantiates it as `characterRestrict_towerBaseChangeIso`
for a field tower `k ⊆ L ⊆ M`, and deduces its character-lattice form
`characterLattice_baseChange_tower`, where `commTowerIso` is the
commutative-group form of the tower comparison. It then proves
`latticePairing_extendGeometricCocharacters`: pairing a directly base-changed
character with an extended cocharacter equals the pairing over the
intermediate field. It also proves `relativeNorm_relativeExtend` (the
relative norm of an extended point is its power by the order of the Galois
group) and `towerBaseChangeIso_rationalExtend` (two-step extension of a
rational point, compared through the tower isomorphism, is the direct
extension). The instance `baseChanged_isAffine` records that base changes of
affine group schemes over fields have affine total spaces.

`latticePairing_baseChange_eq_zero_of_nsmul` proves the following. Let `H` be a
subgroup of the Galois group. If some nonzero multiple of a cocharacter's image
in the `H`-coinvariants vanishes, then the cocharacter pairs to zero with every
base-changed rational character. The pairing with such a character is Galois
invariant, so it factors through the coinvariants into `ℤ`.

The local section fixes a nonarchimedean local field `F`, an affine
commutative group scheme `T` over `F`, and a finite Galois extension `L` of
`UnramifiedClosure F` inside `SeparableClosure F` over which `T` splits.
The instance `intermediateField_isScalarTower_sepClosure` supplies the scalar
tower `F → L → SeparableClosure F`.

- `pow_card_eq_of_torusNormLawAt` is the identity `κ(t)^n = π(e(ω_L(t)))` for
  any homomorphism `κ` satisfying the norm law at `L`.
- `rationalExtend_mem_characterValuationKernel_unramified`,
  `rationalExtend_mem_characterValuationKernel_tower`,
  `map_rationalExtend_mem_characterValuationKernel_tower` and
  `rationalExtend_mem_characterValuationKernel_split` carry a point of the
  character-valuation kernel of `T(F)` into the character-valuation kernel over
  `L`. The steps are: the published descent theorem
  `characterValuationKernelDescent_proof` with
  `characterValuationKernel_eq_rationalCommonNormKernel`; extension from
  `UnramifiedClosure F` to `L` by `characterValuationKernel_le_comap`; and
  transport along the tower comparison by `map_characterValuationKernel_le`.
- `splitValuation_rationalExtend_eq_one`: for such a point, the split
  valuation over `L` with the normalized valuation is trivial. This is because
  every character value has normalized order zero.
- `mem_characterValuationKernel_of_isOfFinOrder`: if the projected extended
  split valuation of `t` has finite order, then `t` lies in the
  character-valuation kernel. This is the converse argument above. It uses that
  the normalized valuation is equivalent to the spectral valuation on `L`,
  which extends the valuation of `F`.

## Final theorem

The final theorem takes the two inputs, a nonarchimedean local field `F` and
an `F`-torus `T`. It chooses `L` with the published
`exists_finiteGaloisSplittingField_inside`, applied to the base change of `T`
to `UnramifiedClosure F`, and moves the splitting to the direct base change
along the tower comparison. It obtains the normalized valuation on `L` from the
second input, and the norm law for `torusKottwitz F F T hT` from the second
component of the first input. The two directions of the subgroup equality then
follow from `splitValuation_rationalExtend_eq_one` and
`mem_characterValuationKernel_of_isOfFinOrder`, as described above. The target
statement, its field, valuation and torsion conventions, and every module it
imports are unchanged.

The companion [norm-law reduction](TorusCharacterKernelNormLawReduction.md) retains the separately reviewed per-torus result for an arbitrary norm-law homomorphism and valuation equivalence. It reuses this module's common tower, pairing and input declarations.

The public `baseChanged_isAffine` instance delegates to `AffineCharacterTowerDescent.baseChanged_isAffine`, retaining its instance visibility.
