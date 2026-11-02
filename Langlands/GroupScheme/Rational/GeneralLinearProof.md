# Proof: the rational structure of `GL_n`

Author: Worker 1220. The generic-centralizer part uses the helper modules
`Langlands.GroupScheme.Rational.GeneralLinearCentralizer`,
`Langlands.GroupScheme.Rational.GeneralLinearLatticeCentralizer` and
`Langlands.GroupScheme.Rational.GeneralLinearGenericCentralizer` by Worker 176,
which have their own Markdown files.

This module proves

```lean
theorem Langlands.GroupScheme.generalLinearRationalStatement :
    GeneralLinearRationalStatement.{u}
```

where `GeneralLinearRationalStatement` is the statement of
`Langlands.GroupScheme.Rational.GeneralLinearStatement`: for every field
`k : Type u` and every `n : Type` with `Fintype n` and `DecidableEq n`, the
diagonal torus `i = GeneralLinear.diagonalTorus n (CommRingCat.of k)` is a
maximal split torus, its relative roots are the characters `e_a - e_b` with
`a ≠ b`, `HasRelativeRootSystem i` holds, and every generic cocharacter has
the torus centralizer as dynamic Levi subgroup. The auxiliary declarations
below are in the namespace `Langlands.GroupScheme.GeneralLinear`.

Throughout, `𝔻` denotes the split torus
`splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n)`, the
source of `i`, and `characterLatticeEquiv` denotes
`splitTorus.characterLatticeEquiv k (ULift.{u} n) : X*(𝔻) ≃+ (ULift n → ℤ)`,
which sends a character to its exponent vector.

## Sources

- Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
  - Example 21.6 (printed p.426, PDF p.442): the characters `χᵢ` of the
    diagonal torus of `GL_n`.
  - Example 21.36 (printed p.435, PDF p.451): the roots of `(GL_n, D_n)` are
    the characters `χᵢ − χⱼ`, `i ≠ j`.
  - Example 21.40 (printed p.436, PDF p.452): the permutation matrices
    normalize `D_n`, and `W(GL_n, D_n) ≃ Sₙ`.
  - 25.16–25.17 (printed p.549, PDF p.565): the relative root system and the
    identification of `N(k)/Z(k)` with its Weyl group.
  - Appendix C, C.15–C.16 and C.25: the root system of type `A_{n-1}` and its
    Weyl group `Sₙ` (the published module
    `Langlands.LinearAlgebra.RootSystemTypeA` records the exact locators).
- Borel and Tits, *Groupes réductifs* (1965), source ID
  `borel-tits-1965-groupes-reductifs`, SHA-256
  `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
  Printed page = PDF page + 53. 5.8 (printed p.98, PDF p.45): the relative
  root system and the relative Weyl group.

The argument is the standard computation for the split group `GL_n`; its
organization into the lemmas below is internal to this project.

## Imported results

- `isMaximalTorus_diagonalTorus` (module
  `Langlands.GroupScheme.Reductive.GeneralLinearMaximal`): `i` is a closed
  subgroup, and for every torus `T'`, closed subgroup `i' : T' ⟶ GL_n` and
  homomorphism `f : 𝔻 ⟶ T'` with `f ≫ i' = i`, `f` is an isomorphism.
- `roots_diagonalTorus` (module
  `Langlands.GroupScheme.Reductive.GeneralLinearRoots`): the roots of `i` are
  the characters with exponent vector `Pi.single a 1 - Pi.single b 1`,
  `a ≠ b`.
- From `Langlands.GroupScheme.Reductive.RootDatum`: the permutation action
  `permutationAction n k : Equiv.Perm n →* (X*(𝔻) ≃ₗ[ℤ] X*(𝔻))` and the lemma
  `characterLatticeEquiv_permutationAction`: the exponent vector of
  `permutationAction n k w χ` is `c ↦ (exponent vector of χ) ⟨w⁻¹ c.down⟩`.
- From `Langlands.GroupScheme.Reductive.GeneralLinearNormalizer`:
  `weylImage_le_range_permutationAction` (every Weyl action of a normalizing
  point is a permutation action). From
  `Langlands.GroupScheme.Reductive.GeneralLinearWeyl`: the normalizing points
  `permNormalizer k w` given by permutation matrices, with
  `weylAction_permNormalizer`.
- From `Langlands.GroupScheme.Torus.Maximal`: `normalizingAut`,
  `isNormalizingPoint_normalizingAut` and `weylAction_apply`.
- From the published `Langlands.LinearAlgebra.RootSystemTypeA`: the type-`A`
  root pairing `rootPairing` built from an injective linear map
  `Φ : V →ₗ[ℚ] (I → ℚ)` and elements `r p` with `Φ (r p) = e_{p.1} - e_{p.2}`
  spanning `V`, indexed by `Index I = {p : I × I // p.1 ≠ p.2}`, with
  `isRootSystem_rootPairing`, `rootPairing_toLinearMap`,
  `range_rootPairing_root`, `corootFun_r`, `permSubgroup`,
  `weylGroup_map_weightHom` and `perm_eq_one_of_rootVec_comp`.
- From the published `Langlands.LinearAlgebra.RationalSpan`: `toRat`,
  `ratAut`, `tensorEquivPi` and their evaluation lemmas.

## The implemented proof

### Maximality and relative roots

`isMaximalSplitTorus_diagonalTorus` takes the closed-subgroup property and
the maximality clause from `isMaximalTorus_diagonalTorus`; `𝔻` is split by
`isSplitTorus_splitTorus`, and a split subtorus `i' : T' ⟶ GL_n` has `T'` a
torus and `i'` a closed subgroup, so maximality among tori gives maximality
among split subtori.
`relativeRoots_diagonalTorus` is `roots_diagonalTorus`, because
`relativeRoots i` is by definition the set of roots of `i`.

### Rational coordinates

`ratCoord k = tensorEquivPi characterLatticeEquiv` is the linear isomorphism
`ℚ ⊗[ℤ] X*(𝔻) ≃ₗ[ℚ] (ULift n → ℚ)`; it makes the rational character space
finite-dimensional. `ratCoord_ratAut` shows, by induction on tensors, that an
automorphism of `X*(𝔻)` that permutes exponent vectors by `τ` acts on rational
coordinates by precomposition with `τ`. For `w : Equiv.Perm n`,
`ulPerm w : Equiv.Perm (ULift n)` is `c ↦ ⟨w⁻¹ c.down⟩`, and
`characterLatticeEquiv_permutationAction_comp` restates the imported lemma
with it. `exists_permutationAction_eq_weylAction` writes the Weyl action of
every normalizing point `m` as `permutationAction n k w`.

### The root system on the span of the relative roots

Let `V = relativeRootSpan i`. `spanCoord k : V →ₗ[ℚ] (ULift n → ℚ)` is
`ratCoord k` restricted to `V`, and it is injective. For
`p : Index (ULift n)`, `rootChar k p` is the character with exponent vector
`rootVecInt p.1.1 p.1.2`, and `relativeRoots_diagonalTorus_eq_range` shows
that the relative roots are exactly the `rootChar k p`. The element
`rootElt k p = 1 ⊗ rootChar k p` of `V` satisfies
`spanCoord k (rootElt k p) = rootVec p.1.1 p.1.2` (`spanCoord_rootElt`), and
`range_rootElt` identifies its range with the preimage in `V` of the images
`1 ⊗ α` of the relative roots, so the `rootElt k p` span `V`
(`span_range_rootElt`, from `Submodule.span_span_coe_preimage`).

`rootSystem k` is `rootPairing` for these data. It is a Mathlib
`RootPairing (Index (ULift n)) ℚ V (Module.Dual ℚ V)`; Mathlib in this
environment has no separate `RootSystem` structure, and the root-system
property is `isRootSystem_rootPairing`. `isCrystallographic_rootSystem`
computes every pairing `⟨r p, q^∨⟩` with `corootFun_r` as the integer
`rootVecInt p q.1 - rootVecInt p q.2`. `image_range_root_rootSystem` shows
that the roots of `rootSystem k`, viewed in `ℚ ⊗[ℤ] X*(𝔻)`, are the images
`1 ⊗ α` of the relative roots.

### The relative Weyl group

`spanCoord_relativeWeylAction_mk`: if `permutationAction n k w` is the Weyl
action of `m`, then the class of `m` acts on `V` by
`spanCoord k (relativeWeylAction i ⟦m⟧ x) = spanCoord k x ∘ ulPerm w`, by
`coe_relativeWeylAction_mk_apply` and `ratCoord_ratAut`.

`permSubgroup_eq_range_relativeWeylAction` proves that the subgroup of
`V ≃ₗ[ℚ] V` of maps acting on `spanCoord` coordinates by a permutation is the
range of `relativeWeylAction i`. A permutation `σ` of `ULift n` is
`ulPerm w` for `w = (permCongr ulift σ)⁻¹` and is realized by the class of
the permutation-matrix point `permNormalizer k w`; conversely every class is
the class of a normalizing point, whose Weyl action is a permutation action.
With `weylGroup_map_weightHom`, the image of the Weyl group of `rootSystem k`
in `GL(V)` is therefore the range of `relativeWeylAction i`.

`relativeWeylAction_diagonalTorus_injective`: let the class of `m` act
trivially and write its Weyl action as `permutationAction n k w`. Applying
`spanCoord_relativeWeylAction_mk` to every `rootElt k p` shows that
`ulPerm w` fixes every `rootVec a b`, so `ulPerm w = 1` by
`perm_eq_one_of_rootVec_comp`, hence `w = 1` and the Weyl action of `m` is
trivial. `mem_centralizerPoints_of_weylAction_eq_one` then shows that `m`
centralizes `i`: trivial Weyl action means that `(normalizingAut i m).inv`
composed with every character is that character; writing the identity of
`𝔻` as `∑ c, proj c ≫ single c` (`splitTorus.sum_proj_comp_single`) and
using that each `proj c` is a character gives
`(normalizingAut i m).inv = 𝟙 𝔻`, so `normalizingAut i m` is the identity
isomorphism and `isNormalizingPoint_normalizingAut` becomes membership in
`centralizerPoints i`. So the class of `m` is trivial in
`relativeWeylGroup i`.

`hasRelativeRootSystem_diagonalTorus` assembles these facts into
`HasRelativeRootSystem i` with index type `Index (ULift n)`, which is finite.

### Generic centralizers

The last part is Worker 176's
`dynamicCentralizer_diagonalTorus_of_isGeneric`: a cocharacter `ν` of `𝔻` is
generic exactly when its coordinates are pairwise distinct, and then the
dynamic Levi subgroup of `ν ≫ i`, which is block-diagonal for the partition of
the indices by the values of `ν`, is the diagonal subgroup, equal to
`torusCentralizer i`.

### The theorem

`generalLinearRationalStatement` combines
`isMaximalSplitTorus_diagonalTorus`, `relativeRoots_diagonalTorus`,
`hasRelativeRootSystem_diagonalTorus` and
`dynamicCentralizer_diagonalTorus_of_isGeneric`.

## Correspondence with the sources

The root system obtained is the root system of type `A_{n-1}` of Milne
Appendix C on the span of the `eᵢ − eⱼ`, matching Milne 21.36 and 21.40 for
`GL_n`; the relative Weyl group acts on it through the symmetric group by
permuting coordinates, and the identification with the Weyl group of the root
system is Milne 25.17 and Borel–Tits 5.8 in this case. The proof does not use
the general `RelativeRootSystemStatement` or `GenericCentralizerStatement`.

## Errata and boundary cases

The official Milne errata (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, Chapter 25, printed p.549)
flags a gap in the classical proofs of the general relative-root-system
assertion and points to CGP C.2.15 for a complete general proof. This module
constructs the type-A root pairing directly and identifies its Weyl action
using permutation matrices; it does not invoke those general proofs. The
same errata requires the parabolic in 25.6(b) to be minimal. The helper
modules cite the cocharacter-centralizer step as provenance and prove the
GL_n calculation directly from matrices and the published dynamic subgroup
calculation.

No nonemptiness or lower bound on the cardinality of `n` is assumed. For an
empty or one-element index type the root index type is empty and the root
span is zero. The root-pairing and permutation arguments include these
cases, and the genericity condition and distinct-weight calculation retain
their stated quantifiers.
