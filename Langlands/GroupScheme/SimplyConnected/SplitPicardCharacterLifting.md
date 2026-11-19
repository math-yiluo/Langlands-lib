# Character lifting from a Picard-trivial split reductive target

Worker 159, Task 7608. This module proves
`Langlands.GroupScheme.SplitCentralIsogenyPicardCharacterLiftingStatement.{u}`
as `Langlands.GroupScheme.splitCentralIsogenyPicardCharacterLifting`. Let `f : H ⟶ G` be a central isogeny
of connected reductive groups over a field `k`, where `H` and `G` each have a
split maximal torus. Suppose every line bundle on `G.X.left` is trivial. Then
every rational character of the full scheme-theoretic kernel `kernel f`
extends along `kernelι f` to a rational character of `H`. The proof uses only
the split maximal torus of `H` (see "Hypotheses used" below).

It adds no definitions of new mathematical objects. Its auxiliary
definitions, `gmIso` and `degreeHom`, are fixed identifications that the
proof uses.

## Source

The statement is the case `Pic(G) = 0` of the exactness at `X(Ker f)` in
Milne, *Algebraic Groups* (2017), Proposition 18.18, printed p. 391:

```text
0 → X(G) → X(H) → X(Ker f) → Pic(G) → Pic(H) → 0.
```

The paired statement Markdown, `SplitPicardInputsStatement.md`, explains this
specialization. Milne proves Proposition 18.18 from the Borel-subgroup exact
sequences of 18.15 and the snake lemma. The proof below does not follow that
route and does not construct the exact sequence. It takes an affine route
through the quotient `G = H / Ker f` by a diagonalizable group: line-bundle
triviality on `G` gives a homogeneous unit in the coordinate ring of `H`
(compare SGA 3, Exposé VIII, 4.1, 4.6 and 5.1 for the graded description of
such quotients). The unit becomes a character of `H` by Milne, Proposition
12.49 (printed p. 247): every regular map from a connected group variety to a
group of multiplicative type that sends the identity to the identity is a
homomorphism. In Lean this is `MultiplicativeTypePointedMapStatement`, which
assumes the source smooth, quasi-compact and connected; here it is applied to
`H`. Milne derives 12.49 from Proposition 12.48 (printed pp. 246–247), the
splitting of units on a product of irreducible varieties over an algebraically
closed field; that is the input used in the section "Main theorem" below. The
algebraic intermediate steps and their formulation are internal derived
content.

## Declarations

### Helpers (namespace `SplitPicardCharacterLifting`)

- `lineBundlesTrivial_of_isIso`: triviality of every line bundle transfers
  along an isomorphism of schemes `g : Y ⟶ X`. Pull a line bundle on `X` back
  to `Y`, trivialize it there, and descend the isomorphism with the published
  `LineBundle.isoOfPullbackIso` and `LineBundle.pullbackTrivialIso`.
- `exists_isUnit_mem_component`: let `c` be a strong grading of a
  commutative ring `A` by an abelian group `M`, and suppose every line bundle
  on the spectrum of the degree-zero ring is trivial. Then every degree `m`
  contains a unit of `A`. The component of degree `m` is invertible of rank
  one over the degree-zero ring (`invertible_component`,
  `rankAtStalk_component` from `StronglyGradedInvertible`). The published
  `nonempty_linearEquiv_of_lineBundlesTrivial_of_rankAtStalk_eq_one` makes it
  free, and `isUnit_of_linearEquiv` shows that its generator is a unit.
- `gmIso R`: the isomorphism from `𝔾_m` over `Spec R` to the diagonalizable
  group of `PUnit → ℤ`. It composes the published `splitTorus.gmIso` with the
  inverse of `Diagonalizable.splitIso` for the identity of `PUnit → ℤ`.
- `degreeHom m`: the additive map `(PUnit → ℤ) →+ N` sending the constant
  function `1` to `m`.
- `eq_degreeHom`: every additive map `q` out of `PUnit → ℤ` equals
  `degreeHom (q (fun _ => 1))`.
- `diagonalizable_source_ext`: two maps out of the scheme of a diagonalizable
  group agree if they agree after every character point
  `CharacterAction.characterPoint t`. Apply the hypothesis to the universal
  point, whose character point is the identity.

### The main construction

`exists_hom_comp_eq_restrictMap` assumes `MultiplicativeTypePointedMapStatement`
(Milne, Proposition 12.49: pointed maps from connected group varieties to groups
of multiplicative type are homomorphisms). Let
`H` be a smooth, quasi-compact, connected group scheme over `k` with affine
underlying scheme, and let `i` be a homomorphism from the diagonalizable group
of `N` to `H`. The coaction of translation by `i` grades the coordinate ring
`B` of `H` by `N`. Let `u` be a unit of `B` of degree `m`. Then there is a
homomorphism `ψ` from `H` to the diagonalizable group of `PUnit → ℤ` with
`i ≫ ψ = Diagonalizable.restrictMap k (degreeHom m)`.

The proof is as follows.

1. Let `e₀` be the identity point of `H`, as a `k`-algebra map `B → k`.
   Since `u` is a unit, `e₀ u ≠ 0`. Put `v = u * (e₀ u)⁻¹`. Then `e₀ v = 1`, `v`
   is a unit, and `v` has degree `m`, since scalars have degree zero
   (`coaction_scalar`, `mul_mem_component`).
2. The unit `v` defines the character `n ↦ v ^ n(PUnit.unit)` with values in
   `Bˣ`, hence a scheme map `φ` from `H` to the diagonalizable group of
   `PUnit → ℤ`. On a point `y : B ⟶ C` of `H`, `φ` is the character point of
   the character `n ↦ y(v) ^ n` (`characterPoint_mapCharacter`).
3. `φ` is pointed. The identity point is `e₀`, and `e₀ v = 1` makes the
   corresponding character trivial (`characterPoint_one`). The point scheme
   `Spec k` over `Spec k` maps isomorphically to the monoidal unit. So the
   pointed equation for this one point is the equation `η ≫ φ = η`.
4. The hypothesis `hR` (Milne 12.49), applied to the connected group variety
   `H` (smooth, quasi-compact and connected), gives a homomorphism `ψ` with the
   same underlying scheme map as `φ`. The diagonalizable target is of
   multiplicative type by `isMultiplicativeType_of_iso_diagonalizable`.
5. Check `i ≫ ψ = restrictMap (degreeHom m)` with `Grp.hom_ext` and
   `diagonalizable_source_ext`. Let `t` be a character of `N` with values in a
   `k`-algebra `C`. The point `characterPoint t ≫ i` of `H` is the translate of
   the identity point by `t` (`pointEquiv_ofTranslation_act`). On this point
   `v` takes the value `t m`, because `v` has degree `m` and `e₀ v = 1`
   (`act_eq_coaction_evaluate`, `evaluate_single`). So the character that `ψ`
   gives at this point is `t ∘ degreeHom m`. That is the value of
   `restrictMap (degreeHom m)` at `t` (`characterPoint_restrictMap`).

### Assembly

`splitCentralIsogenyPicardCharacterLifting_of_pointedMap` proves the target
statement from `MultiplicativeTypePointedMapStatement`. Take `H`, `G`, `f` and
a character `χ` of `kernel f`.

1. `H` and `G` have affine underlying schemes (`isAffine_of_isAffineHom`).
2. The kernel is diagonalizable. Let `j : T ⟶ H` be a split maximal torus. The
   range of `kernelι f` is central (`kernel_range_le_center`), central points
   centralize `T` (`center_le_torusCentralizer`), and the centralizer of `T` is
   its range (`maximalTorusCentralizer`). So `kernelι f` factors through `j`
   via `IsRepresentedBy.factorHom`. The factor is a closed subgroup of `T`
   (`IsClosedSubgroup.of_comp`), so it is the diagonalizable group of a
   finitely generated `N` by
   `exists_diagonalizableIso_of_isClosedSubgroup_splitTorus`. Write
   `e : kernel f ≅ D(N)` and `i' = e.inv ≫ kernelι f`.
3. `G` is the quotient by translation. `i'` is a closed subgroup
   (`IsClosedSubgroup.iso_comp`) with central, hence normal, range. The
   projection `CharacterAction.quotientHom i'` is an fppf quotient by the range
   of `i'` (`quotientHom_isFppfQuotient`). So is `f`, since its kernel range is
   the same (`SubgroupFunctor.range_iso_comp`). `FppfQuotientComparison.iso`
   identifies the quotient group with `G`. By `lineBundlesTrivial_of_isIso`,
   every line bundle on the quotient scheme is trivial. That scheme is the
   spectrum of the degree-zero ring of the translation grading.
4. Choose a unit. The translation grading is strong
   (`CharacterAction.isStrong_ofTranslation`). By
   `DiagonalizableCharacter.restrictMap_bijective`, the homomorphism
   `e.inv ≫ χ ≫ gmIso` is `restrictMap q₀` for a unique additive map
   `q₀ : (PUnit → ℤ) →+ N`. Let `m = q₀ (fun _ => 1)`, so that
   `q₀ = degreeHom m`. `exists_isUnit_mem_component` gives a unit of degree
   `m`, and `exists_hom_comp_eq_restrictMap` gives `ψ`.
5. The answer is the character `ψ ≫ gmIso.inv` of `H`. Since
   `kernelι f = e.hom ≫ i'`, its restriction to the kernel is
   `e.hom ≫ restrictMap q₀ ≫ gmIso.inv = e.hom ≫ e.inv ≫ χ ≫ gmIso.hom ≫ gmIso.inv = χ`.

### From Rosenlicht's tensor-unit statement

- `multiplicativeTypePointedMap_of_rosenlichtTensorUnits`: the published
  `Langlands.Algebra.RosenlichtTensorUnitsStatement.{u, u, u}` implies
  `MultiplicativeTypePointedMapStatement.{u}`. This only composes published
  reductions: `UnitsProduct.affine_splitting_of_domain_tensor_units`, then
  `UnitsProduct.geometric_reduction`, then
  `multiplicativeTypePointedMap_of_unitsProductDecomposition`.
- `splitCentralIsogenyPicardCharacterLifting_of_rosenlichtTensorUnits`: the
  target statement from `RosenlichtTensorUnitsStatement.{u, u, u}`.

### Main theorem

`splitCentralIsogenyPicardCharacterLifting` has type exactly
`SplitCentralIsogenyPicardCharacterLiftingStatement.{u}` and has no further
hypotheses. It applies
`splitCentralIsogenyPicardCharacterLifting_of_rosenlichtTensorUnits` to the
published proof `Langlands.Algebra.rosenlichtTensorUnits.{u, u, u}` (module
`Langlands.Algebra.RosenlichtTensorUnits`, Task 7617). That proof establishes
Rosenlicht's splitting of units in a tensor product of finite-type domains
over an algebraically closed field (Milne, Proposition 12.48).

## Hypotheses used

The proof uses that `H` is smooth, affine and connected, has a split maximal
torus, and has a self-centralizing maximal torus (`maximalTorusCentralizer`,
which needs `H` connected reductive). It uses that `f` is finite, flat,
surjective and locally of finite presentation with central kernel, that `G`
is affine, and that line bundles on `G` are trivial. The hypothesis that `G`
is connected reductive is used only to make `G` affine. The hypothesis that
`G` has a split maximal torus is not used. The kernel may be non-smooth.
