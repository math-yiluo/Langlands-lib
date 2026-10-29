# Dual-homomorphism functoriality of the actual finite Weil pairing

`Langlands.AbelianScheme.relativeFiniteWeilFunctoriality` proves the published
proposition `Langlands.AbelianScheme.RelativeFiniteWeilFunctorialityStatement.{u}`
from module `Langlands.AlgebraicGeometry.Picard.FiniteWeilFunctorialityStatement`.
The theorem's type is that proposition itself. It adds no outer hypotheses, and
the statement pair and everything it imports are unchanged.

For every quasi-separated `S`, actual abelian schemes `A` and `B` with the seven
dual-constructor propositions, `HasDualScheme` witnesses, inverse Poincaré
bundles `MA`, `MB` and their evaluation isomorphisms, every homomorphism
`f : A ⟶ B` and every `n : ℕ`, it proves the equality of scheme morphisms

```text
prod.map f[n] (𝟙 _) ≫ finiteWeilPairing … hB MB evaluationB n =
  prod.map (𝟙 _) fᵛ[n] ≫ finiteWeilPairing … hA MA evaluationA n
```

where `f[n] = Tate.kernelLevelMap (groupHom f) n` and
`fᵛ[n] = Tate.kernelLevelMap (CommGroupScheme.groupHom df) n` with
`df = dualCommGroupSchemeMapFromEvaluation … f`. On `T`-valued points this is
`e_(B,n)(f[n](x), y) = e_(A,n)(x, fᵛ[n](y))`. The hypothesis `0 < n` of the
statement is not used. The proof is an equality in `Over S`, valid on all test
schemes, including nonreduced ones; no geometric-point argument is involved.

## Implemented proof

The mathematical content is the route of Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, Proposition (11.21)(i): the character attached to the dual
image `fᵛ(y)` is the character attached to `y` precomposed with the restriction
of `f` to the kernels. The Lean proof establishes this over a general base for
the Library's actual Poincaré-derived characters. It proves it first for an
arbitrary commutative square of homomorphisms and then specializes to
multiplication by `n`.

The module sets `maxHeartbeats` to `800000` and the three `backward.*`
transparency options used by the neighbouring finite-Weil modules.

### Section `Square`: kernel translation along a commutative square

Fix homomorphisms `g : A ⟶ A₂`, `h : B ⟶ B₂`, `f : A ⟶ B`, `f₂ : A₂ ⟶ B₂` with
`w : g ≫ f₂ = f ≫ h`. Write `hFSM` for `homFamilySpaceMap`.

- `homFamilySpaceMap_square`: the family maps form a commutative square over
  every test scheme `T`, by `homFamilySpaceMap_comp` and `w`.
- `relativeUnitsPullback_homFamilySpaceMap`: pulling base units back to `B_U`
  and then along `(hFSM f).app U` gives the base units pulled back to `A_U`.
  It follows from `homFamilySpaceMap_fst` on global sections.
- `squareKernelTrivialization`: for a module `N` on the `B₂`-family over `T`
  and a trivialization `β` of `(hFSM h).app T ^* N`, the trivialization of
  `(hFSM g).app T ^* (hFSM f₂).app T ^* N` obtained as
  `squarePullbackIso … N ≪≫ (pullback s).mapIso β ≪≫ pullbackUnitIso s`
  with `s = (hFSM f).app T`.

Now let `φ` map the kernel of `g` to the kernel of `h` with
`hφ : φ ≫ kernelι_h = kernelι_g ≫ f`.

- `kernelShear_square`: kernel translation by `k` on the `A`-family, followed by
  `(hFSM f).app T`, equals `(hFSM f).app U` followed by kernel translation by
  `k ≫ φ` on the `B`-family. Proof: `shear_homFamilySpaceMap` and `hφ`.
- `kernelTranslationAut_square`: the transported kernel action defined from
  `squareKernelTrivialization β` equals the pullback along `(hFSM f).app U`
  (`structureAutPullback`) of the kernel action of `k ≫ φ` defined from `β`.
  Both sides are `equalCompositeUnitAut` automorphisms. The published
  `equalCompositeUnitAut_square` rewrites the left side as the automorphism for
  the composites with `s`. By `(hFSM f).naturality a` and `kernelShear_square`
  these composites are `(hFSM f).app U` precomposed with the maps on the
  `B`-side. Then `equalCompositeUnitAut_precomp` identifies the result with the
  pullback of the target automorphism.
- `kernelTranslationScalar_square`: the corresponding global scalars agree up
  to `Units.map` along `(hFSM f).app U`, by `structureAutScalar_pullback`.
- `kernelTranslationUnit_square`: the descended units on `U` are equal. Both
  sides are compared after `relativeUnitsPullback` to `A_U`, which is injective
  (`relativeUnitsPullback_injective`), using
  `relativeUnitsPullback_kernelTranslationUnit` and
  `relativeUnitsPullback_homFamilySpaceMap`.

For a commutative group-scheme map `Φ` between the kernel group schemes with
`hΦ` as above:

- `intrinsicKernelCharacterHom_square`: the intrinsic character homomorphism of
  `g` for `squareKernelTrivialization β` equals the base change of `Φ` followed
  by the intrinsic character homomorphism of `h` for `β`. Equality is checked
  on points (`hom_ext_points`, then injectivity of `Gm.pointsEquiv`).
  `intrinsicKernelCharacterHom_points` and `baseChangePointsEquiv_comp` reduce
  it to `kernelTranslationUnit_square`.
- `intrinsicKernelCharacter_square`: the intrinsic kernel characters satisfy
  `χ_g = (Cartier.charactersMap Φ).app (op T) χ_h`. This follows by injectivity
  of `Cartier.characterHomEquiv` and `Cartier.characterHomEquiv_precompose`.

### Section `Dual`: the dual-kernel character along a square

- `dualKernelCharacter_congr`: `dualKernelCharacter` depends only on the dual
  point, not on the proof that it lies in the kernel (by `subst`).
- `dualPointFamily_dualSchemeMap_nonempty`: the Poincaré representative of
  `p ≫ dualSchemeMap … f₂` is isomorphic, as a rigidified line bundle, to the
  homomorphism pullback `(homFamilyPullback f₂ T).obj` of the representative of
  `p`. The published `dualPointClass_dualSchemeMap` gives equality of classes,
  and `Quotient.exact` gives the isomorphism.
- `dualKernelCharacter_square`: for `p : T ⟶ Bᵛ₂` in the kernel of `hᵛ` and its
  image `p ≫ f₂ᵛ` in the kernel of `gᵛ`,
  `dualKernelCharacter … g … (p ≫ f₂ᵛ) = charactersMap Φ (dualKernelCharacter … h … p)`.
  The left side is computed by `dualKernelCharacter_eq_of_iso`, with the
  isomorphism of the previous lemma (forgotten to modules) and the
  trivialization `squareKernelTrivialization (dualKernelPullbackModuleIso …)`.
  The right side is computed by `dualKernelCharacter_eq_intrinsic` with
  `dualKernelPullbackModuleIso …`. Then `intrinsicKernelCharacter_square`
  applies.

### Section `Application`: multiplication by `n`

- `multiplication_comp_hom`: `multiplication A n ≫ f = f ≫ multiplication B n`,
  from `GroupScheme.multiplication_naturality`.
- `multiplicationKernelMap f n`: the commutative group-scheme map
  `A[n] ⟶ B[n]` built with `homOfPoints` from postcomposition with
  `Tate.kernelLevelMap (groupHom f) n`. It is a homomorphism on points by the
  published `Tate.kernelLevelMap_comp_one` and `Tate.kernelLevelMap_comp_mul`.
- `comp_multiplicationKernelMap`: on points it is postcomposition with
  `Tate.kernelLevelMap (groupHom f) n` (`comp_homOfPoints`). Hence its
  underlying morphism is `f[n]`.
- `multiplicationKernelMap_ι`: it satisfies `hΦ` for the square
  `[n]_A ≫ f = f ≫ [n]_B`, by `Tate.kernelLevelMap_ι`.
- `dualTorsionCharacter_dualMap`: for `y : T ⟶ Bᵛ[n]`,
  `dualTorsionCharacter … hA … (y ≫ fᵛ[n]) = charactersMap (multiplicationKernelMap f n) (dualTorsionCharacter … hB … y)`.
  After unfolding `dualTorsionCharacter` and `dualKernelPointCharacter`, this
  is `dualKernelCharacter_square` with `g = [n]_A`, `h = [n]_B`, `f₂ = f`,
  combined with `dualKernelCharacter_congr`. The remaining equality of dual
  points uses `relativeDualMultiplicationKernelIso_inv_ι` at `A` and `B` and
  `Tate.kernelLevelMap_ι` for the underlying homomorphism of `df`, whose
  underlying scheme morphism is `dualSchemeMap homPicardZeroPullback f hA hB`
  by definition.
- `finiteWeilPairing_dualMap`: the displayed equation. Both sides are
  evaluated at `prod.lift x y` using `finiteWeilPairing_points`. With
  `finiteWeilValue` unfolded, the left side is `muEvaluation` of the `B`
  character of `y` at `x ≫ f[n]`. The right side is `muEvaluation` of the `A`
  character of `y ≫ fᵛ[n]` at `x`. `dualTorsionCharacter_dualMap`,
  `Cartier.muEvaluation_precompose` and `comp_multiplicationKernelMap`
  identify them. The universal pair `prod.fst`, `prod.snd` then gives the
  morphism equation (`prod.lift_fst_snd`).
- `relativeFiniteWeilFunctoriality`: introduces the statement's binders and
  applies `finiteWeilPairing_dualMap`.

## Scope

All auxiliary declarations are internal lemmas of this proof, in namespace
`Langlands.AbelianScheme`. No Cartier duality, perfectness, alternation,
transition compatibility or inverse-limit statement is asserted. The kernel
square lemmas hold for arbitrary commutative squares of homomorphisms, not only
for multiplication by `n`.
