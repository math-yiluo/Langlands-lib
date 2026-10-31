# Kernel translation units through restriction to points

This module adds three lemmas about the Library's kernel-translation unit
`kernelTranslationUnit f α h a k`: two compute it, and one gives a criterion
for its value `1` under the intrinsic kernel character. No new mathematical
object is defined except the point notation `familyPoint`. The content is internal
infrastructure for the proof of
`Langlands.AbelianScheme.MumfordFiniteWeilAlternationStatement`. It only
re-expresses the published definitions in
`Langlands/AbelianScheme/KernelTranslationScalar.lean` and
`Langlands/AbelianScheme/IntrinsicKernelCharacter.lean`.

## Setting

Let `f : A ⟶ B` be a homomorphism of abelian schemes over `S`, `T` a scheme
over `S`, `M` a module on `T ×_S B`, and
`α : (f × T)^* M ≅ O_{T ×_S A}` a trivialization. Here `p = (homFamilySpaceMap f).app T`.
For `a : U ⟶ T` and a kernel point `k : U ⟶ ker f`, the published
`kernelTranslationAut f α a k` is the automorphism of `O_{U ×_S A}` obtained by
`equalCompositeUnitAut p q r _ α`, where `q = (relativeSpace A.X.hom).map a`
is the change of parameter and `r = kernelShear f a k` is the translation
`(u, x) ↦ (a u, k u · x)`. Its scalar is a global unit of `U ×_S A`, and
`kernelTranslationUnit` is the unique unit on `U` that pulls back to it.

## Declarations

- `familyPoint a c : U.left ⟶ T ×_S A` is the point `(a, c)`, i.e.
  `pullback.lift a.left c.left`.
- `relativeSection_kernelShear` and `relativeSection_relativeSpace_map`: the
  unit section `e_U = (relativeSection A.X.hom (unitSection A) _).app U` composed with the
  translation `r` is `familyPoint a (k ≫ ι)`, and composed with `q` is
  `familyPoint a 1`. Both follow from the published `relativeSection_shear`
  (for `q` one uses `shear_one`).
- `familyPoint_kernel_homFamilySpaceMap`: these two points have the same image
  under `p`, by `kernelShear_homFamilySpaceMap`.
- `kernelTranslationUnit_eq_point_comparison`: the unit equals the scalar of
  `equalCompositeUnitAut p (familyPoint a 1) (familyPoint a (k ≫ ι)) _ α`, an
  automorphism of `O_U`. In words: the kernel character value is the ratio of
  the trivialization `α` restricted at the point `(a, k)` and at the point `(a, 1)`,
  both points lying over the same point of `T ×_S B`.
- `kernelTranslationUnit_eq_section_comparison`: the same formula with the
  points written as `e_U ≫ q` and `e_U ≫ r`.
- `kernelTranslationUnit_eq_one_of_section`: at the identity parameter
  `a = 𝟙 T`, suppose `equalCompositeUnitAut p e_T (e_T ≫ kernelShear f (𝟙 T) k) _ α`
  is the identity. Then `kernelTranslationUnit f α h (𝟙 T) k = 1`.
- `characterEvaluation_intrinsicKernelCharacter_eq_one`: if
  `kernelTranslationUnit f α h (𝟙 T) x = 1` for a point `x : T ⟶ ker f`, then
  the published intrinsic kernel character
  `intrinsicKernelCharacter f α h` evaluates to `1` at `x`
  (`Cartier.characterEvaluation`).

## Proofs

For the section formula, `relativeUnitDescend_eq_section` computes the
descended unit by pulling back along the unit section `e_U`. Next,
`structureAutScalar_pullback` turns this into the scalar of
`structureAutPullback e_U (kernelTranslationAut f α a k)`. Unfolding both
definitions, the published `equalCompositeUnitAut_precomp` identifies this
pullback with `equalCompositeUnitAut p (e_U ≫ q) (e_U ≫ r) _ α`. The point
version then rewrites `e_U ≫ q` and `e_U ≫ r` by the two restriction lemmas
(`congr 1` on the two point arguments; the equality proof is irrelevant).

For the criterion at `a = 𝟙 T`, `e_T ≫ (relativeSpace A.X.hom).map (𝟙 T) = e_T`
by functoriality. Generalizing over the first point and substituting
transports the hypothesis to the comparison automorphism in the section
formula, and `structureAutScalar_refl` gives `1`.

For the character evaluation, injectivity of `Gm.pointsEquiv S T` reduces
the claim to unit values. `Cartier.characterEvaluation_section`,
`characterHomEquiv_intrinsicKernelCharacter` and
`intrinsicKernelCharacterHom_points` turn the evaluation into
`kernelTranslationUnit f α h (kernelCharacterParameter U) k'`, where
`U = Over.mk (𝟙 T.left)` and `k'` is the base-changed section point. The
section point equals `(Cartier.sectionBaseIso T).hom ≫ x` (inverse of
`sectionPointsEquiv`). The parameter `kernelCharacterParameter U` equals
`(Cartier.sectionBaseIso T).hom ≫ 𝟙 T`, checked on underlying morphisms.
Then `kernelTranslationUnit_precomp` reduces the value to the image of
`kernelTranslationUnit f α h (𝟙 T) x = 1`, which is `1`.
