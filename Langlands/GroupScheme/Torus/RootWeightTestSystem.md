# The actual exponent-weight modules as an affine test system

Lean module: `Langlands.GroupScheme.Torus.RootWeightTestSystem`.

## Setting

- `S` is an arbitrary scheme and `G : GroupScheme S` has an affine and smooth structure morphism
  (`[IsAffineHom G.X.hom] [Smooth G.X.hom]`; both hold for reductive groups).
- `t : splitTorus S I ⟶ G` is a coordinate torus, with `I` finite with decidable equality.
- `m : I → ℤ` is an exponent; for a root `α` of a coordinate root datum one takes `m = P.root α`.

## Definitions

- `testTorus I G t a := (splitTorus.baseChangeIso a I).inv ≫ (baseChange a).map t` is the
  normalized coordinate torus of the pullback of `G` along an affine test `a : Spec R ⟶ S`.
- `testWeightSpace I G t m a := exponentWeightSpace I ((baseChange a).obj G) (testTorus I G t a) m`.
  This is exactly the `R`-module named in the task:
  `splitTorus.exponentWeightSpace I ((baseChange a).obj G) ((splitTorus.baseChangeIso a I).inv ≫
  (baseChange a).map t) m`.
- `weightExtComp I G t m a : A ⊗[R] testWeightSpace a ≃ₗ[A] testWeightSpace (p ≫ a)`, for an
  `R`-algebra `A` and `p = Spec.map (algebraMap R A)`, is the composite of two published
  equivalences:
  1. the actual exponent-weight base-change equivalence `exponentWeightBaseChangeEquiv` for the
     group `(baseChange a).obj G` over `R`, with torus `testTorus a`;
  2. the transport `exponentWeightSpaceTransportEquiv` along the ambient normalization
     `(baseChangeCompIso a p G).symm`, with the identity on the torus. The required square
     `baseChangeHom_comp_inv` is the published compatibility `splitTorus.baseChangeTorusHom_comp`.
- `weightExt I G t m h` is the same equivalence for any test `b` with `h : p ≫ a = b`.
- **`weightTestSystem I G t m : AffineTestSystem S`** has `obj a = testWeightSpace I G t m a` and
  `ext = weightExt`. The required cocycle condition is `weightExt_comp`.

## Lemmas

- `weightExt_point`: for `x` in `testWeightSpace a`, the dual-number point of `weightExt h (1 ⊗ x)`
  over `A`, projected to the original group `G` (via `pullback.fst G.X.hom b`), equals the
  projection of `lieKernelMap ((baseChange a).obj G) (Algebra.ofId R A) x` (via
  `pullback.fst G.X.hom a`).
  The proof combines `smoothSchemeScalarExtension_tmul`, `affineBaseChangeEquiv_left` and
  `GroupScheme.baseChangeCompIso_inv_fst`. This is the actual dual-number point compatibility under
  coefficient extension.
- `lieKernel_ext_of_fst`: a dual-number kernel vector of a pullback of `G` is determined by its
  projection to `G` (the other pullback component is fixed by the structure morphism).
- `lieKernelMap_val_left`: coefficient change of dual-number kernel vectors precomposes with the
  spectrum map of the dual-number coefficient map.
- `weightExt_comp`: for a scalar tower `R → A → B`,
  `weightExt hac (1 ⊗ x) = weightExt hbc (1 ⊗ weightExt hab (1 ⊗ x))`. Both sides have the same
  projection to `G` by `weightExt_point`, `lieKernelMap_val_left` and the published
  `Lie.smooth_lieKernelMapLinear_base`; `lieKernel_ext_of_fst` concludes.

## Use

`AffineTestRealization` realizes `weightTestSystem I G t m` as a quasi-coherent sheaf on `S`.
`AffineTestComparison.frame` gives the canonical isomorphisms
`a^* (weightTestSystem ..).toModules ≅ (testWeightSpace a)^~`, and `frame_hom_eq` is their
coherence in terms of `weightExt`, i.e. of the actual exponent-weight base-change equivalence and
`baseChangeCompIso`. `AffineTestLineBundle` turns the system into a line bundle when the weight
modules have rank one, and gives coherent frames under the Picard hypothesis.

## Provenance

This is an internal construction for the task that builds root-weight line bundles over arbitrary
base schemes. It packages published affine results — the actual exponent-weight spaces, their
base-change equivalence, and the weight transport along group isomorphisms — into the
affine-test-system interface. Mathematically, it expresses that the weight spaces of the adjoint
action form a quasi-coherent sheaf whose formation commutes with base change.
