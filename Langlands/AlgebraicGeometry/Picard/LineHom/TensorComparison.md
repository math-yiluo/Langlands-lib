# Gauge coordinates after base change

Helper module for the proof of
`Picard.ProperLineBundleHomRepresentabilityStatement`.

Setting: an ordered affine cover `𝒰` of a scheme `Y` (FLT
`Scheme.OrderedAffineCover`) and families `α`, `β` of unit transition
functions on the intersections `𝒰.U i ⊓ 𝒰.U j`.

Section `Pulled` (a morphism `q : Z ⟶ Y`):

- `pulledGaugeD q 𝒰 α β a`: for a family `a i ∈ Γ(Z, q ⁻¹ᵁ 𝒰.U i)`, the family
  indexed by the increasing pairs `t` of `𝒰.Idx 1` with value
  `a (t 0) * α' (t 0) (t 1) - β' (t 0) (t 1) * a (t 1)` on
  `q ⁻¹ᵁ 𝒰.U (t 0) ⊓ q ⁻¹ᵁ 𝒰.U (t 1)` (restrictions of `a` understood), where
  `α' = pullbackCocycle q α` and `β' = pullbackCocycle q β` (Library
  `Picard/CocycleLineBundlePullback`). It is the gauge differential
  `gaugeD` of `GaugeComplex` with pulled-back transition functions.
  `pulledGaugeD_zero` and `pulledGaugeD_add` say it is additive.
- `pairIdx h`: the pair `(i, j)` as an element of `𝒰.Idx 1`, for `i < j`.
- `pulledGaugeD_eq_zero_iff`: for cocycles `α`, `β`, `pulledGaugeD q 𝒰 α β a = 0`
  holds exactly when `a` is a gauge family of `α'` and `β'`
  (`IsGaugeFamily`, Library `Picard/CocycleLineBundleGauge`).

Section `Tensor` (`p : Y ⟶ Spec R`, a test `T` in `Over (Spec R)`, the base
change `pullback T.hom p` with second projection `q = pullback.snd T.hom p`;
`Γ(T.left, ⊤)` is an `R`-algebra by the Library `sectionsAlgebra`):

- `tensorGauge0 p 𝒰 T : Γ(T.left, ⊤) ⊗[R] GaugeC0 p 𝒰 →+ ∀ i, Γ(_, q ⁻¹ᵁ 𝒰.U i)`
  and `tensorGauge1 p 𝒰 T` (the same in degree one, on the opens
  `q ⁻¹ᵁ 𝒰.U (t 0) ⊓ q ⁻¹ᵁ 𝒰.U (t 1)`): Mathlib `TensorProduct.piRight`
  followed by the map `sectionsTensorHom` of `SectionsTensor` in each
  coordinate. `tensorGauge0_apply` records this. By `tensorGauge0_tmul` and
  `tensorGauge1_tmul`, `x ⊗ b` goes to the family of products of the pullback
  of `x` along the first projection and the pullback of `b i` (resp. `b t`)
  along `q`.
- `pulledGaugeD_tensorGauge0`: `pulledGaugeD q 𝒰 α β ∘ tensorGauge0 =
  tensorGauge1 ∘ (gaugeD p α β).lTensor Γ(T.left, ⊤)`.
- `tensorGauge0_naturality`: for `g : T' ⟶ T`, tensoring with the Library
  `pullSections g` on the left and then applying `tensorGauge0` for `T'`
  gives, in coordinate `i`, the image under
  `((Over.pullback p).map g).left.appLE` of coordinate `i` of
  `tensorGauge0` for `T`.
- `tensorGauge0_bijective`: if `T.left` is affine, `tensorGauge0 p 𝒰 T` is
  bijective. `tensorGauge1_bijective`: the same in degree one, if moreover `p`
  is separated.
- `tensorGauge0_ker_bijective`: if `T.left` is affine and `p` is separated,
  `tensorGauge0` restricts to a bijection from the kernel of
  `(gaugeD p α β).lTensor Γ(T.left, ⊤)` onto the families `a` with
  `pulledGaugeD q 𝒰 α β a = 0`.

Proofs as implemented. `pulledGaugeD_eq_zero_iff` rewrites the gauge
condition with `isGaugeFamily_iff_of_lt` of `FrameHom` (for the pulled-back
cocycles, `IsCocycle.pullback`) and evaluates at the pairs `pairIdx`. The
`_apply` and `_tmul` lemmas hold by definition (the degree-one one after
`Scheme.Hom.app_eq_appLE`). `pulledGaugeD_tensorGauge0` is proved by
induction on tensors: the sum case uses additivity; on `x ⊗ b` both sides are
expanded with `gaugeD_apply` and compared with the restriction lemmas for
`appLE` and `pullbackCocycle_val`, and closed by `ring`.
`tensorGauge0_naturality` is proved by induction on tensors from
`sectionsTensorHom_naturality`. The bijectivity statements compose the
bijection `piRight` with the coordinatewise map, which is bijective by
Mathlib `Function.Bijective.piMap` and `sectionsTensorHom_bijective` for the
affine opens `𝒰.U i` (resp. `𝒰.U (t 0) ⊓ 𝒰.U (t 1)`, affine by the FLT
`Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated`).
`tensorGauge0_ker_bijective`: injectivity is that of `tensorGauge0`; for
surjectivity, a zero `a = tensorGauge0 w` of `pulledGaugeD` satisfies
`tensorGauge1 (gaugeD.lTensor w) = 0`, so `w` lies in the kernel since
`tensorGauge1` is injective.

The statements are internal to this proof: they express base change of the
gauge complex along affine tests.
