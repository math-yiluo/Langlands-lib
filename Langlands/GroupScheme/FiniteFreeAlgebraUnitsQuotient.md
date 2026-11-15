# Fppf quotients by kernels of split homomorphisms, and unit groups of split algebra maps

Module `Langlands.GroupScheme.FiniteFreeAlgebraUnitsQuotient`.

This module has two parts. The first is a general statement about group
schemes. A homomorphism `q : G ⟶ H` with a homomorphic section `s` splits the
source, as a scheme over the target, into the product of the kernel and the
target. Over a field, `q` is therefore an fppf quotient by its kernel. The
second part makes the unit group schemes of the published module
`Langlands.GroupScheme.FiniteFreeAlgebraUnits` functorial in algebra
homomorphisms. Combining the two, the unit-group map of an algebra
homomorphism with an algebra section is an fppf quotient by its kernel.

The intended consumer is the reductive quotient of the special fibre of the
Iwahori model of `GL_N` (module
`Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriModel`). There the
special-fibre algebra maps onto the diagonal algebra `f^N`, and the diagonal
matrices give an algebra section. That consumer is not part of this module.

## Provenance

This is internal infrastructure. The decomposition `G ≅ ker q × H` for a split
homomorphism is the standard semidirect-product argument. Its kernel component
reuses the Library's split-kernel retraction
`Langlands.GroupScheme.SplitKernelRetract.retraction` (module
`Langlands.GroupScheme.SplitKernelRetractGeometry`), whose composite with the
kernel inclusion is `SplitKernelRetract.adjustment q s`, the point
`g ↦ g · s(q g)⁻¹` (`SplitKernelRetract.retraction_ι`). The rest of the argument
uses the Library's group-scheme kernel (`Langlands.GroupScheme.kernel`,
`kernelι`, `kernel_isPullback`, module `Langlands.AbelianScheme.Kernel`) and
Mathlib's flatness, surjectivity and finite-presentation stability under base
change. No statement from an external source is formalized.

Two Library results are related but do not cover this module's statements.
`Langlands.GroupScheme.CommutativeSplitProduct.iso` identifies a commutative
split extension with `kernel q ⊗ V` as a group scheme; the decomposition here
allows noncommutative groups and is an isomorphism of schemes only.
`Langlands.GroupScheme.SectionedSubgroupKernel.isFppfQuotient` (module
`Langlands.GroupScheme.Rational.EnvelopeKernelGeometry`) proves an fppf quotient
property for a composite `h ≫ q` with a section, under the hypotheses that the
source is smooth, affine and locally of finite type and the target affine and
locally of finite type.
`isFppfQuotient_of_section` below needs only a source locally of finite type and
a separated target, and no smoothness.

## Part 1: split homomorphisms (`Langlands.GroupScheme.SectionQuotient`)

Fix a scheme `S`, group schemes `G` and `H` over `S`, a homomorphism
`q : G ⟶ H`, a homomorphism `s : H ⟶ G` and `hs : s ≫ q = 𝟙 H`.

- `decompIso : G.X ≅ (kernel q).X ⊗ H.X`, an isomorphism in `Over S` of the
  underlying schemes (not of group schemes). Its forward map is
  `lift (SplitKernelRetract.retraction q (𝟙 H) q s (Category.comp_id q) hs) q`,
  that is `g ↦ (g · s(q g)⁻¹, q g)`. Its inverse is
  `(fst ≫ kernelι q) * (snd ≫ s)`, that is `(κ, h) ↦ κ · s(h)`. Both composites are
  checked to be the identity in the groups of points, using that `q` is a
  homomorphism, `s ≫ q = 𝟙 H` and `kernelι q ≫ q = 1`.
- `decompIso_hom_snd`: `(decompIso q s hs).hom ≫ snd = q`, so `q` is the second
  projection of the product after this isomorphism.

Now let `k` be a field and `S = Spec k`.

- `kernel_surjective`: the structure morphism of `kernel q` is surjective, since
  its unit section is a section of it.
- `isFppfQuotient_of_section`: if `G.X.hom` is locally of finite type and
  `H.X.hom` is separated, then `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range
  (kernelι q)) q` holds. That predicate (module
  `Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`) asks that the
  underlying morphism of schemes of `q` be flat, surjective and locally of finite
  presentation, and that the range of the actual kernel inclusion be the given
  subgroup functor. The last clause holds by reflexivity. For the first three,
  `decompIso_hom_snd` writes `q` as an isomorphism followed by the second
  projection `(kernel q).X ⊗ H.X ⟶ H.X`, whose underlying morphism is the base
  change `pullback.snd` of the structure morphism of `kernel q`. That structure
  morphism is flat because `Spec k` is the spectrum of a field (Mathlib's
  instance for morphisms to an integral one-point scheme). It is surjective by
  `kernel_surjective`. It is locally of finite type, because the kernel
  inclusion is a closed immersion (the Library's `kernelι_isClosedImmersion`,
  which uses separatedness of `H`) and `G` is locally of finite type. It is
  therefore locally of finite presentation over the noetherian `Spec k`. All
  three properties are stable under base change and composition with
  isomorphisms.

## Part 2: functoriality of unit group schemes (`Langlands.GroupScheme.FiniteFreeAlgebraUnits`)

Fix `R : CommRingCat`, possibly noncommutative `R`-algebras `A`, `A'` and `A''`
with finite bases `b`, `b'` and `b''`, and algebra homomorphisms
`f : A →ₐ[R] A'` and `g : A' →ₐ[R] A''`. The published `groupScheme b` is the
unit group scheme of `A`. Its `T`-points are identified by the published
`pointsEquiv b T` with the units of `Γ(T) ⊗[R] A`.

- `mapPoints b b' f T`: the homomorphism of `T`-point groups induced by the unit
  map of `id ⊗ f : Γ(T) ⊗[R] A → Γ(T) ⊗[R] A'`, transported through `pointsEquiv`.
  `pointsEquiv_mapPoints` states this description, and `mapPoints_naturality`
  proves naturality in `T`. The proof uses that `id ⊗ f` commutes with
  `(algΓ R).map a ⊗ id`, which holds on pure tensors.
- `map b b' f : groupScheme b ⟶ groupScheme b'`, the homomorphism of group
  schemes with these point maps. It is obtained from the Library's Yoneda
  construction `Langlands.GroupScheme.homOfPoints`. `pointsEquiv_map` describes it
  on every test scheme.
- `map_id`: `map b b (AlgHom.id R A) = 𝟙`, and `map_comp`:
  `map b b' f ≫ map b' b'' g = map b b'' (g.comp f)`. Both are proved on points
  with `hom_ext_points`.

For a field `k`, `R = CommRingCat.of k`, algebra homomorphisms `f : A →ₐ[k] A'`
and `g : A' →ₐ[k] A` with `f.comp g = AlgHom.id k A'`:

- `isFppfQuotient_map_of_section`: `map b b' f` is an fppf quotient by its kernel,
  in the sense of `RelativeRoot.IsFppfQuotient` with the range of `kernelι (map b b'
  f)`. The section is `map b' b g`, and `map_comp`, `hfg` and `map_id` give
  `map b' b g ≫ map b b' f = 𝟙`. The published instances
  `groupScheme_locallyOfFiniteType` and `groupScheme_isAffineHom` (affine, hence
  separated) supply the hypotheses of `isFppfQuotient_of_section`. They are passed
  explicitly, because instance search does not find them when the base is
  `CommRingCat.of k`.

## Not claimed

The module does not compute the kernel of `map b b' f`. It does not assert that
the kernel is smooth, connected or unipotent, nor that the target is a torus.
`decompIso` is not a group isomorphism. No consumer in the Bruhat–Tits files is
changed.
