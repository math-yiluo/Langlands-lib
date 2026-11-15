# KP Lemma C.5.3 for actual roots without higher multiples

Lean module: `Langlands.BruhatTits.IntegralModels.RootDepthKernelNoHigher`.

This module proves the conclusion of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Lemma C.5.3, in the form of the Library target
`UnramifiedRootDepthKernelStatement`, for every relative root `a` of the actual
maximal unramified building data such that no multiple `n • a` with `n ≥ 2` is a
relative root. This covers every relative root that is not multipliable,
including divisible roots. The multipliable case (`2 • a` a root) is not covered
here. The main Task 6392 target is unchanged and remains open.

The proof is assembled from published Library results:

- the shifted root-field filtration identity
  `filtration_eq_additiveRootFiltration_rootFieldDepthShift`
  (module `Langlands.Geometry.Building.RootFieldDescentValue`);
- the actual root-field depth models `rootFieldDepthModelOfOrbit`, their
  smoothness, connected fibres, exact point images
  (`rootFieldDepthModelOfOrbit_integralPoints_map`), the deeper-to-shallower
  transition `rootFieldDepthTransitionOfOrbit`, and the kernel properties
  `rootFieldDepthModelOfOrbit_kernel_properties`
  (module `Langlands.GroupScheme.IntegralModel.RootFieldDepthOfOrbit`);
- presentation invariance of special-fibre kernels
  `RootFiltrationModelData.specialFibreKernel_properties_of_presentation`
  (module `Langlands.BruhatTits.IntegralModels.RootModelPresentationIso`);
- the structural theorems on the torus centralizer of a maximal split torus of
  a quasi-split group, used in the same way as in
  `quasiSplitIntegerApartmentExistence_of_multipliableOpposite`.

The Lean proof computes the kernel on explicit root-field vector models, where
it is the kernel of an inclusion of lattices in the root field. It then
transfers the result to the supplied presentations. This route is internal. So
is the formulation through the Library's actual root-field coordinates and
supplied root-model presentations.

## Affine root groups

`RootFiltrationModelData.isAffineHom_rootGroup`. For any supplied root-model
presentation `U` (`RootFiltrationModelData R K C x a r`), the generic group
`U.rootGroup` is affine over `Spec K`. Proof: the base change of the affine model
`U.model.group` to `Spec K` is affine, being a pullback of an affine morphism.
The generic isomorphism `U.model.genericIso` identifies it with `U.rootGroup`,
and composing an affine morphism with an isomorphism keeps it affine.

## The core comparison

`specialFibreKernel_properties_of_rootOrbit`. Setting at arbitrary universe `u`:

- `k` is a field and `L/k` a finite Galois extension.
- `G` is affine, smooth and locally of finite type over `Spec k`, and connected
  reductive (`hG`).
- `f : S ⟶ T` and `j : T ⟶ G`, where `S` and `T` are affine over `Spec k`.
- `j` is a closed (`hjc`) maximal torus (`hj`) that represents the centralizer
  of `i` (`hcent`).
- `i : S ⟶ G` is a maximal split torus equal to `f ≫ j` (`hit`) and is a
  monomorphism.
- `S` is split (`hS`), `T_L` is split (`hT`), and `j_L` is a maximal torus
  (`hjL`).

The arithmetic data:

- `v` is a `ℤ`-valued valuation of `k`, surjective (`hv`), with henselian
  valuation ring (`hH`).
- `O` is a valuation subring of `k` equal to the valuation ring of `v` (`hO`).
- `hext` states that maps of generic fibres that preserve integral points extend
  to model maps from smooth models over `O`
  (`IntegralModel.HasSmoothHomExtension`).

The apartment and root data:

- `D` is an integer apartment class of `i` for the order of `v`, satisfying
  V 6 with a centralizer datum `C` (`hD`), and `y` is a point of `D`.
- `a` is a relative root of `i` with no higher multiples (`hhigh`).
- `β` is an absolute root of `j_L` in the restriction fibre of `a` (`hβ`),
  whose Galois orbit is that whole fibre (`horbit`).

Conclusion: let `r ≤ s`, and let `U`, `V` be any supplied presentations over `O`
of the filtration groups `U_{a,y,r}` and `U_{a,y,s}` (`D.filtration y a r` and
`D.filtration y a s`). Then for every generic map `g` with
`g ≫ U.inclusion = V.inclusion` and every model map `φ` extending it, the
scheme-theoretic kernel of the special-fibre map of `φ` is smooth, connected
and unipotent.

Proof. First `subst` the equalities `hO` and `hit`, so that `O` is the
valuation ring of `v` and `i = f ≫ j`. Let `b` be a basis of the root field
`L_a = rootOrbitField k L j β` over `k`, and `q = U.inclusion`, a representative
of the relative root subgroup of `a` (`U.isRootSubgroup`), affine by the
previous section.

Let `c` be the root-field depth shift `rootFieldDepthShift … D C hD y`, so that
`D.filtration y a t` is the additive root-field filtration at depth `t - c` for
every `t`. Two auxiliary presentations `P'` and `Q'` share the root group and
inclusion of `U`. Their models are the root-field depth models
`rootFieldDepthModelOfOrbit … q b v hH hv (r - c)` and `(s - c)`. These are
smooth with geometrically connected fibres, and their integral points map onto
the additive root-field filtrations at depths `r - c` and `s - c`. By the depth
shift these are exactly `D.filtration y a r` and `D.filtration y a s`, as
`RootFiltrationModelData` requires.

The transition `ψ = rootFieldDepthTransitionOfOrbit … (r - c) (s - c)` is a model
map over the identity of `q`'s group. By
`rootFieldDepthModelOfOrbit_kernel_properties`, its special-fibre kernel is
smooth, connected and unipotent. Finally
`specialFibreKernel_properties_of_presentation`, applied to the presentations
`U, V, P', Q'`, the maps `g` and `𝟙`, and `hext`, transfers these properties to
the kernel of `φ`.

## The actual maximal unramified statement

`UnramifiedNoHigherRootDepthKernelStatement` is a `Prop`-valued definition. It
has exactly the quantifiers and conclusion of `UnramifiedRootDepthKernelStatement`,
with one extra hypothesis after the relative root `a : relativeRoots C.i`:
`RelativeRoot.HasNoHigherRoots C.i a`, i.e. `n • a` is not a relative root for
every `n ≥ 2`. Here:

- `F` is a nonarchimedean local field.
- `G` is affine over the actual maximal unramified extension
  `inertiaFixedField F`.
- `C : MaximalUnramified.BuildingData F G` is the supplied building data, and
  `x` a point of its apartment.
- The models are over `fixedFieldIntegers F`.

`unramifiedNoHigherRootDepthKernel` proves it at arbitrary universe `u`. Proof:

- `G` is connected reductive (`C.isConnectedReductive`), hence smooth, and
  quasi-split by `MaximalUnramified.isQuasiSplit`.
- `fieldCentralizerRepresentability` gives a closed representative
  `j : Z ⟶ G` of the centralizer of the maximal split torus `C.i`.
  `Z` is a torus by `isTorus_of_quasiSplit_torusCentralizer`, together with
  `quasiSplitTorusCentralizerExistence` and `maximalSplitTorusConjugacy`.
- Writing `T` for `Z` with its commutative structure and `t` for the
  factorization `torusCentralizerFactor`, `t ≫ j = C.i`. `j` is its own
  centralizer, hence a maximal torus by `isMaximalTorus_of_torusCentralizer_eq`.
- `torusFiniteGaloisSplitting` gives a finite Galois extension `L` that splits
  `T`, and `j_L` is maximal by `isMaximalTorus_baseChange_of_torusCentralizer_eq`.
- `rootDatumExistence` gives a root datum of `j_L`.
  `rootRestrictionFiber_nonempty` gives an absolute root `β` in the restriction
  fibre of `a`. `rootOrbit_eq_restrictionFiber_of_torusCentralizer` shows that
  its Galois orbit is the whole fibre.
- The core comparison applies with:
  - `v = MaximalUnramified.valuation F`, which is surjective and has henselian
    valuation ring;
  - `O = fixedFieldIntegers F`, via `MaximalUnramified.valuationSubring_eq F`;
  - `hext` given by
    `IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F`;
  - `D = C.apartment`, centralizer datum `C.centralizer`, and V 6
    `C.isOmegaCompatible`.

The statement and proofs use only the standard axioms. They contain no `sorry`
and no new axioms.
