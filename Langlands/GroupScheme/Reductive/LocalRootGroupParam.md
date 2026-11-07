# Root parametrizations over a reduced local ring

Namespace `Langlands.GroupScheme.LocalRootGroup`. The main result is
`exists_rootParametrization`. Let R be a reduced local ring and G a reductive
group over Spec R (`IsReductive G`, affine structure morphism). Let
`i : splitTorus (Spec R) I ⟶ G` be a split torus that is a maximal torus on every
residue-field fibre (`IsFibrewiseMaximalTorus`), and let P be a fibrewise root
datum for `i` (`IsFibrewiseRootDatumOf I G i P`). Then every root α₀ of P has a
root parametrization: there is `u : 𝔾ₐ ⟶ G` with
`IsRootParametrization i (P.root α₀) u`. That is, u is a closed subgroup that
represents the relative root subgroup of the exponent character of P.root α₀,
and the torus acts on it through that character on all points.

The hypotheses are those of `LocalSplitRootGroupStatement` (module
`Reductive.LocalSplitCell`). The theorem gives its root-group half for all
roots. It assumes neither that `i` is a closed subgroup nor that I has
decidable equality.

## Provenance

These are internal results for the local-ring Isomorphism Theorem task
(ab10ec3c). They follow Conrad, *Reductive group schemes* (2014), Theorem 4.1.4
and its dynamic proof (printed pp.110 and 116–119), restricted to a reduced
local base. Conrad's a-root group is U_{Z_G(T_a)}(λ). Here it is
U = U_{Z_G(μ)}(ν), where ν is the coroot of a and μ is a cocharacter in the
kernel of a that is generic for the other roots. The module
`Reductive.LocalRootGroupFibre` shows that the coordinate ring of U is R[x]
(`exists_coordinate`). This module turns x into an isomorphism 𝔾ₐ ≅ U and checks
the group law and the torus action at field-valued points. That check uses the
reducedness of R. It replaces Conrad's étale-local argument for Lemma 4.2.2. The
generic μ comes from the Library's `RootReducedness.exists_cocharacter_pairing_eq_zero`.

## Checking equalities at field points

- `ext_of_fieldPoints`: two morphisms X ⟶ Y over S, with X reduced and Y
  separated over S, are equal once they agree after composing with every
  morphism `Spec K ⟶ X` from the spectrum of a field. It is Mathlib's
  `ext_of_fromSpecResidueField_eq` applied to the residue fields of X.
- `exists_algebra_of_fieldPoint`: a morphism `Spec K ⟶ Spec R` is
  `algebraBaseMap R K` for some R-algebra structure on K.

## Scalar points of 𝔾ₐ

`scalarPoint_add`, `scalarPoint_zero`, `scalarPoint_bijective`: over any base
ring, the scalar point of 𝔾ₐ with coordinate c is additive in c, is the unit at
c = 0, and every point of 𝔾ₐ is the scalar point of exactly one global function.

## The coordinate of U

The algebra-valued test objects and change-of-base point maps are the published
`Corepresented.RingCoordinates` declarations from `Dynamic.RingPointCoordinates`.
Their definitions are unchanged; this module uses their current qualified names.

Here `x : coordU i μ ν` is an element of the coordinate ring of U = `Uc i μ ν`.

- `coordX x y` is the value of x at a point y of U: the global function
  `y.left.appTop x`. `coordX_comp` gives naturality in the test scheme.
- `eval_bijective`, `coordX_bijective`: if `Polynomial.aeval x : R[X] → coordU`
  is bijective, then for every test scheme T the map y ↦ `coordX x y` from
  points of U over T to global functions on T is bijective. Points of U over T
  are algebra maps out of coordU, through `Corepresented.pointsEquiv`.
- Field points. Fix a field K over R and an isomorphism Φ : 𝔾ₐ,K ≅ U_K.
  `under z` is the point of U over `Spec D` that underlies a point z of U_K over
  `Spec D`, for a K-algebra D. `under_mul` says it is multiplicative and
  `under_bijective` says it is bijective. `fibrePoint_add` says that
  `fibrePoint Φ D` is additive. `coordX_under_fibrePoint` evaluates x at the
  point with parameter d: the value is the image of d under
  `fibreAlgHom Φ K[X] X x`.
- `coordX_mul_field`: suppose `fibreAlgHom Φ K[X] X x = C u · X`, so that x
  restricts to a multiple of the coordinate on U_K. Then coordX is additive on
  points of U over `Spec K`.
- `smooth_coordG`, `smooth_coordZ`, `smooth_Uc`: if G is smooth, then its
  coordinate algebra and the coordinate algebra of Z_G(μ) are smooth, and U is
  smooth over R. They come from the Library's `DynamicSmoothRing` results.
- `coordX_mul`: assume G is smooth, R is reduced, and x restricts to a multiple
  of the coordinate on every field fibre. Then coordX is additive on all points:
  `coordX x (y * y') = coordX x y + coordX x y'`. The universal case lives on
  U ×_R U. That scheme is smooth over the reduced ring R, hence reduced (by
  `SmoothReducedBase.isReduced_of_smooth_of_isReduced`), and 𝔾ₐ is affine,
  hence separated. So the universal identity is checked at field points by
  `ext_of_fieldPoints` and `coordX_mul_field`. Pulling back along
  `lift y y'` gives the general case.

## The isomorphism 𝔾ₐ ≅ U and the root map

Assume `Polynomial.aeval x` is bijective (`hx`) and coordX is additive (`hadd`).

- `incl i μ ν : Uc i μ ν ⟶ G` is the inclusion U ⟶ Z ⟶ G, followed by the
  identification of the corepresented model with G.
- `coordX_one`: coordX takes the value 0 at the unit point.
- `coordHom` is the homomorphism y ↦ scalar point of `coordX x y`, and
  `coordHom_bijective` says it is bijective. `pointsEquivGa` is the resulting
  multiplicative equivalence between points of U and points of 𝔾ₐ.
  `pointsEquivGa_naturality` gives naturality in the test scheme.
- `gaIsoU : Ga R ≅ Uc i μ ν` is the isomorphism of group schemes induced by
  these equivalences, via the Library's `isoOfPoints`. `coordX_gaIsoU` says that
  the image of the scalar point c has coordinate c.
- `rootMap = gaIsoU.hom ≫ incl`. `isClosedSubgroup_rootMap` holds because an
  isomorphism, `Corepresented.unipotentHom`, `Corepresented.centralizerHom`
  and an isomorphism are all closed immersions. `rootPoint_rootMap` computes
  the value of the root map at c.

## Torus equivariance

- `under_comp_incl`, `underT`, `underT_comp`, `underT_surjective`: points of G
  and of the torus over `Spec K`, viewed over R, are the underlying points of
  the corresponding base-changed points. They use
  `LocalSplitBigCell.baseChangePointsEquiv_torus`.
- `conj_under`: suppose the torus acts on Φ through a character α of the
  K-torus, as in `exists_fibreIso`. Then conjugating the point with parameter d
  by a torus point t gives the point with parameter α(t)·d. The proof uses
  `tK_comp`, the equivariance of Φ and `weightPointAction_scalarPoint`.
- `charValue_underT`: character values agree under `underT`, by
  `LocalSplitBigCell.charValue_exponentCharacter_baseChange`.
- `rootMap_equivariant_field`: if the torus acts on Φ through the exponent
  character of a, and x restricts to `C u₀ · X`, then the root map is
  a-equivariant on points over `Spec K`. Here u₀ ≠ 0 because coordX is
  injective, so the R-point of U with coordinate u₀·d is the point with
  parameter d.
- `rootMap_equivariant`: if every field fibre has such a Φ, then the torus acts
  on the root map through a on all points. As for `coordX_mul`, the universal
  identity on T ×_R 𝔾ₐ (smooth over the reduced ring R, hence reduced) is checked
  at field points. Pulling back along `lift t (scalarPoint c)` gives the general
  case.

## The root map represents the root subgroup

- `appTop_appTop`: the global-sections maps of composable morphisms compose.
- `rootPoint_mem_subgroup`: for any a-equivariant u : 𝔾ₐ ⟶ G, the value u(c)
  lies in the relative root subgroup of a. The orbit extension is
  (t, s) ↦ u(c·s) on T × 𝔸¹. On the torus it is the orbit by equivariance, and
  its value at s = 0 is u(0) = 1.
- `subgroup_le_centralizer`: if ⟨a, μ⟩ = 0, the root subgroup lies in the dynamic
  centralizer of μ. It uses the Library's `RelativeRoot.subgroup_le_kernelCentralizer`
  and `kernelCentralizer_le_dynamicCentralizer_of_comp_eq_zero`, with
  `exponentCocharacter_comp_exponentCharacter`.
- `subgroup_le_unipotent`: if ⟨a, ν⟩ = m > 0, the root subgroup lies in the
  dynamic unipotent subgroup of ν. It uses the Library's
  `RelativeRoot.subgroup_le_dynamicUnipotent_of_power`.
- `exists_centralizer_point`, `mem_unipotent_of`: a point of G in the dynamic
  centralizer of μ comes from a unique point z of Z. If it also lies in the
  dynamic unipotent subgroup of ν, then z lies in U_Z(ν). These use
  `Dynamic.centralizer_le_comap`, `Dynamic.unipotent_le_comap` and
  `Dynamic.unipotent_eq_comap_of_isClosedSubgroup`.
- `subgroup_le_range_rootMap`: every point of the root subgroup is a value of
  the root map.
- `isRepresentedBy_rootMap`: the root map represents the root subgroup. It is a
  monomorphism because it is a closed immersion. Its range is contained in the
  root subgroup by `rootPoint_mem_subgroup`, and the reverse inclusion is
  `subgroup_le_range_rootMap`.

## Assembly

- `exists_isRootParametrization`: assume G is smooth and R is reduced local.
  Assume ⟨a, μ⟩ = 0, ⟨a, ν⟩ = m > 0, and that every field fibre has an
  isomorphism Φ : 𝔾ₐ,K ≅ U_K under which the torus acts through a. Then some
  u : 𝔾ₐ ⟶ G is a root parametrization for a. The coordinate x comes from
  `exists_coordinate`. Because x is homogeneous of degree m,
  `GradedLine.coeff_eq_zero_of_scaling` with `scaling_fibre` shows that x
  restricts to `C c · X` on every field fibre. The results above then apply.
- `exists_kernel_exponent`: for a root α₀ of a finite reduced root datum P on
  (I → ℤ, I → ℤ), there is μ : I → ℤ with ⟨α₀, μ⟩ = 0 such that every root
  orthogonal to μ is ±α₀. The Library's
  `RootReducedness.exists_cocharacter_pairing_eq_zero` is applied over an
  auxiliary field k. Its output is transported through the exponent
  (co)character identifications, and `RootPairing.IsReduced.eq_or_eq_neg`
  finishes the proof.
- `exists_rootParametrization`: the main theorem. It takes ν := P.coroot α₀,
  so ⟨α₀, ν⟩ = 2 by `IsFibrewiseRootDatumOf.pairing` and `root_coroot_two`. It
  takes μ from `exists_kernel_exponent` over the residue field. On every field
  fibre, G_K is connected reductive (`IsReductive.isConnectedReductive_baseChange`)
  and the torus is maximal (`splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise`).
  The roots are the exponent characters of the roots of P
  (`IsFibrewiseRootDatumOf.mem_roots_iff`), so the roots orthogonal to μ are
  ±α₀. `exists_fibreIso` then gives Φ, and `exists_isRootParametrization`
  finishes the proof.
