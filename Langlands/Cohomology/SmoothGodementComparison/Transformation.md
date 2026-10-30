# The comparison transformation from smooth Godement cohomology to derived compact sections

Author: Worker 61. The module imports my
`Langlands.Cohomology.AcyclicResolution.Comparison` (`comparisonNatTrans`,
`comparisonNatTrans_app`, `comparison_zero`, `homologyZeroIso`, `cyclesZeroIso`,
`toCyclesZero`, `comp_lift_id`, `comparisonNatIso`), Worker 3's
`Langlands.Cohomology.SmoothGodementComparison.Statement` (`comparisonMap`, and through it
`CokernelResolutionStatement` and `CokernelComplex.augmentationMap`) and Worker 3's
`Langlands.Cohomology.SmoothGodement.Statement`
(`SmoothGodementCompactDerivedAcyclicStatement`). It also uses my published
`Godement.smoothComplexFunctor`, `Godement.smoothZeroFunctor`,
`Godement.smoothCoaugmentation`, `Godement.mono_smoothCoaugmentation_app`,
`SmoothGodementCohomology.smoothGodementCompactCohomology` and
`smoothGodementCompactCohomologyZeroIso`, together with
`EquivariantGodementCohomology.cyclesIso`. From Worker 13 it uses
`SmoothSheafCohomology.compactDerived` and `compactDerivedZeroIso`.

Composition `f ≫ g` is `f` followed by `g`.

## Setting

All declarations are in the namespace `Langlands.Cohomology.SmoothGodementComparison`, the
namespace of Worker 3's `comparisonMap`. `R` is a commutative ring, `G` a topological group
and `X` a topological space, all in one universe `u`. `G` acts on `X` by `MulAction` with
`ContinuousConstSMul G X`, and `HasStableNeighbourhoods G X` holds. These are the
hypotheses of the published smooth Godement construction and of `compactDerived`.
`comparisonIso` and `comparisonIso_hom` also assume `T2Space X` and
`LocallyCompactSpace X`.

`Φ` below abbreviates compact sections `smoothSheafCompactSections R G X`, a left exact
additive functor from smooth equivariant module sheaves to smooth representations.

## The resolution hypothesis

The smooth Godement complex `Godement.smoothComplexFunctor R G X` is the cokernel complex
of the smooth Godement functor `T := Godement.smoothZeroFunctor R G X` and its
coaugmentation `η := Godement.smoothCoaugmentation R G X`. Its augmentation is the natural
transformation `CokernelComplex.augmentationNat T η : single₀ ⟶ smoothComplexFunctor`, with
components `CokernelComplex.augmentationMap T η F`.

The constructions take the hypothesis

`hK : ∀ F, QuasiIso (CokernelComplex.augmentationMap T η F)`,

which says that the smooth Godement complex resolves every smooth sheaf. It is not proved
here.

- `quasiIso_augmentationMap R G X h F` derives `hK` from
  `h : CokernelResolutionStatement.{u + 1, u}`. This is the published, unproved
  statement that a cokernel complex with monic coaugmentation resolves its input. It is
  applied to the category of smooth sheaves, with `Godement.mono_smoothCoaugmentation_app`
  for monicity.

## Constructions

- `comparisonTrans hK q : smoothGodementCompactCohomology R G X q ⟶ compactDerived R G X q`
  is `AcyclicResolution.comparisonNatTrans Φ (Godement.smoothComplexFunctor R G X)
  (CokernelComplex.augmentationNat T η) hK q`. The source
  `smoothGodementCompactCohomology R G X q` is, by definition, the degree-`q` cohomology of
  `Φ` applied to the smooth Godement complex. The target `compactDerived R G X q` is, by
  definition, `Φ.rightDerived q`.
- `comparisonTrans_app hK F I φ hφ q : (comparisonTrans hK q).app F =
  comparisonMap R G X I φ q`. This holds for every injective resolution `I` of `F` and every
  cochain map `φ` from the smooth Godement complex of `F` to `I.cocomplex` with
  `augmentationMap T η F ≫ φ = I.ι`. The right side is Worker 3's definition, unchanged.
  Hence the components do not depend on the choice of `I` or `φ`.
- `homologyZeroIso_eq F` (with `[QuasiIso (augmentationMap T η F)]`): the generic
  identification `AcyclicResolution.homologyZeroIso Φ (augmentationMap T η F)` of degree-zero
  cohomology with `Φ.obj F` equals the component at `F` of the published
  `smoothGodementCompactCohomologyZeroIso R G X`. Both are built from a kernel comparison
  whose morphism, composed with the inclusion of cycles, is `Φ.map (η.app F)`.
- `comparisonTrans_zero hK : comparisonTrans hK 0 =
  (smoothGodementCompactCohomologyZeroIso R G X).hom ≫ (compactDerivedZeroIso R G X).inv`.
  In degree zero the transformation is the identification of both sides with compact
  sections. The instance `isIso_comparisonTrans_zero` records that it is an isomorphism.
- `comparisonIso hK hcomp hacyc q : smoothGodementCompactCohomology R G X q ≅
  compactDerived R G X q`, on a locally compact Hausdorff space, takes two hypotheses:
  `hcomp : AcyclicResolutionComparisonStatement.{u + 1, u, u + 1, u}` and
  `hacyc : SmoothGodement.SmoothGodementCompactDerivedAcyclicStatement R G X`. The first is
  Worker 3's statement that acyclic resolutions compute right derived functors. The second
  says that the terms of the smooth Godement complex are acyclic for `compactDerived`. The
  first is proved, at all universes and so at these, by the theorem
  `acyclicResolutionComparisonStatement` in
  `Langlands.Cohomology.AcyclicResolution.ComparisonProof`, which this module does not
  import. The Library has no proof of the second. The isomorphism is
  `AcyclicResolution.comparisonNatIso` for the smooth Godement resolution, and
  `comparisonIso_hom` (`simp`) says that its morphism is `comparisonTrans hK q`.

## Relation to Worker 3's statements

Worker 3's `SmoothGodementComparison.Statement` states three propositions about
`comparisonMap`: the degree-zero identity, invertibility on a locally compact Hausdorff
space, and natural isomorphisms whose components are the comparison maps. None of them is
proved here. The lemmas above reduce them to short arguments.

- `SmoothGodementComparisonZeroStatement` requires no `hK`. It follows from the generic
  `AcyclicResolution.toRightDerivedZero_eq_comparison`, which needs no quasi-isomorphism,
  and from the identification of `toCyclesZero` with `EquivariantGodementCohomology.cyclesIso`
  used in the proof of `homologyZeroIso_eq`, which needs none either.
- Given `hK` (from `CokernelResolutionStatement`), `hcomp` and `hacyc`,
  `SmoothGodementComparisonNaturalStatement` follows from `comparisonIso` with
  `comparisonTrans_app`, and `SmoothGodementComparisonIsIsoStatement` from the same.

`SmoothGodementComparisonZeroStatement` is proved by `smoothGodementComparisonZero` in
`Langlands.Cohomology.SmoothGodementComparison.ZeroProof`. The other two propositions
have no proof in the Library: besides the proved `hcomp`, they need `hK` (or a proof of
`CokernelResolutionStatement`) and `hacyc`, neither of which is proved.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39-2 (1999), section 2, printed p.304 (PDF page 6), describes Berkovich's
construction of "an acyclic resolution of a finite ℓ-torsion sheaf … by a complex of
smooth S(ẽ)-modules", "a smooth G-equivariant version of the Godement flasque resolution".
He records that "the construction is functorial in T", and states Lemma 2.2, an
`RΓ_c`-acyclic resolution `0 → ℤ/ℓ^mℤ → F^0_m → F^1_m → ⋯`. On printed p.305 (PDF page 7)
he concludes: "Thus Lemma 2.2 provides an isomorphism
(2.3) `H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ) ~→ Z^q_m/B^q_m = H^q(G^•_m(U(ẽ)_F̄))`". Both pages were
rendered and read by Worker 61. The construction here is the ordinary-topology analogue
of the map behind (2.3): the smooth Godement complex replaces Berkovich's resolution,
`compactDerived` replaces `H^q_c`, and arbitrary commutative coefficients replace
`ℤ/ℓ^mℤ`. The map is constructed in the direction from Godement cohomology to derived
functors, that of Cartan–Eilenberg's comparison (2); (2.3) is its inverse once it is
invertible. Harris does not construct the isomorphism in this generality; he obtains it
from acyclicity of the resolution, which is why invertibility is conditional here.

The comparison map itself is Cartan–Eilenberg, *Homological Algebra* (1956), Chapter V,
§3, printed p.83 (PDF page 105): for an acyclic right complex `X` over `A`, the natural
homomorphism (2) `H(T(X)) → RT(A)` induced by a map from `X` to an injective resolution
over the identity. Here `T` is `Φ` and `X` is the smooth Godement complex of `F`. This
module specializes the generic construction of
`Langlands.Cohomology.AcyclicResolution.Comparison`, whose Markdown gives the
correspondence in detail. The degree-zero identity relates (2) to the map
`τ⁰ : T → R⁰T` of Chapter V, §5, printed p.89 (PDF page 111).

`quasiIso_augmentationMap`, `homologyZeroIso_eq` and the packaging into `comparisonTrans`
and `comparisonIso` are internal steps.

## Scope

- The site is the ordinary open-set site of a topological space, not Berkovich's étale
  site of an analytic space. Harris's truncated resolutions of Lemma 2.2 bis, the
  `ℓ`-divisible systems in `m` and the torsion coefficients are not treated here.
- `hK`, `AcyclicResolutionComparisonStatement` and
  `SmoothGodementCompactDerivedAcyclicStatement` are hypotheses, not results; no proof of
  them is supplied or implied.
- No invariant version (with `smoothGodementInvariantCompactCohomology` and
  `invariantCompactDerived`) and no compatibility with connecting morphisms are stated.
- `R`, `G` and `X` share one universe, as in the published construction.
