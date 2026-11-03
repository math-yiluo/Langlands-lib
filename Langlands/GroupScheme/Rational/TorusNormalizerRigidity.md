# Rigidity of conjugation by torus-normalizing points

Author: Worker 1122.

This module proves two facts about the published normalizer and centralizer subgroup
functors `torusNormalizer i` and `torusCentralizer i` of
`Langlands.GroupScheme.Rational.TorusNormalizer`:

- **Rigidity** (`TorusConjugation.exists_isNormalizingAut_of_connected`). Let
  `i : T ⟶ G` be a homomorphism over any scheme `S` whose underlying morphism of schemes
  is a monomorphism (`[Mono i.hom.hom.left]`), with `T` a split torus
  (`IsSplitTorus T.toGrp`). Let `U` be a test scheme over `S` whose underlying space is
  connected (`[ConnectedSpace U.left]`, which includes nonemptiness). Then every point
  `g ∈ (torusNormalizer i).carrier U` acts on `T` through one automorphism `σ : T ≅ T` of
  commutative group schemes over `S`: for every `V`, every `a : V ⟶ U` and every
  `t : V ⟶ T.X`,
  `(a ≫ g) * (t ≫ i) * (a ≫ g)⁻¹ = (t ≫ σ) ≫ i`.
- **Injectivity** (`relativeWeylGroupRestrict_injective`). For `k` a field, `i` as above over
  `Spec k`, and every test scheme `U` with a point (`[Nonempty U.left]`), the published
  restriction `relativeWeylGroupRestrict i U : N(k)/Z(k) → N(U)/Z(U)` is injective.

Both are inputs of the target `RelativeWeylGroupRestrictStatement`. Its maximal split tori
satisfy the hypotheses: `IsSplitSubtorus` gives `IsSplitTorus T.toGrp`, and
`IsClosedSubgroup.mono` gives the monomorphism. The surjectivity reduction
`RelativeWeylSurjective.relativeWeylGroupRestrict_surjective_of_rigid` (Worker 823) takes
the rigidity conclusion as its hypothesis `hrig`.

## Unit coordinates of conjugation

Fix an isomorphism `e : T ≅ splitTorus S I`.

- `unitsPoint i e V x : V ⟶ G.X` is the point `((pointsEquiv I V).symm x ≫ e⁻¹) ≫ i` of the
  torus with unit coordinates `x : I → Γ(V, 𝒪)ˣ`. It is multiplicative
  (`unitsPoint_mul`) and natural (`comp_unitsPoint`). Every `t ≫ i` has this form
  (`comp_eq_unitsPoint`), and for a monomorphism `i` it is injective
  (`unitsPoint_injective`).
- For `hg : g ∈ (torusNormalizer i).carrier U` and `a : V ⟶ U`, `conjUnits e hg a x` is
  the unit coordinate family of `(a ≫ g) * unitsPoint x * (a ≫ g)⁻¹`
  (`exists_conj_unitsPoint`, `conjUnits_spec`). It is chosen with `Classical.choose`;
  for a monomorphism `i` it is unique (`conjUnits_eq_iff`), multiplicative
  (`conjUnits_mul`), natural in `V` (`conjUnits_naturality`), and conjugation by `g⁻¹`
  undoes it (`conjUnits_inv_conjUnits`). `conjUnits_congr` replaces a test object
  `Over.mk s₁` by `Over.mk s₂` when the underlying morphisms of schemes agree.
- `ActsBy e hg m a` says that conjugation by `a ≫ g` acts by the monomial map
  `powUnits m` of an exponent matrix `m` on the unit coordinates over every `V' ⟶ V`.
  It is stable under precomposition (`ActsBy.comp`). Acting by the identity matrix is
  membership of `a ≫ g` in the torus centralizer (`actsBy_one_iff`).
- `actsBy_of_forall_affine`: it suffices to test affine schemes `Spec A` over `V`. The
  proof glues along Mathlib's affine open cover `V'.left.affineOpenCover` with
  `Scheme.Cover.hom_ext`.

## Affine charts

For a point `ρ : Over.mk s ⟶ U` with `s : Spec R ⟶ S`, `chartPoint ρ α` is the point over
`Spec A` obtained from `α : R ⟶ A`. `chartFamily e hg ρ` is conjugation by `g` in unit
coordinates over all rings under `R`, transported along `Scheme.ΓSpecIso` (`specUnits`). It
is a `splitTorus.UnitsNatEnd R I` of `Langlands.GroupScheme.Torus.UnitsNaturalEndomorphism`.
The comparison theorem there gives:

- `actsBy_chartPoint_iff`: `ActsBy e hg m (chartPoint ρ β)` holds exactly when
  `β (((chartFamily e hg ρ).coeffs j).coeff (m j)) = 1` for all `j`;
- `actsBy_chart_iff`: the case `β = 𝟙`.

## The locus at points

`ActsAtPoint e hg m x` is `ActsBy` at the canonical point
`U.left.fromSpecResidueField x : Spec κ(x) ⟶ U.left`.

- `actsBy_overHom_iff`: for any field `K` and `y : Spec K ⟶ U.left`, `ActsBy` at `y` is
  `ActsAtPoint` at the image point. The morphism `y` factors through `Spec κ(x)` (Mathlib
  `descResidueField_stalkClosedPointTo_fromSpecResidueField`), and field homomorphisms are
  injective.
- `actsAtPoint_chart_iff`: for a chart `ρ` and a prime `p` of `R`, `ActsAtPoint` at
  `ρ(p)` holds exactly when no coefficient `c_j` lies in `p`. Here `c_j = ((chartFamily e hg ρ).coeffs j).coeff (m j)`. One tests at the residue field of `p` (Mathlib
  `PrimeSpectrum.residueField_comap`); an idempotent maps to `1` there exactly when it is
  not in `p` (`algebraMap_residueField_eq_one_iff`).
- `isLocallyConstant_actsAtPoint`: on the chart, the locus is `⋂ D(c_j)` and its complement
  is `⋃ D(1 - c_j)` (`mem_iff_one_sub_notMem`). Both are open, and the charts of
  `U.left.affineOpenCover` are open embeddings.
- `actsAtPoint_of_preconnected`: on a preconnected `U`, the locus is everything once it
  contains one point.
- `actsBy_of_forall_actsAtPoint`: if the locus is everything, then on every affine
  `b : Spec A ⟶ U` each coefficient lies in no maximal ideal. It is a unit idempotent,
  hence `1`, and `ActsBy e hg m (𝟙 U)` follows from `actsBy_of_forall_affine`.
- `exists_actsAtPoint`: at each point some matrix works (`exists_forall_coeff_eq_one` over
  the field `κ(x)`).
- `exists_actsBy_of_connected` and `mem_torusCentralizer_of_connected` combine these over a
  connected `U`.

## The automorphism σ

`mul_eq_one_of_actsBy`: if `g` acts by `m` and `g⁻¹` by `m'` on a nonempty `U`, then
`m' * m = 1`. Test on the universal family over `Spec κ(x₀)[ℤ^I]`: `powUnits (m' * m)` fixes
the monomials `T_j`, so the rows of `m' * m` are the unit vectors. The generic
`mul_eq_one_comm` (matrices over `ℤ` are Dedekind-finite) gives `m * m' = 1`.

`splitTorusPowIso h₁ h₂ : splitTorus S I ≅ splitTorus S I` is the automorphism with point
maps `pointsEquiv⁻¹ ∘ powUnits m ∘ pointsEquiv` (`splitTorusPowEquiv`, natural by
`splitTorusPowEquiv_naturality`), built with the Library's `isoOfPoints`
(`comp_splitTorusPowIso_hom`). The rigidity theorem takes
`σ = e ≪≫ splitTorusPowIso ≪≫ e⁻¹`, as an isomorphism of `CommGroupScheme`s through
`Additive.ofMul`.

## Injectivity

`mem_centralizerPoints_of_constantPoint`: let `n ∈ normalizerPoints i` over `Spec k`. If its
restriction `G.constantPoint n U` to a test scheme with a point lies in the torus
centralizer, then `n ∈ centralizerPoints i`. Take the chart `𝟙 : Spec k ⟶ Spec k` and the
ring map `γ : k ⟶ κ(x₀)` of a residue point (`Spec.preimage`), and let `c_j` be the
diagonal coefficients of `chartFamily` for this chart and the identity matrix. The
hypothesis gives `γ(c_j) = 1`, injectivity of the field map gives `c_j = 1`, and `actsBy_chart_iff` with
`torusCentralizer_carrier_base` concludes. `relativeWeylGroupRestrict_injective` applies
this to the kernel of the quotient map.

## Provenance

Internal infrastructure, proved from the published definitions; no assertion from the
literature is assumed. The rigidity theorem is a version of Milne, *Algebraic Groups*
(2017), Theorem 12.36, printed p.243 (PDF p.259): "Let G and H be diagonalizable groups
over k, and let X be a connected algebraic scheme over k. Let φ : X × G → H be a morphism
such that, for all k-algebras R and x ∈ X(R), the map g ↦ φ(x, g) : G(R) → H(R) is a
homomorphism. For any x₀ ∈ X(k), we have φ(x, g) = φ(x₀, g) for all k-algebras R and
(x, g) ∈ X(R) × G(R)." Here the parameter scheme is
any connected scheme `U` over any base `S`, and the family is conjugation by a point of
the all-test normalizer functor. The proof goes through idempotent coefficients rather
than Milne's density argument. Milne's Corollary 12.40 (`N_G(H)° = C_G(H)°`) is the
analogous classical consequence.
