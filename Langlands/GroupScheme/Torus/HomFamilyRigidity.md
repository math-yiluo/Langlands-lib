# Rigidity of families of homomorphisms between split tori

Author: Worker 1386.

This module proves that a family of homomorphisms between split tori, parametrized by a
connected scheme, does not depend on the parameter. All declarations are in the namespace
`Langlands.GroupScheme.HomFamily`.

- **Rigidity** (`eq_of_connected`). Let `S` be any scheme and let `T D : GroupScheme S` be
  split tori (`IsSplitTorus T`, `IsSplitTorus D`). Let `U : Over S` be a scheme over `S` whose
  underlying space is connected (`[ConnectedSpace U.left]`, which includes nonemptiness).
  Let `F` assign to every `V : Over S`, every parameter `a : V ⟶ U` and every torus point
  `t : V ⟶ T.X` a point `F V a t : V ⟶ D.X`, such that
  - `F V a (t₁ * t₂) = F V a t₁ * F V a t₂` (each `F V a` is a homomorphism of point groups),
    and
  - `F W (f ≫ a) (f ≫ t) = f ≫ F V a t` for every `f : W ⟶ V` (naturality in the test
    scheme).

  Then `F V a t = F V a' t` for all `V`, all `a a' : V ⟶ U` and all `t : V ⟶ T.X`.
- **Base-point form** (`eq_basePoint`). Over `S = Spec k` for a field `k`, with `U` connected
  and a `k`-point `u₀ : Over.mk (𝟙 (Spec k)) ⟶ U`, every `F` as above satisfies
  `F V a t = F V (c_V ≫ u₀) t`. Here `c_V : V ⟶ Over.mk (𝟙 (Spec k))` is the structure
  morphism `Over.homMk V.hom`, so `c_V ≫ u₀` is the constant parameter `u₀` over `V`. This is
  the case `a' = c_V ≫ u₀` of `eq_of_connected`.

`IsHomFamily F` is the structure bundling the two hypotheses on `F`.

## Unit coordinates

Fix isomorphisms `eT : T ≅ splitTorus S I` and `eD : D ≅ splitTorus S J` with `I`, `J` finite.

- `famUnits eT eD F a x : J → Γ(V, 𝒪)ˣ` is `F V a` in unit coordinates, through the published
  `pointsEquiv` of `Langlands.GroupScheme.Torus.Split`. `eq_famUnits` recovers `F` from it.
  It is multiplicative (`famUnits_mul`) and natural with respect to `unitsRestrict`
  (`famUnits_naturality`). `famUnits_congr` replaces a test object `Over.mk s₁` by
  `Over.mk s₂` when the underlying morphisms of schemes agree.
- `rectPow m x j = ∏ i, x i ^ m j i` is the monomial map of a rectangular exponent matrix
  `m : Matrix J I ℤ`, compatible with ring maps (`rectPow_map`).
- `ActsBy eT eD F m a` says that `famUnits` at `c ≫ a` is `rectPow m` for every `c : V' ⟶ V`.
  It is stable under precomposition (`ActsBy.comp`) and only depends on the underlying
  morphism of schemes (`actsBy_congr`). `actsBy_of_forall_affine` reduces it to affine test
  schemes `Spec A`, gluing along Mathlib's `V'.left.affineOpenCover` with
  `Scheme.Cover.hom_ext`.

## Reduction to square families on `I ⊕ J`

The Library's `splitTorus.UnitsNatEnd R I` (module `Torus.UnitsNaturalEndomorphism`) handles
natural multiplicative endomorphisms of `I → Aˣ` over the rings `A` under `R`. A family
`(I → Aˣ) → (J → Aˣ)` is turned into one of these by padding.

- `extMatrix m : Matrix (I ⊕ J) (I ⊕ J) ℤ` has zero rows on `I` and row `Sum.elim (m j) 0`
  at `Sum.inr j`. By `powUnits_extMatrix`, `powUnits (extMatrix m) x` is `1` on `I` and
  `rectPow m` of the `I`-coordinates on `J`.
- `exists_extMatrix_coeff_eq_one`: let `φ : UnitsNatEnd R (I ⊕ J)` be `1` on the `I` rows and
  depend only on the `I` coordinates. Then for every ring map `β : R ⟶ K` into a domain
  there is `m` with `β (coeff (extMatrix m l)) = 1` for all `l`. The Library's
  `exists_forall_coeff_eq_one` gives a square matrix `M` with this property. The block
  `m j i = M (inr j) (inl i)` also has it, which is checked through
  `forall_app_eq_powUnits_iff` and the two hypotheses on `φ`.
- `chartFamily eT eD hF ρ : UnitsNatEnd R (I ⊕ J)`, for a chart `ρ : Over.mk s ⟶ U` with
  `s : Spec R ⟶ S`, is `Sum.elim 1 (famUnits (chartPoint ρ α) …)` in the coordinates of
  `Scheme.ΓSpecIso` (`specUnits`). Naturality uses the published `specUnits_naturality` and
  `chartMap_comp_chartPoint` of `Rational.TorusNormalizerRigidity`. By definition it is `1`
  on `I` (`chartFamily_app_inl`) and only reads the `I` coordinates (`chartFamily_app_eq`).
- `actsBy_chartPoint_iff`: `ActsBy eT eD F m (chartPoint ρ β)` holds exactly when
  `β (coeff (extMatrix m l)) = 1` for every `l`. `actsBy_chart_iff` is the case `β = 𝟙`.

## The locus at points and connectedness

`ActsAtPoint eT eD F m x` is `ActsBy` at `U.left.fromSpecResidueField x`. The argument follows
the one in `Rational.TorusNormalizerRigidity` for conjugation families, with `chartFamily`
replaced by the padded family.

- `actsBy_overHom_iff`: for any field `K` and `y : Spec K ⟶ U.left`, `ActsBy` at `y` is
  `ActsAtPoint` at the image of the closed point. The morphism `y` factors through the
  residue field (Mathlib `descResidueField_stalkClosedPointTo_fromSpecResidueField`), and
  field homomorphisms are injective.
- `actsAtPoint_chart_iff`: at `ρ(p)` for a prime `p` of `R`, `ActsAtPoint` holds exactly when
  no coefficient `c_l = coeff (extMatrix m l)` of `chartFamily` lies in `p`. The proof tests
  at the residue field of `p` and uses the published `algebraMap_residueField_eq_one_iff`
  for idempotents.
- `isLocallyConstant_actsAtPoint`: on each chart of `U.left.affineOpenCover` the locus is
  `⋂ D(c_l)` and its complement is `⋃ D(1 - c_l)` (published `mem_iff_one_sub_notMem`). Both
  are open, and the charts are open embeddings.
- `actsAtPoint_of_preconnected`: on a preconnected `U`, the locus is everything once it
  contains one point.
- `actsBy_of_forall_actsAtPoint`: if the locus is everything, then on every affine chart each
  `c_l` lies in no maximal ideal. It is then a unit idempotent, hence `1`, and
  `ActsBy eT eD F m (𝟙 U)` follows from `actsBy_chart_iff` and `actsBy_of_forall_affine`.
- `exists_actsAtPoint`: at each point some `m` works, by `exists_extMatrix_coeff_eq_one` over
  the residue field.
- `exists_actsBy_of_connected`: over a connected `U` there is one matrix `m` with
  `ActsBy eT eD F m (𝟙 U)`.

`eq_of_connected` chooses `eT`, `eD` from the split-torus hypotheses. By
`exists_actsBy_of_connected` and `eq_famUnits`, both `F V a t` and `F V a' t` equal the point
with unit coordinates `rectPow m` of those of `t`.

## Provenance

Internal infrastructure, proved from published definitions; no assertion from the literature
is assumed. The rigidity theorem is a version of Milne, *Algebraic Groups* (2017),
Theorem 12.36, printed p.243 (PDF p.259; source id `milne-2017-algebraic-groups`): "Let G and
H be diagonalizable groups over k, and let X be a connected algebraic scheme over k. Let
φ : X × G → H be a morphism such that, for all k-algebras R and x ∈ X(R), the map
g ↦ φ(x, g) : G(R) → H(R) is a homomorphism. For any x₀ ∈ X(k), we have φ(x, g) = φ(x₀, g)
for all k-algebras R and (x, g) ∈ X(R) × G(R)."

Differences from Milne's statement:

- `G` and `H` are split tori rather than arbitrary diagonalizable groups.
- The base is any scheme `S` and the parameter `U` any connected scheme over `S` (not
  necessarily of finite type). `eq_basePoint` is the form over a field `k` with a `k`-point.
- The family is given on points over all test schemes over `S`, as a natural family `F`,
  rather than as a morphism `X × G → H`. By the Yoneda lemma a morphism `U ×_S T → D` that is
  a homomorphism in the torus variable gives such a family; this module does not formalize
  that conversion.
- The proof goes through idempotent coefficients of natural endomorphism families instead of
  Milne's density argument.

The proof adapts `Langlands.GroupScheme.Rational.TorusNormalizerRigidity` (Worker 1122),
which proves the same rigidity for conjugation families `T → T`, and reuses its chart
infrastructure (`specUnits`, `chartPoint`, `chartMap`, `overHom`) and the coefficient theory
of `Langlands.GroupScheme.Torus.UnitsNaturalEndomorphism`. The padding to `I ⊕ J`
(`extMatrix`, `chartFamily`) is new here.
