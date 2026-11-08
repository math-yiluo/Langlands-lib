# Coefficient stability and fixed loci of centralizer-compatible apartment classes

This module has two parts.

1. It defines the Galois-fixed part of a coefficient-stable KP apartment, as an
   affine subspace. It proves that this subspace is preserved by
   coefficient-invariant normalizer points and that its points give
   coefficient-fixed points of the existing reduced building.
2. It shows that an integer-valued apartment class satisfying the full
   centralizer condition (V6, the existing `IntegerValuation.IsOmegaCompatible`)
   for a scalar-extended centralizer datum is stable under every
   order-preserving coefficient automorphism. This uses, over `K`, an actual
   opposite factor pair for every nonidentity rational point of every relative
   root subgroup. That is a hypothesis here and is not proved.

Everything here is an internal consequence of existing definitions and of two
companion modules: `CentralizerGaloisTransport` (the coefficient image of a V6
class is again V6) and `IntegerOmegaApartmentRigidity` (two V6 classes for the
same centralizer datum are equal). The module proves no existence of
apartment classes, centralizer data or opposite pairs. It also does not show
that the fixed affine subspace is nonempty, or identify it with an apartment
over `k`.

## Fixed points of an affine action

`fixedAffineSubspace ρ` is defined for any monoid `M`, real vector space `V`,
affine space `P` over `V` and monoid homomorphism
`ρ : M →* (P ≃ᵃ[ℝ] P)`. Its carrier is the set of points `x` with `ρ m x = x`
for every `m`. To see that this set is an affine subspace, let `p₁`, `p₂`, `p₃`
be fixed points and `c` a real number. For each `m`, the linear part of `ρ m`
fixes `p₁ -ᵥ p₂`, by `AffineMap.linearMap_vsub`. Then `AffineEquiv.map_vadd`
shows that `ρ m` fixes `c • (p₁ -ᵥ p₂) +ᵥ p₃`.
`mem_fixedAffineSubspace_iff` restates membership.

## The fixed apartment of a stable class

Let `k` and `K` be fields in any universe `u`, with an algebra `k → K`. Let `T`
be a commutative group scheme over `k`, and let `G` be a group scheme over `k`
that is affine over the base. Let `i : T.toGrp ⟶ G` be a homomorphism whose
scalar extension `i_K` has a monomorphic underlying scheme map. Let `ω : Kˣ → ℝ`
be any map, and let `D` be a supplied `KPApartmentData` for `i_K` and `ω`.
Assume `hD : KPApartmentData.GaloisStable k K i D`, as in the existing
`ApartmentGaloisAction` module.

`KPApartmentData.galoisFixedApartment k K i D hD` is the affine subspace
`fixedAffineSubspace (galoisAffineAction k K i D hD)` of `D.Apartment`. Here
`galoisAffineAction` is the existing action of `K ≃ₐ[k] K` on the apartment by
affine equivalences.

- `mem_galoisFixedApartment_iff` states that an apartment point `x` lies in this
  subspace exactly when its underlying root-function family is fixed:
  `RootFunctionFamily.galoisAction k K T G σ x.val = x.val` for every `σ`. The
  proof applies `Apartment.ext` in one direction and `congrArg Apartment.val`
  in the other.
- `normalizer_smul_mem_galoisFixedApartment` assumes a normalizer point `n`
  of `i_K` with `rationalConjugate k K G σ n.val = n.val` for every `σ`. It
  shows that `n • x` lies in the fixed subspace whenever `x` does. The proof
  rewrites with the existing `galoisAction_normalizer_smul`. It identifies
  `normalizerGaloisAction k K i σ n` with `n` by `Subtype.ext`.
- `galoisQuotientAction_apartmentMap_of_mem` shows that for `x` in the fixed
  subspace, the existing coefficient action `galoisQuotientAction` on
  `D.ReducedBuilding` fixes `D.apartmentMap x`, for every `σ`. The proof uses
  `galoisQuotientAction_apartmentMap`.
- `galoisQuotientAction_smul_of_fixed` assumes a rational point `g` of `G_K`
  fixed by every `rationalConjugate k K G σ`, and a point `z` of the reduced
  building fixed by every `galoisQuotientAction σ`. It shows that `g • z` is
  again fixed by every `galoisQuotientAction σ`. The proof uses the existing
  semilinearity `galoisQuotientAction_smul`.

## Stability of centralizer-compatible classes

Now let `Z` be a group scheme over `k`, with homomorphisms `j : Z ⟶ G` and
`s : T.toGrp ⟶ Z`. Write `j_K` and `s_K` for their scalar extensions along
`algebraBaseMap k K`. Let `w` be a `WithZero (Multiplicative ℤ)`-valued
valuation on `K`, and let `D` be a `KPApartmentData` for `i_K` and `order w`.
Take the following hypotheses:

- `j_K` is a closed subgroup (`hcl`);
- `j_K` represents the existing `torusCentralizer` of `i_K` (`hrep`);
- `s_K ≫ j_K = i_K` (`hcomp`);
- `Cartan.restrictionEvaluation s_K` is bijective (`hK`);
- `hD`: `IsOmegaCompatible w D` holds for the centralizer datum built from
  these data, with centralizer group `(GroupScheme.baseChange b).obj Z`;
- `G_K` is connected reductive (`hG`);
- `i_K` is a maximal split torus (`hi`), as for a `k`-torus that becomes a
  maximal split torus over `K`;
- for every relative root `a` of `i_K` and every nonidentity `K`-rational point
  `x` of the actual root subgroup `U_a`, there is an actual opposite factor
  pair for `x`: points `p` and `q` of `U_{-a}(K)` with `p * x * q` in the
  actual normalizer of `i_K` (`hpair`, `RelativeRoot.HasOppositeFactorPairs`,
  built from `IsOppositeFactorPair`).

`IntegerValuation.IsOmegaCompatible.galoisImage_eq` takes a coefficient
automorphism `σ` with `order w (σ t) = order w t` for every unit `t`. It proves
that the existing actual coefficient image is the class itself:
`KPApartmentData.galoisImage k K i D σ hw = D`. The proof has two steps.
First, `IsOmegaCompatible.galoisImage` from `CentralizerGaloisTransport` shows
that the image class also satisfies `IsOmegaCompatible` for the same
scalar-extended centralizer datum. Second,
`IsOmegaCompatible.eq_of_hasOppositeFactorPairs` from
`IntegerOmegaApartmentRigidity` shows that two classes compatible with one
centralizer datum are equal under `hG`, `hi` and `hpair`.

`IntegerValuation.IsOmegaCompatible.galoisStable` assumes that every
`σ : K ≃ₐ[k] K` preserves `order w` on units. Under the same hypotheses, it
concludes the existing `KPApartmentData.GaloisStable k K i D`. Given `σ` and a
member `φ` of `D.carrier`, it rewrites `D` as its own image using
`galoisImage_eq`. Then the transported family
`RootFunctionFamily.galoisAction k K T G σ φ` is a member of the image by
definition. This stability is exactly the input that the existing
`galoisAffineAction` and `galoisQuotientAction` need, and also the input of the
fixed apartment above.

## Provenance

This module is internal. It formalizes no single cited original-source
statement. It combines the companion modules `CentralizerGaloisTransport` and
`IntegerOmegaApartmentRigidity` with the existing `ApartmentGaloisAction` and
`GaloisApartmentQuotientAction` constructions. The fixed-subspace construction
is elementary affine geometry. The hypotheses of the stability theorem are
exactly the Lean premises listed above; no cited result is claimed.
