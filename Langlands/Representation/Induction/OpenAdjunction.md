# Compact induction from an open subgroup is left adjoint to restriction

Author: Worker 61. Built on the published
`Langlands.Representation.Induction.Definitions` (`LeftQuotient`,
`quotientMap`, `quotientRight`, `quotientSupport`, `eval`,
`CompactFunctions`, `compactFunctionOf`, `compactInduced`,
`compactInducedMap`, `compactInductionFunctor`),
`Langlands.Representation.Category.Abelian` (`SmoothRep`,
`SmoothRep.epi_iff_surjective`, `SmoothRep.mono_iff_injective`),
`Langlands.Representation.Smooth.Transfer.PullbackProof` (`isSmooth_comp`)
and Worker 3's `Langlands.Cohomology.SupercuspidalExt.Statement` (the functors
`restriction` and `compactInduction`). From Mathlib it uses `finsum`,
`Adjunction.mkOfHomEquiv`, `Functor.preservesEpimorphisms_of_adjunction`,
`Adjunction.map_projective` and `Adjunction.map_injective`.

Everything except the last section is in the namespace `Langlands.Induction`.
Throughout, `R` is a commutative ring, `G` a topological group, `H` a subgroup
of `G`, and `hH : IsOpen (H : Set G)` where stated. Composition `f ≫ g` is `f`
followed by `g`.

## Conventions of the published compact induction

`LeftQuotient H` is `H \ G`, the quotient of `G` by the right cosets `H x`,
with `quotientMap H x` the coset of `x`. For a representation `σ` of `H` on
`V`, `CompactFunctions H σ` consists of the functions `f : G → V` with
`f (h x) = σ h (f x)`, fixed under right translation by some open subgroup of
`G`, whose support has compact image in `H \ G`; `eval H σ f.1 x` is the value
`f x`. `compactInduced H σ` lets `g` act by right translation,
`(g f)(x) = f (x g)`, and `compactInducedMap H T` composes values with an
`H`-equivariant map `T`. These are the conventions of Vignéras 1996, I.5.1.

## Cosets of an open subgroup

- `quotientMap_eq_iff H x y`: `quotientMap H x = quotientMap H y` if and only
  if `y * x⁻¹ ∈ H`.
- `quotientRight_quotientMap H g x`: right translation by `g` sends the coset
  of `x` to the coset of `x * g` (simp lemma).
- `quotientRightEquiv H g`: right translation by `g` on `H \ G`, as an
  equivalence with inverse right translation by `g⁻¹`.
- `discreteTopology_leftQuotient H hH`: for open `H`, the quotient `H \ G` is
  discrete (each coset `H x` is the open set `H x` of `G`).
- `openSubgroupMap H hH K`: the image in `G` of an open subgroup `K` of `H`,
  an open subgroup of `G` because `H` is open.

## Compactly induced functions

- `compactFunctions_ext`: two compactly induced functions with the same values
  are equal.
- `evalAddHom H σ y`: evaluation at `y`, as an additive map.
- `eval_compactInduced`, `eval_compactInducedMap`: the value of `g f` at `x`
  is `f (x g)`; the value of `compactInducedMap H T f` at `x` is `T (f x)`.
- `quotientSupport_finite H σ hH f`: for open `H`, the image of the support of
  `f` in `H \ G` is finite (compact in a discrete space).

## The unit

Let `hσ : IsSmooth σ` (every vector is fixed by an open subgroup of `H`).

- `unitFunction H hH σ hσ v`: the function equal to `σ h v` at `h ∈ H` and to
  `0` off `H`. It is a compactly induced function: it is `H`-covariant, it is
  fixed under right translation by the image in `G` (`openSubgroupMap`) of an
  open subgroup of `H` fixing `v`, chosen from `hσ v`, and its support lies in
  the single coset `H`. This is Vignéras's `i_w` (I.5.2 b)).
- `eval_unitFunction`, `eval_unitFunction_one`: its values, and its value `v`
  at `1`.
- `unitMap H hH σ hσ`: `v ↦ unitFunction H hH σ hσ v`, an `H`-equivariant
  linear map from `σ` to the restriction of `compactInduced H σ` to `H`
  (`unitMap_apply`).

## The inverse reciprocity map

Let `τ` be a representation of `G` on `W` and
`φ : σ.IntertwiningMap (τ.comp H.subtype)` an `H`-equivariant map from `σ` to
the restriction of `τ`.

- `resIntertwining H τ T`: a `G`-equivariant map `T`, viewed as an
  `H`-equivariant map between the restrictions (`resIntertwining_apply`).
- `cosetTerm H τ σ φ f q`: for the coset `q = H x`, the vector
  `τ(x⁻¹) φ(f x)`; it does not depend on the representative `x`, by the
  covariance of `f` and the equivariance of `φ` (`cosetTerm_quotientMap`).
- `support_cosetTerm_subset`, `hasFiniteSupport_cosetTerm` (needs `hH`): the
  support of `cosetTerm H τ σ φ f` lies in the image of the support of `f`, so
  is finite for open `H`.
- `cosetSum H hH τ σ φ`: the `G`-equivariant map
  `f ↦ ∑ᶠ q, cosetTerm H τ σ φ f q`, that is
  `f ↦ ∑_{H x ∈ H \ G} τ(x⁻¹) φ(f x)` (`cosetSum_apply`). Equivariance comes
  from reindexing the finite sum by `quotientRightEquiv H g`. With `g = x⁻¹`
  this is Vignéras's `f ↦ ∑_{g ∈ G/K} g φ(f(g⁻¹))` (I.5.7 (ii), I.5.8).
- `cosetTerm_resIntertwining_comp`, `cosetSum_resIntertwining_comp`: for a
  `G`-equivariant `T`, `cosetSum` of `(resIntertwining H τ T).comp φ` is
  `T` applied to `cosetSum` of `φ`.
- `cosetTerm_comp_compactInducedMap`, `cosetSum_comp_compactInducedMap`: for
  an `H`-equivariant `ψ`, `cosetSum` of `φ.comp ψ` is `cosetSum` of `φ`
  applied after `compactInducedMap H ψ`.
- `cosetSum_unitMap H hH σ hσ f`: `cosetSum` of `unitMap` (with
  `τ = compactInduced H σ`) is the identity: every compactly induced function
  is the finite sum `f = ∑_{H x} x⁻¹ · unitFunction (f x)` (Vignéras I.5.2 b)).
  At a point `y` only the coset `H y` contributes.
- `cosetSum_comp_unitMap H hH τ σ hσ φ v`: `cosetSum H hH τ σ φ` sends
  `unitFunction v` to `φ v`; only the coset `H` contributes.

## The adjunction

- `smoothRestriction R H : SmoothRep R G ⥤ SmoothRep R H`: restriction along
  the inclusion `H → G`, which is continuous for the subspace topology on `H`,
  so smoothness is preserved (`isSmooth_comp`). It is the same formula as
  Worker 3's `SupercuspidalExt.restriction`, in all universes.
  `smoothRestriction_hom_apply`: it does not change the underlying maps.
- `smoothCompactInduction R H`: the abbreviation
  `SmoothRep.toRep ⋙ compactInductionFunctor H`, from
  `SmoothRep.{uR, uG, max uG uV} R H` to `SmoothRep.{uR, uG, max uG uV} R G`.
  Compact induction raises the universe of the underlying module to
  `max uG uV`, so the adjunction is stated with both categories in that
  universe.
- `compactInductionHomEquiv H hH A B`: the bijection
  `((smoothCompactInduction R H).obj A ⟶ B) ≃ (A ⟶ (smoothRestriction R H).obj B)`
  sending `T` to `T ∘ unitMap` (restricted to `H`), with inverse
  `φ ↦ cosetSum φ`. The two inverse laws are `cosetSum_resIntertwining_comp`
  combined with `cosetSum_unitMap`, and `cosetSum_comp_unitMap`.
- `compactInductionAdjunction H hH :
  smoothCompactInduction R H ⊣ smoothRestriction R H`, built with
  `Adjunction.mkOfHomEquiv` from `compactInductionHomEquiv`; naturality in the
  induced variable is `cosetSum_comp_compactInducedMap`, naturality in the
  other variable holds by definition.
- `compactInductionAdjunction_homEquiv`: its hom-equivalence is
  `compactInductionHomEquiv`.
- `compactInductionAdjunction_unit_app_apply`: the unit at `A` sends `v` to
  `unitFunction H hH A.representation A.isSmooth v`.
- `compactInductionAdjunction_counit_app_apply`: the counit at `B` sends `f`
  to `∑ᶠ q, cosetTerm` of the identity of `B` restricted to `H`, that is
  `f ↦ ∑_{H x} B(x⁻¹) (f x)`.

## Exactness properties

- Instances `smoothRestriction_preservesEpimorphisms` and
  `smoothRestriction_preservesMonomorphisms` (any subgroup `H`):
  epimorphisms and monomorphisms of smooth representations are the surjective
  and injective intertwiners (`SmoothRep.epi_iff_surjective`,
  `SmoothRep.mono_iff_injective`), and restriction does not change underlying
  maps.
- Instance `smoothCompactInduction_preservesMonomorphisms` (any subgroup
  `H`): compact induction acts by composition on values, so it preserves
  injectivity.
- `smoothCompactInduction_preservesEpimorphisms H hH`: for open `H`, compact
  induction preserves epimorphisms, being a left adjoint. It is a theorem
  rather than an instance since it needs `hH`.
- `projective_smoothCompactInduction H hH P hP`: for open `H`, compact
  induction sends projective objects to projective objects (left adjoint of a
  functor preserving epimorphisms).
- `injective_smoothRestriction H hH I hI`: for open `H`, restriction sends
  injective objects to injective objects (right adjoint of a functor
  preserving monomorphisms).

These are the parts of Vignéras 1996, I.5.9 d) that follow from this
adjunction. Restriction also preserves projective objects there; that uses the
other adjunction (restriction is left adjoint to smooth induction) and is not
covered here.

## Specialization to Worker 3's functors

In the namespace `Langlands.Cohomology.SupercuspidalExt`, for `R` and `G` in
one universe `u`:

- `compactInductionAdjunction R G H hH :
  compactInduction R G H ⊣ restriction R G H`, where `compactInduction` and
  `restriction` are the functors on `SmoothRep.{u, u, u}` from
  `Langlands.Cohomology.SupercuspidalExt.Statement`. It is
  `Induction.compactInductionAdjunction.{u, u, u} H hH`; Worker 3's functors
  are definitionally `smoothCompactInduction R H` and `smoothRestriction R H`
  in these universes.

## Provenance and interpretation

Vignéras 1996, Chapter I, §5 works over a commutative ring `R` with a locally
profinite group `G`. I.5.1 defines compact induction with the conventions
above, I.5.2 b) introduces the functions `i_w` supported on an open subgroup
`K` and the decomposition of every compactly induced function into
translates of them, I.5.7 (ii) states that for open `K` the compact induction
`ind_K^G` is left adjoint to restriction (its proof sends `A` to
`w ↦ A(i_w)` and uses the decomposition of I.5.2 b)), I.5.8 lists the unit `w ↦ i_w` and counit
`f ↦ ∑_{G/K} g f(g⁻¹)`, and I.5.9 d) states that restriction to `K`
preserves injectives and compact induction from `K` preserves projectives.
This module follows that proof. It assumes only that `G` is a topological
group and `H` an open subgroup; total disconnectedness of `G` is not used.

Harris 1999 uses this reciprocity in the proof of Proposition 4.10, printed
p.311: the complexes
`⊕ Hom_{O/ℓ^m O[GJ]}(⊕ c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ), Hom(O_m[C_p/H_p]^M, L_m))`
"can be rewritten" as (4.10.2)
`⊕ Hom_{O/ℓ^m O[S(ẽ)]}(C^j_m(ẽ), Hom(O_m[C_p/H_p]^M, L_m))`; by (4.4.4) on
p.310 the modules here are compactly induced from compact (mod center) open
subgroups of `GJ`. `compactInductionHomEquiv` is this rewriting for one
summand; the direct sums over `i + j = k` and `(e, δ)`, the Hom complexes and
Harris's particular groups are not formalized here. On p.310 (proof of
Proposition 4.4) Harris also uses that "compact induction preserves
projectivity with arbitrary coefficients [Vi, 5.9 (d)]", which is
`projective_smoothCompactInduction`. The Ext form of reciprocity is Worker 3's
separate `CompactInductionExtReciprocityStatement`.

## Scope

- This module constructs the adjunction and its formal consequences. It does
  not prove Worker 3's `CompactInductionExtReciprocityStatement` (the Ext
  version of reciprocity) or the clause `OpenSubgroupAdjunctionClause` of
  `Langlands.Representation.Induction.StructuralStatement` (a linear
  equivalence over `ℂ` with a support formula), although it is the main input
  for both.
- Smooth induction, the adjunction for closed non-open subgroups, and modulus
  characters do not appear.
