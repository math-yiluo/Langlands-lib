# Actual integral models and root depths at Galois-fixed apartment points

Author: Worker 200.

Lean module: `Langlands.Geometry.Building.UnramifiedFixedRootModelStatement`.

This module states `UnramifiedFixedRootModelStatement.{u}` without proof. It is a
structural existence prerequisite for the fixed-point depth-zero opposite-factor
statement. Its provenance is derived from the point models and fixer comparisons
used in Kaletha–Prasad Proposition 9.4.9, expressed with the Library's actual
integral-model and restricted-root-function interfaces.

## Common data

The telescope through the definitions of `fixed` and `φ` is that of the published
`UnramifiedFixedDepthZeroOppositeStatement`. The local field `F : Type u` has
maximal unramified extension `K = inertiaFixedField F`. The connected reductive
`F`-group `G` has a maximal split torus `iS : S.toGrp ⟶ G` contained in `iT` by
`f : S ⟶ T`. The scalar extension `iT_K` is maximal split. An apartment class
`D : KPApartmentData iT_K ω` and a compatible centralizer datum are supplied,
where `ω` is the order of `MaximalUnramified.valuation F`.

`fixed z` means that every `K/F` automorphism fixes the root-function family of
`z : D.Apartment`. The family `φ z` is the published torus-then-field restriction
of that family along `f_K`. These are exactly the two `let` bodies in the target;
the statement makes no additional assumption on them.

## Existential conclusion

For every fixed `z`, the statement requires actual data

- `D₀ : RelativeComponentModelData ↥𝒪[F] F G`;
- `T₀ : IntegralTorusData D₀ S iS` with `T₀.IsClosedSplit`;
- `Q₀ : SpecialFibreQuotientData D₀` with `Q₀.IsReductiveQuotient`.

The neutral integral model is affine and smooth with connected fibres and a
specified generic-fibre identification with `G`. The torus is closed and split
over the valuation ring and has the specified generic fibre `iS`. The specified
radical is the actual unipotent radical of the neutral special fibre; the
specified quotient represents its fppf quotient and is connected reductive.
Neither the model nor the quotient is an abstract point subgroup.

For every actual relative root `a` and every `g ∈ U_a(F)`, including the identity,
the same data satisfy both exact comparisons

```
g ∈ D₀.neutral.integralPoints ↔ 0 ≤ φ z a g,
g ∈ Q₀.positivePoints        ↔ 0 < φ z a g.
```

Here `Q₀.positivePoints` is the actual radical-reduction preimage in generic
points, as defined in `SpecialFibre`. The strict comparison implies that each
prescribed root element of value zero lies outside this preimage. It is stronger
than lifting some nontrivial residue root point to a value-zero point. No root
is assumed nonmultipliable.

The assertion does not supply the full building, all facet models, functorial
maps between models, or the full list of Bruhat–Tits axioms. The unused full
model inside `D₀` is retained to reuse the Library's existing torus and quotient
interfaces. No uniqueness of the existential data is asserted.

## Source and provenance

Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- Axiom 4.1.20, for the smooth models, relative component and split integral torus;
  Axiom 4.1.22(4), for the special-fibre reduction preimages.
- Proposition 9.4.3(3), printed pp. 345–346 / PDF pp. 376–377: a nontrivial root
  point fixes precisely the half-apartment defined by its affine root function.
- Proposition 9.4.9 and its proof, printed pp. 349–350 / PDF pp. 380–381: the
  point model and the assertion that a prescribed value-zero root point has
  reduction outside the unipotent radical. The proof uses the neighbourhood
  consequence of Axiom 4.1.22(4).
- Construction 9.6.1 and Lemma 9.6.3, printed pp. 365–366 / PDF pp. 396–397,
  for the root functions and their torus-then-field restriction comparison.

This is an internal derived interface, not a transcription of one numbered
source assertion. The integral comparison records the root intersection of the
point model; the strict comparison records the root intersection of the radical
preimage. In KP these arise from the building models, their special fibres and
the fixed-half-apartment and neighbourhood statements. Here the common input is
an arbitrary compatible `KPApartmentData` class and its Galois action, so a proof
must also establish the model and comparison constructions for those supplied
data. The source's global building construction is not silently available as a
Lean theorem.

The registered *Corrections and additions*, version 1 November 2024, source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 39–41, do not change Proposition 9.4.9.

Together with `IntegralOppositeFactorsStatement`, this interface is intended to
imply the exact published `UnramifiedFixedDepthZeroOppositeStatement`. Neither
prerequisite is proved in this module; it adds no premise to that target.
