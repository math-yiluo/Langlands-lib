# Statement: cohomology of quasi-split trialitarian groups over totally complex number fields

`Langlands.GroupScheme.TotallyComplexQuasiSplitTrialitarianCocycleVanishingStatement.{u} : Prop`
is a statement-only, `Prop`-valued definition with one universe parameter `u`,
in the namespace `Langlands.GroupScheme`. The module
`Langlands.GroupScheme.Rational.TotallyComplexQuasiSplitTrialitarian` does not
prove it, and it adds no other definitions, theorems or axioms. It imports:

- [`GaloisCocycle`](../GaloisCocycle.md), for the field cover
  `GaloisCocycle.cover`. Through its imports it also brings in
  [`TorsorCocycle`](../TorsorCocycle.md), for `Cocycle` and `Cocycle.IsTrivial`.
- [`Reductive.AbsolutelyAlmostSimple`](../Reductive/AbsolutelyAlmostSimple.md),
  for `IsAbsolutelyAlmostSimple`.
- [`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), for `IsQuasiSplit`.
- [`Reductive.TitsIndex`](../Reductive/TitsIndex.md), for `TitsIndexData`,
  its simple vertices `Vertex`, its Cartan pairings `cartan` and its star
  action `star`.
- [`SimplyConnected.Basic`](../SimplyConnected/Basic.md), for
  `IsSimplyConnected`.
- Mathlib's `Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex`,
  for `NumberField.IsTotallyComplex`.

## Lean statement

```lean
def TotallyComplexQuasiSplitTrialitarianCocycleVanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → IsQuasiSplit G →
    (∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b)) →
    (∀ a : d.Vertex, e a ≠ 1 →
      ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.IsTrivial
```

## Objects and predicates used

- **Totally complex number fields.** `NumberField.IsTotallyComplex F` is
  Mathlib's class saying that every infinite place of `F` is complex
  (`InfinitePlace.IsComplex`). Equivalently, `F` has no real embedding: it is
  a totally imaginary number field.
- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. The instances
  `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom` are the standing
  hypotheses of `TitsIndexData`.
- `IsSimplyConnected G` ([`SimplyConnected.Basic`](../SimplyConnected/Basic.md)):
  `G` is semisimple, which includes `IsConnectedReductive G` (smooth, affine,
  connected, with trivial geometric unipotent radical), and every central
  isogeny `H ⟶ G` from a semisimple group `H` is an isomorphism.
- `IsAbsolutelyAlmostSimple G`
  ([`Reductive.AbsolutelyAlmostSimple`](../Reductive/AbsolutelyAlmostSimple.md)):
  `G` is almost simple (`IsAlmostSimple`: semisimple, noncommutative, and its
  only smooth connected closed normal subgroups are trivial or the whole group)
  and remains almost simple after base change to the algebraic closure.
- `IsQuasiSplit G` ([`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md)):
  `G` is connected reductive and has a closed subgroup `B ⟶ G` defined over
  `F` that is a Borel subgroup over `F` and remains a Borel subgroup over the
  algebraic closure.
- **Index data** ([`Reductive.TitsIndex`](../Reductive/TitsIndex.md)).
  `d : TitsIndexData G` consists of a pinning of `G` over the separable closure
  of `F` (a maximal torus with a based absolute root datum), a maximal `F`-split
  torus and a compatible positivity. `d.Vertex` is the set of simple roots of
  the based absolute root datum, `d.cartan a b` is the integral pairing
  `d.pinning.rootDatum.pairing a b` of two simple roots, and, for `σ` in the
  absolute Galois group `SeparableClosure F ≃ₐ[F] SeparableClosure F`,
  `d.star σ` is the star action of `σ` on the simple vertices.
- **The numbering.** `e : d.Vertex ≃ Fin 4` carries the actual pairings to
  Mathlib's `CartanMatrix.D 4`. In that matrix the off-diagonal entries are
  `-1` exactly for the pairs `{0, 1}`, `{1, 2}` and `{1, 3}`, and `0` otherwise.
  So vertex `1` is the centre of the `D_4` diagram and `0`, `2`, `3` are its three
  leaves. The matrix is symmetric, so the comparison does not depend on the
  order of the arguments of the pairing.
- **The leaf hypothesis.** Every vertex `a` with `e a ≠ 1` is moved by some
  element of the absolute Galois group: no leaf is fixed by the full star action.
- **The cover.** For a finite Galois extension `L/F` in the same universe,
  `GaloisCocycle.cover F L` ([`GaloisCocycle`](../GaloisCocycle.md)) is the
  `F`-scheme `Spec L`.
- **Cocycles and triviality** ([`TorsorCocycle`](../TorsorCocycle.md)). For
  `U : Over S`, `Cocycle G U` gives, for every test object `Z` over `S` and every
  pair `a b : Z ⟶ U`, a point `ξ.toFun a b : Z ⟶ G.X`, natural in `Z` and
  satisfying `ξ.toFun a c = ξ.toFun a b * ξ.toFun b c`. `ξ.IsTrivial` means that
  there is one point `f : U ⟶ G.X` with
  `ξ.toFun a b = (a ≫ f) * (b ≫ f)⁻¹` for all `Z`, `a` and `b`: `ξ` is a
  coboundary on the same cover.

On a finite Galois cover these notions are ordinary Galois cocycles. The
module [`GaloisCocycle`](../GaloisCocycle.md) defines the value
`GaloisCocycle.value ξ σ`, a point of `G` with values in `L`, for every
`σ : L ≃ₐ[F] L`. Its theorem `value_mul` gives
`value ξ (σ * τ) = value ξ σ * σ(value ξ τ)`, where `σ` acts on points by
`GaloisPoint.conjugate`, and `isTrivial_iff` says that `ξ.IsTrivial` holds
exactly when there is an `L`-point `f` of `G` with
`value ξ σ = f * σ(f)⁻¹` for every `σ`.

## Statement in words

Let `F` be a number field with no real places, and let `G` be a simply
connected, absolutely almost-simple, quasi-split group over `F` of type `D_4`
whose star action fixes none of the three leaves of the Dynkin diagram, that is,
a quasi-split group of type `³D_4` or `⁶D_4`. Then for every finite Galois
extension `L/F`, every cocycle of `G` on the cover `Spec L → Spec F` is a
coboundary on that cover. No local triviality is assumed.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Pure and
Applied Mathematics 139, Academic Press, 1994, source ID
`platonov-rapinchuk-1994-algebraic-groups-number-theory`, SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`. Page
numbers are printed page numbers; printed page `p` is page `p + 10` of the PDF
file, counting its first page as page `1`.

- §6.8, printed p. 368, opening paragraph: "In this section we shall complete
  the proof of Theorems 6.4 and 6.6 for groups of type ³,⁶D₄, ¹,²E₆, E₇, E₈, F₄
  and G₂. Throughout this section G denotes a simply connected simple K-group of
  one of the above types, and G₀ denotes a quasisplit K-group of the same inner
  type as G."
- Printed p. 371, "Groups of types ³,⁶D₄": "As before, we show first that
  H¹(K, G₀) = 1 if K is a local field or a totally imaginary number field."
- Printed p. 373, end of that argument: "This completes the proof that
  H¹(K, G₀) is trivial." Its last step reads: "But then ξ ∈ H¹(K, T₀), where T₀
  is a maximal torus of a Borel K-subgroup of G₀. Analysis of the index of G₀
  shows that T₀ has the form G_m × R_{M/K}(G_m), where M ⊂ L is a subfield of
  degree 3 over K; so H¹(K, T₀) = 1".

J.-P. Serre, *Galois Cohomology*, Springer Monographs in Mathematics, 1997
(corrected second printing 2002), source ID `serre-1997-galois-cohomology`,
SHA-256 `343aafc5fe7ebb6605effc6f6e09338f622bb977325e8cdd166152cbd6eb7cf2`;
printed page `p` of Chapter I is page `p + 8` of the PDF file.

- Chapter I, §5.8 a), printed p. 56, for a closed normal subgroup `H` of `G`
  and a `G`-group `A`: "We have the exact sequence:
  1 → H¹(G/H, A^H) → H¹(G, A) → H¹(H, A)^{G/H}, and the map
  H¹(G/H, A^H) → H¹(G, A) is injective."

## Derivation from the source (provenance: derived)

The statement is the totally imaginary half of the sentence on printed p. 371,
proved on printed pp. 371–373, written in the Library's language. The half for
local fields is not stated here.

- **Field.** A totally imaginary number field is a number field without real
  places, which is `NumberField.IsTotallyComplex F`.
- **Group.** The source's `G₀` is a quasi-split simply connected group of type
  `³D_4` or `⁶D_4`; conversely every such group is the `G₀` of the group
  `G = G₀`. Platonov and Rapinchuk's types `³,⁶D_4` are types of absolutely
  almost-simple groups with absolute root system `D_4`, so the Lean statement
  assumes `IsSimplyConnected G`, `IsAbsolutelyAlmostSimple G` and
  `IsQuasiSplit G` (the affine and finite-type instances are needed to form
  `TitsIndexData G`).
- **Type.** The absolute type `D_4` is the condition that the actual Cartan
  pairings of `d` are those of `CartanMatrix.D 4` under `e`. In Tits' notation
  `ᵗD_4`, `t` is the order of the image of the absolute Galois group, under the
  star action, in the automorphism group of the Dynkin diagram, which permutes
  the three leaves and is the symmetric group on them. The subgroups of order
  `1` or `2` of this symmetric group fix a leaf, while the subgroups of order `3`
  and `6` act transitively on the leaves. Thus the image fixes no leaf exactly
  when `t` is `3` or `6`, which is the leaf hypothesis of the statement. The
  module [`SimplyConnected.TypeD4StarOrbits`](../SimplyConnected/TypeD4StarOrbits.md)
  proves, in `TitsIndexData.star_transitive_on_D4_leaves_of_no_fixed_leaf`, that
  under this hypothesis (stated there as the nonexistence of a fixed leaf) any
  leaf is carried to any other by the star action. The module
  [`SimplyConnected.TypeD4CubicLeafField`](../SimplyConnected/TypeD4CubicLeafField.md)
  proves, in `TitsIndexData.exists_cubic_leafField_of_D4_no_fixed_leaf`, that
  each leaf then has a separable cubic field of definition inside the separable
  closure; such a field can serve as the cubic field `M` of printed p. 373.
- **Cohomology on a finite Galois cover.** The source's `H¹(K, G₀)` is the
  Galois cohomology set of the absolute Galois group with values in the points
  of `G₀` over the separable closure. Let `ξ` be a cocycle of `G` on
  `Spec L → Spec F` with `L/F` finite Galois. By `value_mul`, the family
  `σ ↦ value ξ σ` is a cocycle of `Gal(L/F)` with values in `G(L)`. Since
  `G(L)` is the set of points over the separable closure fixed by the absolute
  Galois group of `L`, Serre's injectivity statement, applied to the absolute
  Galois group of `F` and its closed normal subgroup fixing `L`, shows that the
  class of this family in `H¹(Gal(L/F), G(L))` is trivial when `H¹(F, G)` is
  trivial. Hence there is a `b ∈ G(L)` with `value ξ σ = b⁻¹ σ(b)` for every `σ`,
  and `f = b⁻¹` satisfies `value ξ σ = f σ(f)⁻¹`. By `isTrivial_iff`, `ξ` is
  trivial. So the vanishing in the source gives the Lean conclusion for every
  finite Galois `L` and every `ξ`.
- **Universe.** `F` and `L` lie in the same universe `Type u`.

## Relation to the Library

- `NumberFieldTrialitarianTypeDHasseStatement` (module
  [`Rational.NumberFieldHasseKernelTypeReduction`](NumberFieldHasseKernelTypeReduction.md))
  has the same field, group, index and leaf hypotheses, without
  `NumberField.IsTotallyComplex F` and `IsQuasiSplit G`, and assumes that the
  cocycle is locally trivial. Platonov and Rapinchuk prove the Hasse principle
  for groups of types `³,⁶D_4` (printed pp. 373–375) by choosing, with their
  Lemma 6.29, a totally imaginary quadratic extension over which the group
  becomes quasi-split and applying the present vanishing over that extension.
- `SimplyConnectedRealPlacesCohomologyStatement` (module
  [`Rational.SimplyConnectedRealPlacesCohomologyStatement`](SimplyConnectedRealPlacesCohomologyStatement.md);
  Milne, Theorem 25.65) says in its first part that, over a number field without
  real places, any two cocycles of a simply connected group on a finite separable
  field cover are cohomologous. Mathematically this contains the present
  statement. That statement writes the cover as `Over.mk (algebraBaseMap F L)`,
  and this module derives nothing from it.
- `LocalSimplyConnectedCocycleVanishingStatement` (module
  [`SimplyConnected.LocalCocycleVanishingStatement`](../SimplyConnected/LocalCocycleVanishingStatement.md))
  states the vanishing for every semisimple simply connected group over a
  nonarchimedean local field, which contains the nonarchimedean local half of
  the sentence on printed p. 371.
