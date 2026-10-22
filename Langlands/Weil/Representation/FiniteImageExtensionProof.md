# Finite-image extension from the integer pullback

`Langlands.Weil.finiteImageExtension.{u, v}` proves exactly the published
`Langlands.Weil.FiniteImageExtension.{u, v}`. Its complete unapplied type is

```lean
Langlands.Weil.finiteImageExtension.{u, v} :
  Langlands.Weil.FiniteImageExtension.{u, v}
```

Unfolding the proposition gives

```lean
∀ (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
  [NonarchimedeanGroup Γ] [CompactSpace Γ] [T2Space Γ]
  (φ : Γ →ₜ* Langlands.Weil.ProfiniteIntegers), Function.Surjective φ →
  ∀ (V : Type v) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Langlands.Weil.Pullback φ) V),
    Continuous (fun w => (ρ w).toContinuousLinearMap) →
    ((Set.range ρ).Finite ↔
      ∃! σ : Representation ℂ Γ V,
        Continuous (fun g => (σ g).toContinuousLinearMap) ∧
        σ.comp (Langlands.Weil.projection φ).toMonoidHom = ρ)
```

The group and vector-space universes are independent. The objects, topology,
and projection are those of the existing `Langlands.Weil.Pullback` module.
The theorem has no additional term parameters. Existence and uniqueness of the
extension are conclusions, and the proof includes the zero-dimensional case.

## Implemented proof

The private `section_of_lifting` chooses an ambient element over the canonical
integer generator. Its integer powers define a homomorphism `t` into the actual
pullback whose degree is the identity. The published `profiniteIntegerLifting`
extends the projection of these powers to a continuous homomorphism `s` from
the genuine profinite integers into the ambient group. The composite `φ ∘ s`
agrees with the identity on the dense integer image; Hausdorffness of the
profinite integers therefore makes `s` a section of `φ`.

The private `projection_dense_of_section` proves density of the actual
pullback projection. The continuous map `(i, z) ↦ i * s z` from inertia times
the profinite integers onto the ambient group is surjective: the inertia
factor of `g` is `g * (s (φ g))⁻¹`. The product of inertia with the integer
image is dense, and its image under this map lies in the projection of the
pullback. This establishes the density used later in the proof.

The private `finite_integer_lift` treats a homomorphism `f` from `Degree` into
a topological monoid with finite image. The induced map from `Degree ⧸ f.ker`
is injective with the same image, so this quotient is finite. Evaluate a
profinite integer at this finite-index normal kernel and compose with the
quotient lift of `f`. The coordinate projection is continuous, and the finite
quotient has its discrete topology, so the composite is continuous for the
given target topology. Its restriction to the integer image is `f`.
This construction permits the monoid to lie in a universe independent of
`Degree` and does not require the target to be a group.

For a continuous finite-image homomorphism `ρ` from the pullback into a
Hausdorff topological monoid, `extend_finite_hom` applies this finite lift to
`ρ ∘ t`, obtaining `ψ`. It defines the ambient function

```text
F(g) = ρ(inertiaInclusion(g * (s(φ(g)))⁻¹)) * ψ(φ(g)).
```

Both factors are continuous. The section and integer restriction identities
show that `F(projection(w)) = ρ(w)`. This gives preservation of the identity.
The two continuous functions `(g, h) ↦ F(g*h)` and `(g, h) ↦ F(g)*F(h)` agree
on the product of the dense pullback images, so they agree everywhere.
Thus `F` is a continuous monoid homomorphism. Any other extension agrees with
it on the dense projection image, proving uniqueness by Hausdorffness.

The private `continuousRepresentation` and `extend_finite_representation`
transport this result through the finite-dimensional identification of linear
maps with continuous linear maps. Finite image passes to continuous linear
maps by taking the image of a finite set. The extension is then converted
back to a representation, with continuity, restriction, and uniqueness
transported by evaluation on vectors.

For the reverse implication, the published helper
`continuous_compact_nonarchimedean_representation_finite_range` makes the
image of any continuous ambient representation finite. Its restriction along
the pullback projection has image contained in that finite image. The private
`finiteImageExtension_of_lifting` assembles both implications, and the closing
theorem supplies the published `profiniteIntegerLifting` to its only premise.

## Provenance and dependencies

This is an internally derived proof of the existing generic structural target.
The source correspondence remains that of [Structure.md](Structure.md):
Henniart 1980, section 2.1, p. 158/PDF 5, and Tate, section 2.2, p. 10/PDF 19,
identify finite-image local Weil representations with Galois type. The
published statement explicitly generalizes that structural fact to the
integer pullback over a compact Hausdorff nonarchimedean group. The implemented
proof constructs a section directly and extends multiplicativity by density;
it does not use the finite-inertia-quotient route outlined in that statement's
explanatory paragraph. No local-field identification is asserted here.

The imported [profinite lifting proof](../ProfiniteIntegerLiftingProof.md)
supplies the arbitrary-universe completion property. The imported
[continuity proof](ContinuityProof.md) supplies the compact representation
finite-image consequence. Their public declarations are used without changes.
The finite-quotient evaluation construction follows the mechanism illustrated
by the published private `liftFinite` in
[finite-field comparison](../../Galois/FiniteField/ComparisonProof.lean),
generalized here to finite-image monoid homomorphisms. Its inputs are Mathlib's
actual finite-quotient completion, quotient-group lift, and discrete finite
quotient topology. Density arguments use `DenseRange.equalizer` and the
canonical `ProfiniteCompletion.denseRange`.

All helper declarations in this module are private. The target statement,
its paired Markdown, and all imported definitions remain unchanged.

## Development verification

The module and separate development checks compile without errors or warnings.
The checks assign the full unapplied `@finiteImageExtension.{u, v}` both to the
published proposition and to the complete expanded telescope above. Declaration
inspection reports exactly the independent universe parameters `u` and `v`,
with only `propext`, `Classical.choice`, and `Quot.sound` as axioms. These checks
do not replace the submission's formal exact-target validation, independent
semantic review, or Library publication.
