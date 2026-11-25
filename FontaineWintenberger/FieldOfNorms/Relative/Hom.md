# Homomorphisms of the relative field of norms

Module `FontaineWintenberger.FieldOfNorms.Relative.Hom`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `L/K` an infinite separable APF extension. For separable algebraic extensions `M₁`, `M` of `L`, the file proves that every homomorphism `RelFieldOfNorms K L M₁ → RelFieldOfNorms K L M` over the base norm field `FieldOfNorms K L` is induced by a unique `L`-embedding `M₁ → M`. This is the full faithfulness in Wintenberger's Theorem 3.2.2(ii), extended from finite extensions to arbitrary separable algebraic ones, with its consequence for automorphism groups.

## Main definitions

* `RelFieldOfNorms.homEquiv`: the bijection between `M →ₐ[L] N` and the algebra homomorphisms `RelFieldOfNorms K L M → RelFieldOfNorms K L N` over `FieldOfNorms K L`, given by `RelFieldOfNorms.algMap`.
* `RelFieldOfNorms.endHom`, `RelFieldOfNorms.endEquiv`: the same for endomorphisms, as a monoid homomorphism and a monoid isomorphism.
* `RelFieldOfNorms.autEquiv`: the group isomorphism from `M ≃ₐ[L] M` to the automorphisms of `RelFieldOfNorms K L M` over `FieldOfNorms K L`.

## Main results

* `RelFieldOfNorms.exists_algHom_factor`: a homomorphism from a finite extension of `FieldOfNorms K L` into `RelFieldOfNorms K L M` factors through one finite stage.
* `RelFieldOfNorms.exists_finite_preimage`: a homomorphism from `FieldOfNorms K Q`, with `Q` finite over `L`, into the limit is induced by an `L`-embedding of `Q` into a finite stage `R` of `M`.
* `RelFieldOfNorms.finiteHom_faithful`: two such embeddings inducing the same map into the limit agree in `M`.
* `RelFieldOfNorms.exists_hom`: a homomorphism `f` of limits determines an embedding `t : M₁ → M` whose restrictions to finite stages induce the restrictions of `f`.
* `RelFieldOfNorms.algMap_surjective`, `algMap_injective`, `algMap_bijective`: the full Hom correspondence.
* `RelFieldOfNorms.autEquiv_of`: on a finite stage `Q`, the automorphism attached to `σ` is transport to the stage `σ(Q)`.
* `RelFieldOfNorms.autEquiv_valuation`, `RelFieldOfNorms.algEquiv_valuation`: every automorphism of `RelFieldOfNorms K L M` over `FieldOfNorms K L` preserves `RelFieldOfNorms.valuation`.

## Proofs

The finite case is an input: `FieldOfNorms.algHomEquiv K L Q R`, from `FontaineWintenberger.FieldOfNorms.Functor.FullyFaithful`, is the bijection between `L`-embeddings `Q → R` of finite extensions and homomorphisms of their norm fields. Given `f`, each finite stage `Q` of `M₁` yields an embedding into a finite stage of `M`; faithfulness at finite level makes these compatible, and `FiniteIntermediateField.liftAlgHom` glues them to `t`. `RelFieldOfNorms.algMap_of_factor` shows that `t` induces `f`.

## Remarks

* Morphisms are algebra homomorphisms over `FieldOfNorms K L`, with no continuity assumed; preservation of the valuation is a consequence.
* Several statements take the target before the source in their explicit arguments: `RelFieldOfNorms.algMap_bijective K L N M` concerns maps from `M` to `N`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3, Theorem 3.2.2(ii).

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Relative/Hom.lean` (SHA-256 of the source file `0791a70399eed80158a64287e58ed59f994a99caf9de2f47c21f41d85cd84322`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
