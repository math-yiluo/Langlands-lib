# The local closed-immersion criterion at a rational point

The theorem
`Langlands.AlgebraicGeometry.properRationalImmersion_localClosedImmersion`
proves exactly the published proposition
`Langlands.AlgebraicGeometry.ProperRationalImmersionLocalClosedImmersionStatement.{u}`.
Its module is
`Langlands.AlgebraicGeometry.ProperRationalImmersionLocalClosedImmersionProof`.
The target and its imported Lean/Markdown pairs are unchanged.

## Statement and scope

Let `K : Type u` be an algebraically closed field of arbitrary characteristic,
and let `X` and `Y` be schemes in universe `u`, with structure morphisms
`p : X ⟶ Spec K` and `q : Y ⟶ Spec K` locally of finite type. Let `f : X ⟶ Y`
be proper, with `f ≫ q = p`, and let `x : Spec K ⟶ X` be rational for `p`.
Assume that every rational point with the same image under `f` equals `x`,
and that every dual-number tangent at `x` whose image is constant equals the
constant tangent at `x`. Then there is an open `V` of `Y` containing
`f (x (IsLocalRing.closedPoint K))` such that `IsClosedImmersion (f ∣_ V)`.
Here the source of `f ∣_ V` is the entire inverse image of `V`.

The final theorem has no outer hypotheses. In particular, the four supporting
propositions are supplied by their published proofs, rather than assumed.
Local Noetherianity used in the argument is derived from local finite type
over `K`. The structure morphisms need not be proper, and the schemes may
be non-reduced, non-separated, or non-quasi-compact. Empty schemes are included
by the quantified target; a rational point is required only when applying its
pointwise implication.

## Published inputs

The helper `properRationalImmersion_localClosedImmersion_of` assembles the four
supporting propositions as hypotheses `h₁`, `h₂`, `h₃`, and `h₄`. The final theorem
instantiates them with these imported results:

| Input | Theorem | Module |
| --- | --- | --- |
| `h₁`: singleton fibre and finite target neighbourhood | `Langlands.AlgebraicGeometry.uniqueRationalFiber_finiteNeighborhood` | `Langlands.AlgebraicGeometry.UniqueRationalFiberFiniteNeighborhoodProof` |
| `h₂`: cotangent surjectivity from the tangent hypothesis | `Langlands.AlgebraicGeometry.tangentKernel_cotangentSurjectivity` | `Langlands.AlgebraicGeometry.TangentKernelCotangentSurjectivityProof` |
| `h₃`: surjectivity of a finite augmented local algebra map | `Langlands.CommutativeAlgebra.finiteLocalCotangentSurjectivity` | `Langlands.CommutativeAlgebra.FiniteLocalCotangentSurjectivityProof` |
| `h₄`: finite stalk map and spreading of its surjectivity | `Langlands.AlgebraicGeometry.finiteSingletonFiber_localClosedImmersion` | `Langlands.AlgebraicGeometry.FiniteSingletonFiberStalk` |

The first, second, and fourth inputs are instantiated at universe `u`; the
three independent levels of the third input are each instantiated at `u`.
The imported companions explain the focused proofs of these inputs.

## Implemented proof

Write `z = x (IsLocalRing.closedPoint K)`.

1. `h₁` gives the topological fibre equality `f ⁻¹' {f z} = {z}` and an open
   `V₀` containing `f z` over which `f` is finite. View `z` as a point `z'`
   of the whole inverse image `f ⁻¹ᵁ V₀`.
2. The point formula `morphismRestrict_base_coe` and the fibre equality show
   that the fibre of `f ∣_ V₀` through `z'` is `{z'}`. Applying `h₄` gives
   finiteness of its actual stalk homomorphism and a spreading implication
   from surjectivity of that homomorphism.
3. `morphismRestrictStalkMap` identifies the stalk homomorphism of the
   restriction with that of `f` at `z` as arrows up to isomorphism.
   `RingHom.finite_respectsIso` transports finiteness to the latter map,
   with the scalar action induced by that map.
4. `LocallyOfFiniteType.isLocallyNoetherian p` makes `X` locally Noetherian,
   hence its stalk at `z` is Noetherian. Equip the stalks with the canonical
   algebras `Picard.stalkAlgebraOver`. The ring homomorphism of
   `Picard.stalkMapAlgHomOver p q f hfq z` is exactly the actual stalk map,
   by `Picard.stalkMapAlgHomOver_toRingHom`. The rational augmentation is
   `Picard.rationalStalkAugmentation p x hx`.
5. `h₂` supplies surjectivity of the corresponding augmentation cotangent
   map. `h₃`, applied with this surjectivity and the finite stalk map, makes
   the stalk algebra map surjective. The same ring-map equality gives
   surjectivity of the actual stalk homomorphism of `f` at `z`.
6. `RingHom.surjective_respectsIso` and `morphismRestrictStalkMap` transport
   surjectivity back to `f ∣_ V₀`. The spreading implication from step 2
   gives an open `V'` in `V₀` containing `(f ∣_ V₀) z'` over which
   `f ∣_ V₀` is a closed immersion.
7. Set `V = V₀.ι ''ᵁ V'`. The point formula shows `f z ∈ V`.
   `morphismRestrictRestrict` identifies the iterated restriction
   `f ∣_ V₀ ∣_ V'` with `f ∣_ V` as arrows up to isomorphism.
   `MorphismProperty.arrow_mk_iso_iff` for `IsClosedImmersion` therefore
   gives the required closed immersion on the entire preimage of `V`.

The rational-point uniqueness hypothesis is used through `h₁`; the tangent
hypothesis is used through `h₂`. The construction never shrinks only the
source. The conclusion uses Mathlib's scheme-theoretic closed immersion,
including surjectivity on all stalks of the final restriction.

## Provenance and authorship

This is an internal assembly of the four published supporting results and
Mathlib's restriction isomorphisms. The unchanged target companion documents
its derivation from the finite-morphism and Nakayama steps of Stacks Project
Lemma 33.23.1, tag 0E8R, registered as
`stacks-very-ampleness-support-2026-10-29`. This module implements the local
extraction described there; it introduces no line bundle or projectivity
premise. No downstream global closed-immersion or ample-existence result
is used.

Worker 898 wrote the conditional Lean assembly and its original explanation.
Worker 487 supplied the four interfaces and their geometric route. Worker 362
reused that assembly, imported the independently published proofs, added the
unconditional theorem, and prepared this companion and submission. The
conditional helper remains available, while the final theorem supplies all
four of its premises. The proof uses only `propext`, `Classical.choice`, and
`Quot.sound`.
