# Flat finitely presented models from pointwise flat stages

Authors: Worker 1103, Worker 866.

This helper module carries out the global step of Stacks Project, Algebra,
Lemma 10.168.1, part (1) (Tag 02JO), in the case `M = S`. Let `B` be a
finitely presented `A`-algebra with a presentation `P`. Assume that every prime
of `B` lies in the flat set of some stage of `P` (defined below). Then some
stage model is flat over its base ring. Combined with the pointwise step from
`Langlands.Algebra.FinitePresentationStageFlatness`, this gives
`Langlands.Algebra.exists_flat_finitePresentation_model`: a flat finitely
presented algebra has a flat finitely presented model over a subring of finite
type over `ℤ`. That theorem lives in the namespace `Langlands.Algebra`; all
other declarations live in `Langlands.Algebra.FlatFinitePresentationModel`.
The module adds no axioms.

The stages, their transitions and the colimit facts come from Worker 866's
module `Langlands.Algebra.FinitePresentationStages`. Openness of the flat locus
comes from `Module.Flat.isOpen_setOf_flat_localization_atPrime`, imported through
`Langlands.Algebra.NoetherianFlatLocusOpen`.

## Provenance

- The statement `exists_flat_model_of_forall_mem_flatSet` is the step of the
  proof of Stacks 10.168.1(1) (Tag 02JO) that comes after the pointwise
  statement. Stacks shows that for every prime `q` of `S` some stage
  `S_λ` is flat over `R_λ` at the prime under `q`. Then it uses openness of
  the flat locus of `S_λ` over the Noetherian ring `R_λ` and
  quasi-compactness of `Spec S` to find one stage that is flat at all primes
  under primes of `S`. Finally the complement of the flat locus of that
  stage is `V(I)` for an ideal `I` with `IS = S`. Then `I S_μ = S_μ` for some
  later stage `μ`, and `S_μ` is flat over `R_μ`.
- The Lean proof follows this route. The pointwise statement is the
  hypothesis `hstage`, supplied by Worker 866's module
  `Langlands.Algebra.FinitePresentationStageFlatness`. Openness of the flat
  locus is the Noetherian case `M = S` of Stacks Algebra, Theorem 10.129.4
  (Tag 00RC).
- The lemmas about flat sets, transitions and extended ideals are standard
  internal steps of this proof, stated separately.

## Declarations

`flat_atPrime_of_eq`: if `I = J` are prime ideals of an `R`-algebra `S` and
the localization at `I` is flat over `R`, then so is the localization at
`J`. Proof by substitution. The lemma moves flatness along equalities of
prime ideals, which the type of `Localization.AtPrime` depends on.

`flatSet P t`: the set of primes `Q` of `B` such that the localization of the
stage model `model P t` at the prime `Q ∩ model P t` (the preimage of `Q`
under `toB P t`) is flat over the stage base `base P t`. `mem_flatSet`
unfolds the definition.

`flatSet_mono`: for `t ⊆ t'`, `flatSet P t ⊆ flatSet P t'`. The prime of
`model P t` under `Q` is the preimage of the prime of `model P t'` under `Q`
(`comap_trans_comap_toB`). Worker 866's `flat_localization_trans` passes
flatness from a stage to every later stage at every prime over it.

`directed_flatSet`: the flat sets form a directed family. For stages `t` and
`t'`, the stage `t ∪ t'` contains both flat sets.

`isOpen_flatSet`: for a presentation with finitely many variables and
relations, each flat set is open in `Spec B`. It is the preimage under
`Spec B → Spec (model P t)` of the flat locus of `model P t` over the
Noetherian ring `base P t`, and that locus is open by
`Module.Flat.isOpen_setOf_flat_localization_atPrime`.

`trans_comp`: the transition from `t` to `t'` followed by the transition from
`t'` to `t''` is the transition from `t` to `t''`, as ring homomorphisms.

`trans_mem_map_trans`: if `x` lies in the extension of an ideal `J` of
`model P t` to `model P t'`, then the transition of `x` to `model P t''`
lies in the extension of `J` to `model P t''`.

`exists_mem_map_trans`: every element `b` of the extension of an ideal `J` of
`model P t` to `B` is the image of an element of the extension of `J` to some
later stage. Proof by induction on `b` as an element of the span of the image
of `J`. Generators come from stage `t` itself. Sums are handled at the union
of the two stages. For a multiple `c b`, Worker 866's `exists_lift` lifts
`c` to some later stage.

`exists_map_trans_eq_top`: if an ideal `J` of `model P t` generates the unit
ideal of `B` and `P` has finitely many relations, then `J` generates the unit
ideal of some later stage. By `exists_mem_map_trans`, `1 ∈ J B` comes from
some `x ∈ J model P t'` with image `1` in `B`. Worker 866's
`exists_trans_eq_zero` makes `x - 1` vanish at a later stage `t''`. So `1`
lies in the extension of `J` to `model P t''`.

`flat_of_univ_subset_flatSet`: if every prime of `B` lies in `flatSet P t`,
then for every prime `Q` of `B` the localization of `model P t` at
`Q ∩ model P t` is flat over `base P t`.

`exists_ideal_flat_iff`: for finitely many variables and relations, there is
an ideal `J` of `model P t` such that the localization of `model P t` at a
prime `q` is flat over `base P t` exactly when `J` is not contained in `q`.
The complement of the open flat locus is closed, so it is the zero locus of an
ideal.

`map_toB_eq_top`: if every prime of `B` lies in `flatSet P t`, and `J` is an
ideal of `model P t` that is not contained in any prime at which `model P t`
is flat, then `J` generates the unit ideal of `B`. Otherwise `J B` lies in a
maximal ideal `M` of `B`. Then `J` lies in `M ∩ model P t`, but the stage is
flat at that prime.

`flat_of_map_trans_eq_top`: let `t ⊆ t'` and let `J` be an ideal of
`model P t` such that `model P t` is flat at every prime not containing `J`.
If `J` generates the unit ideal of `model P t'`, then `model P t'` is flat
over `base P t'`. Flatness is checked at the maximal ideals `M` of
`model P t'` (Mathlib's `Module.flat_of_isLocalized_maximal`). The prime
`M ∩ model P t` does not contain `J`, since otherwise `M` would contain the
unit ideal. So `model P t` is flat there, and `flat_localization_trans`
gives flatness of `model P t'` at `M`.

`exists_flat_model_of_forall_mem_flatSet`: **glue for Stacks 10.168.1(1).**
Let `P` have finitely many variables and relations, and assume every prime of
`B` lies in some flat set. Then `model P t` is flat over `base P t` for some
stage `t`. The flat sets are open (`isOpen_flatSet`), directed
(`directed_flatSet`) and cover `Spec B`, which is quasi-compact. So one flat
set `flatSet P t₁` is all of `Spec B`. Take `J` from
`exists_ideal_flat_iff` for `t₁`. By `map_toB_eq_top` it generates the unit
ideal of `B`, and by `exists_map_trans_eq_top` the unit ideal of a later
stage `t₂`. Then `flat_of_map_trans_eq_top` shows that `model P t₂` is flat.

`exists_flat_model_of_forall_mem_flatSet_ofFinitePresentation`: the previous
theorem for a finitely presented `A`-algebra `B`, with `A` and `B` in the
same universe, and Mathlib's standard presentation
`Algebra.Presentation.ofFinitePresentation A B`. If every prime of `B` lies
in a flat set of this presentation, then there are a `ℤ`-subalgebra `A₀` of
`A` of finite type over `ℤ` and a finitely presented, flat `A₀`-algebra `B₀`
with an `A`-algebra isomorphism `A ⊗[A₀] B₀ ≃ₐ[A] B`. Take `A₀ = base P t`
and `B₀ = model P t` for the stage `t` from the previous theorem. The
isomorphism is Worker 866's `nonempty_tensor_model`.

`Langlands.Algebra.exists_flat_finitePresentation_model`: **Stacks
10.168.1(1)** (Tag 02JO) in the case `M = S`, for `A` and `B` in the same
universe. If `B` is a finitely presented and flat `A`-algebra, then there are
a `ℤ`-subalgebra `A₀` of `A` of finite type over `ℤ` and a finitely
presented, flat `A₀`-algebra `B₀` with an `A`-algebra isomorphism
`A ⊗[A₀] B₀ ≃ₐ[A] B`. Proof: apply the previous theorem. Its hypothesis, that
every prime `Q` of `B` lies in a flat set of the standard presentation, is
Worker 866's `exists_flat_stage` (module
`Langlands.Algebra.FinitePresentationStageFlatness`) for the prime
`Q.asIdeal`.

The module allows 4,000,000 elaboration heartbeats and 400,000
typeclass-search heartbeats for localization module structures and
finite-presentation comparisons with the imported flat-locus theorem.
These options change only compiler resource limits.
