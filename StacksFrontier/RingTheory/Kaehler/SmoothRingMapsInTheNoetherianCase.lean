module

import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Smooth.Locus
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Smooth ring maps in the Noetherian case

Let `R` be a Noetherian ring, let `S` be an `R`-algebra of finite type and let `q` be a prime of
`S`. Then `R → S` is smooth at `q` if and only if the lifting property of formal smoothness holds
along a very restricted class of surjections: it suffices to test it on *small extensions* of
Artinian local rings, that is on surjections `B' → B` of local Artinian rings whose kernel has
length `1` as a `B'`-module, and even only on those small extensions along which the induced map
of residue fields `κ(q) → κ(𝔪)` is an isomorphism. Concretely, four conditions are equivalent:

1. `R → S` is smooth at `q`;
2. every surjection of local `R`-algebras `B' → B` with square-zero kernel, and every `R`-algebra
   map `S → B` pulling the maximal ideal of `B` back to `q`, admit a lift `S → B'`;
3. the same, with `B' → B` ranging only over small extensions;
4. the same, with `B' → B` ranging over small extensions along which the induced map of residue
   fields `κ(q) → κ(𝔪)` is an isomorphism.

## Main results

* `Algebra.isSmoothAt_tfae`: the equivalence of (1)–(4), as a `List.TFAE`.

## Implementation notes

Smoothness at `q` is `Algebra.IsSmoothAt R q`, that is `Algebra.FormallySmooth R S_q`, rather than
"there is `g ∉ q` with `R → S_g` smooth". The two agree because `R` is Noetherian and
`R → S` of finite type, hence of finite presentation, and Mathlib carries the equivalence for
finitely presented algebras in `Algebra.IsSmoothAt.exists_notMem_smooth`.

A square-zero extension is presented as a surjective `R`-algebra map `f : B' →ₐ[R] B` with
`ker f ^ 2 = ⊥`, rather than as `B' → B' ⧸ I` with `I ^ 2 = ⊥` in the manner of
`Algebra.FormallySmooth.iff_comp_surjective`, so that the target of `S → B` is a ring carrying
`IsLocalRing` as a hypothesis: Mathlib has no instance making `B' ⧸ I` a local ring, and the
maximal ideal `𝔪` of `B` is part of the data. The two forms are interchangeable along
`Ideal.quotientKerAlgEquivOfSurjective`.

"`ker (B' → B)` has length `1` as a `B'`-module" is `IsSimpleModule B' (ker f)`, which is
`Module.length B' (ker f) = 1` by `Module.length_eq_one_iff`. Condition (3) therefore does not
repeat `ker f ^ 2 = ⊥`: a simple `B'`-module is killed by the maximal ideal `𝔪'` of `B'`, and
`ker f ⊆ 𝔪'`, so `(ker f)² ⊆ 𝔪' · ker f = 0`.

The residue field isomorphism of (4) is surjectivity of the canonical map
`Ideal.ResidueField.mapₐ q (maximalIdeal B) g hq.symm : κ(q) →ₐ[R] κ(𝔪)` attached to the equality
`q = g⁻¹(𝔪)` that the condition already carries; surjectivity is the whole of "isomorphism", a
ring map between fields being injective. Here `κ(q)` is the residue field of `S_q` and not of `S`:
surjectivity of the composite `S → B → κ(𝔪)` is strictly stronger, and strong enough to force `q`
maximal, that composite having kernel `g⁻¹(𝔪) = q` and hence image the field `S/q`. What is true
is that the image of `κ(q)` in `κ(𝔪)` is the *fraction field* of the image of `S/q`, and that
image need not be all of it — for `S = ℤ`, `q = (0)`, `B = ℚ` the map `κ(q) = ℚ → ℚ = κ(𝔪)` is an
isomorphism while `ℤ → ℚ` is not onto. Read on `S_q` the class of test objects in (4) is nonempty
at every prime, maximal or not: the small extension `κ(q)[ε]/(ε²) → κ(q)` induces the identity of
`κ(q)`. Read on `S` it would be empty at every non-maximal prime, and the equivalence false there.

The auxiliary rings `B'`, `B` range over `Type max u v` for `R : Type u` and `S : Type v`, the
universe in which `Algebra.FormallySmooth.iff_comp_surjective` states the lifting property of
formal smoothness; as there, this costs no generality, every witness being transportable along a
`ULift` equivalence. No prime `𝔭 ⊂ R` under `q` is a hypothesis: none of (1)–(4) mentions it,
and it is determined by `q` as `q.comap (algebraMap R S)`.

For the implication (4) ⇒ (1), `S_q` is presented as a quotient of the local ring
`P = R[x_1, …, x_n]_{q'}`, formally smooth over `R`, with `q'` the prime of the polynomial ring
under `q`. The Jacobian criterion for local algebras,
`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`, reduces smoothness
at `q` to injectivity of the single map of `κ(q)`-vector spaces `κ(q) ⊗_P J → κ(q) ⊗_P Ω[P⁄R]`,
where `J = ker (P → S_q)`. That injectivity is proved by duality: a functional separating a
nonzero element of `κ(q) ⊗_P J` restricts to a `P`-linear `u : J → κ(q)`, functionals on
`κ(q) ⊗_P Ω[P⁄R]` are `R`-derivations `P → κ(q)`, and so it suffices to extend every such `u` to a
derivation, which one small extension built from `u` and Artin–Rees provides.

## References

* [StacksProject 02HT](https://stacks.math.columbia.edu/tag/02HT); small extensions are
  [Tag 02HS](https://stacks.math.columbia.edu/tag/02HS) and smoothness at a prime is
  [Tag 00TB](https://stacks.math.columbia.edu/tag/00TB).
* [StacksProject 00IN](https://stacks.math.columbia.edu/tag/00IN), Artin–Rees, which is
  `Ideal.exists_pow_inf_eq_pow_smul`.
-/

@[expose] public section

universe u v

open IsLocalRing

/-- A proper quotient of a local ring is a local ring. -/
theorem isLocalRing_quotient {P : Type*} [CommRing P] [IsLocalRing P] {b : Ideal P}
    (hb : b ≠ ⊤) : IsLocalRing (P ⧸ b) :=
  have : Nontrivial (P ⧸ b) := Submodule.Quotient.nontrivial_iff.mpr hb
  .of_surjective' _ Ideal.Quotient.mk_surjective

namespace Algebra

end Algebra

end
