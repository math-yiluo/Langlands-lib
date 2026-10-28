# Finite generation of the kernel of the canonical tensor retraction

The module `Langlands.Algebra.TensorRetractionKernelFGStatement` defines
`Langlands.Algebra.TensorRetractionKernelFGStatement.{u, v, w} : Prop`.
Take a compatible tower of commutative rings `R → S → T` in which `S` is
essentially of finite type over `R`. The statement says that the kernel of
the canonical `S`-algebra map `μ : S ⊗[R] T →ₐ[S] T`, sending `s ⊗ t` to
`algebraMap S T s * t`, is a finitely generated ideal of `S ⊗[R] T`.
The module only defines the statement. It contains no Lean proof and
assumes no theorem.

## Exact statement

```lean
def TensorRetractionKernelFGStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T],
    Algebra.EssFiniteType R S →
      (RingHom.ker ((AlgHom.liftEquiv R S T T) (AlgHom.id R T))).FG
```

The universes `u`, `v` and `w` are independent. All three algebra
structures are given, and `IsScalarTower R S T` requires the map `R → T`
to equal the composite `R → S → T`.

## The map `μ`

The map is `μ := (AlgHom.liftEquiv R S T T) (AlgHom.id R T)`. Mathlib's
`AlgHom.liftEquiv R S A B` is the base-change adjunction
`(A →ₐ[R] B) ≃ (S ⊗[R] A →ₐ[S] B)`. Here it is used with `A = B = T`
and applied to the identity `R`-algebra map of `T`. The equivalence uses
the given `Algebra S T`, the given `Algebra R T` (both as the algebra
structure of `A` and that of `B`), and `IsScalarTower R S T`. No other
`S`-algebra structure on `T` is chosen or quantified over.

The ring `S ⊗[R] T` has Mathlib's tensor-product ring structure. Its
`S`-algebra structure acts on the left factor, and `μ` is `S`-linear for
it. By `AlgHom.liftEquiv_tmul`, which holds by `rfl`, the map satisfies

```lean
μ (s ⊗ₜ[R] t) = s • t = algebraMap S T s * t
```

The second equality is `Algebra.smul_def`. Moreover, `μ (1 ⊗ₜ t) = t`, so `μ`
is a retraction of the inclusion `t ↦ 1 ⊗ₜ t` of `T` into `S ⊗[R] T`; in
particular, it is surjective. This explains the name. When `T = S`, with the
identity algebra structure, `μ` is the multiplication map
`S ⊗[R] S → S`. Its kernel then coincides with the ideal
`KaehlerDifferential.ideal R S`, defined in Mathlib as
`RingHom.ker (TensorProduct.lmul' R)`.

`RingHom.ker μ` is the kernel ideal of `μ` in `S ⊗[R] T`, using the ring
homomorphism underlying the algebra map. The conclusion elaborates to
Mathlib's `Ideal.FG`. It asserts that some `Finset` of `S ⊗[R] T`
spans this ideal under `Ideal.span`. It is definitionally equal to
`Submodule.FG` for the ideal as an `S ⊗[R] T`-submodule.

## Hypotheses and scope

`Algebra.EssFiniteType R S` is Mathlib's unchanged class. It asserts the
existence of a finite set `σ ⊆ S` such that `S` is the localization of
the subalgebra `R[σ]` at the elements of `R[σ]` that become units in `S`.
The module does not define essential finiteness or tensor products itself.

There are no hypotheses on `T` beyond the tower: no finite type,
finite presentation, essential finite presentation, locality,
Noetherianity, flatness, injectivity or nontriviality. Nor is any
finite-presentation, finite-denominator-generation or Noetherian
assumption made on `S`. Zero rings are allowed. The conclusion
concerns only finite generation of this one kernel. It asserts no
cancellation result for essential finite presentation.

## Internal provenance

This is an internal supporting lemma. It is not a displayed statement
of a cited source. It serves the cancellation proof task
`111a8cec-091c-4186-bfe2-036cc141210a`, whose target is the published
`Langlands.Algebra.EssFinitePresentationTowerCancellationStatement`.
That route uses the published base-change theorem
`Langlands.Algebra.essFinitePresentation_baseChange`, which makes
`S ⊗[R] T` essentially finitely presented over `S` when `T` is
essentially finitely presented over `R`. It also uses the published
quotient closure `Langlands.Algebra.essFinitePresentationFiniteQuotient`.
Since `μ` is surjective, `S ⊗[R] T ⧸ RingHom.ker μ` is isomorphic to `T`
as an `S`-algebra. The present kernel statement is the remaining input
that makes this quotient a quotient by a finitely generated ideal. That
consumer would also need essential finite type of `S` over `R`, obtained
from essential finite presentation. That step and the transport along the
quotient isomorphism belong to the consumer, not to this module.

The statement generalizes Mathlib's `KaehlerDifferential.ideal_fg`, which
covers the case `T = S` described above. The informal argument below follows
the pattern of that Mathlib proof.

## Finite-relations justification

The following is an informal derivation of the stated assertion. It is
not a Lean proof; the proof is left to a separate successor task.

Choose a finite set `σ ⊆ S` that witnesses essential finite type, for
example Mathlib's `Algebra.EssFiniteType.finset R S`. Let `J` be the
ideal of `S ⊗[R] T` spanned by the finitely many elements
`s ⊗ 1 - 1 ⊗ algebraMap S T s` for `s ∈ σ`. Each of these lies in
`ker μ`, because both terms map to `algebraMap S T s`. Hence `J ≤ ker μ`.

For the reverse inclusion, let `q : S ⊗[R] T → (S ⊗[R] T) ⧸ J` be the
quotient map. Consider two `R`-algebra maps `S → (S ⊗[R] T) ⧸ J`. The
first is `s ↦ q (s ⊗ 1)`. The second is `s ↦ q (1 ⊗ algebraMap S T s)`;
it is `R`-linear because of `IsScalarTower R S T`. The two maps agree on
`σ`, by the definition of `J`. Therefore they agree on all of `S`, by
`Algebra.EssFiniteType.algHom_ext`: an `R`-algebra map out of an
essentially finite type algebra is determined by its values on the
chosen finite set. Hence, for every pure tensor,

```text
q (s ⊗ t) = q (s ⊗ 1) * q (1 ⊗ t)
          = q (1 ⊗ algebraMap S T s) * q (1 ⊗ t)
          = q (1 ⊗ μ (s ⊗ t)).
```

Both sides are additive in the tensor, so tensor-product induction gives
`q x = q (1 ⊗ μ x)` for every `x`. If `μ x = 0`, then `q x = 0`, so `x ∈ J`.
Thus `ker μ = J`, and `J` is spanned by a finite set.
