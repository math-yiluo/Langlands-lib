# Proof of Galois descent for the actual idele inclusion

`Langlands.ClassField.Global.ideleGaloisDescent` proves exactly the published
proposition `Langlands.ClassField.Global.IdeleGaloisDescent.{u, v}` from
`IdeleGaloisDescentStatement`. Its type is the unapplied proposition
`IdeleGaloisDescent.{u, v}`. The universes `u` of `K` and `v` of `E` stay
independent. The proof uses the published maps unchanged:
`ideleInclusion`, `adeleInclusion`, `finiteAdeleInclusion` and
`infiniteAdeleMap (algebraMap K E)` from `AdelicFunctoriality.Inclusion`, and
`ideleEquiv`, `adeleEquiv`, `finiteAdeleEquiv`, `infiniteAdeleEquiv`,
`finiteCompletionEquiv` and `infiniteCompletionEquiv` from
`AdelicFunctoriality.Finite`, `Infinite` and `Isomorphism`. No substitute
carrier, model or descent hypothesis is introduced.

All auxiliary results are in the namespace
`Langlands.ClassField.Global.IdeleGaloisDescentProof`.

## Fixed tensors are pure tensors

The section `TensorInvariants` works for any `K`-module `A` and finite Galois
extension `E/K` with `CharZero K`.

- `sum_lTensor_aut` sums the automorphisms acting on the second factor of
  `A ⊗[K] E`. The sum equals `lTensor` of the trace followed by
  `algebraMap K E`, by induction on tensors and Mathlib's
  `trace_eq_sum_automorphisms`.
- `lTensor_algebraMap_eq` shows that `lTensor` of `algebraMap K E` sends
  `w : A ⊗[K] K` to `(rid w) ⊗ 1`.
- `exists_tmul_one_of_lTensor_aut_eq`: suppose `t` is fixed by every `σ`.
  Then the sum is `|Gal(E/K)| • t`, which is `[E : K] • t` by
  `IsGalois.card_aut_eq_finrank`. The two facts above write the sum as
  `z ⊗ 1`. Since `[E : K]` is nonzero in `K`, `t = ([E : K]⁻¹ • z) ⊗ 1`.
- `exists_tmul_one_of_comparison` transfers this through a bijection `T`
  that turns the second-factor action into a given action on its target.
  Every fixed point of the target action is `T (x ⊗ 1)` for some `x : A`.

## Finite places

Let `p` be a finite place of `K`, and let `σ : E ≃ₐ[K] E`.

- `finitePlaceEquiv_under` and `liesOver_finitePlaceEquiv`: the published
  place transport `finitePlaceEquiv σ.toRingEquiv` keeps the prime of `𝓞 K`
  below a prime of `𝓞 E`. So it permutes `FinitePlacesAbove E p`.
- `finiteCompletionEquiv_completionMap`: if `q` lies over `p`, then
  `finiteCompletionEquiv σ q` composed with the completed embedding of `K_p`
  into the completion at the transported place is the completed embedding of
  `K_p` into `E_q`. Both sides are continuous and agree on the dense image of
  `K`, because `σ` fixes `K`.
- `finiteAdeleInclusion_apply_of_liesOver`: if `q` lies over `p`, the
  `q`-coordinate of `finiteAdeleInclusion x` is
  `FiniteExtension.completionMap p q (x p)`.
- `finiteAdeleInclusion_injective`: every finite place of `K` has a place
  above it (`finitePlacesAbove_nonempty`), and each completed embedding is
  injective.
- `finiteAdeleEquiv_finiteAdeleInclusion`: the image of
  `finiteAdeleInclusion` is fixed by `finiteAdeleEquiv σ.toRingEquiv`. This
  follows coordinatewise from the two previous coordinate formulas.
- `finiteAboveAction σ p` acts on tuples indexed by `FinitePlacesAbove E p`.
  Its `q`-coordinate applies `finiteCompletionEquiv σ q` to the coordinate
  at the transported place. `finiteTensorMap_lTensor` proves
  `finiteTensorMap p ∘ lTensor σ = finiteAboveAction σ p ∘ finiteTensorMap p`.
  On a pure tensor this is the multiplicativity of `finiteCompletionEquiv`,
  the previous compatibility, and `finiteCompletionEquiv_coe`.
- `exists_finite_descent`: let `a` be a finite adele of `E` fixed by every
  `finiteAdeleEquiv σ.toRingEquiv`. Its coordinates above `p` form a fixed
  point of `finiteAboveAction`. The published theorem
  `completedTensorComparison` makes `finiteTensorMap p` bijective. So the
  tensor lemma gives `x : K_p` with
  `FiniteExtension.completionMap p q x = a q` for every `q` above `p`.
- `exists_finiteAdele_descent` chooses such an `x p` for every `p`. It shows
  that the family is a restricted product. Fix a place `q` of `E` above `p`.
  By `FiniteExtension.completionMap_mem_integers_iff`, if `x p` is not
  integral then `a q` is not integral. So the exceptional places of the
  family lie in the image, under `under`, of the finite exceptional set of
  `a`. The resulting finite adele maps to `a`, by the coordinate formula of
  `finiteAdeleInclusion`.

## Infinite places

Let `p` be an infinite place of `K`.

- `liesOver_of_comap_eq` and `liesOver_infinitePlaceEquiv`: the place
  transport `infinitePlaceEquiv σ.toRingEquiv` permutes the places above `p`,
  because `σ` fixes `K`.
- `infiniteAdeleMap_apply_of_liesOver`: if `q` lies over `p`, the
  `q`-coordinate of `infiniteAdeleMap (algebraMap K E) x` is
  `NumberField.LiesOver.completionMap (x p)`. Both are continuous and agree
  on the dense image of `K`.
- `infiniteAdeleMap_injective` uses `InfinitePlace.comap_surjective` and
  injectivity of each completed embedding.
- `infiniteAdeleEquiv_infiniteAdeleMap`: the image is fixed, by
  `infiniteAdeleMap_comp` and `σ ∘ algebraMap K E = algebraMap K E`.
- `infiniteTransport σ q` is `infiniteCompletionEquiv σ.toRingEquiv q`,
  with its source written as the completion at
  `infinitePlaceEquiv σ.toRingEquiv q`. The two source types are
  definitionally equal. This form lets the rewriting below typecheck
  syntactically. `infiniteTransport_coe` and
  `infiniteTransport_completionMap` are the analogues of the finite
  lemmas. The second is again proved by density.
- `infiniteAboveAction`, `infiniteTensorMap_lTensor`,
  `exists_infinite_descent` and `exists_infiniteAdele_descent` follow the
  finite argument. They use bijectivity of `infiniteTensorMap p` from
  `completedTensorComparison`. No integrality condition is needed, since the
  infinite adele ring is the full product.

## Adeles and ideles

`adeleInclusion_injective`, `adeleEquiv_adeleInclusion` and
`exists_adele_descent` combine the two components of the published
`adeleInclusion` and `adeleEquiv`.

In `ideleGaloisDescent`, injectivity of `ideleInclusion` follows from
injectivity of `adeleInclusion` on underlying adeles. For the equivalence,
let `a` be an idele fixed by every `ideleEquiv σ.toRingEquiv`. The adeles
underlying `a` and `a⁻¹` are both fixed, since `ideleEquiv σ.toRingEquiv` is
multiplicative. So they have preimages `b` and `b'` under `adeleInclusion`.
`adeleInclusion` is a ring homomorphism, so it sends `b * b'` and `b' * b`
to `1`. By injectivity both products equal `1`. So `b` is a unit of the
adele ring of `K`, and its image under `ideleInclusion` is `a`. Conversely,
the image of every idele of `K` is fixed, by `adeleEquiv_adeleInclusion` on
underlying adeles.

## Dependencies and route

The module imports the target statement, the module
`AdelicFunctoriality.CompletedTensorComparisonProof` with the published
theorem `completedTensorComparison`, the module
`AdelicFunctoriality.LocalDegree`, and `Mathlib.RingTheory.Trace.Basic`.
Through these imports it uses the published results
`finitePlacesAbove_nonempty` (`LocalDegree`), `finitePlacesAbove_under`
(`Norm`), `liesOver_under` (`Inclusion`) and
`FiniteExtension.completionMap_mem_integers_iff` (`CompletedRamification`).
Apart from `ideleGaloisDescent`, every declaration of the module is a helper
in the namespace above. The module adds no axioms.

The mathematical statement is from Emil Artin and John Tate, *Class Field
Theory*, AMS Chelsea edition (2009), Preliminaries section 1, printed
pp. 1–2 (PDF pp. 10–11), registered as `artin-tate-2009-class-field-theory`.
The source says that `J_k ≅ J_K^G` follows from the definitions of ideles and
of the embedding. The Lean proof does not use the source's decomposition
groups. It obtains the local descent at each place of `K` from the published
bijection `K_p ⊗[K] E ≅ ∏_{q | p} E_q` and averaging over `Gal(E/K)`.
