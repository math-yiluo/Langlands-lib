# Connectedness of finite-type Weil restrictions over a local Artinian coefficient algebra

This internal helper module proves the connectedness input for the
equal-characteristic Greenberg point model
(`EqualCharacteristicGreenbergProof.md`). It is stated purely algebraically,
for the spectrum of the Library's finite-type Weil restriction
`WeilRestrictionFiniteType k B O`.

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem A.4.19(4)
(printed p. 628–629, PDF p. 659–660) asserts `Grₙ(X⁰) = Grₙ(X)⁰`. In residue
characteristic zero it cites Conrad–Gabber–Prasad, Propositions A.5.2(4) and
A.5.11(3). In positive characteristic it cites A.4.12 and an induction through
the vector-group kernels of part (3). This module does not follow either route.
It proves the special case needed by the target directly. If the special fibre
of a smooth affine group is connected, the Weil restriction is connected. The
argument is an affine-line path argument together with a formal-smoothness
section of the special fibre.

## Setting

Throughout, `k` is a field, `B` is a finite `k`-algebra, and `O` is a
finite-type `B`-algebra. The final results also assume the following:

* `k` is algebraically closed;
* `B` has an algebra map `B → k` with `IsScalarTower k B k`, so `B → k`
  is a retraction of `k → B`;
* the kernel of `B → k` is a nilpotent ideal (`hnil`);
* `O` is formally smooth over `B`.

Each lemma states its own hypotheses. `omit` removes the ones a lemma does not
use.

## Topology and points

* `connectedSpace_of_closedPoints`: let `X` be a compact T0 space with a point
  `x₀`. If every closed point lies in the connected component of `x₀`, then
  `X` is connected. Let `s` be a nonempty clopen set. Its complement, if
  nonempty, is closed. A nonempty closed subset of a compact T0 space contains a
  closed point (`IsClosed.exists_closed_singleton`). So both `s` and any
  nonempty complement would meet the component of `x₀`. A clopen set contains
  or misses each connected component entirely, so this is impossible.
* `ratPoint ψ` is the prime `ker ψ` of a `k`-algebra map `ψ : R → k`.
  `comap_ratPoint` says that pulling back along `φ` sends `ratPoint t` to
  `ratPoint (t ∘ φ)`.
* `ratPoint_mem_connectedComponent`: let `T` have connected spectrum. Then any
  two rational points that factor through `φ : R → T` lie in one connected
  component. They lie in the image of the connected space `Spec T` under the
  continuous map `comap φ`.
* `exists_ratPoint_eq` (Nullstellensatz): let `k` be algebraically closed and
  `R` of finite type over `k`. Then every closed point of `Spec R` is
  `ratPoint ψ` for some `ψ`. The residue field `R/𝔪` is of finite type over
  `k`. Mathlib's `finite_of_finite_type_of_isJacobsonRing` makes it finite over
  `k`. It is integral over the algebraically closed field `k`, so it equals
  `k` (`IsAlgClosed.algebraMap_bijective_of_isIntegral`).

## Affine-line paths

`exists_path` is a general lemma. The data are:

* an `O` that is formally smooth over `B`;
* `B`-algebras `P` and `D`, with a map `ι : D → P` and two maps
  `e₀, e₁ : P → D`, each a retraction of `ι`;
* an element `t ∈ P` with `e₀ t = 0` and `e₁ t = 1`;
* a nilpotent ideal `I` of `D` and two maps `f, g : O → D` with
  `f - g ∈ I` pointwise.

Then there is `h : O → P` with `e₁ ∘ h = f` and `e₀ ∘ h = g`. The proof sets
`u(o) = ι(g o) + t · ι(f o - g o)` and `J = (t(t-1)) · I P`. The ideal `J` is
nilpotent because `I` is. A computation by `ring` gives

  `u(ab) - u(a)u(b) = t(t-1) · ι(-(f a - g a)(f b - g b)) ∈ J`.

So `u` is an algebra map modulo `J`. Formal smoothness of `O` lifts it to
`h : O → P` with `h - u ∈ J`. The ideal `J` lies in the kernel of `e₀` and of
`e₁`, because `e(t(t-1)) = 0` for both. Hence `e₁ ∘ h = e₁ ∘ u = f` and
`e₀ ∘ h = e₀ ∘ u = g`.

## Rational points of the Weil restriction

* `basePoint ψ` is the `B`-point of `O` attached to a rational point
  `ψ : W → k` of `W = WeilRestrictionFiniteType k B O`. It is the
  `k`-point of `W` under the Library's
  `WeilRestrictionFiniteType.homEquiv`, a map `O → B ⊗[k] k`, followed by
  `B ⊗[k] k ≅ B` (`Algebra.TensorProduct.rid`).
* `basePoint_comp` computes `basePoint (t ∘ φ)` from
  `homEquiv φ : O → B ⊗[k] T`. It uses
  `WeilRestrictionFiniteType.homEquiv_comp`.
* `basePoint_bijective`: rational points of `W` correspond bijectively to
  `B`-points of `O`. This follows because `homEquiv` and `rid` are bijections.

## Connectedness

* `ratPoint_mem_of_reduction_eq`: suppose two rational points `ψ, ψ'` of `W`
  have `B`-points with the same image in `k`. Then they lie in one connected
  component. The proof applies `exists_path` with:
  * `P = B ⊗[k] k[X]`, `D = B` and `ι` the left inclusion;
  * `eᵢ` evaluation at `X = i`, followed by `rid`;
  * `t = 1 ⊗ X` and `I = ker(B → k)`.

  This gives a `B ⊗[k] k[X]`-point `γ`, that is, a `k[X]`-point `φ` of `W`.
  Its evaluations at `1` and `0` are `ψ` and `ψ'` (`basePoint_bijective`).
  `Spec k[X]` is connected, so `ratPoint_mem_connectedComponent` applies.
* `connectedSpace_of_section`: suppose the following hold:
  * `A` is a `k`-algebra with connected spectrum;
  * `s : O → B ⊗[k] A` is a `B`-algebra map;
  * for every `B`-point `p` of `O`, some `a : A → k` satisfies
    `(B → k)(rid ((B ⊗ a)(s o))) = (B → k)(p o)` for all `o`;
  * `O` has a `B`-point `e`.

  Then `Spec W` is connected. Let `φ` be the `A`-point of `W` attached to
  `s`. By the previous lemma, every rational point `ψ` lies in the component of
  some `a ∘ φ`. These points all lie in one component, the image of
  `Spec A`. The point `e` provides a base rational point `ψ₀`. `W` is of
  finite type over `k`, so every closed point of `Spec W` is rational
  (`exists_ratPoint_eq`). `connectedSpace_of_closedPoints` then concludes,
  since a prime spectrum is compact and T0.
* `exists_section`: there is a section `s : O → B ⊗[k] (k ⊗[B] O)` that
  realizes every reduction, as required above. Let `C = B ⊗[k] (k ⊗[B] O)`
  and let `I` be the extension to `C` of the nilpotent ideal `ker(B → k)`. The
  canonical map `inc : O → k ⊗[B] O → C` is not `B`-linear. It is `B`-linear
  modulo `I`, because `b - (k → B)((B → k) b) ∈ ker(B → k)`. Formal smoothness
  lifts it to a `B`-algebra map `s` with `s - inc ∈ I`. For a `B`-point `p`,
  take `a : k ⊗[B] O → k` to be `id ⊗ ((B → k) ∘ p)`. The composite
  `F : C → k` kills `I`. So `F(s o) = F(inc o) = (B → k)(p o)`.
* `connectedSpace_weilRestriction` (main result): let `k` be algebraically
  closed and `ker(B → k)` nilpotent. Let `O` be formally smooth and of finite
  type over `B`, with connected special fibre `Spec (k ⊗[B] O)` and a `B`-point
  `e`. Then `Spec (WeilRestrictionFiniteType k B O)` is connected. It combines
  `exists_section` with `connectedSpace_of_section`, taking `A = k ⊗[B] O`.

## Provenance

These are derived lemmas, specific to this formalization, used in the proof of
the Library statement `EqualCharacteristicGreenbergPointModelStatement`. They
replace the cited connectedness argument of Theorem A.4.19(4). The affine-line
interpolation `g + t(f - g)` and the lifting of a special-fibre map through a
nilpotent thickening are standard uses of the lifting property of formal
smoothness (Mathlib's `Algebra.FormallySmooth.lift`). The Nullstellensatz input is
Mathlib's Jacobson-ring theory.
