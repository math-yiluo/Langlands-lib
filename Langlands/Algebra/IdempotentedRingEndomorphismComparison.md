# Comparison and closure targets for the actual right-linear endomorphism model

Author: Worker 1126.

This module contains statement targets only: five Prop-valued component
definitions and one aggregate. It proves none of them. The imported
constructions keep their original authorship. Proofs are a separate
exact-target successor task.

## Source

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained source is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Chapter I conventions and I.1.1–I.1.6, printed pp.5–12/PDF11–18, supply
the setting. Rings need not have an identity, and their multiplication need
not be commutative. An idempotented ring has, for every finite subset, an
idempotent that is a two-sided unit for it.

- The remark at the end of I.1.4, printed p.10/PDF16, notes that the
  constructions of I.1.4 carry over to right modules, so that
  `Ā ≃ End_{A°}(A)`. The notation `A°` indicates right-module structures.
  The proposition of I.1.4 on the same page gives the maps for left modules.
  The map is `φ ↦ {φ(e)}_e`. Its inverse sends a family `m̄` to
  `φ(a) = a · m̄(e)` for any `e` with `a e = a`.
- I.1.6, printed p.11/PDF17, says that every `ā ∈ Ā` acts on `A` on the
  left. This action gives an additive endomorphism that commutes with right
  multiplications. So `Ā` can be identified with the subgroup
  `End_{A°}(A)` of `End_Z(A)`.
- The same page gives `End_Z(A)` the topology of simple (pointwise)
  convergence. Its basic zero neighborhoods are
  `O(U_1,…,U_n, a_1,…,a_n) = {β | β(a_i) ∈ U_i}`, and one may take
  `U_i = A(1-e_i)`. The text says that the induced topology on `Ā` coincides
  with the one defined before, in I.1.3. It checks this with a local unit
  `f` such that `f a_i = a_i`, and with `Ā(1-f) = O(A(1-f), f) ∩ Ā`.
- It then says that `Ā` is clearly contained in the closure of the left
  multiplications ("Il est clair que"). Conversely, that closure "est bien
  sûr elle-même contenue dans le commutant des multiplications à droite,
  c'est-à-dire dans `End_{A°}(A) = Ā`". The lemma follows: "L'anneau `Ā` s'identifie avec
  l'adhérence dans `End_Z(A)`, pour la topologie de la convergence simple,
  de l'ensemble des multiplications à gauche par des éléments de `A`."

The supplementary 2010-edition *Corrections et compléments*, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, were
read at PDF1. For p.13, l.3 of the 2010 edition they replace
`O(Ā(1-f), f) ∩ Ā` by `O(A(1-f), f) ∩ Ā`. The bar is removed from the
original-value neighborhood `A(1-f)`, and the intersection with the
completed ring `Ā` is kept. A rendered image of the governing 2026 PDF17
shows that the 2026 text already prints the corrected
`Ā(1-f) = O(A(1-f), f) ∩ Ā`. The targets below follow it. Values of
endomorphisms carry the uniformity of the original ring `A`, not of `Ā`.

## Objects used

Every object is a published construction imported by Lean name. None is
redefined here. Throughout, `A : Type uA` carries its original
`NonUnitalRing A`, and `hA : IsIdempotented A` is the published
finite-local-unit condition.

- `IdempotentedRingRightLimit A` is the published carrier of compatible
  families `e ↦ x.val e`, indexed by idempotents. This is the source's `Ā`.
  `IdempotentedRingRightLimit.ring hA` is its published ring. Its
  multiplication is `IdempotentedRingRightLimit.product hA` and its
  identity is `IdempotentedRingRightLimit.unit`.
  `IdempotentedRingRightLimit.applyOriginal hA x a` is `x.val e * a`
  for a chosen idempotent `e` with `e * a = a`. By the published
  `applyOriginal_eq`, any such `e` gives the same value. This is the
  source's left action `ā · a`.
- `rightLinearEnd A` is the published `Subring (AddMonoid.End A)`. Its
  membership is exactly `∀ a b : A, β (a * b) = β a * b`. This is the
  source's `End_{A°}(A)` inside `End_Z(A) = AddMonoid.End A`.
  `RightLinearEnd A` is its subtype. Multiplication is composition:
  `(β * γ).val a = β.val (γ.val a)`, so the left factor acts after the
  right factor.
- `toRightLinearEnd hA` is the published unital ring homomorphism from
  the family ring `IdempotentedRingRightLimit.ring hA` to
  `RightLinearEnd A`. The underlying endomorphism of `x` sends `a` to
  `applyOriginal hA x a`. It is the source's `ā ↦ (a ↦ ā · a)`.
- `idempotentEvaluation` is the published additive map
  `RightLinearEnd A →+ IdempotentedRingRightLimit A`. It is given by
  `(idempotentEvaluation β).val e = β.val e`. It is the right-module form
  of the source's `φ ↦ {φ(e)}_e`.
- `leftMultiplication : A →ₙ+* AddMonoid.End A` is the published map
  `a ↦ (b ↦ a * b)`.
- `idempotentedRingUniformSpace A` is the published uniformity of the
  original ring. It is the infimum over idempotents `e` of the pullbacks of
  the discrete uniformity along `a ↦ a * e`. Its zero neighborhoods are the
  source's `A(1-e) = {a | a * e = 0}`.
- `pointwiseUniformSpace A` on `AddMonoid.End A` is the pullback, along
  the inclusion into `A → A`, of the product uniformity in which every value
  coordinate carries `idempotentedRingUniformSpace A`. This is the source's
  simple convergence. `rightLinearEndUniformSpace A` is its restriction to
  `RightLinearEnd A`.
- `IdempotentedRingRightLimit.uniformSpace A` is the published family
  uniformity. It is the infimum over idempotents `e` of the pullbacks of
  the discrete uniformity along `x ↦ x.val e`. Its zero neighborhoods are
  the source's `Ā(1-e) = {ā | ā(e) = 0}`.

None of these rings or uniformities is a global instance. Every statement
that uses a ring, uniformity or topology selects the named construction
explicitly, with `letI` or `@`. A competing
ring or uniformity on any of the carriers therefore cannot replace it.

## The five component statements

Each component is closed. It quantifies over every
`(A : Type uA) [NonUnitalRing A]` and takes the local-unit hypothesis
explicitly.

1. `IdempotentedRingEndomorphismInverseIdentities`: for every `hA`, both
   `∀ x, idempotentEvaluation (toRightLinearEnd hA x) = x` and
   `∀ β : RightLinearEnd A, toRightLinearEnd hA (idempotentEvaluation β) = β`.
   No inverse law is a hypothesis.
2. `IdempotentedRingEndomorphismRingEquivalence`: for every `hA`, with
   `IdempotentedRingRightLimit.ring hA` installed by `letI`, there is
   `Φ : IdempotentedRingRightLimit A ≃+* RightLinearEnd A`. Its forward
   function equals the whole function `toRightLinearEnd hA`. Its inverse
   function `Φ.symm` equals the whole function `idempotentEvaluation`.
   Both are equalities of complete functions. An unspecified equivalence
   would not satisfy the statement.
3. `IdempotentedRingEndomorphismUniformityComparison`: for every `hA`,
   `UniformSpace.comap (toRightLinearEnd hA) (rightLinearEndUniformSpace A) = IdempotentedRingRightLimit.uniformSpace A`.
   The left side is the restricted pointwise uniformity with original-ring
   values, pulled back along the actual forward map. The right side is the
   discrete-coordinate family uniformity. These are different
   constructions, and the equality is not definitional.
4. `IdempotentedRingEndomorphismRightLinearClosed`: if `IsIdempotented A`,
   then the set `(rightLinearEnd A : Set (AddMonoid.End A))` is closed in
   `AddMonoid.End A` for `(pointwiseUniformSpace A).toTopologicalSpace`.
5. `IdempotentedRingEndomorphismClosureLemma`: if `IsIdempotented A`, then
   in `AddMonoid.End A`, with the same topology,
   `closure (Set.range leftMultiplication) = rightLinearEnd A` as sets. This
   is the topological closure of the image of left multiplication among all
   additive endomorphisms. It is not a generated subring, not a closure
   inside the right-linear subtype, and not an image under an unspecified
   identification.

Statements 4 and 5 take the hypothesis without a name, because their
objects do not depend on it.

## Aggregate

`IdempotentedRingEndomorphismComparisonTheorem` (universe `uA`) is the
conjunction of the five components at the same universe, in the order 1–5:

```
IdempotentedRingEndomorphismInverseIdentities.{uA} ∧
  IdempotentedRingEndomorphismRingEquivalence.{uA} ∧
  IdempotentedRingEndomorphismUniformityComparison.{uA} ∧
  IdempotentedRingEndomorphismRightLinearClosed.{uA} ∧
  IdempotentedRingEndomorphismClosureLemma.{uA}
```

Proof tasks can target the aggregate or any component by these exact names.

## Hypotheses and universes

The only hypothesis is `IsIdempotented A`. There is no global identity,
commutativity, nontriviality, field, countability, finite dimension,
topology parameter, completeness, density, chosen equivalence or
conclusion-shaped premise. The universe `uA` is arbitrary. The family
carrier and `RightLinearEnd A` stay in `Type uA`. Zero rings and trivial
endomorphism rings are included.

## Checks in the Lean file

- Complete unapplied `example : Prop := @X.{u}` checks for all six
  declarations, at arbitrary `uA`, at `0` and at `1`.
- `rfl` unfoldings:
  - The ring equivalence equals the version written with
    `@RingEquiv`, with the `Mul` and `Add` of
    `IdempotentedRingRightLimit.ring hA` passed explicitly.
  - With that ring installed, `x * y` is `product hA x y` and `1` is `unit`.
  - Multiplication in `RightLinearEnd A` is composition, left after right.
  - The uniformity comparison equals the formula with nested comaps of the
    product uniformity `@Pi.uniformSpace` with values
    `idempotentedRingUniformSpace A`. Its right side is
    `⨅ e, UniformSpace.comap (fun x => x.val e) ⊥`.
  - Closedness and closure use exactly the induced product topology. The set
    is `{β | ∀ a b, β (a * b) = β a * b}` and the range is that of
    `AddMonoidHom.mulLeft`.
- Proved reformulations:
  - The uniformity comparison is equivalent to the same equality with
    `UniformSpace.comap (applyOriginal hA)` of the product uniformity.
  - The inverse identities are equivalent to the two complete composites
    being `id`.
- Consistency examples. These do not prove any target.
  - Statement 1 is equivalent to statement 2.
  - Statements 1 and 3 give a `UniformEquiv` for the named uniformities
    whose two functions are exactly `toRightLinearEnd hA` and
    `idempotentEvaluation`.
  - Statement 3 gives
    `TopologicalSpace.induced (toRightLinearEnd hA) (rightLinearEndUniformSpace A).toTopologicalSpace = (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace`.
    This is the source's statement that the induced topology coincides.
  - Statement 5 implies statement 4.
- Specializations:
  - The aggregate at universes `0` and `1` yields each complete component
    body.
  - At `0` it gives the closure identity for `ℤ`.
  - At `1` it gives the uniformity comparison for `ULift.{1} ℤ`.
  - At arbitrary `uA` it gives the specified ring equivalence for the zero
    ring `PUnit.{uA+1}`.
- Competing structures: a competing `Ring` on the family carrier and
  competing uniformities on the family carrier, `A`, `A → A`,
  `AddMonoid.End A` and `RightLinearEnd A` are placed in typeclass search.
  Each component at `uA`, and the aggregate at `0` and at `1`, still gives
  the bodies written with the named constructions.

`lean_check` inspection reports the aggregate as returning `Prop`, with the
single level parameter `uA`. Its only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

- **Statements 1 and 2** come from the source's identification of `Ā` with
  `End_{A°}(A)`, in the I.1.4 remark and I.1.6, with the maps of the I.1.4
  proposition in their right-module form. The source calls `Ā` a ring
  ("L'anneau `Ā`") in the lemma. Specifying both complete functions and
  packaging the result as a `RingEquiv` are internal. Multiplicativity of
  the forward map is the published ring homomorphism `toRightLinearEnd`.
- **Statement 3** is the source's comparison of topologies ("La topologie
  induite sur `Ā` coïncide alors avec celle définie précédemment"), in the
  corrected form `Ā(1-f) = O(A(1-f), f) ∩ Ā`. Stating it as an equality of
  uniformities is internal packaging and is not a separate numbered
  assertion of Renard. Together with statement 1, it gives a uniform
  isomorphism (checked above). With statement 2, this is the source's
  topological ring isomorphism of `Ā` onto the right-linear subring.
- **Statement 4** makes explicit the source's "bien sûr" step: the closure
  stays inside the commutant of right multiplications. Closedness of the
  commutant is used, not stated, in the source.
- **Statement 5** is the set-level content of the source's lemma inside
  `End_Z(A)`. With statements 1 and 2 it gives the source's identification
  of the ring `Ā` with that closure.

A possible proof route, for guidance only, is the following. It is not a
premise of any target. For statement 1, evaluate at `a = e` for the first
identity. For the second, use `e * a = a` and right linearity:
`β e * a = β (e * a) = β a`. For statement 3, use
`applyOriginal hA x a * e = x.val f * a * e` for `f * a = a` in one
direction. In the other, use `x.val e = applyOriginal hA x e * e`. For
statement 5, every left multiplication is right-linear by associativity.
Conversely, for right-linear `β` and finitely many `a_i`, take `f` with
`f * a_i = a_i`. Then `leftMultiplication (β f)` agrees with `β` at every
`a_i`. Closedness uses continuity of evaluations and of right
multiplications, and that the topology of `A` is Hausdorff under local
units.

## Remaining obligations

The proofs of these statements are a separate exact-target task, to be
published after this statement is accepted and published. The following
are also outside this module:

- the natural endomorphisms of the forgetful functor `M(A) → Z-mod`, the
  rest of I.1.6 from printed p.11/PDF17 to p.12/PDF18;
- categorical centres in I.1.7;
- further completion results;
- the rest of the book.
