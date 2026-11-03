# Points of schemes over finite fields and their algebraic closures

Module `Langlands.GroupScheme.FiniteFieldTorsorPoint.PointDescent`. These are internal
helper results for the proof of `Langlands.GroupScheme.FiniteFieldTorsorPointStatement`.
They are standard facts, proved here directly. The module adds no statements, definitions
or axioms. Points use the Library's `RingPoint k X A`, the morphisms
`ringTest k A ⟶ X` over `Spec k`, where `ringTest k A` is `Spec A → Spec k`. The map
`ringTestMap k f : ringTest k B ⟶ ringTest k A` is induced by a `k`-algebra map
`f : A →ₐ[k] B`.

## `mem_range_algebraMap_of_pow_card_eq`

Let `k` be a finite field with `q` elements and `K` a field extension of `k`. Every
`z : K` with `z ^ q = z` lies in the image of `k`.

The polynomial `X ^ q - X` over `K` is nonzero of degree `q`
(`FiniteField.X_pow_card_sub_X_ne_zero`, `FiniteField.X_pow_card_sub_X_natDegree_eq`).
Its root set contains the `q` distinct images of `k` (`FiniteField.pow_card`) and `z`.
If `z` were not among those images, the root set would have more than `q` elements,
contradicting `Polynomial.card_roots'`.

## `nonempty_ringPoint_of_frobenius_fixed`

Let `k` be a finite field, `X` a scheme over `Spec k`, and `K` a field extension of `k`.
Let `p : RingPoint k X K` be fixed by the `k`-linear `q`-power Frobenius `F` of `K`,
in the sense `ringTestMap k (FiniteField.frobeniusAlgHom k K) ≫ p = p`. Then `X` has a
`k`-point: `Nonempty (RingPoint k X k)`.

Proof in Lean. By `Scheme.SpecToEquivOfField`, the underlying morphism of `p` is
`Spec ι ≫ X.fromSpecResidueField x` for a point `x` of `X` and a ring map
`ι : κ(x) → K`. Since this description is a bijection and `p` is fixed by Frobenius,
`ι ≫ F = ι`, so each `ι y` satisfies `(ι y) ^ q = ι y`. By the previous lemma, `ι`
factors as `τ` followed by `algebraMap k K` for a ring map `τ : κ(x) → k`. The candidate
point is `Spec τ ≫ X.fromSpecResidueField x : Spec k ⟶ X` (named `q` in the Lean proof).
To see that it lies over `Spec k`, let `f` be its composite with `X.hom`, an
endomorphism of `Spec k`, and let `t : Spec K → Spec k` be the structure map. Then
`t` followed by the candidate point is `p`, so `t ≫ f = p ≫ X.hom = t`. As `f` is
`Spec` of a ring endomorphism of `k` (`Spec.map_preimage`) and `algebraMap k K` is
injective, `f` is the identity.

## `nonempty_ringPoint_of_locallyOfFiniteType`

Let `k` be a field and `X` a nonempty scheme over `Spec k` whose structure map is
locally of finite type. Then `X` has a point over every algebraically closed field
extension `K` of `k`.

Proof in Lean. Let `t : Spec K ⟶ Spec k` and `P := pullback X.hom t`. The map `t` is
surjective because `Spec k` has one point, so the base change `P → X` is surjective and
`P` is nonempty. The second projection `P → Spec K` is locally of finite type, so `P` is
a Jacobson space (`LocallyOfFiniteType.jacobsonSpace`) and has a closed point `z`
(`nonempty_inter_closedPoints`). Over the algebraically closed field `K`, the point
`pointOfClosedPoint` gives a section `Spec K ⟶ P` of the projection through `z`.
Composing it with `P → X` gives a `K`-point of `X`. It lies over `t` by
`pullback.condition`.
