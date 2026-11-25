# Primitive elements, group-like spans and scalar extension

Module `Langlands.RingTheory.Coalgebra.PrimitiveGroupLike`, namespace
`Langlands.CoetaleHopf`.

This is an internal helper module for the proof of
`Langlands.GroupScheme.MultiplicativeTypeCharacterizationStatement` (Milne, *Algebraic
Groups* (2017), Theorem 12.18). It proves four algebraic facts about primitive and
group-like elements, in Mathlib's conventions: `Bialgebra.IsPrimitiveElem K p` means
`ε p = 0` and `Δ p = 1 ⊗ p + p ⊗ 1`; `IsGroupLikeElem K g` means `ε g = 1` and
`Δ g = g ⊗ g`. No new definitions are introduced. The statements are derived lemmas;
they are not quoted from a source.

## Declarations

- `eq_zero_of_isPrimitiveElem_of_mem_span` (field `K`, bialgebra `H` over `K`, `H` a
  ring): a primitive element `p` lying in the `K`-span of the group-like elements is `0`.
- `eq_zero_of_comul_eq_of_isGroupLikeElem` (field `K`, Hopf algebra `H` over `K`): if
  every primitive element of `H` is `0`, `a` is group-like and `Δ b = a ⊗ b + b ⊗ a`,
  then `b = 0`.
- `tmul_tmul_comm`: in `(K ⊗[k] M) ⊗[K] (K ⊗[k] M)` one has
  `(c ⊗ y) ⊗ (1 ⊗ z) = (1 ⊗ y) ⊗ (c ⊗ z)` for `c : K` (a bookkeeping identity).
- `distribBaseChange_tmul_comul`: for a commutative `k`-bialgebra `A` and a field
  extension `K`, Mathlib's `TensorProduct.AlgebraTensorModule.distribBaseChange` sends
  `c ⊗ Δ a` to the comultiplication of `c ⊗ a` in the `K`-coalgebra `K ⊗[k] A`
  (Mathlib's `TensorProduct.instCoalgebra` with `K` as a coalgebra over itself).
- `eq_zero_of_isPrimitiveElem_baseChange` (fields `k`, `K`, `Algebra k K`, commutative
  `k`-bialgebra `A`): if every primitive element of `A` is `0`, then every primitive
  element of the `K`-bialgebra `K ⊗[k] A` is `0`.
- `exists_algHom_ker_eq` (algebraically closed field `K`, finite commutative
  `K`-algebra `B`): every maximal ideal of `B` is the kernel of some `K`-algebra
  homomorphism `B → K`.
- `eq_zero_of_forall_mem_maximal` (commutative noetherian ring `B`): if `m ≤ m ^ 2` for
  every maximal ideal `m`, an element lying in every maximal ideal is `0`.
- `span_isGroupLikeElem_eq_top_of_skewPrimitive` (algebraically closed field `K`,
  finite-dimensional cocommutative `K`-coalgebra `E`): if, for all `a b : E` with `a`
  group-like and `Δ b = a ⊗ b + b ⊗ a`, one has `b = 0`, then the group-like elements
  span `E`.

## Proofs

**Primitive elements in a group-like span.** Mathlib's `linearIndepOn_isGroupLikeElem`
says the group-like elements are linearly independent; `Module.Basis.extend` extends them
to a basis `b` of `H`. Every coordinate functional `f = b.coord i` takes the values `0`
or `1` on group-like elements, so `f g * f g = f g` for every group-like `g`. The linear
map `R x = mul' (map f f (Δ x))` agrees with `f` on group-like elements (`Δ g = g ⊗ g`),
hence on their span (`LinearMap.eqOn_span'`), so `R p = f p`. Primitivity gives
`R p = f 1 * f p + f p * f 1`. Since `1` is group-like, `f 1 * f 1 = f 1`; the identity
`f p = (1 - 2 f 1)(f p - 2 f 1 f p) - 4 f p (f 1 ^ 2 - f 1)` (`linear_combination`)
then gives `f p = 0`. All coordinates vanish, so `p = 0`. This holds in every
characteristic.

**Skew-primitive elements.** For group-like `a`, the antipode `S a` is group-like
(`IsGroupLikeElem.antipode`) with `S a * a = 1 = a * S a`. Multiplicativity of `Δ`
gives `Δ (S a * b) = (S a ⊗ S a)(a ⊗ b + b ⊗ a) = 1 ⊗ (S a * b) + (S a * b) ⊗ 1`, so
`S a * b` is primitive and hence `0`; therefore `b = a * (S a * b) = 0`.

**Scalar extension of primitive-freeness.** Let
`ψ = Δ - (1 ⊗ ·) - (· ⊗ 1) : A →ₗ[k] A ⊗[k] A`. By
`Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul`, `ψ x = 0` iff `x` is
primitive, so the hypothesis makes `ψ` injective. Its base change, followed by
`distribBaseChange : K ⊗ (A ⊗ A) ≃ (K ⊗ A) ⊗_K (K ⊗ A)`, is injective because `K` is
flat over the field `k` (`Module.Flat.lTensor_preserves_injective_linearMap`). By
tensor induction, using `distribBaseChange_tmul_comul`, `tmul_tmul_comm` and
`1 = 1 ⊗ 1`, this composite is `y ↦ Δ y - 1 ⊗ y - y ⊗ 1` on `K ⊗[k] A`. So a
primitive element of `K ⊗[k] A` lies in the kernel of an injective map and is `0`.

**Maximal ideals over an algebraically closed field.** For a maximal ideal `m` of a
finite `K`-algebra `B`, the field `B ⧸ m` is finite, hence integral, over `K`, so
`algebraMap K (B ⧸ m)` is bijective (`IsAlgClosed.algebraMap_bijective_of_isIntegral`).
The inverse of this bijection composed with the quotient map has kernel `m`.

**Idempotent maximal ideals.** Suppose `x ≠ 0` lies in every maximal ideal. Its
annihilator `J` is a proper ideal, contained in a maximal ideal `m`. Since `m` is
finitely generated and `m * m = m`, Mathlib's `Ideal.isIdempotentElem_iff_of_fg` gives
an idempotent `e` with `m = (e)`. Then `x = r e`, so `(1 - e) x = 0` and `1 - e ∈ J ⊆ m`;
with `e ∈ m` this puts `1` in `m`, a contradiction.

**Group-like spanning.** Write `B = WithConv (E →ₗ[K] K)`, a finite commutative
`K`-algebra (commutative because `E` is cocommutative), hence noetherian. By the
library lemma `Langlands.CoalgebraDescent.span_isGroupLikeElem_eq_top_of_algHom_separating`
it suffices that an element of `B` killed by every `K`-algebra map `B → K` is `0`. By
`exists_algHom_ker_eq` such an element lies in every maximal ideal, so by
`eq_zero_of_forall_mem_maximal` it is enough to show `m ≤ m ^ 2` for each maximal ideal
`m`. Let `φ : B → K` have kernel `m` and suppose `y ∈ m \ m ^ 2`. A `K`-linear functional
`l` on `B` with `l y ≠ 0` vanishing on `m ^ 2` exists
(`Submodule.exists_dual_map_eq_bot_of_notMem`). Then
`δ u = l (u - φ(u) · 1)` satisfies `δ (u v) = φ u δ v + δ u φ v`, because
`(u - φ u)(v - φ v) ∈ m ^ 2`. The library lemma
`Langlands.CoalgebraDescent.exists_isGroupLikeElem_of_algHom` writes `φ` as evaluation
at a group-like `a ∈ E`, and double duality (`Module.evalEquiv`) writes `δ` as
evaluation at some `b ∈ E`. The derivation identity, evaluated on `toConv f * toConv g`
(`LinearMap.convMul_apply`), and the library's tensor separation lemma
`Langlands.CoalgebraDescent.tensor_eq_of_forall_dual` give `Δ b = a ⊗ b + b ⊗ a`. The
hypothesis gives `b = 0`, so `δ = 0`; but `δ y = l y ≠ 0` since `φ y = 0`.

## Provenance

Internal derivation. The arguments implement steps of Milne's proof of Theorem 12.18
(*Algebraic Groups* (2017), registered source `milne-2017-algebraic-groups`, printed
pp. 237–238): the group algebra `K[Λ]` has no nonzero primitive elements, primitivity is
a linear condition and so commutes with field extension, and in the proof of
(b) ⇒ (c) a non-reduced local factor of the dual of a finite-dimensional subcoalgebra
over an algebraically closed field gives `Δ b = a ⊗ b + b ⊗ a` with `b ≠ 0`, whence the
nonzero primitive element `b a⁻¹`. The implementation replaces Milne's surjection onto
the dual numbers by the equivalent derivation at a maximal ideal and concludes via
idempotent maximal ideals instead of the local-factor decomposition.
