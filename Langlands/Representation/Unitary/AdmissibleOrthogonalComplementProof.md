# The orthogonal of an invariant subspace (Renard IV.2.2, Proposition): proof

Module `Langlands.Representation.Unitary.AdmissibleOrthogonalComplementProof`.
Namespace `Langlands`. Universe parameters `uG` (the group) and `uV` (the carrier).

The module contains one theorem,

```lean
theorem admissibleUnitaryOrthogonalComplement :
    AdmissibleUnitaryOrthogonalComplementStatement.{uG, uV}
```

It proves the published statement
[AdmissibleOrthogonalComplementStatement](AdmissibleOrthogonalComplementStatement.md):
for a topological group `G` in which compact open subgroups are cofinal among open
subgroups, an admissible representation `ρ` of `G` on `V`, an invariant positive definite
Hermitian form `b` and a `G`-stable subspace `V₁`, the orthogonal
`V₁^⊥ = {v | ∀ v₁ ∈ V₁, b(v, v₁) = 0}` is a `G`-stable subspace with `V = V₁ ⊕ V₁^⊥`.
The theorem adds no hypothesis. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, registered as
`renard-2026-representations-groupes-reductifs-padiques`, IV.2.2, Proposition (printed
p.98 / PDF p.104). Renard proves `V = V₁ + V₁^⊥` by orthogonal projection inside the
finite-dimensional fixed space `V^K` of a compact open subgroup `K`. The Lean proof
gets the same decomposition differently, from the published surjectivity of the
smooth-dual map of an invariant positive form on an admissible representation. It
follows the published proof
[AdmissibleSemisimplicityProof](AdmissibleSemisimplicityProof.md)
(`admissibleUnitarySemisimplicity`), which builds the same complement but whose theorem
asserts only that *some* invariant complement exists.

## The proof

Let `V₁` be `G`-stable.

1. **`V₁` as an admissible subrepresentation.** `S : Subrepresentation ρ` has underlying
   submodule `V₁`; the stability hypothesis gives `apply_mem_toSubmodule`. The inclusion
   `i : S.toRepresentation → ρ` is an injective intertwining map, so `S.toRepresentation`
   is admissible (`isAdmissible_of_injective`). Pulling `b` back along `i` gives an
   invariant positive form `bS` on `S` (`InvariantPositiveForm.comap`).
2. **The orthogonal.** `W` is the submodule with carrier
   `{v | ∀ v₁ ∈ V₁, b.inner v v₁ = 0}`. It is closed under zero, addition and scalars
   because `b` is conjugate-linear in its first variable (`b.add_left`, `b.smul_left`).
   Its underlying set is the statement's set by `rfl`.
3. **`W` is `G`-stable.** For `v ∈ W`, `g ∈ G` and `v₁ ∈ V₁`, write
   `v₁ = ρ g (ρ g⁻¹ v₁)` (`Representation.self_inv_apply`). Invariance of `b`
   (`b.invariant`) gives `b(ρ g v, v₁) = b(v, ρ g⁻¹ v₁)`. This is zero because
   `ρ g⁻¹ v₁ ∈ V₁`.
4. **Every vector splits (`hdecomp`).** Fix `v ∈ V`. The smooth functional
   `b.toSmoothDual hρ.1 v` sends `w` to `b(v, w)`. Restrict it to `S` along `i`
   (`contragredientMap i`). The result `ℓ` is a smooth functional on the admissible `S`.
   By `InvariantPositiveForm.toSmoothDual_surjective`, which uses the cofinality
   hypothesis and admissibility of `S`, there is `s ∈ V₁` with `bS.toSmoothDual s = ℓ`.
   Evaluating at `t ∈ V₁` gives `b(s, t) = b(v, t)`, so `b(v - s, t) = 0`
   (`inner_sub_left`), that is, `v - s ∈ W`.
5. **`IsCompl V₁ W`.**
   - *Disjointness:* if `v ∈ V₁ ⊓ W`, then `b(v, v) = 0` (take `v₁ = v`), so `v = 0` by
     `b.definite`.
   - *Codisjointness:* for every `v`, step 4 gives `s ∈ V₁` with `v - s ∈ W`, so
     `v = s + (v - s) ∈ V₁ ⊔ W` (`Submodule.add_mem_sup`, `add_sub_cancel`).

The witness is `W`, with clause 1 `rfl`, clause 2 step 3 and clause 3 step 5.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Unitary.AdmissibleOrthogonalComplementStatement` | The target statement, `IsAdmissible` and `InvariantPositiveForm` |
| `Langlands.Representation.Unitary.HermitianDual` | `InvariantPositiveForm.toSmoothDual` and `toSmoothDual_surjective`; through its imports also `InvariantPositiveForm.comap` (`Unitary.Basic`) and `contragredientMap`, `smoothDualPairing` (`Smooth.Contragredient.Definitions`) |
| `Langlands.Representation.Smooth.Admissibility.EmbeddingProof` | `isAdmissible_of_injective`: a subrepresentation of an admissible representation is admissible |
