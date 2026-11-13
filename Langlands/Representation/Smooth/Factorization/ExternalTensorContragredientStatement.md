# The contragredient of an external tensor product (Renard III.1.14, Proposition): statement

Module `Langlands.Representation.Smooth.Factorization.ExternalTensorContragredientStatement`.
Namespace `Langlands`. Universe parameters `uG₁`, `uG₂` (the groups) and `uV₁`, `uV₂` (the
representation spaces).
The module contains one **statement**, the `Prop`-valued definition
`AdmissibleExternalTensorContragredientStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published `FlathTwoFactorStatement`
([TwoFactorStatement](TwoFactorStatement.md), proof Task 5771) states the other assertions of
the III.1.14 Proposition for two factors: the fixed vectors of `V₁ ⊗ V₂`, admissibility and
irreducibility of `π₁ ⊠ π₂`, and existence and uniqueness of the factorization of an
irreducible admissible representation of `G₁ × G₂`. It does not state the second assertion,
`(⊠_i π_i)^∼ = ⊠_i π̃_i`, which this unit states.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.1.14, printed pp.66–67 / PDF pp.72–73:

> Proposition. Avec les notations ci-dessus, supposons que toutes les représentations
> `(π_i, V_i)` soient admissibles. Alors `⊠_i(π_i, V_i)` est admissible. D'autre part,
> `(⊠_i(π_i, V_i))^∼ = ⊠_i(π̃_i, Ṽ_i)`. […]
>
> Démonstration. Il suffit de traiter le cas `r = 2`. Soient `K_i ⊂ G_i` […] des sous-groupes
> ouverts compacts et posons `K = K_1 × K_2 ⊂ G_1 × G_2`. On vérifie facilement que […]
> `(V_1 ⊗ V_2)^K = V_1^{K_1} ⊗ V_2^{K_2}`, de sorte que `(V_1 ⊗ V_2)^K` est de dimension finie.
> L'application naturelle
> `Ṽ_1^{K_1} ⊗ Ṽ_2^{K_2} = (V_1^{K_1})^* ⊗ (V_2^{K_2})^* → ((V_1 ⊗ V_2)^K)^* = (V_1 ⊗ V_2)^{∼K}`
> est un isomorphisme. Ceci prouve les deux premières assertions. […]

Here `⊠_i(π_i, V_i)` is the representation `(g_1, …, g_r) ↦ π_1(g_1) ⊗ … ⊗ π_r(g_r)` of
`∏_i G_i` on `V_1 ⊗ … ⊗ V_r`.

## Published objects used

- `Representation.tprod` (Mathlib) and the projections `MonoidHom.fst`, `MonoidHom.snd`:
  `π₁ ⊠ π₂ = tprod (π₁ ∘ fst) (π₂ ∘ snd)`, the same construction as in
  `FlathTwoFactorStatement`.
- `SmoothDual ρ`, `smoothContragredient ρ` and `smoothDualPairing ρ`: the smooth
  contragredient and its pairing ([Contragredient/Definitions](../Contragredient/Definitions.md)).
- `IsAdmissible` ([Definitions](../Definitions.md)).

## The statement

**`AdmissibleExternalTensorContragredientStatement`.** Let `G₁`, `G₂` be t.d. groups
(Hausdorff, locally compact, totally disconnected) and `ρ₁`, `ρ₂` admissible complex
representations. Write `ρ = ρ₁ ⊠ ρ₂` and `ρ′ = ρ̃₁ ⊠ ρ̃₂`. Then there is an equivalence of
representations of `G₁ × G₂`

```text
e : Ṽ₁ ⊗ Ṽ₂ ≃ (V₁ ⊗ V₂)^∼    with    e(ℓ₁ ⊗ ℓ₂)(v₁ ⊗ v₂) = ℓ₁(v₁) ℓ₂(v₂).
```

## Formalization choices

- **Two factors.** As in Renard's proof ("il suffit de traiter le cas `r = 2`") and in the
  published `FlathTwoFactorStatement`, the statement has two factors. The case of `r`
  factors follows by induction, using the associativity of the tensor product.
- **The isomorphism is the natural map.** The pairing formula determines `e`, because pure
  tensors span `V₁ ⊗ V₂`. So the statement says that the natural map `Ṽ₁ ⊗ Ṽ₂ → (V₁ ⊗ V₂)^∼`
  is an isomorphism, as in the proof. In particular it is asserted to land in smooth
  functionals and to be `G₁ × G₂`-equivariant.
- **Admissibility of both factors** is the source's hypothesis. Without it, the natural map
  is still injective, but it need not be surjective.

## Why the statement is true

The map `ℓ₁ ⊗ ℓ₂ ↦ (v₁ ⊗ v₂ ↦ ℓ₁(v₁) ℓ₂(v₂))` is equivariant. A pure tensor `ℓ₁ ⊗ ℓ₂` with
`ℓ_i` fixed by `K_i` goes to a functional fixed by `K₁ × K₂`, so the image consists of
smooth functionals. The subgroups `K₁ × K₂` with `K_i` compact open are cofinal among open
subgroups of `G₁ × G₂`. For such `K`, `(V₁ ⊗ V₂)^K = V₁^{K₁} ⊗ V₂^{K₂}` is finite
dimensional. Hence `((V₁ ⊗ V₂)^∼)^K = ((V₁ ⊗ V₂)^K)^*` is
`(V₁^{K₁})^* ⊗ (V₂^{K₂})^* = Ṽ₁^{K₁} ⊗ Ṽ₂^{K₂}`, and the map restricts to this isomorphism
on `K`-fixed vectors. Taking the union over `K` shows that the map is bijective.

## Remaining obligations

The proof is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Smooth.Definitions` | `IsAdmissible` |
| `Langlands.Representation.Smooth.Contragredient.Definitions` | `SmoothDual`, `smoothContragredient`, `smoothDualPairing`; through its imports Mathlib's `Representation.Equiv` (`Mathlib.RepresentationTheory.Intertwining`) |
| `Mathlib.RepresentationTheory.Basic` | `Representation.tprod` |
| `Mathlib.Basic.Complex.Basic` | `ℂ` |
| `Mathlib.Topology.Connected.TotallyDisconnected` | `TotallyDisconnectedSpace` |
