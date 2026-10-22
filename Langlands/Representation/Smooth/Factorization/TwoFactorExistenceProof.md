# Proof of two-factor existence for admissible irreducible representations

This module proves the published proposition
`Langlands.AdmissibleProductFactorizationStatement.{uG₁,uG₂,uV}` from
`Langlands.Representation.Smooth.Factorization.TwoFactorStatement`. The
closing theorem is

```lean
theorem Langlands.admissibleProductFactorization :
    AdmissibleProductFactorizationStatement.{uG₁, uG₂, uV}
```

The statement pair and everything it imports are unchanged. The theorem
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

Let `G₁` and `G₂` be Hausdorff, locally compact, totally disconnected
topological groups. Let `ρ` be a complex representation of `G₁ × G₂` on a
space `V : Type uV`, and suppose `ρ` is admissible (`Langlands.IsAdmissible`)
and irreducible (`Representation.IsIrreducible`). Then there are:

- complex modules `V₁ V₂ : ModuleCat.{uV} ℂ`;
- representations `ρ₁` of `G₁` on `V₁` and `ρ₂` of `G₂` on `V₂`, both
  admissible and irreducible;
- an equivalence of representations from `ρ` to
  `Representation.tprod (ρ₁.comp (MonoidHom.fst G₁ G₂)) (ρ₂.comp (MonoidHom.snd G₁ G₂))`.

Admissibility is the published all-open-subgroups convention: smoothness, and
a finite-dimensional fixed space for every open subgroup. Both factors are
proved admissible in exactly this sense. The proof never passes through a
compact-open convention, so no comparison between the two conventions is
needed. It adds no countability, finite-dimensionality, unitarity or
smallness hypothesis.

Not every hypothesis of the target is used. For `G₂` the proof needs only
`Group` and `TopologicalSpace`. For `G₁` it uses the topological-group,
Hausdorff, locally compact and totally disconnected hypotheses: they give a
compact open subgroup inside a given open subgroup, and averaging over it.

## Construction of the factors

All auxiliary declarations live in the namespace `Langlands.TwoFactorExistence`.
Write `first ρ = ρ.comp (MonoidHom.inl G₁ G₂)` and
`second ρ = ρ.comp (MonoidHom.inr G₁ G₂)` for the restrictions to the two
factors. The operators of the two restrictions commute
(`first_second_comm`).

- **First factor.** `spanOrbit ρ y` is the `first ρ`-subrepresentation
  spanned by the orbit `{ρ(g,1) y : g ∈ G₁}`. The first factor is
  `U = spanOrbit ρ y` for a vector `y` chosen as described below. Its carrier
  is the submodule `U.toSubmodule` of `V`, so it lives in `Type uV`, and the
  representation is `U.toRepresentation`.
- **Second factor.** `Mult U` is the space of intertwiners
  `U.toRepresentation → first ρ`. Here `G₂` acts by post-composition with
  `ρ(1,g)` (`secondOp`, `multRep`). These maps commute with `first ρ`, so they
  are intertwiners. The carrier is a type of bundled linear maps from a
  submodule of `V` to `V`, so it also lives in `Type uV`.
- **Comparison map.** `eval : U ⊗ Mult U → V` sends `u ⊗ f` to `f u`. The
  lemma `eval_comm` shows that it intertwines the external tensor
  `tensorRep U` with `ρ`. Packaged as an intertwiner, it is `evalHom U`.

The closing theorem takes `V₁ = ModuleCat.of ℂ U.toSubmodule`,
`V₂ = ModuleCat.of ℂ (Mult U)`, `ρ₁ = U.toRepresentation` and
`ρ₂ = multRep U`. The equivalence is the inverse of
`IntertwiningMap.ofBijective (evalHom U)`.

## Choice of the vector `y` (`exists_cyclic`)

`V` is nonzero because it is irreducible. Choose any `x ≠ 0` and an open
subgroup `W` of `G₁ × G₂` that fixes `x`. Then apply the published
`Langlands.Hecke.TestFunction.commonCompactOpenBiInvariance` to the empty set
of test functions. This gives a compact open subgroup `K₁` of `G₁` inside the
pullback of `W` along `inl`. Let `K₂` be the pullback of `W` along `inr`, an
open subgroup of `G₂`.

Let `M = V^{K₁} ⊓ V^{K₂}`, where `K₁` acts through `first ρ` and `K₂` through
`second ρ`. This space lies in the `K₁ × K₂`-fixed space of `ρ`, so it is
finite-dimensional by admissibility, and it contains `x`. Among the nonzero
`z ∈ M`, choose `y` minimizing the dimension of `spanOrbit ρ z ⊓ M`. The
choice uses `Nat.find`.

The key property is that every nonzero `u ∈ spanOrbit ρ y` regenerates `y`:
`y ∈ spanOrbit ρ u`. The proof:

1. `spanOrbit ρ u` is a nonzero `first ρ`-subrepresentation. By
   `exists_fixed_of_ne_bot` (below), it contains a nonzero `K₁`-fixed vector
   `n`.
2. `n` lies in `spanOrbit ρ y`. Every vector of that span is `K₂`-fixed: the
   `K₂`-fixed vectors form a `first ρ`-subrepresentation (`secondFixed`),
   and that subrepresentation contains `y`. Hence `n ∈ M`.
3. `spanOrbit ρ n ⊓ M ≤ spanOrbit ρ y ⊓ M`. By minimality the two have the
   same dimension, so they are equal (`Submodule.eq_of_le_of_finrank_le`).
4. Therefore `y ∈ spanOrbit ρ n ≤ spanOrbit ρ u`.

## Nonzero subrepresentations meet the fixed space (`exists_fixed_of_ne_bot`)

Let `K` be a compact open subgroup of `G₁` and let `x ≠ 0` be fixed by `K`.
Then every nonzero `first ρ`-subrepresentation `N` contains a nonzero
`K`-fixed vector. This is where compactness and the irreducibility of `ρ`
are used.

Let `e` be the published averaging projection
`Langlands.Compact.averageMap (first ρ) _ K _` onto `V^K`. By
`averageMap_commute`, `e` commutes with every `ρ(1,g)`, and also with the
inclusion of `N`. Suppose, for contradiction, that `N` has no nonzero
`K`-fixed vector. Then `e` vanishes on `N`: for `n ∈ N`, `e n` lies in `N`
and is `K`-fixed (`averageMap_mem_fixedVectors`).

Now let `Z = ⋂_{g ∈ G₁} ker(e ∘ ρ(g,1))`. This is a subrepresentation of `ρ`.
It is stable under `ρ(h,1)` by reindexing the intersection, and under
`ρ(1,g)` because `e` commutes with it. `Z` contains `N`, so it is nonzero.
`Z` does not contain `x`, because `e x = x ≠ 0` (`averageMap_id`). This
contradicts the irreducibility of `ρ`.

## The first factor is irreducible and admissible

- `isIrreducible_spanOrbit` uses the regeneration property: every nonzero
  subrepresentation of `U` contains a vector that generates `y`, hence
  contains all of `U`. `U` is nonzero because `y ≠ 0`.
- `isAdmissible_of_le_secondFixed` handles admissibility. Smoothness is
  inherited from `ρ`. For an arbitrary open subgroup `L` of `G₁`, every
  vector of `U^L` is fixed by `L × K₂`, because `U` lies in
  `secondFixed ρ K₂`. So `U^L` embeds linearly into the `L × K₂`-fixed space
  of `ρ`, which is finite-dimensional. This works for every open `L`
  directly, so no compact open subgroup is needed here.
- Schur's lemma for `U` is the published
  `Langlands.admissibleSchur_scalarEndomorphism`: every endomorphism of `U`
  is a scalar.

## Evaluation is bijective

- **Surjectivity** (`eval_surjective`). `evalHom U` is an intertwiner into
  the irreducible `ρ`. It is nonzero because the inclusion `subtypeHom U`
  of `U` into `V` is an element of `Mult U`, and `eval (y ⊗ subtypeHom U) = y ≠ 0`.
  Mathlib's `Representation.IsIrreducible.surjective_or_eq_zero` then gives
  surjectivity.
- **Injectivity** (`eval_injective`). Expand a tensor `t` in a basis `bᵢ` of
  `U` as `t = Σ bᵢ ⊗ cᵢ`. Fix an index `j` and a vector `u ∈ U`. The lemma
  `exists_algebra_eq` is Jacobson density for `U` as a simple module over
  `MonoidAlgebra ℂ G₁`; it applies Mathlib's `jacobson_density`. Because
  every endomorphism of `U` is scalar, it gives an element `r` of the group
  algebra that sends each `bᵢ` in the support to `coord_j(bᵢ) • u`. The maps
  `cᵢ` commute with the group algebra (`intertwining_asAlgebraHom`). So if
  `eval t = 0`, applying `r` gives `c_j u = 0`. Hence every `c_j` is zero,
  and `t = 0`.

## The second factor is irreducible and admissible

Let `u = ⟨y, _⟩ ∈ U`, a nonzero vector. Since `U` is irreducible, every
nonzero intertwiner out of `U` is injective
(`Representation.IsIrreducible.injective_or_eq_zero`). So `f ↦ f u` is
injective on `Mult U` (`evalAt_injective`).

- **Admissibility** (`isAdmissible_multRep`). For smoothness, `f u` is fixed
  by some open subgroup `W` of `G₁ × G₂`. The pullback of `W` along `inr`
  then fixes `f`, by injectivity of evaluation at `u`. For an arbitrary open
  subgroup `L` of `G₂`, `f ↦ f u` maps `(Mult U)^L` injectively into the
  `K₁ × L`-fixed space of `ρ`, because `u` is `K₁`-fixed and `f` is
  `G₁`-equivariant. That space is finite-dimensional.
- **Irreducibility** (`isIrreducible_multRep`). `Mult U` is nonzero because
  it contains `subtypeHom U`. Let `N` be a nonzero `G₂`-subrepresentation.
  1. The range `R` of `eval` restricted to `U ⊗ N` is a nonzero
     subrepresentation of `ρ`, so `R = V`.
  2. Hence for any `f ∈ Mult U`, `f u = eval (T t)` for some `t ∈ U ⊗ N`,
     where `T` is the map induced by the inclusion `N → Mult U`.
  3. Injectivity of `eval` gives `T t = u ⊗ f`.
  4. Choose a linear functional `φ` on `U` with `φ u = 1`
     (`Module.Projective.exists_dual_eq_one`). Applying `φ ⊗ id` followed by
     `TensorProduct.lid` maps the image of `T` into `N` and sends `u ⊗ f` to
     `f`. So `f ∈ N`, and `N` is everything.

## Relation to the source

The statement is Flath, *Decomposition of representations into tensor
products*, Proc. Sympos. Pure Math. 33, Part 1 (1979), Theorem 1, clause
(1.2), printed p.179 (literature ID `flath-1979-tensor-products`; PDF page
175 of the retained Corvallis Part I volume). Flath's printed proof, p.180
(PDF page 176), takes a different route. It factors the finite-dimensional
`K₁ × K₂`-invariants as modules over the Hecke algebras `H(Gᵢ, Kᵢ)`, then
assembles the factors as an inductive limit over shrinking compact open
subgroups.

The Lean proof uses no Hecke algebra and no inductive limit. The second
factor is realized directly as a multiplicity space of `G₁`-intertwiners.
The finite-dimensionality that Flath gets from the invariants is replaced by
two ingredients:

- the minimal-dimension choice of `y`, together with compact averaging, to
  make `U` irreducible;
- Jacobson density plus Schur's lemma to make evaluation injective.

This route is internal to this module. It is a standard argument for
factorizations of irreducible modules over a tensor product of algebras,
written out here for the group setting.

## Dependencies

Library results used, by Lean name:

- `Langlands.AdmissibleProductFactorizationStatement`
  (`Langlands.Representation.Smooth.Factorization.TwoFactorStatement`), the
  target;
- `Langlands.admissibleSchur_scalarEndomorphism`
  (`Langlands.Representation.Smooth.Schur.Proof`);
- `Langlands.Compact.averageMap`, `averageMap_mem_fixedVectors`,
  `averageMap_id` and `averageMap_commute`
  (`Langlands.Representation.Compact.ProjectionProof`);
- `Langlands.Hecke.TestFunction.commonCompactOpenBiInvariance`
  (`Langlands.Representation.Hecke.CommonInvarianceProof`), used only with
  an empty set of test functions to obtain a compact open subgroup inside a
  given open subgroup.

From Mathlib it uses `jacobson_density` (`Mathlib.RingTheory.SimpleModule.Basic`),
`TensorProduct.eq_repr_basis_left` (`Mathlib.LinearAlgebra.TensorProduct.Basis`),
and the Mathlib API for subrepresentations, intertwining maps and irreducible
representations.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). The module adds no
axioms and contains no proof holes.

The unchanged first- and second-factor action declarations, through `secondOp`,
are imported from [`MultiplicityDefinitions`](MultiplicityDefinitions.md).
