# Trivialising unit cocycles over a semilocal base

This module proves a concrete form of Hilbert's Theorem 90 for Weil restrictions of `𝔾ₘ`.
Let `B` be a finite algebra over a field `k`, and let `L/K` be an extension of fields
over `k`. Every system of `(B ⊗[k] T)ˣ`-valued descent cocycles for `L/K` that is natural
in `T` is a coboundary of a single unit of `B ⊗[k] L`. The module is a helper for
`Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityProof`. All declarations are in
namespace `Langlands.Algebra.Semilocal`, and all rings lie in one universe `u`.

## Provenance

The content is internal and derived. It implements the classical facts behind
`H¹(K, R_{B/k} 𝔾ₘ) = 1`: faithfully flat descent of modules and triviality of invertible
modules over a semilocal ring (compare Milne, *Étale Cohomology*, Proposition III.4.9, and
Platonov–Rapinchuk, Lemma 2.4). These sources are already cited by the statement
`InducedTorusQuotientPointSurjectivityStatement`. The descent step is the published Library
theorem `Langlands.Algebra.unitCocycleLocalUnits` (Stacks Project, Tag 023N). The
semilocal step is `Langlands.Algebra.SemilocalUnitProduct`.

Notation: for `x ∈ S ⊗[R] S`, write `x₁₂`, `x₂₃` and `x₁₃` for its images in
`S ⊗[R] (S ⊗[R] S)` under `map id includeLeft`, `includeRight` and `map id includeRight`.
This is the convention of `Langlands.Algebra.UnitCocycleLocalUnitsStatement`.

## Core: unit cocycles over a semilocal base

- `cocycleSubmodule u` is the `R`-submodule `{m ∈ S | u * (m ⊗ 1) = 1 ⊗ m}` of `S`, for
  `u ∈ S ⊗[R] S`. `mem_cocycleSubmodule` unfolds membership.
- `exists_isUnit_of_unitCocycle`: let `R` have finitely many maximal ideals, let `S` be a
  faithfully flat `R`-algebra, and let `u, v ∈ S ⊗[R] S` with `u v = 1` and
  `u₁₃ = u₂₃ · u₁₂`. Then there is a unit `m` of `S` with `u * (m ⊗ 1) = 1 ⊗ m`.

*Proof of `exists_isUnit_of_unitCocycle`.*

1. Take `m ∈ M_u := cocycleSubmodule u` and `m' ∈ M_v`. Then
   `(m m') ⊗ 1 = (u v)(m ⊗ 1)(m' ⊗ 1) = (u (m ⊗ 1))(v (m' ⊗ 1)) = 1 ⊗ (m m')`.
2. `R → S` is faithfully flat, hence effective (`Algebra.IsEffective.of_faithfullyFlat`).
   So the equaliser of the two maps `S → S ⊗[R] S` is the image of `R`
   (`eqLocus_includeLeft_includeRight`). Hence `m m'` comes from `R`.
3. By `Langlands.Algebra.unitCocycleLocalUnits`, the elements of `R` arising in this way
   generate the unit ideal. `R → S` is injective (`FaithfulSMul.algebraMap_injective`).
   `exists_isUnit_of_span_eq_top` therefore gives `m ∈ M_u`, `m' ∈ M_v` and a unit
   `r ∈ R` with `algebraMap r = m m'`. Then `m (m' w⁻¹) = 1`, where `w` is the image of `r`,
   so `m` is a unit.

## Generic cover lemma

Let `β : B →ₐ[k] R` be an algebra map, and let `T` be an `R`-algebra (with compatible
`k`-structure). `mulMap β T : B ⊗[k] T →ₐ[k] T` sends `b ⊗ t ↦ β(b) t` (`mulMap_tmul`).
`mulMap_naturality` says that it commutes with `R`-algebra maps `f : T →ₐ[R] T'`. Precisely,
`f (mulMap β T x) = mulMap β T' ((id ⊗ f) x)`.

`exists_unit_coboundary_of_cover` uses the following data:

- `R`, `S` with `k → R → S`, where `S` is faithfully flat over `R` and `R` has finitely many
  maximal ideals;
- `k`-algebra maps `β : B → R`, `j : L → S` and `θ : S → B ⊗[k] L`, such that:
  - every `j(x)` with `x ∈ K` comes from `R` (`hj`);
  - `θ (j l) = 1 ⊗ l` (`hθj`);
  - `θ (β b) = b ⊗ 1` (`hθβ`);
  - every `θ(r)` with `r ∈ R` lies in the image of `B ⊗[k] K → B ⊗[k] L` (`hθR`);
- a family `c T a b ∈ (B ⊗[k] T)ˣ`, for every commutative `k`-algebra `T` and every pair of
  `k`-algebra maps `a b : L → T`. It is constrained only for pairs that agree on `K`. On
  such pairs it is natural in `T`: `c T' (φ ∘ a) (φ ∘ b) = (id ⊗ φ)(c T a b)` (`hnat`). It
  also satisfies `c T a d = c T a b * c T b d` (`hcoc`).

The conclusion is that there is `f ∈ (B ⊗[k] L)ˣ` with
`c T a b * (id ⊗ a)(f) = (id ⊗ b)(f)` for all `T` and all `a, b` that agree on `K`.

*Proof.*

1. Let `pr₁, pr₂ : L → S ⊗[R] S` be `j` followed by the two inclusions. They agree on `K` by
   `hj`. Put `u₀ := mulMap β (c (S ⊗[R] S) pr₁ pr₂)`, a unit of `S ⊗[R] S`.
2. By `hnat` and `mulMap_naturality`, every `R`-algebra map `f : S ⊗[R] S → T` satisfies
   `f(u₀) = mulMap β (c T (f ∘ pr₁) (f ∘ pr₂))`.
3. Apply step 2 to the three maps `f₁₃`, `f₂₃` and `f₁₂`. They satisfy
   `f₁₃ ∘ pr₁ = f₁₂ ∘ pr₁`, `f₂₃ ∘ pr₁ = f₁₂ ∘ pr₂` and `f₂₃ ∘ pr₂ = f₁₃ ∘ pr₂`. With `hcoc`
   and commutativity, this gives `u₀₁₃ = u₀₂₃ · u₀₁₂`.
4. `exists_isUnit_of_unitCocycle` gives a unit `m ∈ S` with `u₀ (m ⊗ 1) = 1 ⊗ m`. Put
   `f := θ(m)`.
5. Fix `T` and `a, b` that agree on `K`. Let `A' = (id ⊗ a) ∘ θ` and `B' = (id ⊗ b) ∘ θ`,
   both maps `S → B ⊗[k] T`. By `hθR` they agree on `R`. Make `B ⊗[k] T` an `R`-algebra
   through `A'`. Then `A'` and `B'` are `R`-algebra maps, and they induce
   `ψ : S ⊗[R] S → B ⊗[k] T`. By `hθj`, `ψ ∘ pr₁ = includeRight ∘ a` and
   `ψ ∘ pr₂ = includeRight ∘ b`.
6. By step 2 and `hnat`, `ψ(u₀) = mulMap β ((id ⊗ includeRight)(c T a b))`. This equals
   `c T a b`, because `mulMap β ∘ (id ⊗ includeRight)` is the identity of `B ⊗[k] T` by
   `hθβ`. Applying `ψ` to `u₀ (m ⊗ 1) = 1 ⊗ m` gives `c T a b * A'(m) = B'(m)`, which is
   the claim.

## Specialisation to `K ⊗[k] B`

- `coverIncl k B K L : L →ₐ[k] (K ⊗[k] B) ⊗[K] L` is `l ↦ 1 ⊗ l` (`coverIncl_apply`).
- `coverMap k B K L : (K ⊗[k] B) ⊗[K] L →ₐ[k] B ⊗[k] L` sends
  `(κ ⊗ b) ⊗ l ↦ b ⊗ κ l` (`coverMap_tmul`). Further lemmas are `coverMap_coverIncl` and
  `coverMap_algebraMap`.
- `exists_unit_coboundary [Module.Finite k B]` has the same family `c` and the same
  hypotheses `hnat` and `hcoc` as the generic lemma, and the same conclusion. It holds for
  every extension of fields `L/K` over `k`.

*Proof.* Apply `exists_unit_coboundary_of_cover` with `R := K ⊗[k] B`,
`S := (K ⊗[k] B) ⊗[K] L`, `β := includeRight`, `j := coverIncl` and `θ := coverMap`.

- `R` is finite over the field `K`, hence Artinian, and so it has finitely many maximal
  ideals.
- `S` is faithfully flat over `R`, being a base change of the field extension `L/K`.
- `hj`: `1 ⊗ x = algebraMap (x ⊗ 1)` for `x ∈ K`.
- `hθj` is `coverMap_coverIncl`.
- `hθβ` and `hθR` follow from `coverMap_algebraMap`. Each `θ(κ ⊗ b) = b ⊗ κ` comes from
  `B ⊗[k] K`, and this extends additively.
