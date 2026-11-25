# Extensions with connected quotient in Hopf-algebra terms

This module is part of the proof that extensions of groups of multiplicative
type over a field are of multiplicative type (`multiplicativeTypeFieldExtension`
in `Langlands.GroupScheme.Torus.MultiplicativeTypeFieldExtensionProof`); it
treats the connected case. It is the algebraic core of the statement "an extension of a connected diagonalizable group by a
diagonalizable group is commutative".

## Setting

Let `K` be a field and `A` a commutative `K`-Hopf algebra (`G = Spec A`).
Consider bialgebra maps `φ : K[M] → A` and `π : A → K[N]` for commutative
groups `M`, `N`. The structure `IsExtension φ π` has four fields:

- `injective`: `φ` is injective (the quotient map `G → D(M)` is faithfully
  flat);
- `surjective`: `π` is surjective (`D(N) → G` is a closed immersion);
- `comp_eq`: `π ∘ φ = algebraMap ∘ ε` (`D(N)` lies in the kernel);
- `invariants`: every element of degree `0` for the `N`-grading defined by `π`
  ([`GroupAlgebraCoaction`](GroupAlgebraCoaction.md)) lies in the image of
  `φ`, i.e. `D(M) = G / D(N)`.

Unlike `CentralTorusExtensionHopf.IsCentralExtension`, centrality is not
assumed. The main results assume only that `K[M]` has no idempotents other than
`0` and `1` (geometrically: `D(M)` is connected), and prove:

- `isCentral`: `π` is central (`GroupAlgebraCoaction.IsCentral`);
- `comm_comul`, `isCocomm`: `A` is cocommutative (`G` is commutative).

No finiteness, smoothness or freeness assumption on `M`, `N` or `A` is made.

## Points and convolution

The proofs use points of `G` with values in commutative `K`-algebras `B`
(algebra maps `A → B`), multiplied by convolution.

- `conv ξ ξ'`: the algebra map `c ↦ ∑ ξ(c₁) ξ'(c₂)`, defined as
  `productMap ξ ξ' ∘ Δ`. It agrees with Mathlib's convolution product
  (`conv_eq_ofConv`, `AlgHom.convMul_apply`). It is defined separately because
  Mathlib's `WithConv` multiplication fails to find its instances when the
  target is a nested tensor product of group algebras.
- `comp_productMap`, `productMap_map`, `comp_conv`, `conv_comp_bialgHom`:
  naturality of `productMap` and of `conv` under composition with algebra maps
  and bialgebra maps.
- `conv_assoc`, `one_conv`, `conv_one`: the group laws, from Mathlib's
  `AlgHom.convGroup`.
- `T₃ K N D` and `A₃ K A` are the triple tensor products
  `K[N] ⊗ (K[N] ⊗ D)` and `A ⊗ (A ⊗ A)`, wrapped as types with their own ring
  structure. `u₁`, `u₂`, `u₃` and `j₁`, `j₂`, `j₃` are their universal points,
  and `T₃.lift` (with `T₃.lift_comp_u₁`, `T₃.lift_comp_u₂`,
  `T₃.lift_comp_u₃`) maps out of `T₃`. The wrappers avoid the same
  instance-path problem for nested tensor products.

## Rigidity over a connected coefficient ring

`exists_eq_single_tmul_one`: let `D` be a nonzero `K`-algebra whose only
idempotents are `0` and `1`, and let `W ∈ K[N] ⊗ D`. Suppose `W` is
"multiplicative in the first variable" and normalized:

- `W(u₁ ⋆ u₂, u₃) = W(u₁, u₃) · W(u₂, u₃)` at the universal points of `T₃`,
  where `W(ξ, η) = productMap ξ η W`;
- `W(1, id) = 1`.

Then `W = Xᵘ ⊗ 1` for some `μ`.

Proof: let `y ∈ D[N]` be the image of `W` under `K[N] ⊗ D ≅ D[N]`
(`AddMonoidAlgebra.scalarTensorEquiv`; `productMap_ξ₀_η₀` identifies it with
`productMap ξ₀ η₀`). Map the multiplicativity identity along the algebra map
`T₃ → D[N × N]` sending the three universal points to `Xᵐ ↦ X^(m,0)`,
`Xᵐ ↦ X^(0,m)` and the constants. This gives
`diagMap y = inlMap y · inrMap y`, and the normalization gives
`groupCounit y = 1`. The Library's
`HopfPointConnected.exists_eq_single_of_grouplike` then gives
`y = single μ 1`.

## The extension

Fix `n : N`. `exists_unitFamily` gives a finite family `(aᵢ, bᵢ)` (a
multiset) with `aᵢ` of degree `n`, `bᵢ` of degree `-n` and `∑ aᵢ bᵢ = 1`. It
uses the Library's `one_mem_grade_neg_mul_grade` and an element of degree
`-n` with counit `1` (`exists_mem_grade_counit_eq_one'`, from surjectivity of
`π`). Further lemmas about the extension:

- `map_mem_grade_zero'`: elements of `φ(K[M])` have degree `0`. The proof
  repeats `CentralTorusExtensionHopf.map_mem_grade_zero` for an arbitrary
  `M`.
- `comp_eq_one`: `π ∘ φ` is the trivial point.
- `conv_apply_of_mem_grade_zero`, `conv_comp_φ`: left translation by a point
  `ψ ∘ π` of `D(N)` does not change a point of `G` on degree-zero elements.
  Such elements are of the form `φ(c)`, and `ψ ∘ π ∘ φ` is trivial.
- `eq_of_forall_mul`: if `c · x(a) = d · x(a)` for every `a` of degree `n`,
  then `c = d`. Multiply by `x(bᵢ)` and sum.
- `map_eq_single_of_mem_grade`: `π(a) = ε(a) Xⁿ` for `a` of degree `n`.
- `conv_right_of_mem_grade`: `(x ⋆ ψπ)(a) = x(a) ψ(Xⁿ)` for `a` of degree
  `n`.

### Centrality (`isCentral`)

For a point `ψ` of `D(N)` and a point `x` of `G`, the conjugation character is
`E(ψ, x) = ∑ (ψπ ⋆ x)(aᵢ) · x(bᵢ)` (`charE`). It satisfies:

- `conv_eq_charE_mul`: for `a` of degree `n`,
  `(ψπ ⋆ x)(a) = E(ψ, x) · x(a)`. Insert `1 = ∑ aᵢ bᵢ`. Each `bᵢ a` has degree
  `0`, so the left translation does not change it.
- `charE_eq_productMap`, `charE_univ_mem`, `charE_eq_W`: `E` is the evaluation
  of a universal element of `K[N] ⊗ A`. That element lies in
  `K[N] ⊗ φ(K[M])`, because `Δ aᵢ ∈ A ⊗ A_n` (`comul_of_mem`) and
  `A_n · A_{-n} ⊆ A_0`. So `E(ψ, x) = W(ψ, x ∘ φ)` for some
  `W ∈ K[N] ⊗ K[M]`.
- `charE_conv_right`: `E(ψ, ψ'π ⋆ x) = E(ψ, x)`. The point `x` enters only
  through `x ∘ φ`.
- `charE_conv`: `E(ψ ⋆ ψ', x) = E(ψ, x) E(ψ', x)`, by `conv_eq_charE_mul`
  twice and `eq_of_forall_mul`.
- `charE_one`: `E(1, x) = 1`.
- `exists_charE_univ_eq`: the universal `E` is `Xᵘ ⊗ 1`. Transport
  `charE_conv` to `T₃ K N K[M]` along the injective map
  `id ⊗ (id ⊗ φ) : T₃ K N K[M] → T₃ K N A` (flatness over a field), then
  apply `exists_eq_single_tmul_one`. `charE_eq_of_univ` evaluates.

To finish, an element `a₀` of degree `n` with counit `1` gives
`π(a₀) = Xᵘ`, so `μ = n` by `map_eq_single_of_mem_grade`. Hence
`(ψπ ⋆ x)(a) = ψ(Xⁿ) x(a) = (x ⋆ ψπ)(a)` for every `a` of degree `n`, and so
for every `a` (`sum_proj`). At the universal points of `K[N] ⊗ A` this is the
centrality identity `rTensor π (Δa) = comm (lTensor π (Δa))`.

### Commutativity (`comm_comul`, `isCocomm`)

Assume in addition that `π` is central (true by `isCentral`). Facts about the
quotient:

- `conv_comm_groupAlgebra`: points of `K[M]` commute, since group-like
  monomials span.
- `conv_comm_of_mem_grade_zero`: hence points of `G` commute on degree-zero
  elements.

The commutator pairing is
`U(g, k) = ∑ (g ⋆ k)(aᵢ) · (k ⋆ g)(bᵢ)` (`commU`). It satisfies:

- `conv_eq_commU_mul`: `(g ⋆ k)(a) = U(g, k) · (k ⋆ g)(a)` for `a` of degree
  `n`.
- `conv_left_eq_commU_mul`: `(z ⋆ g ⋆ k)(a) = U(g, k) · (z ⋆ k ⋆ g)(a)`, using
  `Δa ∈ A ⊗ A_n`.
- `conv_right_eq_commU_mul`: `(g ⋆ k ⋆ w)(a) = U(g, k) · (k ⋆ g ⋆ w)(a)`, using
  `Δa ∈ A_n ⊗ A` (centrality, `IsCentral.rTensor_proj_comul`).
- `commU_conv`: `U(x ⋆ x', y) = U(x, y) U(x', y)`. Expand `(x ⋆ x' ⋆ y)(a)`
  in two ways and cancel with `eq_of_forall_mul`.
- `commU_one`, `one_commU`: `U(g, 1) = U(1, g) = 1`.
- `commU_eq_productMap`, `commU_univ_mem`, `commU_eq_V`: the universal `U` on
  `A ⊗ A` lies in `φ(K[M]) ⊗ φ(K[M])`. With centrality,
  `Δ aᵢ ∈ A_n ⊗ A_n` and `Δ bᵢ ∈ A_{-n} ⊗ A_{-n}`. So `U(g, k) = V(gφ, kφ)`
  for some `V ∈ K[M] ⊗ K[M]`.
- `commU_univ_eq_one`: `U = 1`. Transport `commU_conv` to `T₃ K M K[M]`
  along the injective map `φ ⊗ (φ ⊗ φ)` into `A₃ K A`. Then
  `exists_eq_single_tmul_one` (with `D = K[M]`) gives `V = Xᵡ ⊗ 1`.
  `U(id, 1) = 1` gives `φ(Xᵡ) = 1`, so `Xᵡ = 1` by injectivity.

Then `(g ⋆ k)(a) = (k ⋆ g)(a)` for every homogeneous `a`, so for every `a`. At
the universal points of `A ⊗ A`, this says `comm (Δa) = Δa` (`comm_comul`).
`isCocomm` packages it as Mathlib's `Coalgebra.IsCocomm`.

## Provenance

Internal to this project. Geometrically, the module proves the connected case
of SGA 3, Exposé IX, Proposition 8.2 (i), as in Milne, *Algebraic Groups*
(2017), source ID `milne-2017-algebraic-groups`, Corollary 12.42 (printed
p.244). There, rigidity (Corollaries 12.37 and 12.41) shows:

- the conjugation action of `G` on the normal multiplicative subgroup factors
  through the connected quotient and is trivial;
- the commutator pairing is trivial.

The Lean proof does not use any rigidity theorem for schemes. The rigidity
step is the algebraic statement `exists_eq_single_tmul_one`: group-like
elements of a group algebra over a connected ring are monomials. It is
applied to the conjugation character and to the commutator pairing.
