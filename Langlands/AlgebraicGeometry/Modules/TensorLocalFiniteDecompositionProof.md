# Proof of local finite pure-tensor decompositions of sections

This module proves the published proposition
`Langlands.Scheme.Modules.TensorLocalFiniteDecompositionStatement` from
`Langlands.AlgebraicGeometry.Modules.TensorLocalFiniteDecompositionStatement`,
which it imports unchanged.

## Main result

`Langlands.Scheme.Modules.tensorLocalFiniteDecomposition` is the theorem

```lean
theorem tensorLocalFiniteDecomposition (X : AlgebraicGeometry.Scheme.{u}) :
    TensorLocalFiniteDecompositionStatement X
```

for an arbitrary universe `u`. It adds no hypothesis on `X`, `M` or `N`.
For all `M N : X.Modules`, every open `U`, every section `z` of
`tensorObj M N` over `U` and every `x ∈ U`, it supplies an open `V ≤ U`
with `x ∈ V`, a natural number `n`, and sections `s i ∈ M(V)`,
`t i ∈ N(V)` for `i : Fin n`, such that

```text
((tensorSheafifyUnit M N).app (op V)).hom (∑ i, s i ⊗ₜ t i)
  = (tensorObj M N).val.map (homOfLE hVU).op z.
```

The tensors are over the section ring `X.presheaf.obj (op V)`.

## Helper lemma

`Langlands.Scheme.Modules.exists_fin_sum_tmul` states that every element `x`
of an algebraic tensor product `M ⊗[R] N` over a commutative semiring `R` is
`∑ i : Fin n, s i ⊗ₜ[R] t i` for some `n : ℕ` and families
`s : Fin n → M`, `t : Fin n → N`. The proof is Mathlib's tensor-product
induction `TensorProduct.inductionOn`. A pure tensor `m ⊗ₜ n` uses `n = 1`
with constant families. For a sum `x + y` it concatenates the two
families with `Fin.append`; `Fin.sum_univ_add` splits the sum over
`Fin (n₁ + n₂)` into the two given sums. The induction has no separate zero
case, so the lemma never needs to produce `n = 0`; the statement still
permits it.

## Proof of the main theorem

1. **Local surjectivity of the unit.** `tensorSheafifyUnit M N` is the unit
   of `sheafifyAdjunction X`, which is Mathlib's
   `PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)`, at
   the sectionwise tensor presheaf `M.val ⊗ N.val`. After the forgetful
   functor `PresheafOfModules.toPresheaf`, this unit is by definition the
   abelian-group sheafification map `CategoryTheory.toSheafify J P.presheaf`
   (Mathlib's `rfl` lemma
   `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`).
   Here `J` is `Opens.grothendieckTopology X` and `P` is the sectionwise
   tensor. The proof restates the goal with `change` and obtains
   `Presheaf.IsLocallySurjective J (toSheafify J P.presheaf)` from Mathlib's
   instances stating that sheafification maps are locally surjective.

2. **A neighborhood and a local preimage.** `Presheaf.imageSieve_mem`
   applied to `z` shows that the image sieve of `z` covers `U`. Membership in
   `Opens.grothendieckTopology X` unfolds to: for every `x ∈ U` there are an
   open `V` and a morphism `f : V ⟶ U` in the sieve with `x ∈ V`. Being in
   the image sieve gives a section `w` of the sectionwise tensor over `V`,
   that is `w ∈ M(V) ⊗[O_X(V)] N(V)`, whose image under the unit component
   at `op V` is the restriction of `z` along `f.op`.

3. **Finite pure tensors.** `exists_fin_sum_tmul w` rewrites `w` as
   `∑ i : Fin n, s i ⊗ₜ t i`.

4. **Conclusion.** The witnesses are `V`, `hVU := leOfHom f`, `x ∈ V`, `n`,
   `s` and `t`. The required equation is the image-sieve equation, accepted
   by `exact` up to definitional unfolding. In particular,
   `homOfLE (leOfHom f)` is definitionally `f`, and the restriction of the
   underlying abelian-group presheaf is the module restriction.

The neighborhood `V` is shrunk inside the original `U` and contains the
original point `x`. The equation uses the actual unit component and the
actual restriction morphism of `tensorObj M N`, as required.

## Source and scope

This is the arbitrary-section form of the local finite-sum choice in the
second proof paragraph of Stacks Project Lemma 17.25.2 (registered source
`stacks-local-freeness-invertibility-sections-2026-10-21`, file `01CR.html`).
The source picks finitely many local pure tensors that map to the unit
section under an isomorphism `L ⊗ N ≅ 𝒪_X`. This proof treats any section of
the tensor of any two module sheaves and goes through the sheafification
unit. The source's route is therefore not followed literally; only the
proposition is proved. Nothing here proves the invertible-implies-locally-
free-of-rank-one implication or any pullback/tensor comparison.

## Verification

The development check passes with zero errors and zero warnings at the
default heartbeat limit. The theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
