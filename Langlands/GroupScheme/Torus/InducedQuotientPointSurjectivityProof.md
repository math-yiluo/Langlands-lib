# Proof: point surjectivity of quotients by induced central tori

This module proves the published proposition
`Langlands.GroupScheme.InducedTorusQuotientPointSurjectivityStatement` (module
`Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityStatement`):

```text
theorem Langlands.GroupScheme.inducedTorusQuotientPointSurjectivity :
    InducedTorusQuotientPointSurjectivityStatement.{u}
```

Recall the statement. Let `k` be a field and `K/k` any field extension. Let `Z` be an induced
torus over `k`, and let `i : Z ⟶ H` be a closed subgroup. Let `p : H ⟶ G` be an fppf quotient
whose kernel subgroup functor is the image of `i`. Then the actual map `H(K) → G(K)`,
`x ↦ x ≫ p`, is surjective. The statement keeps every field `k` and every extension `K/k`,
with no separability, perfectness, algebraicity or finiteness assumption, and the proof adds
no hypothesis.

The proof uses only part of the hypotheses:

- that the underlying scheme morphism of `p` is surjective;
- that the kernel equality `range (kernelι p) = range i` holds on every affine test;
- that `i` is a closed immersion, hence a monomorphism;
- that `Z` is induced.

It does not use centrality of `i`, reductivity of `H` or `G`, or the flatness and
finite-presentation parts of `IsFppfQuotient`. `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`.

## Route and provenance

The literature argument is the one cited in the statement's Markdown (Kaletha–Prasad §2.5
and §11.5; Platonov–Rapinchuk (2.7) and Lemma 2.4; Milne III.3.9, III §4 and III.4.9). The
fibre of `p` over a `K`-point is a torsor under `Z_K`. By Shapiro's lemma and Hilbert's
Theorem 90, `H¹(K, Z_K) = 1`, so the torsor has a `K`-point.

The Lean proof makes this argument concrete without building torsors or Galois cohomology:

1. Lift the point to a field extension `L/K`, where a point of the fibre exists.
2. The ambiguity of the lift over `L ⊗[K] L`, and over every other test algebra, is a
   descent cocycle with values in `Z(T) ≅ (B ⊗[k] T)ˣ`. Here `Z ≅ R_{B/k} 𝔾ₘ` for a finite
   `k`-algebra `B`, by the Library theorem `inducedTorusWeilDecomposition`.
3. The cocycle is a coboundary (`Langlands.Algebra.Semilocal.exists_unit_coboundary`). This
   is Hilbert 90 for the semilocal ring `K ⊗[k] B`.
4. Correct the lift by the resulting unit. The corrected lift descends to `K` by fpqc descent
   along `Spec L → Spec K` (`Langlands.GroupScheme.FieldPoints`).

## Helper modules

The proof imports three new helper modules, each with its own Markdown:

- `Langlands.Algebra.SemilocalUnitProduct`: over a ring with finitely many maximal ideals, a
  generating family of products contains a unit product.
- `Langlands.Algebra.UnitCocycleSemilocal`: unit cocycles over a semilocal base are
  coboundaries, and its consequence `exists_unit_coboundary` for natural
  `(B ⊗[k] T)ˣ`-valued cocycles of a field extension `L/K`.
- `Langlands.GroupScheme.FieldPoints`: lifting points along surjective morphisms to a field
  extension (`exists_field_lift`), injectivity of restriction (`affineMap_injective`), and
  descent of points (`exists_affineMap_eq`).

## Declarations in `Langlands.GroupScheme.InducedQuotientPointSurjectivity`

Throughout, `H` and `G` are group schemes over `Spec k`, and `B` is a commutative
`k`-algebra.

- `affineMap_comp_hom`: restriction along `φ : A →ₐ[k] T` commutes with postcomposition by
  `p`.
- `mul_inv_comp_hom`: `(x * y⁻¹) ≫ p = (x ≫ p) * (y ≫ p)⁻¹`, from `affinePointsTarget`
  being a homomorphism.

### `surjective_of_unitsKernel` (points-level core)

Assume `[Module.Finite k B]` and that the underlying scheme morphism of `p` is surjective.
Also assume homomorphisms `ψ T : (B ⊗[k] T)ˣ →* H(T)`, one for every commutative `k`-algebra
`T`, such that:

- each `ψ T` is injective (`hinj`);
- `ψ` is natural: `ψ T' ((id ⊗ φ) v) = φ_* (ψ T v)` (`hnat`);
- every `x ∈ H(T)` with `x ≫ p = 1` is some `ψ T v` (`hker`);
- `ψ T v ≫ p = 1` for all `v` (`hcomp`).

Then `H(K) → G(K)` is surjective for every field `K` over `k`.

*Proof.* Fix `g ∈ G(K)`.

1. By `exists_field_lift`, there are a field `L ⊇ K` and `h₁ ∈ H(L)` with
   `h₁ ≫ p = g|_L`.
2. Let `T` be a `k`-algebra and `a, b : L → T` two `k`-algebra maps that agree on `K`. Then
   `b_* h₁ · (a_* h₁)⁻¹` maps to `1` in `G(T)`, since both factors map to `g` restricted
   along the common map `K → T`. By `hker` it equals `ψ T v` for some `v`. Let `c T a b` be
   a chosen such `v`, and `1` if `a` and `b` do not agree on `K`.
3. Injectivity of `ψ` and `hnat` give naturality of `c`. They also give the cocycle identity
   `c T a d = c T a b * c T b d`: the units group is commutative, and
   `ψ (c T b d * c T a b) = d_* h₁ (b_* h₁)⁻¹ · b_* h₁ (a_* h₁)⁻¹ = d_* h₁ (a_* h₁)⁻¹`.
4. `exists_unit_coboundary` gives `f ∈ (B ⊗[k] L)ˣ` with `c T a b * a_*(f) = b_*(f)` for all
   `T` and all `a, b` that agree on `K`.
5. Put `F := ψ L f` and `h₂ := F⁻¹ h₁`. Let `a, b : L → L ⊗[K] L` be the two inclusions.
   Applying `ψ` to the coboundary identity and using `hnat` gives
   `b_* h₁ (a_* h₁)⁻¹ · a_* F = b_* F`. Rearranging gives `a_* h₂ = b_* h₂`.
6. By `exists_affineMap_eq`, `h₂ = y|_L` for some `y ∈ H(K)`.
7. `(y ≫ p)|_L = h₂ ≫ p = (F ≫ p)⁻¹ (h₁ ≫ p) = g|_L`, using `hcomp` for `F ≫ p = 1`.
   `affineMap_injective` for `G` gives `y ≫ p = g`.

### Weil restriction model

- `lTensor_apply_eq_map`: `Algebra.TensorProduct.lTensor B φ` and `map (AlgHom.id k B) φ`
  agree as functions.
- `weilPointsEquiv k B T`: `Lie.AffinePoints (WeilGm.groupScheme k B) T ≃* (B ⊗[k] T)ˣ`. It
  is the Library's `Corepresented.affinePointsEquiv` for the corepresentable functor
  `WeilGm.functor`.
- `weilPointsEquiv_affineMap`: this equivalence is natural in `T`. It follows from
  `Corepresented.affinePointsEquiv_naturality` and `lTensor_apply_eq_map`.
- `surjective_of_weil` (with `[Module.Finite k B] [Module.Projective k B]`): let
  `e : Z ≅ WeilGm.commGroupScheme k B`, let `i : Z ⟶ H` be a closed subgroup, and let `p`
  satisfy `IsFppfQuotient (SubgroupFunctor.range i) p`. Then `H(K) → G(K)` is surjective.

*Proof of `surjective_of_weil`.* Apply `surjective_of_unitsKernel` with
`ψ T v := ((weilPointsEquiv k B T).symm v ≫ e⁻¹) ≫ i`.

- Surjectivity of `p` on underlying schemes is the second component of `IsFppfQuotient`.
- Injectivity: `i` is a monomorphism (`IsClosedSubgroup.mono_overHom`), `e` is an
  isomorphism and `weilPointsEquiv` is a bijection.
- Naturality comes from `weilPointsEquiv_affineMap` and associativity of composition.
- `hker` and `hcomp` both come from the kernel component
  `range (kernelι p) = range i` of `IsFppfQuotient`, together with the Library lemma
  `mem_range_kernelι_iff` (`x ∈ range (kernelι p) ↔ x ≫ p = 1`). For `hker`, a point of
  `range i` is `z ≫ i`, which is `ψ T (weilPointsEquiv k B T (z ≫ e))`.

## Main theorem

`inducedTorusQuotientPointSurjectivity` introduces the data of the statement.

1. Unfolding `IsInducedTorus Z` gives a finite Galois extension `E/k` such that `Z_E` is
   split.
2. The Library theorem `inducedTorusWeilDecomposition` then gives `n` and intermediate
   fields `F : Fin n → IntermediateField k E` with
   `Z ≅ WeilGm.commGroupScheme k (∀ m, F m)`.
3. The algebra `B := ∀ m, F m` is finite and projective over `k`, so `surjective_of_weil`
   applies.
