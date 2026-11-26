# Split components of nested Levi subgroups over a field extension

**Exact target.** `Langlands.GroupScheme.FieldLeviSplitComponentInclusionStatement`.

Let `G` be a connected reductive group scheme over a field `k`, affine and locally of finite type over `Spec k` (these two properties are explicit instance arguments). Let `K` be a field with a `k`-algebra structure, `f = algebraBaseMap k K` and `BC = GroupScheme.baseChange f`. The data are

- a parabolic subgroup `p : P ⟶ G` and a rational Levi subgroup `l : M ⟶ P` (`IsParabolicSubgroup`, `IsRationalLeviSubgroup`);
- a parabolic subgroup `p₁ : P₁ ⟶ G_K` and a rational Levi subgroup `l₁ : M₁ ⟶ P₁` of the base change;
- a homomorphism `m : M₁ ⟶ M_K` with `m ≫ BC.map (l ≫ p) = l₁ ≫ p₁`, so that `M₁` lies in `M_K` compatibly with the two inclusions into `G_K`;
- split components `a : A ⟶ M` and `a₁ : A₁ ⟶ M₁` (`IsSplitComponent`).

The statement asserts a homomorphism `j : A_K ⟶ A₁` of commutative group schemes over `K` with `j ≫ a₁ ≫ m = BC.map a`. In Arthur's notation this is the inclusion `A_M ⊆ A_{M₁}` after base change, which gives the inclusion `𝔞_M ⊆ 𝔞_{M₁}` of real cocharacter spaces.

The extension `K/k` is arbitrary: it need not be finite, separable or Galois, and no characteristic is assumed. The parabolic `P₁` need not be contained in `P_K`.

**Source.** J. Arthur, *An introduction to the trace formula* (2005), §17, printed p.99 (PDF p.111), in `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: "Suppose that `M` contains a Levi subgroup `M₁` of `G` over some extension `k₁` of `k`. Then `𝔞_M` is contained in the vector space `𝔞_{M₁}` attached to `M₁`." The mathematical reason is that a Levi subgroup of a parabolic is the centralizer of its split component (A. Borel and J. Tits, *Groupes réductifs* (1965), 4.15 b), printed pp.90–91, `borel-tits-1965-groupes-reductifs`): `A_{M,K}` is central in `M_K`, hence commutes with `A₁ ⊆ M₁`, lies in the centralizer `M₁` of `A₁`, is a central split torus there, and so lies in the largest central split torus `A₁`.

This file states the proposition and does not prove it.
