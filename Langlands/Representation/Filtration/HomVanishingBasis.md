# A basis of maps out of a filtered functor value, from rank-one graded pieces

Author: Worker 5226. This is an internal construction with supporting lemmas, derived for the planned proof of the free-module conjunct of the first lemma of Renard VI.10.4 (printed pp.209–212 / PDF pp.215–218). Reference: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Renard does not state these lemmas.

The file combines two earlier units:
- the vanishing filtration `homVanishing` of `Langlands/Representation/Filtration/HomVanishingFiltration.lean`, with its descent to graded pieces;
- the basis `FilteredModule.basisOfFilteredRankOne` of `Langlands/Algebra/FilteredRankOneExpansion.lean`, built from a filtration whose steps are trivial or free of rank one.

The planned use takes `F = r_P ∘ i_P` with the natural geometric-lemma filtration, `X = Π_D` and `Y = Π_D`, so that `Hom(r_P i_P Π_D, Π_D) ≅ End(i_P Π_D)` becomes free over `End(Π_D)` with one basis vector per double coset of the relevant type. This file does not prove that application. Everything here is unconditional and works for an arbitrary filtered additive functor.

## Setting

Throughout:
- `R` is a commutative ring and `G` a monoid;
- `C` is a preadditive category and `F : C ⥤ Rep R G` an additive functor (`[F.Additive]`);
- `s : RepFunctorFiltration F n` is a published natural filtration with graded functors `s.graded j` for `j : Fin n`;
- `X : C` is an object and `Y : Rep R G` a target.

## Declarations

### The module structure

- `precompModule F X Y` is the left `(End X)ᵐᵒᵖ`-module structure on `F.obj X ⟶ Y` given by `op a • f = F.map a ≫ f`. It is a `def` used through `letI`, not a global instance.
  - The ring is the opposite ring because `F.map (b * a) ≫ f = F.map a ≫ F.map b ≫ f`, where `b * a = a ≫ b` in `End X`.
  - The module axioms follow from `F.map_id`, `F.map_comp`, `F.map_add`, `F.map_zero` and bilinearity of composition. Additivity of `F` is used for `add_smul` and `zero_smul`.
- `precompModule_smul` (by `rfl`) unfolds the action.

### The filtration as submodules

- `homVanishingSubmodule s X Y i` is `homVanishing s X Y i` as an `(End X)ᵐᵒᵖ`-submodule. Closure under the action is `map_comp_mem_homVanishing`.
- `mem_homVanishingSubmodule` (by `Iff.rfl`) unfolds membership.

### Lifts of maps out of graded pieces

The section hypothesis `hsec` says that for every `k : Fin n` there is `σ` with `σ ≫ s.gradedProjection X k = 𝟙`. Fix a family `θ j : (s.graded j).obj X ⟶ Y`.

- `gradedLift s X Y hsec θ j : F.obj X ⟶ Y` is a map chosen by `Classical.choose` from `exists_gradedDescent_eq_of_sections`.
  - `gradedLift_mem`: it vanishes on step `j`.
  - `gradedDescent_gradedLift`: its graded descent at `j` is `θ j`.

### Rank-one and invisible steps

Fix `S : Finset (Fin n)` and assume:
- `hθ`: for `j ∈ S`, the map `a ↦ (s.graded j).map a ≫ θ j` from `X ⟶ X` to `(s.graded j).obj X ⟶ Y` is bijective;
- `hzero`: for `j ∉ S`, every map `(s.graded j).obj X ⟶ Y` is zero.

The two lemmas below check the hypotheses `huniq` and `hzero` of `basisOfFilteredRankOne`.

- `existsUnique_sub_smul_gradedLift_mem` (uses `hθ`): for `j ∈ S` and `x` vanishing on step `j`, there is exactly one `a : (End X)ᵐᵒᵖ` with `x - a • gradedLift j` vanishing on step `j + 1`. The proof first shows, for each `a`, that this condition is equivalent to `(s.graded j).map a.unop ≫ θ j = gradedDescent x`. It rewrites with:
  - `gradedDescent_eq_zero_iff`, so that vanishing on step `j + 1` is vanishing of the descent;
  - `gradedDescent_sub`, so that the descent of the difference is the difference of descents;
  - `gradedDescent_map_comp` and `gradedDescent_gradedLift`, so that the descent of `F.map a.unop ≫ gradedLift j` is `(s.graded j).map a.unop ≫ θ j`.

  Surjectivity in `hθ` then gives existence, and injectivity gives uniqueness.
- `homVanishing_castSucc_le_succ` (uses `hzero`): for `j ∉ S`, a map vanishing on step `j` also vanishes on step `j + 1`, because its descent is zero by `hzero` and `gradedDescent_eq_zero_iff` applies.

### The basis

- `homVanishingBasis s X Y hsec θ S hθ hzero : Module.Basis S (End X)ᵐᵒᵖ (F.obj X ⟶ Y)`, for the precomposition action, is the main definition of the file. It is `basisOfFilteredRankOne` applied to:
  - the filtration `homVanishingSubmodule`, decreasing by `homVanishing_succ_le`;
  - `K 0 = ⊤` from `homVanishing_zero` and `K n = ⊥` from `homVanishing_last`;
  - the vectors `gradedLift j`, which lie in step `j` by `gradedLift_mem`;
  - the two lemmas of the previous subsection.
- `homVanishingBasis_apply`: the basis vector at `j : S` is `gradedLift j`. It is `basisOfFilteredRankOne_apply`.
- `existsUnique_precomp_expansion` restates the basis property without the module structure. Every `f : F.obj X ⟶ Y` equals `∑_{j : S} F.map (a j) ≫ homVanishingBasis j` for exactly one family `a : S → (X ⟶ X)`.
  - Existence: take `a j = (b.equivFun f j).unop`. Then use `Module.Basis.equivFun_symm_apply` and `LinearEquiv.symm_apply_apply`.
  - Uniqueness: an expansion with family `a` says `b.equivFun.symm (op ∘ a) = f`. Applying `b.equivFun` recovers `op ∘ a = b.equivFun f`.

## Hypotheses not proved here

The section hypothesis `hsec`, the bijectivity `hθ` and the vanishing `hzero` are assumptions. In the planned application:
- `hsec` comes from projectivity of the graded pieces;
- `hθ` comes from the full pieces of the geometric lemma being twists of `Π_D` by Weyl elements fixing its class;
- `hzero` comes from the vanishing of the other pieces.

None of these is proved in this file.
