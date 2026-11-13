# A basis of the endomorphisms of an induced object, through an adjunction

Author: Worker 5226. This is an internal construction with supporting lemmas. It was derived for the planned proof of the free-module conjunct of the first lemma of Renard VI.10.4 (printed pp.209–212 / PDF pp.215–218). Reference: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Renard does not state these lemmas, and this file does not follow his first step. Renard's proof (printed p.210 / PDF p.216, equation (VI.10.4.3)) uses Bernstein's second adjointness: it identifies `End(i_P Π_D)` with `Hom(Π_D, r_{P̄} i_P Π_D)`, where `P̄` is the opposite parabolic, and then with `Hom(Π_D, r_D i_P Π_D)` through the block projection `r_D`. This file takes a different route, devised by the author, that uses only the first adjunction (Frobenius reciprocity) `r_P ⊣ i_P`. It identifies `End(i_P Π_D)` with `Hom(r_P i_P Π_D, Π_D)`: the Hom arguments are reversed and the Jacquet functor is taken along `P` instead of `P̄`. The file gives this alternative identification in an abstract categorical form. It is a supporting step toward the same freeness conclusion, not a formalization of Renard's argument.

The file builds on `homVanishingBasis` of `Langlands/Representation/Filtration/HomVanishingBasis.lean`. That basis is of the maps `F.obj X ⟶ Y` out of the value of a filtered functor, over `(End X)ᵐᵒᵖ`. Here it is transported along an adjunction to a basis of `End(Ind X)`.

The planned use takes:
- `Ind = leviInductionFunctor` and `Res = leviJacquetFunctor`, with the adjunction `leviFirstAdjunction`;
- `T = SmoothRep.toRep`;
- `X = Π_D`.

This file does not prove that application. Everything here is unconditional and works for an arbitrary adjunction.

## Setting

Throughout:
- `C` and `D` are preadditive categories;
- `Res : D ⥤ C` and `Ind : C ⥤ D` are additive functors with an adjunction `adj : Res ⊣ Ind`;
- `T : C ⥤ Rep R G` is additive, full and faithful, where `R` is a commutative ring and `G` a monoid;
- `X : C` is an object.

## Declarations

### The precomposition module on maps out of a functor value

- `endPrecompModule Φ X Z`, for an additive functor `Φ : C ⥤ D` between preadditive categories, is the left `(End X)ᵐᵒᵖ`-module structure on `Φ.obj X ⟶ Z` given by `op a • f = Φ.map a ≫ f`.
  - It is the analogue of `precompModule` (in `HomVanishingBasis.lean`), which is stated only for functors into `Rep R G`.
  - It is a `def` used through `letI`, not a global instance.
  - The module axioms follow from `Φ.map_id`, `Φ.map_comp`, `Φ.map_add`, `Φ.map_zero` and bilinearity of composition. The ring is the opposite ring because `b * a = a ≫ b` in `End X`.
- `endPrecompModule_smul` (by `rfl`) unfolds the action.

### The adjunction transport

- `inducedEndEquiv adj T X : (Ind.obj X ⟶ Ind.obj X) ≃+ ((Ind ⋙ Res ⋙ T).obj X ⟶ T.obj X)` is an additive equivalence, the composite of two equivalences:
  - the inverse of Mathlib's `Adjunction.homAddEquiv` at `(Ind.obj X, X)`, which sends `x` to `(adj.homEquiv _ _).symm x : Res.obj (Ind.obj X) ⟶ X`;
  - `T.map`, which is a bijection by `Functor.FullyFaithful.ofFullyFaithful T` and additive by `T.map_add`.
- `inducedEndEquiv_apply` (by `rfl`): `inducedEndEquiv adj T X x = T.map ((adj.homEquiv _ _).symm x)`.
- `inducedEndEquiv_map_comp`: `inducedEndEquiv (Ind.map a ≫ x) = (Ind ⋙ Res ⋙ T).map a ≫ inducedEndEquiv x`. The proof rewrites with `Adjunction.homEquiv_naturality_left_symm`, which gives `(adj.homEquiv _ _).symm (Ind.map a ≫ x) = Res.map (Ind.map a) ≫ (adj.homEquiv _ _).symm x`, and then with `T.map_comp`.
- `inducedEndLinearEquiv adj T X` is `inducedEndEquiv` as an `(End X)ᵐᵒᵖ`-linear equivalence. The source carries `endPrecompModule Ind X (Ind.obj X)` and the target carries `precompModule (Ind ⋙ Res ⋙ T) X (T.obj X)`. Linearity is `inducedEndEquiv_map_comp`.

### The basis

Let `s : RepFunctorFiltration (Ind ⋙ Res ⋙ T) n` be a natural filtration. The remaining arguments are the hypotheses of `homVanishingBasis` for this filtration, the object `X` and the target `T.obj X`:
- `hsec`: every graded projection `s.gradedProjection X k` has a section;
- `θ j : (s.graded j).obj X ⟶ T.obj X` is a family of maps out of the graded pieces;
- `S : Finset (Fin n)` is a set of steps;
- `hθ`: for `j ∈ S`, the map `a ↦ (s.graded j).map a ≫ θ j` from `X ⟶ X` is bijective;
- `hzero`: for `j ∉ S`, every map `(s.graded j).obj X ⟶ T.obj X` is zero.

The declarations are:
- `inducedEndBasis adj T s X hsec θ S hθ hzero : Module.Basis S (End X)ᵐᵒᵖ (Ind.obj X ⟶ Ind.obj X)`, for the action `op a • x = Ind.map a ≫ x`. This is the main definition of the file. It is `homVanishingBasis …` mapped along the inverse of `inducedEndLinearEquiv` with `Module.Basis.map`.
- `inducedEndEquiv_inducedEndBasis`: the transport of the basis vector at `j : S` is the vector of `homVanishingBasis` at `j`. It is `LinearEquiv.apply_symm_apply`.
- `existsUnique_inducedEnd_expansion` restates the basis property without the module structure. Every `x : Ind.obj X ⟶ Ind.obj X` equals `∑_{j : S} Ind.map (a j) ≫ inducedEndBasis … j` for exactly one family `a : S → (X ⟶ X)`. The proof is the same as for `existsUnique_precomp_expansion`:
  - existence takes `a j = (b.equivFun x j).unop` and uses `Module.Basis.equivFun_symm_apply` and `LinearEquiv.symm_apply_apply`;
  - uniqueness applies `b.equivFun` to `b.equivFun.symm (op ∘ a) = x`.

## Hypotheses not proved here

The assumptions `hsec`, `hθ` and `hzero` are not proved in this file. In the planned application, `s` is the natural geometric-lemma filtration of `r_P ∘ i_P`, and:
- `hsec` comes from projectivity of the graded pieces at `Π_D`;
- `hθ` comes from the full pieces being twists of `Π_D` by Weyl elements that fix its class;
- `hzero` comes from the vanishing of the other pieces.

The instance argument `[Res.Additive]` could be derived from `[Ind.Additive]` by `Adjunction.left_adjoint_additive`. It is kept as an argument because `Adjunction.homAddEquiv` and the precomposition module on `Ind ⋙ Res ⋙ T` need it as an instance.
