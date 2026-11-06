# The category of smooth representations is Noetherian

Author: Worker 6. Module `Langlands.Representation.Exponents.SmoothRepNoetherianCategoryStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `SmoothRepNoetherianCategoryStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.7.5 "Noethérianité de M(G)", printed p.186 / PDF p.192. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation:

- Definition (VI.7.5, opening paragraph): an object of an abelian category is Noetherian if every increasing sequence of subobjects is stationary (cf. Appendix A.I.2). An abelian category in which every object of finite type is Noetherian is called Noetherian.
- **Proposition.** The category `M(G)` is Noetherian.

The Theorem of VI.7.5 (`i_P^G` preserves finite type) is the separate statement `LeviInductionFiniteTypeStatement` in this namespace.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then asserts

`Langlands.Renard.IsNoetherianCategory (SmoothRep.{0, u, v} ℂ (rationalPoints G))`

for an arbitrary carrier universe `v`.

## The objects

- `Langlands.Renard.IsNoetherianCategory C` (published `Langlands.CategoryTheory.RenardFiniteType`, Appendix A.I.2–A.I.3, printed pp.248–249) is the conjunction of two conditions. The first is `HasAllSubobjectUnions C`: every set of subobjects of every object has a least upper bound in the categorical subobject order. The second is that every `X` with `IsFiniteTypeObject X` satisfies `IsNoetherianObject X`.
  - `IsNoetherianObject X` is the definition of A.I.3: every nonempty set of subobjects of `X` has a maximal element.
  - `IsFiniteTypeObject X` is the definition of A.I.3: unions exist, and the union of a nonempty chain of proper subobjects is proper.
- `SmoothRep.{0, u, v} ℂ (rationalPoints G)` is the published category of smooth complex representations of `G(F)` with carriers in universe `v`; this is Renard's `M(G)`. The published `Langlands.SmoothRep.renardFiniteType_iff` (module `Langlands.Representation.Category.RenardFinitenessProof`) proves that `IsFiniteTypeObject A` holds exactly when the carrier of `A` is finitely generated over the group algebra `ℂ[G(F)]`. This is the notion of finite type used by `LeviInductionFiniteTypeStatement` and by the published VI.1.3 statement `LeviJacquetFiniteTypeStatement`.

## Faithfulness notes

- Noetherian objects. VI.7.5 recalls the ascending-chain form ("every increasing sequence of subobjects is stationary") and refers to the Appendix. A.I.3 defines a Noetherian object by the maximal-element condition, says that the two forms are equivalent, and says that in practice increasing sequences suffice. The Library definition `IsNoetherianObject` is the maximal-element form of A.I.3. The equivalence with the ascending-chain form is not asserted here.
- Unions. A.I.3 assumes that the category has arbitrary unions before defining objects of finite type. `IsNoetherianCategory` includes this as the conjunct `HasAllSubobjectUnions`. For smooth representations it holds because subobjects correspond to subrepresentations. It is part of what the statement asserts, not a hypothesis.
- Scope. The statement covers every connected reductive `G`, so it applies to every Levi `M` of a rational parabolic, which is connected reductive by `hl.isConnectedReductive`. The canonical topology `leviPointTopology l hl` on `rationalPoints M` used by the published Levi functors is by definition `RationalPointFamily.pointTopology`. So the statement for `M` concerns the same category as the source of `leviInductionFunctor`, as the proof of the Theorem of VI.7.5 requires.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses.

## Remaining obligations

The proof is a separate obligation. The source argument uses:

- the Corollary of VI.4.4: each supercuspidal block `M(G)_[ρ]` is equivalent to the category of unital right modules over a Noetherian `ℂ`-algebra, hence is Noetherian;
- the decomposition of VI.3.5 of `M(M)_sc` over the inertia classes `D` of supercuspidal representations of `M`, and the fact that a finite-type object of the product over `(M, D)` has finitely many nonzero components, so that the product is Noetherian;
- the functor `R : M(G) → Cusp(G)` of VI.7.2, its faithfulness and exactness, and finite type of `R(V)` for `V` of finite type (VI.1.3).

Related published statements, none of which is asserted here: `LeviJacquetFiniteTypeStatement` (VI.1.3) in this namespace; `Langlands.Renard.ModuleNoetherian.ModuleNoetherianStatement` (categorical and algebraic Noetherianity agree for modules, A.I.3); and, on the standard rational-point family rather than the represented-parabolic interface, `Langlands.Aubert.General.RationalPointFamily.RationalSupportCategoryDecompositionStatement` (the decomposition of VI.7.2).

## Provenance

This is a source statement of the Proposition of VI.7.5. It uses the Library's encoding of Renard's own definitions from Appendix A.I.2–A.I.3, applied to the published category of smooth representations of the rational points of an actual connected reductive group.
