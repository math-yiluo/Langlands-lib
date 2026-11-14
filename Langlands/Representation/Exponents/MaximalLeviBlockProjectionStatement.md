# Renard VII.1.3, Corollary (ii)–(iii): the functor `r_D` (statement)

Module `Langlands.Representation.Exponents.MaximalLeviBlockProjectionStatement`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters: `u` (the
field and the group schemes) and `v` (the representation spaces; the carriers live in
`Type (max u v)`).

The module contains one `Prop`-valued definition,
`MaximalLeviBlockProjectionEquivalenceStatement`. It proves nothing and defines no new
objects.

Worker 4 wrote this unit under the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`.
It addresses gap 2 of the Chapter VII item ledger (`notes/renard/item-ledger-vii.md`, row
"VII.1.3 Corollary (i)–(iii)"): "the functor `r_D`, its faithfulness as stated by the
source, and the unit isomorphism `π → i_P^G r_D(π)`". Worker 6's published
`MaximalLeviBlockStatements` (module `Langlands.Representation.Exponents.MaximalLeviBlockStatements`)
states parts (i)–(iii) of the Corollary without naming `r_D`. Its correspondence note 4
says that `r_D` was not named because no projection onto `M(M)_D` exists in the Library. This unit names `r_D`. It
characterizes the projection by its universal property (a left adjoint of the inclusion of
`M(M)_D`), asserts that such a projection exists, and then states the claims of (ii) and
(iii) about `r_D`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF page numbers are
one-based and equal printed page numbers plus six. The author read PDF pp.150–151 and
232–233.

- VII.1.3, Corollary, printed p.226 / PDF p.232:

  > **Corollaire.** Soit `P = MN`, avec `M` sous-groupe de Levi maximal de `G`. Posons
  > `W(M, ∗) = {1, w}` et soit `D` une classe d'inertie de représentations supercuspidales
  > de `M` telle que `w · D ≠ D` (c'est le cas par exemple si `w · M ≠ M`). Soit `Ω` la
  > composante connexe de `Ω(G)` associée à `(M, D)`. Alors
  > […]
  > (ii) Soit `r_D` la composition du foncteur `r_P^G` et de la projection sur `M(M)_D`.
  > Alors `r_D` est un foncteur fidèle de `M(G)_Ω` vers `M(M)_D`.
  > (iii) Pour toute représentation `(π, V)` dans `M(G)_Ω`, le morphisme naturel
  > `π → i_P^G r_D(π)` est un isomorphisme. Le foncteur `r_D : M(G)_Ω → M(M)_D` est une
  > équivalence de catégories dont l'inverse est `i_P^G`.

- The proof of the Corollary, printed pp.226–227 / PDF pp.232–233, identifies the natural
  morphism as an adjunction morphism:

  > Le foncteur `i_P^G : M(M)_D → M(G)_Ω` est l'adjoint à droite de
  > `r_D : M(G)_Ω → M(M)_D`. Le morphisme d'adjonction (voir A.V)
  > `α_π : π → i_P^G r_D(π)` est injectif d'après le lemme VI.7.2 (iii).

  It ends: "Les morphismes d'adjonctions `α` et `β` sont donc respectivement des
  isomorphismes naturels entre l'identité de `M(G)_Ω` et `i_P^G ∘ r_D` et entre
  `r_D ∘ i_P^G` et l'identité de `M(M)_D`. Ceci montre l'équivalence de catégories."

- VI.3.3, printed p.145 / PDF p.151, the decomposition behind "la projection sur
  `M(M)_D`": for an irreducible supercuspidal `π`, every smooth `W` splits as
  `W = ρ(e_[π]) · W ⊕ (1 − ρ(e_[π])) · W`. With `M(G)_[π]` (resp. `M(G) \ [π]`) the full
  subcategory of the representations all (resp. none) of whose irreducible subquotients are
  in `[π]`, "on obtient une décomposition de `M(G)` en
  (VI.3.3.1) `M(G) = M(G)_[π] × (M(G) \ [π])`." The Corollary applies this to `M` and the
  class `D`.

## The statement

**`MaximalLeviBlockProjectionEquivalenceStatement`.** The binders, the hypotheses and the
three `let`s `IsTwist`, `InBlockM` and `InBlockG` are copied word for word from the
published `MaximalLeviBlockStatements`, whose Markdown explains them:

- `k : Type u` is a nonarchimedean local field and `G` a connected reductive group scheme
  over `Spec k`, with the canonical topology on `G(F)`, assumed locally compact and
  nonarchimedean;
- `p : P ⟶ G` is an actual proper (`¬ IsIso p`) and maximal rational parabolic with
  rational Levi `l : M ⟶ P`, matching unipotent radical `r : U ⟶ P` and `hmul`. `M(F)`
  carries `leviPointTopology l hl` and the derived instances;
- `ρ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)` is irreducible and supercuspidal
  (every normalized Jacquet module along an actual proper parabolic of `M` is zero), and
  its inertial class `D` is not fixed by the nontrivial element of `W(M, ∗)`;
- `IsTwist σ`: `σ ≃ ρ ⊗ ψ` for an unramified character `ψ`, so the members of `D` are the
  representations with `IsTwist`;
- `InBlockM X`: every irreducible subquotient of `X` satisfies `IsTwist`. This is
  `M(M)_D`, the factor `M(M)_[ρ]` of VI.3.3.1 applied to `M`;
- `InBlockG Y`: every irreducible subquotient of `Y` is a subquotient of `i_P^G σ` for some
  `σ` with `IsTwist σ`. This is `M(G)_Ω` (correspondence note 2 of the published
  Markdown).

Write `r_P^G := leviJacquetFunctor p l r hp hr hl hmul` and
`i_P^G := leviInductionFunctor p l r hp hr hl hmul`. These are the published normalized Jacquet and induction functors between smooth
representations of `M(F)` and of `G(F)`. The conclusion is the conjunction of:

- **(a)** `InBlockM.ι.IsRightAdjoint`: the inclusion of `M(M)_D` into the smooth
  representations of `M(F)` has a left adjoint, that is, the projection onto `M(M)_D`
  exists;
- **(b)** for every functor `L : SmoothRep ℂ (rationalPoints M) ⥤ InBlockM.FullSubcategory`
  with an adjunction `adjL : L ⊣ InBlockM.ι`, put
  `r_D := InBlockG.ι ⋙ r_P^G ⋙ L : InBlockG.FullSubcategory ⥤ InBlockM.FullSubcategory`.
  Let `adj := (leviFirstAdjointnessAdjunction p l r hp hl hr hmul).comp adjL` be the composite of the published
  Frobenius reciprocity `r_P^G ⊣ i_P^G` with `adjL`. It is an adjunction
  `r_P^G ⋙ L ⊣ InBlockM.ι ⋙ i_P^G`. Then:
  - (ii) `r_D.Faithful`;
  - (iii) for every object `Y` of `InBlockG.FullSubcategory`, the morphism
    `adj.unit.app Y.obj : Y.obj ⟶ i_P^G (r_D Y)` is an isomorphism of smooth
    representations of `G(F)`; and
  - (iii) there is an equivalence `E : InBlockG.FullSubcategory ≌ InBlockM.FullSubcategory`
    with `E.functor = r_D` and a natural isomorphism
    `E.inverse ⋙ InBlockG.ι ≅ InBlockM.ι ⋙ i_P^G`.

## Formalization choices and correspondence notes

1. **The projection onto `M(M)_D` as a left adjoint.** Under the decomposition (VI.3.3.1)
   `M(M) = M(M)_D × (M(M) \ D)`, write `W = W_D ⊕ W'` with `W_D` in `M(M)_D` and no
   irreducible subquotient of `W'` in `D`. The projection `W ↦ W_D` with the map
   `W → W_D` is a left adjoint of the inclusion: for `Y` in `M(M)_D`,
   `Hom(W, Y) = Hom(W_D, Y) ⊕ Hom(W', Y) = Hom(W_D, Y)`, because morphisms between the
   two factors vanish. A left adjoint of a fully faithful functor is unique up to unique
   isomorphism, so every pair `(L, adjL)` is the source's projection up to a unique natural
   isomorphism. Clauses (ii) and (iii) are invariant under such isomorphisms. The statement
   therefore quantifies over all of them, and needs neither a chosen splitting nor the
   central idempotent `e_[ρ]`. Clause (a) asserts that a projection exists. Without (a), (b) would hold vacuously.
2. **`r_D` and the natural morphism.** `r_D` is literally "la composition du foncteur
   `r_P^G` et de la projection sur `M(M)_D`", restricted to `M(G)_Ω`. The source calls the
   natural morphism `π → i_P^G r_D(π)` the adjunction morphism `α_π` of
   `r_D ⊣ i_P^G : M(M)_D → M(G)_Ω`. That adjunction is the composite of Frobenius
   reciprocity with the adjunction of the projection: for `π` in `M(G)_Ω` and `τ` in
   `M(M)_D`,
   `Hom_{M(M)_D}(L r_P^G π, τ) = Hom_M(r_P^G π, τ) = Hom_G(π, i_P^G τ)`.
   Its unit at `π` is `adj.unit.app π`, which by `Adjunction.comp` equals the unit of
   Frobenius reciprocity at `π` followed by `i_P^G` applied to the unit of `adjL` at
   `r_P^G π`. The categories `M(G)_Ω` and `M(M)_D` are full subcategories, so the unit is
   stated as a morphism of smooth representations of `G(F)`. An isomorphism there is the
   same as an isomorphism in `InBlockG.FullSubcategory`.
3. **The equivalence and its inverse.** "`r_D` est une équivalence de catégories dont
   l'inverse est `i_P^G`" is the existence of an equivalence `E` whose functor is `r_D`
   (a functor is the functor of some equivalence exactly when it is an equivalence),
   together with `E.inverse ⋙ InBlockG.ι ≅ InBlockM.ι ⋙ i_P^G`. The latter says that
   the inverse is `i_P^G` on `M(M)_D`, viewed in all smooth representations of `G(F)`.
   The statement does not repeat that `i_P^G` maps `M(M)_D` into `M(G)_Ω`. That is part
   (iii) of the published `MaximalLeviBlockStatements`. It also follows from the
   isomorphism, because isomorphic representations have the same irreducible
   subquotients.
4. **Faithfulness is stated separately.** Clause (ii) follows from the equivalence in
   (iii). It is kept because the source states it as a separate claim and proves it first.
5. **Relation to the published statement.** The published `MaximalLeviBlockStatements`
   states (ii) as a nonvanishing criterion and (iii) through `InBlockM.ι ⋙ i_P^G` (full,
   faithful, essentially surjective onto `InBlockG`). Its correspondence notes 4 and 5
   record that `r_D` and the unit isomorphism were not stated. This unit states exactly
   these missing claims. It reuses the same setting and encodings, so the published
   discussion of `w · D ≠ D`, of `M(M)_D` and of `M(G)_Ω` applies unchanged.
6. **Universes.** As in the published statement, all smooth representations have carriers
   in `Type (max u v)`. The adjunction is the published
   `leviFirstAdjointnessAdjunction.{u, v}`, between `leviJacquetFunctor.{u, max u v}` and
   `leviInductionFunctor.{u, max u v}`. Induction does not enlarge the universe
   `max u v`.

## Expected proof route

Not proved here; this is for the proof task.

- **(b) from the published part (iii).** Let `I : InBlockM.FullSubcategory ⥤
  InBlockG.FullSubcategory` be the lift of `InBlockM.ι ⋙ i_P^G`
  (`ObjectProperty.lift`), using the first conjunct of part (iii) of
  `MaximalLeviBlockStatements`. The published conjuncts give that `I` is full, faithful
  and essentially surjective, hence an equivalence. Restricting `adj` along the fully
  faithful `InBlockG.ι` gives an adjunction `r_D ⊣ I` whose unit at `Y` has underlying
  morphism `adj.unit.app Y.obj`. By `Adjunction.isEquivalence_left_of_isEquivalence_right`,
  `r_D` is an equivalence. Hence `r_D` is faithful and full, and the unit of `r_D ⊣ I` is
  an isomorphism (`Adjunction.unit_isIso_of_L_fully_faithful`); applying `InBlockG.ι`
  gives (iii) for the unit. Take `E := r_D.asEquivalence`. Uniqueness of right adjoints
  gives `E.inverse ≅ I`, and `I ⋙ InBlockG.ι = InBlockM.ι ⋙ i_P^G`. So (b) needs no input
  beyond the published `MaximalLeviBlockStatements`, which is not yet proved.
- **(a) from VI.3.3.1 for `M`.** Apply the published, unproved
  `CuspidalSupport.RationalCuspidalInertiaDecompositionStatement` to the connected reductive
  group `M` (`hl.isConnectedReductive`), with a maximal split torus of `M`, a generic
  cocharacter and the other structural inputs it takes. Transport the supercuspidality of
  `ρ` from the represented form in the hypothesis to the standard form `IsCuspidal` it
  requires: the published `isCuspidal_of_all_represented_parabolics_of_standardCocharacter`
  goes in this direction. Then identify `InBlockM` with the published
  `rationalInertiaBlockProperty M ρ`. Both say that every irreducible subquotient is an
  unramified twist of `ρ`; the two encodings of unramified characters
  (`Plancherel.unramifiedCharacters` of the norm characters, and the character group used
  by `IsRationalInertiaRelated`) must be compared. Finally, the published
  `exists_rationalInertiaBlockProjection` gives, for every `W`, maps `p : W ⟶ τ` and
  `j : τ ⟶ W` with `τ` in the block and `f ≫ p ≫ j = f` for every `f` from a block
  object. With the vanishing of morphisms between the two factors, `p` is a universal
  arrow from `W` to the inclusion. These universal arrows give the left adjoint.

## Relation to published work

At Library commit `4f6abf4c`:

- `MaximalLeviBlockStatements` (Worker 6) states VII.1.3 Corollary (i)–(iii) without
  `r_D`. Its reduction module `MaximalLeviBlockReductionStatements` reduces it to the
  VII.1.3 Theorem and further inputs. Neither is proved;
- `leviFirstAdjointnessAdjunction` (module
  `Langlands.Representation.Exponents.LeviInductionDualityAdjunction`) is the published
  first adjointness `r_P^G ⊣ i_P^G` on the Levi points, used here to form `adj`;
- `CuspidalSupport.RationalCuspidalInertiaDecompositionStatement` states VI.3.3.1 as an
  actual category decomposition, `IsRationalInertiaCategoryDecomposition`; it is not
  proved.

No theorem of the Library proves this statement or any part of it.

## Provenance

Derived from Renard VII.1.3, Corollary (ii)–(iii), and its proof, for the
represented-parabolic interface of the published `MaximalLeviBlockStatements`. The
characterization of the projection onto `M(M)_D` by a left adjoint of the inclusion is a
formalization choice explained in note 1, justified by VI.3.3.1. Clause (a) makes explicit the existence of
the projection, which the source takes from VI.3.3.1.
