# Abelian-scheme lifts from smooth proper pointed lifts

Module `Langlands.AbelianScheme.AbelianArtinianLiftingReduction`, namespace
`Langlands.AbelianScheme`.

## Declarations

- `GroupScheme.identitySection_baseChange_fst t G`: for a morphism `t : T ⟶ S` and a group scheme `G`
  over `S`, the identity section of `(GroupScheme.baseChange t).obj G`, followed by the
  projection `pullback.fst G.X.hom t`, equals `t ≫ η[G.X].left`. The identity section of
  the base change is `ε ≫ (Over.pullback t).map η[G.X]` (Mathlib's `Functor.obj.η_def`
  for the monoidal functor `Over.pullback t`). Mathlib's `Over.ε_pullback_left`
  identifies `ε.left` with the inverse of `pullback.snd (𝟙 S) t`, and the pullback square
  of `𝟙 S` and `t` finishes the computation.
- `isoOfPointedIso F hF`: an isomorphism `F : A.X ≅ B.X` in `Over S` between the
  underlying schemes of two abelian schemes over an arbitrary scheme `S` that carries
  `η[A.X]` to `η[B.X]` gives an isomorphism `A ≅ B` of abelian schemes. The published
  theorem `pointedMorphismRigidity` (module
  `Langlands.AbelianScheme.PointedMorphismRigidityProof`) shows that `F.hom` preserves
  multiplication. Its hypotheses hold because `A` is smooth, proper and geometrically
  connected (`AbelianScheme.isAbelian`) and `B` is smooth, quasi-compact and separated
  over `S`. Mathlib's `Grp.mkIso` then gives an isomorphism of group objects, which is an
  isomorphism in the category `AbelianScheme S`.
- `abelianArtinianLifting_of_smoothLifting hS hP`: the implication

  ```text
  AbelianSmoothArtinianLiftingStatement.{u} →
    PointedAbelianArtinianLiftingStatement.{u} →
      AbelianArtinianLiftingStatement.{u}
  ```

## Proof of `abelianArtinianLifting_of_smoothLifting`

Fix `φ : R' →+* R` as in `AbelianArtinianLiftingStatement`, put
`t := Spec.map (CommRingCat.ofHom φ)`, and let `B` be an abelian scheme over `Spec R`.

1. `hS` gives a smooth proper `p : X ⟶ Spec R'` with a section `s`, and an isomorphism
   `e₀ : B.X.left ≅ pullback p t` over `Spec R` carrying the identity section of `B` to
   the section induced by `s`.
2. This is exactly the hypothesis of `PointedAbelianArtinianLiftingStatement` for the
   same `φ`, `X`, `p`, `s` and the abelian scheme `B`. So `hP` gives an abelian scheme
   `A` over `Spec R'` and an isomorphism `e : A.X.left ≅ X` over `Spec R'` with
   `η[A.X].left ≫ e.hom = s`.
3. The base change `(baseChange t).obj A` has underlying scheme `pullback A.X.hom t`.
   The morphism `m := pullback.map A.X.hom t p t e.hom (𝟙 _) (𝟙 _)` is an isomorphism
   onto `pullback p t` (Mathlib's `pullback.map_isIso`), and `m ≫ e₀.inv` is an
   isomorphism over `Spec R` onto `B.X.left`, because `m` commutes with the second
   projections and `e₀.hom ≫ pullback.snd p t = B.X.hom`.
4. It preserves identity sections. After composing with `e₀.hom` it suffices to compare
   both projections of `pullback p t`. On the first, `GroupScheme.identitySection_baseChange_fst` and
   `η[A.X].left ≫ e.hom = s` give `t ≫ s`, which is also the image of the identity
   section of `B` by step 1. On the second, both identity sections are sections of the
   structure morphisms.
5. `isoOfPointedIso` turns this pointed isomorphism into an isomorphism of abelian
   schemes `(baseChange t).obj A ≅ B`, which is the conclusion of
   `AbelianArtinianLiftingStatement`.

## Provenance

The reduction follows Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura
varieties*, Harvard thesis revised 14 March 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`: the proof of
Proposition 2.2.4.1 (printed pp. 152–154) obtains a lift of the abelian scheme from a
lift of its underlying scheme through Propositions 2.2.2.3 and 2.2.2.5 (printed
pp. 144–145). The isomorphism of reductions over \(\operatorname{Spec}R\) preserves
identity sections, and a morphism of an abelian scheme to a separated group scheme
of finite presentation over the same base that preserves identity sections is a
homomorphism: Lan's Corollary 1.3.1.6 (printed pp. 70–71). The Library theorem
`pointedMorphismRigidity` extends Lan's corollary to target group schemes of finite
presentation, including nonseparated targets (its diagonal hypothesis is
quasi-separatedness). The target in `isoOfPointedIso` is an abelian scheme over
\(\operatorname{Spec}R\) and hence separated, so this application also lies within Lan's
hypotheses; `isoOfPointedIso` applies the theorem directly over
\(\operatorname{Spec}R\). (Lan's
Corollary 2.2.2.2, printed p. 144, uses the same rigidity principle for a different
purpose: it translates a morphism over the thicker base to normalize a lift of a
group homomorphism.) The Lean proof is an assembly of the two
propositions with the published rigidity theorem; it adds no other mathematical input.
