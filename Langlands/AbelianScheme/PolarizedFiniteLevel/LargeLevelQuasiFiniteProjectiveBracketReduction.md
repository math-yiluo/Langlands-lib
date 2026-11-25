# Locally quasi-finite maps to projective space from torsion bracket maps

The module
`Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelQuasiFiniteProjectiveBracketReduction`
proves four general lemmas about schemes, one lemma about representing level
bases, and one proved definition. None of them has hypotheses beyond its
displayed arguments.

## General lemmas (namespace `Langlands.AlgebraicGeometry`)

- `finite_of_jacobsonSpace_of_finite_closedPoints`. A Jacobson topological space
  with finitely many closed points is finite.

  *Proof.* In a Jacobson space the closed points are dense
  (`closure_closedPoints`). A finite union of closed singletons is closed, so the
  set of closed points is closed and hence is everything.
- `exists_geometricPoint_of_mem_closedPoints`. Let `f : X ⟶ Y` be locally of
  finite type, `y ∈ Y`, and `z` a closed point of the scheme-theoretic fibre
  `f.fiber y`. Let `κ̄` be the algebraic closure of the residue field `κ(y)`. Then
  there is `t : Spec κ̄ ⟶ X` with `t ≫ f = Spec κ̄ → Spec κ(y) → Y` whose closed
  point maps to the image `f.fiberι y z` of `z` in `X`.

  *Proof.* Since `z` is closed, `Spec κ(z) → f.fiber y` is a closed immersion
  (`isClosed_singleton_iff_isClosedImmersion`). The fibre is locally of finite
  type over `Spec κ(y)`, so the composite `Spec κ(z) → Spec κ(y)` is locally of
  finite type. Its target is a Jacobson space, so it is finite
  (`isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`). Thus `κ(z)` is a finite
  extension of `κ(y)`. It embeds into `κ̄` over `κ(y)` (`IsAlgClosed.lift`), and
  `t` is `Spec κ̄ → Spec κ(z) → f.fiber y → X`. This lemma sets the Lean option
  `backward.isDefEq.respectTransparency.types false`.
- `finite_preimage_singleton_of_finite_geometricFibres`. Let `f : X ⟶ Y` be locally
  of finite type between schemes in universe `u`. Assume that for every
  algebraically closed field `K : Type u` and every `y : Spec K ⟶ Y` the set of
  `x : Spec K ⟶ X` with `x ≫ f = y` is finite. Then every set-theoretic fibre
  `f ⁻¹' {y}` is finite.

  *Proof.* Apply the hypothesis to `Spec κ̄ → Spec κ(y) → Y`. Sending each closed
  point `z` of `f.fiber y` to the geometric point `t` of the previous lemma is
  injective, because `t` determines the image of `z` in `X` and `f.fiberι y` is
  an embedding. So the fibre has finitely many closed points. It is locally of
  finite type over a field, hence a Jacobson space, so it is finite by the first
  lemma. Its image is `f ⁻¹' {y}` (`Scheme.Hom.range_fiberι`).
- `locallyQuasiFinite_of_finite_geometricFibres`. Under the same hypotheses `f`
  is locally quasi-finite. This follows from the previous lemma and Mathlib's
  `LocallyQuasiFinite.of_finite_preimage_singleton`.

## A lemma on representing level bases

`eq_of_isomorphic_pullback`. Let `P : Prerequisites.{0}`, `0 < d`, `3 ≤ n`, and
let `X : LevelBase n` represent the moduli functor through
`e : uliftYoneda.{1}.obj X ≅ moduliFunctor P g d n hd hn`. Let `b` be a datum
over `X.obj` whose class is the universal class
`e.hom.app (op X) ⟨𝟙 X⟩`. Let `K : Type` be a field and
`t t' : Spec K ⟶ X.obj`. If the pullbacks `b.pullback t` and `b.pullback t'` are
isomorphic, then `t = t'`.

*Proof.* `Spec K` is noetherian and `n` is a unit on it, because `n` is a unit on
`X.obj`. So `Spec K` is a level base `T_K` (`LevelBase.ofScheme`), and `t` and
`t'` are morphisms of level bases. By naturality of `e.hom` and the published
`moduliFunctor_map_classOf`, `e.hom` sends `t` to the class of `b.pullback t`,
and similarly for `t'`. The two classes are equal by hypothesis. The component
of the isomorphism `e.hom` at `T_K` is injective, so `t = t'`.

## The reduction

`Langlands.AbelianScheme.PolarizedFiniteLevel.largeLevelQuasiFiniteProjective_of_torsionBrackets`
is a proved definition of type

`LargeLevelFiniteTypeStatement → TorsionBracketMapStatement →
TorsionConfigurationDeterminationStatement.{0} →
LargeLevelQuasiFiniteProjectiveStatement`.

`LargeLevelFiniteTypeStatement` and `LargeLevelQuasiFiniteProjectiveStatement`
are published statements toward eventual quasi-projectivity of the fine moduli
schemes, in the modules of the same names. `TorsionBracketMapStatement` and
`TorsionConfigurationDeterminationStatement` are companion statements, in the
modules of the same names. The definition is an internal derivation. It makes
no mathematical claim beyond those of its three premises.

### The proof

Fix `P`, `g`, `d` with `0 < g` and `0 < d`. The three premises give bounds `N₁`,
`N₂`, `N₃`, and the bound is `max N₁ (max N₂ N₃)`. Let `n` be at least this bound
with `3 ≤ n`, and let `X : LevelBase n` represent the moduli functor through `e`.

1. `LargeLevelFiniteTypeStatement` shows that `X.toLocalizationSpec` is locally
   of finite type.
2. Choose a datum `b` over `X.obj` representing the universal class
   `e.hom.app (op X) ⟨𝟙 X⟩` (`Quotient.exists_rep`).
   `TorsionBracketMapStatement`, applied to `X` and `b`, gives `m` and
   `j : X.obj ⟶ ProjectiveSpace ℤ[1/n] m`. Then
   `j ≫ projectiveSpaceToSpec ℤ[1/n] m = X.toLocalizationSpec`, by
   `LevelBase.eq_toLocalizationSpec`. This is the second requirement of the
   target.
3. The composite `j ≫ projectiveSpaceToSpec` is locally of finite type by step 1,
   so `j` is locally of finite type (`locallyOfFiniteType_of_comp`).
4. By `locallyQuasiFinite_of_finite_geometricFibres`, it remains to show that
   for every algebraically closed `K : Type` and `y : Spec K ⟶ ProjectiveSpace`,
   the `K`-points `t` of `X.obj` with `t ≫ j = y` form a finite set.
   `TorsionBracketMapStatement` gives a finite set `s` such that each such `t`
   is configuration-equivalent, after pulling back `b`, to `b.pullback t'` for
   some `t' ∈ s`. The characteristic of `K` does not divide `n`, because `n` is a
   unit on `X.obj` and hence in `K`. So
   `TorsionConfigurationDeterminationStatement` makes `b.pullback t` and
   `b.pullback t'` isomorphic, and `eq_of_isomorphic_pullback` gives `t = t'`.
   Hence the set of such `t` is contained in `s`.

## Relation to the earlier intended proof

The `LargeLevelQuasiFiniteProjectiveStatement` Markdown sketches a route
through balanced bracket monomials and GIT stability. This reduction follows a
different route. It replaces balanced monomials by `n`-th powers of single
brackets (see the intended proof in `TorsionBracketMapStatement.md`), and it
replaces the stability analysis by the determination statement.
