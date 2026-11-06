# Properness of a smooth scheme embedded in a proper scheme, from its field fibres

Module `Langlands.AlgebraicGeometry.ProperOfFibres.Criterion`, namespace
`Langlands.AlgebraicGeometry.ProperOfFibres`. This is the global step of the properness
criterion used for relative parabolic quotients: over an arbitrary base scheme `S`, a
smooth, separated, quasi-compact `S`-scheme that is a monomorphic subscheme of a proper
`S`-scheme of finite presentation is proper as soon as all of its field fibres are proper
and connected. Compare Conrad, *Reductive group schemes* (2014), proof of Theorem 2.3.6(2)
(pp. 73–75), which deduces properness of `G/H` from proper, geometrically connected fibres
by a general fact that Conrad notes is a special case of EGA IV₃ 15.7.10. The statements are
internal helpers for the relative parabolic quotient proof; the proofs below are the
implemented Lean proofs, which use the valuative criterion of Mathlib together with
`isProper_of_isLocalRing` (module `ValuationCore`) instead of the arguments in the
literature.

## Helper lemmas

- `mono_pullbackMap`: if `j : X ⟶ Y` is a monomorphism with `j ≫ g = f` for
  `f : X ⟶ S`, `g : Y ⟶ S`, then for every `t : T ⟶ S` the induced map
  `pullback.map f t g t j (𝟙 _) (𝟙 _) _ _ : X ×_S T ⟶ Y ×_S T` is a monomorphism. Proof:
  two maps into `X ×_S T` with equal composites to `Y ×_S T` have equal second
  projections, and equal first projections after composing with `j`; cancel the
  monomorphism `j` and use `pullback.hom_ext`.
- `isProper_pullback_snd_pullback_snd`: for `f : X ⟶ S`, `t : T ⟶ S`, a field `k` and
  `φ : Spec k ⟶ T`, if `pullback.snd f (φ ≫ t)` is proper then so is
  `pullback.snd (pullback.snd f t) φ`. Proof: the two morphisms agree up to the
  isomorphism `pullbackLeftPullbackSndIso f t φ` (`pullbackLeftPullbackSndIso_hom_snd`),
  and properness is stable under composition with isomorphisms. (The lemma holds for any
  `φ`; the field is only the case used.)

## Main theorem `isProper_of_fibres`

Hypotheses: `f : X ⟶ S` is smooth, separated and quasi-compact; `g : Y ⟶ S` is proper and
locally of finite presentation; `j : X ⟶ Y` is a monomorphism with `j ≫ g = f`; for every
field `k` (in the universe of `S`) and every `φ : Spec k ⟶ S`, the morphism
`pullback.snd f φ` is proper and the scheme `pullback f φ` is connected.
Conclusion: `f` is proper.

Proof as implemented:

1. The connectedness hypothesis says exactly that `f` is geometrically connected
   (`geometrically_iff_of_isClosedUnderIsomorphisms`).
2. Universal closedness is checked with the existence part of the valuative criterion
   (`UniversallyClosed.of_valuativeCriterion`, which uses that `f` is quasi-compact). Let a
   valuative square be given: a valuation ring `R` with fraction field `K`, a morphism
   `i₂ = t : Spec R ⟶ S` and `i₁ : Spec K ⟶ X` over `S`.
3. Base change along `t`: put `f' = pullback.snd f t`, `g' = pullback.snd g t` and
   `j' = pullback.map …` as in `mono_pullbackMap`, so `j'` is a monomorphism with
   `j' ≫ g' = f'`. Base change keeps `f'` smooth and quasi-compact and `g'` proper and
   locally of finite presentation, and `R` is an integrally closed local domain.
4. The generic fibre of `f'` (along `Spec K ⟶ Spec R`) and its closed fibre (along
   `Spec κ(R) ⟶ Spec R`) are proper by `isProper_pullback_snd_pullback_snd` and the fibre
   hypothesis at `Spec K ⟶ Spec R ⟶ S` and `Spec κ(R) ⟶ Spec R ⟶ S`. The generic fibre is
   geometrically connected because geometric connectedness is stable under base change
   (instance search). The closed fibre is nonempty, since it is isomorphic
   (`pullbackLeftPullbackSndIso`) to the fibre of `f` over `Spec κ(R) ⟶ S`, which is
   connected and hence nonempty.
5. `isProper_of_isLocalRing` (module `ValuationCore`) then shows that `f'` is proper. In
   particular `f'` is universally closed, so it satisfies the existence part of the
   valuative criterion (`UniversallyClosed.eq_valuativeCriterion`).
6. Apply that to the valuative square for `f'` with top map
   `pullback.lift i₁ (Spec K ⟶ Spec R) _` and bottom map `𝟙 (Spec R)`. This gives a lift
   `l : Spec R ⟶ X ×_S Spec R`, and `l ≫ pullback.fst f t` is the required lift for the
   original square. Its two triangles follow from `pullback.lift_fst`,
   `pullback.condition` and the two triangles of `l`.
7. With `f` separated, universally closed, and locally of finite type (from smoothness),
   `f` is proper.

## Corollaries

- `isProper_hom_of_fibres`: the same statement for a morphism `j : X ⟶ Y` in `Over S`,
  with the fibres written as `(Over.pullback φ).obj X`. It is `isProper_of_fibres` applied
  to `X.hom`, `Y.hom`, `j.left` and `Over.w j`; the fibre hypothesis has the same form,
  because `(Over.pullback φ).obj X` is the object `pullback.snd X.hom φ` of `Over (Spec k)`.
- `properAmbientCriterion`: the universally quantified form
  `∀ S (X Y : Over S) (j : X ⟶ Y), Smooth X.hom → IsSeparated X.hom → QuasiCompact X.hom →
  IsProper Y.hom → LocallyOfFinitePresentation Y.hom → Mono j.left → (fibre hypothesis) →
  IsProper X.hom`, with every hypothesis an explicit implication. It is
  `isProper_hom_of_fibres`, and its statement is the proposition used as the generic
  properness input by the relative parabolic quotient assembly.
