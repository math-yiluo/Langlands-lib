# Proof of the centre of the category of nondegenerate modules (Renard I.1.7, Theorem)

Author: Worker 142 (Lean proof and Markdown), under Task 5709
(`56b7aa00-3ccf-44fb-9c6d-7f84b98504bd`).

This module proves the published statement
`Langlands.Algebra.NondegenerateModuleCenterTheoremStatement` from
`Langlands.Algebra.NondegenerateModuleCenterStatements`. It changes nothing in the statement
module or in anything that module imports. The final theorem is

```
Langlands.Algebra.NondegenerateModuleCenterProof.nondegenerateModuleCenterTheorem :
  NondegenerateModuleCenterTheoremStatement.{uA, uM}
```

for arbitrary universes `uA` and `uM`. It adds no hypothesis: the only assumptions are those
inside the statement, an original `NonUnitalRing A` and `hA : IsIdempotented A`.
`lean_check` reports 0 errors, 0 warnings and the axioms `propext`, `Classical.choice` and
`Quot.sound`.

The unital Remark of I.1.7 is proved separately, in
[UnitalNondegenerateModuleCenterProof](UnitalNondegenerateModuleCenterProof.md).

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques` (SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), I.1.7, the paragraph
after the Lemma and the Theorem, printed pp.12–13 / PDF pp.18–19. The statement Markdown
quotes the passage. The Lean proof does not follow the source's route step by step. Instead it
reuses the published proof of the I.1.6 classification, as described below. The source says
only that the commutant equals the centre "par continuité"; the proof below replaces this with
an algebraic argument.

## Notation

- `Â = IdempotentedRingRightLimit A`, the compatible right families, with the ring
  `IdempotentedRingRightLimit.ring hA`. Its product is `IdempotentedRingRightLimit.product`,
  and `IdempotentedRingRightLimit.canonical a` is the image of `a : A`.
- `act M x m = IdempotentedRingRightLimitAction.act M.property x m`, the published action of
  `x ∈ Â` on a nondegenerate module `M`. If `e • m = m` it is `x(e) • m`.
- `L = NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA`, the regular
  module `ULift A` (with `a • up b = up (a * b)`), an object of
  `NondegenerateModuleCat.{uA, max uA uM} A`.
- All modules below are in `NondegenerateModuleCat.{uA, max uA uM} A`, the universe used by
  the statement.

## Imports

- `Langlands.Algebra.NondegenerateModuleCenterStatements`: the target statement, and through it
  `NondegenerateModuleCenter` (the commutant, the map `fromCommutantRingHom`, `forget`,
  `component`) and `IdempotentedRingCenterComparison` (the centre `Center hA` of `Â`,
  `Center.toFamily`, `Family.toCenter`).
- `Langlands.Algebra.NondegenerateModuleNaturalEndClassificationProof`: the published proof of
  Renard I.1.6. Three of its lemmas are used, all at universe `max uA uM`:
  - `coordinateRecovery hA x e`: the coordinate at `e` of the family recovered by evaluation
    at `L` from the action of `x` is `x(e)`. In other words, `(act L x (up e)).down = x(e)`.
  - `componentPointRecovery hA θ M m`: for a natural endomorphism `θ` of the forgetful functor,
    the family `φ = familyAddHom hA θ` (evaluation of `θ` at `L`) satisfies
    `act M φ m = θ_M m`.
  - `app_eq_evaluation_smul`, used only in the unital module.

Other published lemmas used: `IdempotentedRingRightLimitAction.product_act`
(`act (product x y) m = act x (act y m)`), `canonical_act` (`act (canonical a) m = a • m`),
`map_act` (an original module map `f` satisfies `f (act x m) = act x (f m)`),
`NondegenerateModuleCenter.mem_commutantSubring_iff` (membership in the commutant means
`canonical a * x = x * canonical a` for all `a`),
`IdempotentedRingRightLimit.mem_centerSubring_iff` and `mem_centerSubring_iff_mul` (membership
in the centre of `Â`), and the extensionality lemmas `CatCenter.ext`,
`ObjectProperty.hom_ext`, `NonUnitalModuleHom.ext` and `IdempotentedRingRightLimit.Center.ext`.

## Auxiliary lemma

`eq_of_act_eq`: two families `x, y ∈ Â` that act equally on every module of
`NondegenerateModuleCat.{uA, max uA uM} A` are equal. Proof: for each idempotent `e`, apply the
hypothesis to `L` and `up e`. By `coordinateRecovery`, the two sides have `down` equal to
`x(e)` and `y(e)`. So `x(e) = y(e)` for all `e`, and `x = y` by subtype and function
extensionality. Renard identifies a family with its action on `A` itself. This lemma is the
same fact, at the lifted object `L`.

## Proof of the four parts

1. **Injectivity of `fromCommutantRingHom.{uA, max uA uM} hA`**
   (`fromCommutantRingHom_injective`). Suppose that `x` and `y` in the commutant have the same
   image. The component at `M` of the image of `x` is the published action of `x` on `M`, by
   definition (`component`). So applying the components of both images to `m` gives
   `act M x m = act M y m` for all `M` and `m`. Then `eq_of_act_eq` gives `x = y` in `Â`, and
   subtype extensionality gives equality in the commutant.

2. **Surjectivity** (`fromCommutantRingHom_surjective`). Let `θ` be in the centre of the
   category. Let `φ = familyAddHom hA (forget θ)`: this is Renard's `θ_A`, the evaluation of
   (the forgetful image of) `θ` at the regular module `L`. By `componentPointRecovery`,
   `act M φ m = θ_M m` for every `M` and `m` (`hφ`).
   - `φ` is in the commutant. By `mem_commutantSubring_iff` it suffices to show that
     `canonical a * φ = φ * canonical a` for each `a : A`. By `eq_of_act_eq`, it suffices to
     compare the actions on every `M` and `m`. With `product_act`, `canonical_act` and `hφ`,
     the two sides become `a • θ_M m` and `θ_M (a • m)`. These are equal because the
     component `θ_M` is an original module map (`map_smul`).
   - The image of `⟨φ, _⟩` is `θ`: by `CatCenter.ext`, `ObjectProperty.hom_ext` and
     `NonUnitalModuleHom.ext` it suffices to compare components pointwise, and that is `hφ`.

3. **Commutant = centre of `Â`** (`commutantSubring_eq_centerSubring`, by `Subring.ext` from
   two inclusions).
   - Centre ⊆ commutant (`mem_commutantSubring_of_mem_centerSubring`): a central `x`
     commutes with every element of `Â`, in particular with each `canonical a`.
   - Commutant ⊆ centre (`mem_centerSubring_of_mem_commutantSubring`). Let `x` be in the
     commutant and `y ∈ Â`. By `mem_centerSubring_iff` we must show
     `product y x = product x y`. By `eq_of_act_eq` (used here at `uM = 0`, that is on modules
     in `Type uA`; the conclusion is an equation in `Â` and does not depend on the universe),
     it suffices to show `act M y (act M x m) = act M x (act M y m)` for every `M` and `m`,
     after `product_act` on both sides. The action of `x` on `M` is the original module map
     `NondegenerateModuleCenter.component hA ⟨x, hx⟩ M`. By `map_act`, the action of every
     family `y` commutes with original module maps. This gives the equation.
     This replaces Renard's "par continuité". It also differs from the algebraic argument
     sketched in the statement Markdown: it uses the action on modules instead of a
     computation inside `Â`.

4. **The inverse identities** (`toCenter_toFamily` and `toFamily_toCenter`). By the published
   definitions, the coordinate at `e` of `toFamily hA z` is the corner element `e z e`, whose
   value in `A` is `z(e)` (`cornerCoordinate`). The family `toCenter hA x` has coordinate
   `(x e)` viewed in `A` (`toCenter_coordinate`). So both composites keep every coordinate
   definitionally. The first identity follows from `Center.ext` with `rfl` at each `e`. The
   second follows from subtype and function extensionality, then two more subtype
   extensionality steps (a corner centre element is a subtype of a corner, which is a subtype
   of `A`), and `rfl`.

The final theorem `nondegenerateModuleCenterTheorem` introduces `A`, its ring instance and `hA`.
It returns the four results in the order of the statement.

## Relation to the source

Renard's inverse construction sends `θ` to `θ_A ∈ End_{A°}(A) = Â`. Here that construction is
the published evaluation map `familyAddHom` of I.1.6, at the lifted regular object `L`, applied
to the forgetful image of `θ`. The published I.1.6 proof already contains the two facts that
Renard leaves to the reader: the action of `θ_A` on a module `M` is `θ_M`
(`componentPointRecovery`), and a family is recovered from its action on `A`
(`coordinateRecovery`). The statement's universe `max uA uM` is exactly the one at which these
lemmas are stated, so no change of universe is needed. The only extra input the centre adds
is that the components `θ_M` are `A`-linear. That makes `θ_A` commute with `A`.
