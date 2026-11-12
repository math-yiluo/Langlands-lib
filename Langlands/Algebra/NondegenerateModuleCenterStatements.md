# The centre of the category of nondegenerate modules (Renard I.1.7): statements

Module `Langlands.Algebra.NondegenerateModuleCenterStatements`.
Namespace `Langlands.Algebra`. Universe parameters `uA` (the ring) and `uM` (module
carriers, enlarged to `max uA uM`).
The module contains two **statements**, the `Prop`-valued definitions
`NondegenerateModuleCenterTheoremStatement` and `UnitalNondegenerateModuleCenterStatement`.
It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published constructions it uses record the
assertions as missing. [NondegenerateModuleCenter](NondegenerateModuleCenter.md) builds the
Lemma's action but "do[es] not assume the inverse or classification assertions of the I.1.7
prose and theorem". [IdempotentedRingCenterComparison](IdempotentedRingCenterComparison.md)
builds both comparison maps but says "Not included: the identities saying the two maps are
mutually inverse, the resulting ring equivalence and the final comparison theorem.
Identification of the centre with the commutant … and with the categorical centre … is also
not included."

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read I.1.7, printed pp.12–13 / PDF pp.18–19. The completion
`Â = End_{A°}(A)` is that of I.1.3–I.1.6.

> Lemme. Soit `φ ∈ Â = End_{A°}(A)` un morphisme commutant aussi avec l'action par
> multiplication à gauche de `A` sur lui-même […]. Alors pour tout `A`-module non dégénéré
> `M`, il existe un morphisme `φ̃_M : M → M` tel que `φ̃_M(a · m) = φ(a) · m` […]. De plus
> `φ ↦ φ̃_M` est naturel en `M` […].
>
> Autrement dit, tout `φ ∈ Â` commutant avec l'action par multiplication à gauche de `A` sur
> lui-même définit une transformation naturelle du foncteur `Id_{M(A)}` dans lui-même.
> Réciproquement, une telle transformation naturelle `θ` détermine un morphisme
> `φ = θ_A ∈ Â = End_{A°}(A)` commutant avec les multiplications à gauche. Ces deux
> constructions sont inverses l'une de l'autre.
>
> Théorème. Le centre de `M(A)` s'identifie au commutant de `A` dans `Â`, ou encore au centre
> de `Â`. C'est la limite projective sur `ℐ = Idem(A)` des centres des anneaux `eAe`,
> `e ∈ ℐ`.
>
> Remarque. Lorsque `A` est unitaire, le centre `ℨ(A)` s'identifie au centre de l'anneau
> `A`, résultat bien connu.

## Published objects used

- `NondegenerateModuleCat.{uA, uM'} A`: the category `M(A)` of nondegenerate original
  modules (every vector fixed by an idempotent), with carriers in `Type uM'`.
- `NondegenerateModuleCenter.{uA, uM'} A`: its centre, Mathlib's `CatCenter`, the natural
  endomorphisms of the identity functor. Components are original module intertwiners.
- `IdempotentedRingRightLimit A` with `IdempotentedRingRightLimit.ring hA`: the completion
  `Â` as compatible right families (I.1.3), with its canonical map from `A`.
- `NondegenerateModuleCenter.commutantSubring hA`: the centralizer in `Â` of the image of `A`.
  `NondegenerateModuleCenter.fromCommutantRingHom hA`: the ring map from that commutant to the
  categorical centre, sending `φ` to the family `(φ̃_M)_M` of the Lemma.
- `IdempotentedRingRightLimit.centerSubring hA` and its subtype `Center hA`: the centre of
  `Â` (Mathlib's `Subring.center`).
- `IdempotentedRingCornerCenter.Family A`: coherent families of central elements of the
  corners `eAe` under the transitions `a ↦ eae`, that is the projective limit of the corner
  centres. `IdempotentedRingRightLimit.Center.toFamily hA` (`z ↦ (eze)_e`) and
  `IdempotentedRingCornerCenter.Family.toCenter hA` are the two comparison maps of Renard's
  proof.

## The statements

**`NondegenerateModuleCenterTheoremStatement`.** For every nonunital ring `A` with
idempotents (`hA : IsIdempotented A`):

1. `fromCommutantRingHom.{uA, max uA uM} hA` is bijective. This is the paragraph after the
   Lemma, "ces deux constructions sont inverses l'une de l'autre", and the first
   identification of the Theorem.
2. `commutantSubring hA = centerSubring hA`: the commutant of `A` in `Â` is the centre of `Â`.
3. `toCenter hA ∘ toFamily hA = id` and `toFamily hA ∘ toCenter hA = id`: the centre of `Â`
   is the projective limit of the centres of the `eAe`.

**`UnitalNondegenerateModuleCenterStatement`.** For every unital ring `A`:

1. every `θ ∈ ℨ(A)` acts on every nondegenerate module `M` as multiplication by a unique
   central element `z` of `A`;
2. every central `z` arises in this way from some `θ`.

Together these give the bijection `Z(A) ≃ ℨ(A)` of the Remark. It is compatible with
addition and multiplication because both act by composition of the actions on each `M`.

## Formalization choices

- **Module universe.** The inverse construction evaluates `θ` at `A` itself, viewed as a left
  module over itself. The category therefore has carriers in `Type (max uA uM)`, so that it
  contains `A`. The published II.3.13 statement `RenardCenter.CategoricalComparisonSpecification`
  uses the centre at the same universe `max uG uM`.
- **Commutant.** Renard's "commutant de `A` dans `Â`" is the centralizer of the image of
  `A`. The source's argument for its equality with the centre of `Â` is "par continuité". An
  algebraic argument is available: a commuting `x` satisfies `x(y(b)) = y(e)x(b) = y(x(b))`
  for `y ∈ Â` and `b = eb`.
- **Projective limit.** `Family A` is the actual set of coherent families. The two inverse
  identities say that `toFamily` is a ring isomorphism onto it, with inverse `toCenter`.
- **Unital remark.** For a unital ring, a nondegenerate module is exactly a unital module:
  if `e · m = m` then `1 · m = m`. The statement compares `ℨ(A)` with the centre of `A`
  directly through the action. It does not pass through `Â`, and it avoids a separate
  identification of `Â` with `A`. The published
  `CategoryTheory.RenardModuleCatCenterStatements` (A.X) states the analogous fact for
  Mathlib's `ModuleCat`, which is a different category object.

## Why the statements are true

1. Renard's inverse sends `θ` to `θ_A`. Naturality of `θ` with respect to the right
   multiplications `a ↦ ab`, which are module maps `A → A`, makes `θ_A` right-linear, so
   `θ_A ∈ Â`. Naturality with respect to the module maps `A → M`, `a ↦ a · m` for `m` with
   `e · m = m`, gives `θ_M(m) = θ_A(e) · m`. So `θ` is the image of `θ_A`. Conversely, the
   action of `φ` on `A` is left multiplication by `φ`, so the image of `φ` evaluated at `A` is
   `φ` again.
2. Each element of `A` is in `Â`, so the centre lies in the commutant. For the converse, see
   the algebraic argument above.
3. This is Renard's proof of the last assertion: `e z̄ e` is central in `eAe`. Conversely, a
   coherent family defines `z̄` with `e z̄ = z̄ e` for every `e`. Then `z̄` commutes with each
   `eAe`, and `A` is the union of the `eAe`.
4. The unital case is the classical identification of the centre of the category of modules
   (Renard's appendix A.X example), applied through 1: the image of `A` in `Â` is all of `Â`
   when `A` has a unit.

## Remaining obligations

The proofs are separate obligations. The published constructions supply all the maps; the
inverse identities and the two bijectivity assertions remain to be proved.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Algebra.NondegenerateModuleCenter` | `NondegenerateModuleCenter`, `commutantSubring`, `fromCommutantRingHom`, `NondegenerateModuleCat` |
| `Langlands.Algebra.IdempotentedRingCenterComparison` | `IdempotentedRingRightLimit.centerSubring`, `Center`, `Center.toFamily`, `IdempotentedRingCornerCenter.Family`, `Family.toCenter` |
