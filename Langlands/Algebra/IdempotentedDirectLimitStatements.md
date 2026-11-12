# Direct-limit descriptions of rings and modules with idempotents (Renard I.1.2, I.1.4): statements

Module `Langlands.Algebra.IdempotentedDirectLimitStatements`. Namespace `Langlands.Algebra`.
Universe parameters `uA` (the ring), `uM` (the module) and `uT` (the test groups and rings).
The module contains three **statements**, the `Prop`-valued definitions
`IdempotentedRingDirectLimitStatement`, `NondegenerateModuleDirectLimitStatement` and
`LeftLimitNotNondegenerateStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published
[IdempotentedRing](IdempotentedRing.md) proves the set equality `A = ⋃ eAe` and says that
the direct-limit statement "requires a separate diagram and universal property and is not
claimed here". [NonUnitalModule](NonUnitalModule.md) lists "categorical colimit universal
properties, cofinal or relatively directed idempotent systems" among the deferred
obligations. [NonUnitalModuleLeftLimit](NonUnitalModuleLeftLimit.md) says that "the
subsequent action need not be nondegenerate" and leaves this as an obligation. This unit
states these assertions.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read I.1.2, printed p.7 / PDF p.13, and I.1.4, printed p.10 / PDF p.16:

> On peut reformuler la définition ci-dessus en disant qu'un anneau à idempotents est un
> anneau `A` tel que : `A = lim_{e ∈ ℐ} eAe = ⋃_{e ∈ ℐ} eAe`. La limite inductive étant
> formée par rapport aux morphismes d'inclusion `eAe ↪ fAf`, `e ≤ f` dans `ℐ` (voir A.IV.2
> pour la notion de limite inductive).
>
> Définition. Un module `M` de l'anneau à idempotents `A` est dit non dégénéré si pour tout
> élément `m ∈ M`, il existe un idempotent `e` de `A` tel que `e · m = m`. De manière
> équivalente, `M` est non dégénéré si `M = lim_{e ∈ ℐ} e · M`.
>
> Remarques. […] 2. […] Dans un anneau à idempotents, une partie `𝒥` de `ℐ` sera dite
> filtrante si toute famille finie d'éléments de `ℐ = Idem(A)` admet un majorant dans `𝒥`.
> Pour qu'un module `M` soit non dégénéré, il suffit que tout élément de `M` soit fixé par un
> idempotent dans un système filtrant `𝒥`. Pour un tel `𝒥`, et pour tout module non dégénéré
> `M`, on a […] `A = lim_{e ∈ 𝒥} eAe` et `M = lim_{e ∈ 𝒥} e · M`.

and, after the I.1.4 Proposition:

> Cette structure étend celle de `M`, mais le module `M̂` n'est plus nécessairement non
> dégénéré.

## Published objects used

- `Idempotent A`, ordered by `e ≤ f` iff `eAe ⊂ fAf`; `e.corner : NonUnitalSubring A`, the
  corner `eAe` ([IdempotentedRing](IdempotentedRing.md)); `IsIdempotented A`.
- `e.leftImage M : AddSubgroup M`, the subgroup `e · M = {m | e · m = m}`
  ([NonUnitalModuleLeftLimit](NonUnitalModuleLeftLimit.md)). It is not an `A`-submodule in
  general, which is why the direct limit is taken in abelian groups.
- `IsNondegenerate A M`: every vector is fixed by an idempotent.
- `NonUnitalModuleLeftLimit A M`, the completion `M̂` of I.1.4 (compatible families), and
  `NonUnitalModuleLeftLimit.nonUnitalModule hA`, its original action
  `(a · φ)(b) = φ(ba)` ([NonUnitalModuleLeftLimitAction](NonUnitalModuleLeftLimitAction.md)).

## The statements

Throughout, `A` is a nonunital ring with idempotents and `J : Set (Idempotent A)` is a
**filtering system** in Renard's sense: every finite set of idempotents has an upper bound in
`J`. The whole set `ℐ = Idem(A)` is filtering by the I.1.2 Lemma.

**`IdempotentedRingDirectLimitStatement`.** `A` is the direct limit of the corners `eAe`,
`e ∈ J`, along the inclusions:

1. in abelian groups: for every abelian group `T` and every family of additive maps
   `g_e : eAe → T` (`e ∈ J`) such that `g_e(a) = g_f(a)` whenever `e ≤ f` and `a ∈ eAe`,
   there is a unique additive `h : A → T` with `h(a) = g_e(a)` for all `e ∈ J`, `a ∈ eAe`;
2. in nonunital rings: the same with nonunital rings `T` and nonunital ring maps.

**`NondegenerateModuleDirectLimitStatement`.** For every original `A`-module `M`:

1. `M` is nondegenerate if and only if every vector is fixed by an idempotent of `J`;
2. `M` is nondegenerate if and only if it is the direct limit, in abelian groups, of the
   subgroups `e · M`, `e ∈ J`, along the inclusions (the same universal property as above).

**`LeftLimitNotNondegenerateStatement`.** There exist a ring with idempotents `A` and a
nondegenerate `A`-module `M` such that the completion `M̂`, with its original action, is
not nondegenerate.

## Formalization choices

- **Direct limits as universal properties.** A.IV.2 defines `lim` by its universal property.
  The statements spell it out for the cocone of inclusions, without building a diagram
  functor. Compatibility is required on vectors lying in both `e · M` and `f · M` for
  `e ≤ f`, which is the transition `e · M ↪ f · M`. The test objects live in an arbitrary
  universe `uT`.
- **Which category.** Renard does not say. The rings' limit is stated both in abelian groups
  and in nonunital rings, since the inclusions `eAe ↪ fAf` are ring maps. The subgroups
  `e · M` are not `A`-modules, so the modules' limit is stated in abelian groups.
- **The full system and Remark 2 together.** Taking `J = Idem(A)` gives the reformulations
  of the Definitions. A general `J` gives Remark 2. Clause 1 of the module statement is
  Renard's "il suffit que tout élément de `M` soit fixé par un idempotent dans `𝒥`", made an
  equivalence. The converse direction is immediate.
- **The equivalence in the Definition.** Renard's "de manière équivalente, `M` est non
  dégénéré si `M = lim e · M`" is stated as an equivalence with the universal property of
  the inclusions into `M`. For a degenerate module the inclusions are not a direct limit:
  the union of the `e · M` is the nondegenerate part `M_A`, a proper subgroup.
- **The counterexample is existential.** "N'est plus nécessairement non dégénéré" asserts
  that the completion can be degenerate. The statement asserts one instance, with `A` and
  `M` in `Type`.
- **Remark 3** of I.1.2 (relative nondegeneracy) only says that the notion can be
  generalized. It makes no assertion and is not stated.

## Why the statements are true

1. For `a ∈ A` choose `e` with `a ∈ eAe` (`IsIdempotented`) and `f ∈ J` above `e`; then
   `a ∈ fAf`. Put `h(a) = g_f(a)`. Two such choices agree by compatibility through a common
   upper bound in `J`. Any two elements lie in a common corner `fAf`, `f ∈ J`, so `h` is
   additive, and multiplicative when the `g_e` are ring maps. Uniqueness is clear.
2. If `e · m = m` and `e ≤ f`, then `f · m = m` (I.1.1 (ii), `Idempotent.mul_eq_of_le`).
   This gives clause 1, and makes the union of the `e · M`, `e ∈ J`, a directed union of
   subgroups. If `M` is nondegenerate that union is `M`, and the argument of 1 applies.
   Conversely, if the universal property holds, let `N` be that union. The zero family has
   two extensions, `0` and `M → M/N → ℚ/ℤ` for any map `M/N → ℚ/ℤ`. `ℚ/ℤ` is an injective
   cogenerator in every universe, so uniqueness forces `N = M`.
3. Take `A = ⊕_{n ∈ ℕ} ℂ` with coordinatewise multiplication and `M = A`. The idempotents
   are the indicators `1_S` of finite sets `S`, and `A` is a ring with idempotents. The
   compatible families are exactly the sequences in `∏_ℕ ℂ`. The constant family `1` is
   fixed by no `1_S`, since `1_S · 1 = 1_S ≠ 1`.

## Remaining obligations

The proofs are a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Algebra.NonUnitalModuleLeftLimitAction` | `NonUnitalModuleLeftLimit.nonUnitalModule`; through its imports `Idempotent`, `Idempotent.corner`, `Idempotent.leftImage`, `IsIdempotented`, `IsNondegenerate`, `NonUnitalModuleLeftLimit` |
