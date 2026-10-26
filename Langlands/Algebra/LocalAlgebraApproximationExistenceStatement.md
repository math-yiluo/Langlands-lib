# Existence of local algebra approximation systems (Stacks 00QV)

The module defines
`Langlands.Algebra.LocalAlgebraApproximationExistenceStatement.{uR,uS} : Prop`.
It states Lemma 10.127.11 of the Stacks Project, tag
[00QV](https://stacks.math.columbia.edu/tag/00QV). It supplies a proposition
for a later proof; this file does not prove existence.

## Source and reading

The registered original is
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The source folder is
`Stacks Project - Algebra flatness criteria and essentially finite presentation (HTML snapshot 2026-10-22)`.
The complete `00QV.html` statement, proof and all four comments were read,
together with Remark 10.127.12 (tag 00QW) in `00QL.html`.
No source-specific errata file was found in the project or current Library
notes at authoring.

Comments 6226 and 6360 record the correction to the polynomial quotient map in
the proof: the source and target are the quotients over the component base
and over `R`, respectively. The snapshot includes this corrected map.
Comments 9811 and 10379 discuss strengthening condition (3) to essential finite
presentation and explicitly retain the original wording. Accordingly the
statement uses essential finite type for the component algebras.

## Hypotheses and quantifiers

The statement universally quantifies `R : Type uR` and `S : Type uS`,
their commutative-ring and local-ring structures, an `Algebra R S` structure,
and `IsLocalHom (algebraMap R S)`. It assumes the published predicate
`EssFinitePresentation R S`. This predicate uses a finitely generated ideal
in a polynomial ring with finitely many variables, localization at an
arbitrary submonoid of its quotient, and an `R`-algebra equivalence with `S`.
It is imported unchanged.

The conclusion existentially quantifies an index type `ι`, a preorder on it,
`Nonempty ι`, `IsDirectedOrder ι`, and a
`D : LocalAlgebraSystem ι R S` satisfying `D.IsApproximation`.
The preorder and its two properties are witnesses, not hypotheses imposed on
the caller. A directed preorder presents the directed system of the source;
antisymmetry is unnecessary for the maps and their composition laws.
Nonemptiness is explicit.

The imported structure supplies actual commutative local rings `D.base i`
and `D.alg i`, local component algebra maps, local transition homomorphisms,
and compatible local cocone maps into the given `R` and `S`.
Its commuting-square equations bind the colimit arrow to the specified
`algebraMap R S`.

## The four conclusion clauses

The conclusion is precisely the existing `LocalAlgebraSystem.IsApproximation`.

| Stacks 00QV clause | Lean condition and meaning |
| --- | --- |
| (1) The colimit of the arrows is `R → S`. | `D.IsColimit`: the canonical ring homomorphisms `D.baseColimitMap` and `D.algebraColimitMap` from the actual `Ring.DirectLimit` constructions to `R` and `S` are bijective. The structure's commuting squares give compatibility with the given arrow. |
| (2) Each base is essentially of finite type over the integers. | `∀ i, Algebra.EssFiniteType ℤ (D.base i)`, using the canonical integer algebra structure. |
| (3) Each component algebra is essentially of finite type over its base. | `∀ i, Algebra.EssFiniteType (D.base i) (D.alg i)`, using the structure's component algebra instance. |
| (4) Each base-changed transition is localization at a prime. | `∀ i j (h : i ≤ j), D.IsPrimeLocalization h`, for the actual tensor transition described below. |

For `h : i ≤ j`, the domain `D.RingBaseChange h` is
`D.alg i ⊗[D.base i] D.base j`, where the algebra structure on `D.base j`
comes from `D.baseMap i j h`. The map `D.ringBaseChangeMap h` sends
`s ⊗ r` to
`D.algMap i j h s * algebraMap (D.base j) (D.alg j) r`.
The localization predicate installs exactly
`(D.ringBaseChangeMap h).toAlgebra`, then asks for an actual prime ideal
of that tensor product and `IsLocalization.AtPrime (D.alg j)` at that prime.
It does not replace localization by bijectivity of the tensor transition.

Remark 00QW exhibits a local finite-type approximation for which clause (4)
fails: in characteristic two its transitions kill a new square. The source
therefore requires a carefully chosen system, as expressed by the existential
conclusion with all four clauses together.

## Internal universe packaging

The only universe parameters of the proposition are the independent ambient
levels `uR` and `uS`. The witnesses are chosen as

```lean
ι : Type (max uR uS)
D : LocalAlgebraSystem.{max uR uS, max uR uS, max uR uS, uR, uS} ι R S
```

Thus the index, every `D.base i`, and every `D.alg i` lie in the common maximum.
This is an internal size choice for existential witnesses. It does not equate
the universes of `R` and `S`, move those target carriers, or demand small
representatives for arbitrary ambient rings. In particular there are no
universally quantified index or component universe levels.

The source construction can be organized using finite sets of elements of `R`,
the integer subalgebras they generate, localization at the contraction of the
maximal ideal, and finite polynomial quotients. Such finite-set indices and
ring constructions can be formed in the universe of `R`; restricting to a
tail containing the finite set of relation coefficients preserves that bound.
They can then be raised to the displayed maximum without changing the target
carriers. This is the mathematical justification for the witness size, not
an implemented transport proof. A later exact-target proof must implement any
needed `ULift` transport of the rings, actions, maps, colimit comparisons and
prime-localization properties.

## Proof boundary and provenance

The source proof chooses a prime localization of a finite polynomial quotient
representing `S`, descends finitely many relation coefficients to one stage
of a local finite-type approximation of `R`, and restricts to the directed
tail above that stage. It takes each component algebra to be the corresponding
polynomial quotient localized at the inverse image of the target prime.
Verifying the four clauses, including the actual comparison maps, remains
the later proof task.

The mathematical assertion is source-derived. The proposition packaging,
directed preorder, explicit comparison maps and maximum-universe witnesses
are internal formalization choices. The imported `LocalApproximationSystem`
and `EssFinitePresentation` Lean/Markdown pairs are unchanged. No module
system, flatness assumption or conclusion, compatible-map approximation,
or synchronized tower existence is included.
