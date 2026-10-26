# Simultaneous local approximation of a module map (Stacks 046Y, first proof step)

The declaration
`Langlands.Algebra.LocalCompatibleMapApproximationExistenceStatement.{uR,uS,uM,uN} : Prop`
states the approximation step in the first paragraph of the proof of Stacks
Project, Lemma 10.128.4, tag [046Y](https://stacks.math.columbia.edu/tag/046Y).
This module defines the proposition; its proof is a separate obligation. It
does not state or prove Lemma 10.128.4 itself.

## Source

The original is the registered source
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The passages read are:

- `00R3.html`, Lemma 10.128.4 (046Y) and the first paragraph of its proof:
  "By Lemma 10.127.13 and its proof we can find a system
  `R_λ → S_λ` of local ring maps together with maps of `S_λ`-modules
  `u_λ : M_λ → N_λ` satisfying the conclusions (1) – (6) for both `N` and `M`
  of that lemma and such that the colimit of the maps `u_λ` is `u`."
  The setting of the lemma is a local homomorphism `R → S` of local rings,
  `S` essentially of finite presentation over `R`, and `M,N` finitely
  presented over `S`, with an `S`-module map `u : M → N`.
- `00QL.html`, Lemma 10.127.13 (00QX), all six conclusions and its proof.
  The proof writes `R` as a directed colimit of local rings essentially of
  finite type over `ℤ`, chooses `S_λ` as prime localizations of polynomial
  quotients over a tail of the index set, and descends the entries of a
  presentation matrix of `M` to one stage, defining `M_λ` as cokernels on the
  tail above it.
- The preceding Remark 10.127.12 (00QW) warns that an arbitrary ring system
  with the earlier finite-type properties may fail the prime-localization
  property, so the ring system must be chosen with care. The ring
  construction is Lemma 10.127.11 (00QV).

The remaining flatness and residue-fibre arguments of 046Y (the use of
Lemma 10.128.3, the maps `Ψ_λ`, and Lemma 10.99.1) are not part of this
statement. No separate source-specific errata note was found in the current
project or Library notes.

## Hypotheses and quantifiers

The proposition universally quantifies `R : Type uR`, `S : Type uS`,
`M : Type uM` and `N : Type uN` in four independent universes. Both rings
are commutative local rings, `S` has an `R`-algebra structure, and its actual
structure map `algebraMap R S` is local. The carriers `M` and `N` have
additive commutative group structures and `S`-module structures.

The three substantive hypotheses are:

1. `EssFinitePresentation R S`, the published predicate for a localization
   of a finitely presented `R`-algebra (Stacks 00QM);
2. `Module.FinitePresentation S M`;
3. `Module.FinitePresentation S N`, Mathlib's finite-presentation predicate
   for modules.

Then, for every actual `S`-linear map `f : M →ₗ[S] N`, the conclusion holds.
There are no nonzero, flatness, Noetherian or injectivity hypotheses on
`M`, `N` or `f`, and no finite-presentation hypothesis on `R`. In
particular `N` is not assumed flat over `R`, and the residue map of `f` is
not assumed injective; those hypotheses of 046Y are used only in its later
paragraphs.

## Conclusion

The conclusion chooses a type `ι`, a preorder on it, nonemptiness and
directedness, and then jointly chooses

```
D : LocalAlgebraSystem ι R S
E : LocalModuleSystem D M
F : LocalModuleSystem D N
φ : LocalModuleSystem.CompatibleMap E F f
```

with `φ.IsApproximation`. Both module systems lie over exactly the same
ring system `D`. A directed preorder expresses the directed-system indexing;
antisymmetry is unnecessary for these data or conditions. The ring system is
existentially chosen together with both module systems and the map; the
proposition does not quantify over every preselected `D`.

The structure `CompatibleMap E F f`, published in
`Langlands.Algebra.LocalApproximationMap`, consists of:

- `φ.component i : E.obj i →ₗ[D.alg i] F.obj i`, an actual `D.alg i`-linear
  map, the source's `u_λ : M_λ → N_λ`;
- `φ.map_comm i j h m`:
  `φ.component j (E.map i j h m) = F.map i j h (φ.component i m)`, so the
  component maps form a map of directed systems;
- `φ.ιM_comm i m`: `F.ιM i (φ.component i m) = f (E.ιM i m)`, so the
  component maps are compatible with the specified `f` through the two
  cocones.

The published lemma `φ.moduleColimitMap_comp` proves that the additive map
`φ.colimitMap` induced on the actual direct limits satisfies
`F.moduleColimitMap.comp φ.colimitMap = f.toAddMonoidHom.comp E.moduleColimitMap`.
Under the colimit clauses below, the two comparison maps are bijective, so
the colimit of the component maps is identified with `f`. This is the
source's requirement that the colimit of the maps `u_λ` is `u`. The map `f`
is the given `S`-linear map, not an `R`-linear or other substitute.

## The six approximation conditions for both modules

By its published definition, `φ.IsApproximation` is exactly
`E.IsApproximation ∧ F.IsApproximation`, the source's conclusions (1)–(6)
for both `M` and `N`. Both six-clause predicates are reused unchanged. Write
`Rᵢ = D.base i`, `Sᵢ = D.alg i`, and let `Pᵢ` be `E.obj i` or `F.obj i`, with
`P` the corresponding module `M` or `N`. For each of the two systems:

1. The canonical ring maps `D.baseColimitMap` from `Ring.DirectLimit D.base`
   to `R` and `D.algebraColimitMap` from `Ring.DirectLimit D.alg` to `S` are
   bijective, and the canonical additive map from
   `AddCommGroup.DirectLimit` of the components `Pᵢ` to `P` is bijective
   (`E.moduleColimitMap`, respectively `F.moduleColimitMap`).
2. Every `Rᵢ` is essentially of finite type over `ℤ`.
3. Every `Sᵢ` is essentially of finite type over `Rᵢ`.
4. Every `Pᵢ` is finite over `Sᵢ`.
5. For every `h : i ≤ j`, `D.IsPrimeLocalization h`: the canonical ring map
   `D.ringBaseChangeMap h : Sᵢ ⊗[Rᵢ] Rⱼ →+* Sⱼ`, sending `s ⊗ r` to
   `D.algMap i j h s * algebraMap Rⱼ Sⱼ r`, presents `Sⱼ` as the
   localization of that actual tensor product at a prime ideal, using the
   algebra structure `(D.ringBaseChangeMap h).toAlgebra`.
6. For every `h : i ≤ j`, the canonical `Sⱼ`-linear map
   `moduleBaseChangeMap h : Sⱼ ⊗[Sᵢ] Pᵢ →ₗ[Sⱼ] Pⱼ`, with formula
   `s ⊗ m ↦ s • map i j h m`, is bijective.

The ring part of clause 1 and clauses 2, 3 and 5 concern only the shared
`D` and therefore appear in both conjuncts. Clause 6 uses the published scalar-first tensor convention; the
source writes `M_λ ⊗_{S_λ} S_μ`, and tensor symmetry exchanges the factors.

## Witness sizes and provenance of the packaging

Let `U = max uR uS uM uN`. The index `ι` lives in `Type U`, as do every
`Rᵢ`, `Sᵢ`, `E.obj i` and `F.obj i`. The explicit universe arguments of
`LocalAlgebraSystem` and of both `LocalModuleSystem`s fix these five witness
levels to `U`; the target rings and modules keep their own independent
universes `uR,uS,uM,uN`. Choosing one common level lets both module systems
share the same `D` and lets one statement cover all four ambient universes.

This follows the size convention of the published single-module statement
`Langlands.Algebra.LocalModuleApproximationExistenceStatement`, with `uN`
added to the maximum. Finite subsets, polynomial quotients, localizations,
finite matrices and their cokernels can be constructed at this level, and
restricting to a directed tail does not increase it. If a proof first
constructs smaller witnesses, it must transport their structures and maps to
level `U` and verify the required properties; no such transport is assumed
here. The statement imposes no equality among `uR,uS,uM,uN` and does not
claim existence in every independently prescribed smaller witness universe.

The Lean structures, canonical maps, directed-preorder presentation, the
compatible-map packaging and the universe choice are internal formalization
choices for the source's system of local ring maps, module systems and
component maps. This module imports the published
`Langlands.Algebra.LocalApproximationMap` (which imports
`Langlands.Algebra.LocalApproximationSystem`) and
`Langlands.Algebra.EssFinitePresentation` without modifying them, and adds
only this existence proposition. Eventual flatness of the `N`-components,
residue-fibre injectivity and the remaining steps of 046Y are separate units.
