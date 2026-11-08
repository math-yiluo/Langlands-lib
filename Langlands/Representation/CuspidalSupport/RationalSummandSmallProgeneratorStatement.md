# Renard VI.4.1, Proposition: the single-summand small progenerator

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locators are the opening paragraphs of VI.4.1 and the Proposition with its proof, on printed p.149 / PDF p.155. The small-progenerator conventions are those of A.VIII.2, printed pp.266–267 / PDF pp.272–273. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

Renard fixes an irreducible supercuspidal representation (π,V) of G. By Proposition VI.3.2, the restriction of π to ⁰G is a direct sum of irreducible compact representations. Renard picks one of them, (ρ,W), and puts (Π,V_Π) = ind_{⁰G}^G(ρ,W). The Proposition says that Π is a small progenerator of M(G)[π]. The proof shows four things:

- projectivity, from the adjunction (VI.4.1.1) and semisimplicity of restrictions to ⁰G in the block;
- the generator property, since Hom_G(Π,τ) ≠ 0 for every nonzero τ in the block;
- finite type, using the functions f_{i,w} of (VI.4.1.2);
- smallness, from finite type.

The Library already states the analogous property for the alternative progenerator Π₁ = ind_{⁰G}^G(Res π) of the following Remark: `RationalUniversalSmallProgeneratorStatement` by Worker 1758. The present unit states the Proposition itself, for the single summand.

## Lean content

Write H = G(F), with its canonical rational-point topology. Write H⁰ = `Plancherel.rationalCommonNormKernel G` for the common kernel of the norms of all rational characters. This is Renard's ⁰G, and it carries the subspace topology.

- `IsRationalInertiaSmallProgenerator G π X` takes an arbitrary actual smooth representation X of H. The carrier universe of X is `max uF uV`. The predicate is the conjunction in `IsRationalNormKernelSmallProgenerator` (Worker 1758), with Π₁ replaced by X. It first asserts membership of X in the existing full category `RationalInertiaBlock G (rationalInertiaBaseLift G π)`: every irreducible actual subquotient of X is isomorphic to an actual unramified twist of the lifted π. Let P be the resulting object of that block. The predicate then asserts four conditions:
  1. Lifting along epimorphisms. For every epimorphism q : Y → Z of the block and every f : P → Z, there is g : P → Y with g ≫ q = f. This is projectivity.
  2. The published integer-module Hom functor `Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P` is faithful. This is the generator condition of A.VIII.2.
  3. The block has coproducts indexed by every type in `Type (max uF uV)`.
  4. That Hom functor preserves all such coproducts. This is A.VIII.2 smallness: Hom(P,•) preserves direct sums.

  `isRationalNormKernelSmallProgenerator_iff` records, by `Iff.rfl`, that Worker 1758's predicate is this predicate at Π₁ = `rationalNormKernelCompactInduction G π`. So both progenerator statements use the same conditions.
- `rationalNormKernelSummandInduction G ρ` is Renard's Π for an actual smooth representation ρ of H⁰ with carrier in `Type uV`. It is literally the published `Induction.compactInductionFunctor (rationalCommonNormKernel G)` applied to `SmoothRep.toRep.obj ρ`. Its carrier is the type of functions f : H → W with f(hx) = ρ(h)f(x) for h ∈ H⁰. These functions are invariant under right translation by an open subgroup and have compact support modulo H⁰. Since H⁰ is open, the latter means support in finitely many cosets H⁰g. The action is right translation. The construction has no modulus factor. This matches Renard's ind_{⁰G}^G: H⁰ is open in G and unimodular, as Renard notes in the proof.
- `RationalSummandSmallProgeneratorStatement` covers every arbitrary connected reductive G over every nonarchimedean local field F. Its premises are the same as those of `RationalUniversalSmallProgeneratorStatement`:
  - a maximal split torus inclusion i and a generic cocharacter ν;
  - explicit `StandardCocharacterStatement`, relative-root-system and standard-unipotent-closedness premises, from which the finite simple-root index set and the actual semidirect decompositions are derived;
  - local compactness, the nonarchimedean group property and Hausdorffness of H.

  Take π irreducible, and cuspidal in the sense of the published `Aubert.General.IsCuspidal`: every proper standard normalized Jacquet module vanishes. Comparing this with cuspidality along all proper rational parabolics is a separate obligation, as in the Π₁ statement. Take ρ an irreducible actual smooth representation of H⁰ with carrier in `Type uV`, together with an H⁰-equivariant linear map j : ρ → `SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π` that is injective. The statement asserts `IsRationalInertiaSmallProgenerator G π (rationalNormKernelSummandInduction G ρ)`.

## Correspondence and conventions

**Choice of ρ.** Renard's ρ is "one of these representations", an irreducible summand of Res π. The Lean statement instead takes every irreducible ρ with an injective equivariant map into Res π. By VI.3.2 these are, up to isomorphism, exactly the summands: an irreducible subrepresentation of a direct sum of irreducibles is isomorphic to one of them, and conversely each summand embeds. Compact induction is a functor, so isomorphic ρ give isomorphic Π. The Lean statement does not use or assert this comparison. Renard's remark that the class of Π depends only on [π] is also not stated here.

**Universes.** The universe conventions are those of the Π₁ statement. The field and group universe `uF` and the carrier universe `uV` are independent. π and ρ have carriers in `Type uV`, and Π has carrier in `Type (max uF uV)`. So the block is formed at carrier universe `max uF uV`, from the lift of π along the published fully faithful `SmoothRep.universeLiftFunctor` (`rationalInertiaBaseLift`). Coproducts are indexed by `Type (max uF uV)`, the carrier universe, not by the larger universe of all objects. Coefficients are ℂ in universe zero.

**Abelianness.** A.VIII.2 is phrased in an abelian category. The published `Renard.HomSmallProgenerator` predicate requires an abelian-category instance. The present conditions are stated on the actual preadditive full block, without assuming abelianness. Coproduct existence is asserted in the conclusion, not supplied as a premise.

**Finite type.** Renard deduces smallness from Π being of finite type. Finite type is a step of the proof, not part of the stated Proposition, so it is not stated separately here.

There is no splitness, characteristic-zero, admissibility, compactness or finite-dimensionality premise on ρ or π. In particular, compactness of ρ is not assumed.

## Scope

This module defines Prop-valued targets and a construction. It also proves the definitional `Iff.rfl` comparison with the Π₁ predicate. It does not prove block membership, projectivity, generation, coproduct existence or smallness. The Theorem of VI.4.1, that F_Π = Hom_G(Π,•) is an equivalence onto right modules over End_G(Π), is the separate statement `RationalSummandHomEquivalenceStatement`.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
