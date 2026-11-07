# Renard VI.9.5: the Jacquet module of an admissible `(G, B)`-module is admissible

Author: Worker 6. Module
`Langlands.Representation.Families.RenardFamilyJacquetAdmissibilityStatement`,
namespace `Langlands.Renard.AlgebraicFamily`. It contains one **statement**, the
closed `Prop`-valued definition `JacquetAdmissibleStatement` (universe parameters
`u', uB', uV'`). It proves nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**:

- VI.9.5, "Une autre conséquence", printed p. 201 / PDF p. 207;
- VI.8.3, "`(G, B)`-modules et restriction", printed p. 191 / PDF p. 197, whose
  hypotheses VI.9.5 adopts;
- VI.8.1, the definition of `(G, B)`-modules and of their admissibility, printed
  p. 187 / PDF p. 193;
- VI.6.1, the Corollary of the Jacquet lemma, printed p. 176 / PDF p. 182, whose
  argument VI.9.5 refers to.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 6 read PDF pages 182–183, 193, 197 and 207.

The passage of VI.9.5 is: "Plaçons-nous dans les hypothèses de la section VI.8.3.
Le foncteur de restriction `r_P^G : M(G, B) → M(M, B)` préserve la
`B`-admissibilité. L'argument est le même que celle du corollaire VI.6.1."

The hypotheses of VI.8.3 are a parabolic subgroup `P = MN` of `G` and, as
throughout VI.8, "une `ℂ`-algèbre commutative noethérienne de type fini réduite"
`B`. By the Definition of VI.8.1, a `(G, B)`-module is a smooth representation
`(π, V)` of `G` with a structure of flat `B`-module commuting with the action of
`G`, and it is admissible if `V^K` is a finitely generated `B`-module for every
compact open subgroup `K` of `G`. VI.8.3 shows that `r_P^G(V)` is again a flat
`B`-module, which gives the functor `r_P^G : M(G, B) → M(M, B)`. VI.9.5 asserts
that this functor sends admissible `(G, B)`-modules to admissible
`(M, B)`-modules.

## Lean model

The binders are those of the VI.6.1 Corollary statement
[ArbitraryParabolicJacquetAdmissibilityStatement](../Exponents/ArbitraryParabolicJacquetAdmissibilityStatement.md)
for complex representations, with Worker 709's coefficient ring and family
conventions of VI.8:

- a field `k : Type u'` with `[Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]`, so any nonarchimedean local field
  of any characteristic;
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. The
  statement installs `hG.isAffineHom` and the canonical topology
  `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes
  `[LocallyCompactSpace (rationalPoints G)]` and
  `[NonarchimedeanGroup (rationalPoints G)]`;
- every actual rational parabolic `p : P ⟶ G` (`hp : IsParabolicSubgroup p`)
  with rational Levi `l : M ⟶ P` (`hl : IsRationalLeviSubgroup l`) and matching
  geometric unipotent radical `r : U ⟶ P` (`hr`, and
  `hmul : IsIso (subgroupMultiplication l r)`). The statement installs
  `hl.isConnectedReductive.isAffineHom` and the canonical topology
  `leviPointTopology l hl` on `rationalPoints M`, which the compact open
  subgroups of `M(F)` use. `P = G` is allowed;
- the coefficient ring `B : Type uB'` with `[CommRing B] [Algebra ℂ B]
  [IsNoetherianRing B] [Algebra.FiniteType ℂ B] [IsReduced B]`.

A family over `B` is a `B`-linear representation, as in the published
[RenardFamilyStatements](RenardFamilyStatements.md). A `(G, B)`-module is
`ρ : Representation B (rationalPoints G) V`, with `V : Type uV'`, together with
`IsSmooth ρ` and `Module.Flat B V`. It is admissible when moreover
`Module.Finite B (fixedVectors ρ K.toSubgroup)` for every compact open subgroup
`K`, that is, every `K : OpenSubgroup (rationalPoints G)` with
`IsCompact (K : Set _)`.

Renard's normalized Jacquet module `r_P^G(V)` is the published
`leviJacquetRepresentation p l r hp hr hl hmul ρ` of
[RenardFamilyParabolicFunctors](RenardFamilyParabolicFunctors.md): the
coinvariants `V_N = V/V(N)` of the unipotent radical image, as a family of
`M(F)` over `B` with the normalized action `m · [v] = c_U(m)^{-1/2} [ρ(m) v]`.
That module's Markdown explains Renard's reciprocal `δ_P` convention.

## Declaration

| Declaration | Source | Statement |
| --- | --- | --- |
| `JacquetAdmissibleStatement` | VI.9.5, PDF p. 207 | For every smooth `ρ` on a flat `B`-module `V` such that `fixedVectors ρ K` is finitely generated over `B` for every compact open `K` of `G(F)`, `fixedVectors (leviJacquetRepresentation p l r hp hr hl hmul ρ) K'` is finitely generated over `B` for every compact open `K'` of `M(F)` |

## Correspondence notes

1. The hypotheses are exactly those of an admissible `(G, B)`-module in the
   sense of VI.8.1: smoothness, flatness over `B` and finite generation of every
   compact-open fixed module. The `B`-linearity of the action is built into
   `Representation B`.
2. The source's conclusion is that `r_P^G(V)` is an admissible `(M, B)`-module.
   That consists of three properties. Flatness is the VI.8.3 claim, stated by
   Worker 709 as `JacquetFlatStatement` in the sibling module
   `RenardFamilyParabolicFlatnessStatements` (accepted as candidate
   `ec9f856f-48d8-4387-9bc8-0e7f08049065`, not yet in the Library at commit
   `7e84f6ad`). Smoothness is the published law `isSmooth_jacquetRepresentation`
   for the Jacquet family of a subgroup decomposition; this module asserts no
   smoothness for the transported family of `M(F)`. The remaining property,
   finite generation of the compact-open fixed modules, is what
   `JacquetAdmissibleStatement` states. So this statement, Worker 709's flatness
   statement and the smoothness of the transported family together give
   Renard's claim.
3. The flatness hypothesis on `V` is part of the source's notion of a
   `(G, B)`-module and is kept, although the finiteness argument below does not
   use it.
4. The fixed vectors are taken for the normalized action, as in the source,
   where `r_P^G` is normalized. On a compact subgroup of `M(F)` the modulus
   character is trivial, so these are also the fixed vectors of the unnormalized
   action on `V_N`; the statement does not use this.
5. The functor `r_P^G : M(G, B) → M(M, B)` is not bundled; the statement is
   about objects.

## Proof route in the source

The source refers to the proof of the VI.6.1 Corollary. For a compact open
subgroup `K` of `G` with an Iwahori decomposition along `P`, the Jacquet lemma
gives a surjection `V^K → (V_N)^{K_M}`, `K_M = K ∩ M`, and such `K_M` form a
basis of neighbourhoods of the identity of `M`. In the family setting `V^K` is
infinite-dimensional over `ℂ`, so the needed surjection is the generalized
Jacquet lemma of VI.9.1, which assumes no admissibility. The surjection is
`B`-linear, so `(V_N)^{K_M}` is a finitely generated `B`-module. Every compact
open subgroup of `M` contains such a `K_M`, and the fixed module of the larger
group is a `B`-submodule of `(V_N)^{K_M}`; as `B` is Noetherian, it is again
finitely generated.

## Relation to published work

At Library commit `7e84f6ad`:

- [ArbitraryParabolicJacquetAdmissibilityStatement](../Exponents/ArbitraryParabolicJacquetAdmissibilityStatement.md)
  (Worker 15) is the complex VI.6.1 Corollary for every represented parabolic.
  It is not proved, and it does not imply this statement, because a
  `(G, B)`-module need not be admissible as a complex representation;
- the VI.9.1 Theorem is the published `GeneralizedJacquetLemmaStatement` of
  [UniformCompressionStabilizationStatement](../Exponents/UniformCompressionStabilizationStatement.md),
  stated for complex coefficients and for the dynamic parabolic of a
  cocharacter. It is not proved; `generalizedJacquetLemma_of_uniformCompressionStabilization`
  derives it from the companion uniform stabilization statement. A proof of
  `JacquetAdmissibleStatement` along the source's route would apply it to the
  underlying complex representation of `V` and relate the dynamic parabolic to
  the represented one.

No theorem of the Library proves `JacquetAdmissibleStatement`. Its proof is a
separate obligation.
