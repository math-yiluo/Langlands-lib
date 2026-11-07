# Renard VI.8.6: endomorphisms of an admissible family with irreducible fibers

This module contains one **statement**, the closed `Prop`-valued definition
`Langlands.Renard.AlgebraicFamily.EndomorphismScalarStatement`, with universe
parameters `uB, uG, uV`. It proves nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**:

- VI.8.6, "Une autre application": the opening paragraph, printed p. 194 /
  PDF p. 200, and the paragraph on matrices, the Proposition and its proof,
  printed p. 195 / PDF p. 201.
- The setting it refers to, "la situation de VI.8.4, avant l'énoncé de la
  proposition": printed p. 192 / PDF p. 198.
- `(G, B)`-modules, admissibility and specialization: VI.8.1, printed
  pp. 187–189 / PDF pp. 193–195.
- Irreducible representations: III.1.4, printed p. 60 / PDF p. 66, which
  transfers the terminology of A.VI.3 to smooth representations.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 checked this hash and read PDF pages 66, 140, 193 and 198–201.

The setting on PDF p. 198 reads: "Soit `(π, V)` un `(G, B)`-module admissible,
et soit `φ` un morphisme de `(G, B)`-module de `V` dans lui-même". VI.8.6 opens
with: "Dans ce contexte, soit `Ξ` un ensemble de points Zariski dense dans `S`
(comme `B` est réduite, les `x ∈ Ξ` séparent les éléments de `B`)". The
Proposition reads: "Supposons que pour tout `x ∈ Ξ`, la spécialisation en `x`
de `V` soit irréductible. Alors `φ` est l'action d'un élément `b ∈ B`".

## Lean model

The binders are those of the sibling module
[RenardFamilyStatements](RenardFamilyStatements.md):

- `B : Type uB` with `[CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
  [Algebra.FiniteType ℂ B] [IsReduced B]`, the standing hypothesis of VI.8.1:
  "une `C`-algèbre commutative noethérienne de type fini réduite".
- `G : Type uG` with `[Group G] [TopologicalSpace G] [IsTopologicalGroup G]`
  and `Langlands.Topology.IsLocallyProfinite G`.
- `V : Type uV` with `[AddCommGroup V] [Module B V]` and
  `ρ : Representation B G V`, so the actions of `G` and `B` commute.
- "`(G, B)`-module admissible" is spelled out as three hypotheses:
  `Langlands.IsSmooth ρ`, `Module.Flat B V`, and `Module.Finite B` of
  `Langlands.fixedVectors ρ K.toSubgroup` for every `K : OpenSubgroup G` with
  `IsCompact (K : Set G)`.
- The morphism of `(G, B)`-modules is `φ : V →ₗ[B] V` with
  `φ (ρ g v) = ρ g (φ v)` for all `g` and `v`.
- The points of `S` are `χ : B →ₐ[ℂ] ℂ`, as in VI.8.1, and `Ξ` is a
  `Set (B →ₐ[ℂ] ℂ)`.
- Zariski density of `Ξ` is the hypothesis: every `b : B` with `χ b = 0` for
  all `χ ∈ Ξ` satisfies `χ b = 0` for every `χ : B →ₐ[ℂ] ℂ`.
- The specialization at `χ ∈ Ξ` is the one of
  `SpecializationAdmissibilityStatement`: the local instance
  `χ.toRingHom.toAlgebra` makes `B` act on `ℂ` through `χ`, the space is
  `ℂ ⊗[B] V`, and `g` acts by `Module.End.baseChangeHom B ℂ V (ρ g)`. Its
  irreducibility is Mathlib's `Representation.IsIrreducible`, that is
  `IsSimpleOrder` of its lattice of subrepresentations.
- The conclusion is `∃ b : B, ∀ v : V, φ v = b • v`.

## Declaration

| Declaration | Source | Statement |
| --- | --- | --- |
| `EndomorphismScalarStatement` | VI.8.6 Proposition, PDF p. 201, in the setting of PDF p. 198 | For smooth flat `ρ` with every compact-open `V^K` finite, every `G`-equivariant `φ : V →ₗ[B] V` and every Zariski-dense `Ξ`, if the specialization at every point of `Ξ` is irreducible, then `φ` is the action of some `b : B` |

## Correspondence notes

1. Zariski density. The Zariski closed subsets of `S` are the common zero
   sets `Z(T)` of subsets `T ⊆ B`. The closure of `Ξ` is therefore `Z(I)`,
   where `I` is the set of elements of `B` vanishing at every point of `Ξ`.
   So `Ξ` is dense exactly when every element of `I` vanishes at every point of
   `S`, which is the Lean hypothesis. This equivalence is Worker 709's remark
   and is not checked in Lean. The source's parenthetical, that the points of
   `Ξ` separate the elements of `B`, says that `I = 0`. Because `B` is reduced
   and of finite type over `ℂ`, it follows from density by the
   Nullstellensatz, as the source's "comme `B` est réduite" indicates. It is a
   consequence, not a hypothesis, so the statement does not assume it.
2. Irreducibility. By III.1.4 the source calls a smooth representation
   irreducible when it is a simple object of `M(G)`: nonzero, with no
   subrepresentations other than `0` and itself. `IsSimpleOrder` expresses
   the same condition for all subrepresentations. These are the same for a
   smooth representation, because its subrepresentations are smooth. The
   fiber is smooth, since each `z ⊗ v` is fixed by the open subgroup fixing
   `v`. The source calls `sp_x(V)` "la spécialisation en `x` de `V`" and
   writes it `V ⊗_B C_{Ψ_x}`. The Lean fiber puts the factors in the opposite
   order, as in note 4 of
   [RenardFamilyStatements](RenardFamilyStatements.md).
3. The setting on PDF p. 198 also chooses a compact open `K`, elements
   `f_i` with `V^K_{f_i}` free, and the specializations `sp_x(φ)` and
   `sp_x(φ_K)`. VI.8.6 then fixes a basis of `V^K_f` and the matrix of
   `φ_{K,f}`. These choices belong to the proof, and the statement does not
   mention them.
4. The group. Chapter VI fixes `G`: "Dans tout ce chapitre, `G` désigne un
   groupe réductif `p`-adique au sens du chapitre précédent" (printed p. 134 /
   PDF p. 140). The statement is made, like those of the sibling module, for every
   locally profinite `G`, which is a generalization. Worker 709 checked that
   the source's proof works in this generality. The source invokes Schur's
   lemma, whose version III.1.8 assumes `G` countable at infinity. Here the
   fiber is admissible by the VI.8.1 Lemma, and for an admissible irreducible
   representation `W` Schur's lemma needs no countability. Choose a compact
   open `K` with `W^K ≠ 0`; an endomorphism `ψ` preserves the
   finite-dimensional space `W^K` and has an eigenvalue `λ` on it; the kernel
   of `ψ − λ` is then a nonzero subrepresentation, hence all of `W`. The
   gluing at the end of the proof is detailed in reading note 6 of the
   [VI.8 note](../../../notes/renard/algebraic-families-progress.md). Neither
   check is in Lean.

## Relation to published work

The sibling module [RenardFamilyStatements](RenardFamilyStatements.md) states
the VI.8.1 Proposition (`AdmissibilityCriterionStatement`), the specialization
Lemma (`SpecializationAdmissibilityStatement`), the comparison of fixed
vectors of tensor products (`FixedTensorComparisonStatement`) and the VI.8.4
Theorem (`LocalFreeCoverStatement`). A proof following the source can use
them; all four are unproved at Library `eec7519b`. This module does not
import them. The VI.8 progress note lists the Proposition as
(P6), with no published statement at Library `eec7519b`. The example after the
Proposition, (Ex6), about the universal induced family of an irreducible
supercuspidal representation, is not stated here.

## Environment

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`. The project imports are
`Langlands.Representation.Smooth.Definitions` (`fixedVectors`, `IsSmooth`) and
`Langlands.Topology.LocallyProfinite` (`IsLocallyProfinite`). No construction
or axiom is introduced. A proof belongs to a separate proof task, which must
prove this declaration unchanged.
