# Renard VI.8.1 and VI.8.4: statements for general algebraic families

This module contains **statements**: five closed `Prop`-valued definitions and
their closed conjunction `Statements`, in namespace
`Langlands.Renard.AlgebraicFamily`. It proves none of them.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**:

- VI.8.1, "`(G, B)`-modules": the Definition, the Proposition and its proof, the
  Remark, the specialization paragraph and the Lemma with its proof, printed
  pp. 187–189 / PDF pp. 193–195.
- VI.8.4, "Utilisation de la platitude": the opening paragraph and the Theorem,
  printed p. 191 / PDF p. 197, with the proof reference on printed p. 192 /
  PDF p. 198.
- Localization of rings and modules: A.III.1, Examples 3 and 4, printed p. 252 /
  PDF p. 258, which VI.8.4 cites for `M_f`.
- t.d. spaces and groups: II.1.1, printed p. 30 / PDF p. 36.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 checked this hash and read PDF pages 193–195, 197–198 and 258.

The standing hypothesis of VI.8.1 is: "Soit `B` une `C`-algèbre commutative
noethérienne de type fini réduite". VI.8.4 repeats it. A `(G, B)`-module is
"un `C`-espace vectoriel `V` muni d'une représentation lisse `(π, V)` de `G` et
d'une structure de `B`-module plat, où les deux actions commutent". It is
admissible if `V^K` is finitely generated over `B` for every compact open
subgroup `K`.

## Lean model

Each statement quantifies over:

- `B : Type uB` with `[CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
  [Algebra.FiniteType ℂ B] [IsReduced B]`. These are the source's hypotheses
  on `B`, with no others.
- `G : Type uG` with `[Group G] [TopologicalSpace G] [IsTopologicalGroup G]` and
  the hypothesis `Langlands.Topology.IsLocallyProfinite G` (Hausdorff, with a
  basis of compact open neighbourhoods). This is the t.d. group of II.1.1,
  which Chapter VI uses for `G`.
- `V : Type uV` with `[AddCommGroup V] [Module B V]` and
  `ρ : Representation B G V`. Each `ρ g` is `B`-linear, so the actions of `G`
  and `B` commute. The source's complex structure on `V` is the one obtained
  from `B` through `ℂ → B`. Smoothness is `Langlands.IsSmooth ρ`: every vector
  is fixed by some open subgroup. Flatness is the separate hypothesis
  `Module.Flat B V`. No structure or category of `(G, B)`-modules is defined.
- A compact open subgroup is `K : OpenSubgroup G` together with
  `IsCompact (K : Set G)`. Its fixed vectors are the `B`-submodule
  `Langlands.fixedVectors ρ K.toSubgroup`.

## Declarations

| Declaration | Source | Statement |
| --- | --- | --- |
| `FixedTensorComparisonStatement` | Proof of the VI.8.1 Proposition, PDF p. 194 | For smooth `ρ`, compact open `K` and every `B`-module `E : Type uE`, the map `(fixedVectors ρ K).subtype.lTensor E : E ⊗[B] V^K → E ⊗[B] V` is injective and its range is `fixedVectors ((Representation.trivial B G E).tprod ρ) K` |
| `FlatnessCriterionStatement` | VI.8.1 Remark, PDF p. 194 | For smooth `ρ`: `Module.Flat B V` if and only if `Module.Flat B (fixedVectors ρ K)` for every compact open `K` |
| `AdmissibilityCriterionStatement` | VI.8.1 Proposition, PDF p. 193 | For smooth `ρ`: `V` is flat with every compact-open `V^K` finite if and only if every compact-open `V^K` is finite and projective |
| `SpecializationAdmissibilityStatement` | VI.8.1 Lemma, PDF p. 195 | For smooth flat `ρ` with every compact-open `V^K` finite, and every `χ : B →ₐ[ℂ] ℂ`, the representation `g ↦ (ρ g).baseChange ℂ` on `ℂ ⊗[B] V`, with `B` acting on `ℂ` through `χ`, is `Langlands.IsAdmissible` |
| `LocalFreeCoverStatement` | VI.8.4 Theorem, PDF p. 197 | A `B`-module `M : Type uM` is finite and projective if and only if there are `r : ℕ` and `f : Fin r → B` with `Ideal.span (Set.range f) = ⊤` such that each `LocalizedModule (Submonoid.powers (f i)) M` is finite and free over `Localization.Away (f i)` |
| `Statements` | — | The conjunction of the five, with universe parameters `uB, uG, uV, uE, uM` |

Each assertion keeps all the source's hypotheses, even where its proof does not
need them. In particular, `IsLocallyProfinite G` and the Noetherian, finite-type
and reduced hypotheses on `B` appear in every statement that the source makes
under them.

## Correspondence notes

1. `FixedTensorComparisonStatement`. The source's proof asserts: "pour tout
   `B`-module `E`, le morphisme naturel `E ⊗_B V^K → (E ⊗_B V)^K` est un
   isomorphisme dont l'inverse est donné par `e ⊗ v ↦ e ⊗ e_K · v`". The
   statement encodes "isomorphism onto `(E ⊗_B V)^K`" as injectivity plus
   equality of the range with the fixed vectors. `G` acts on `E ⊗[B] V` through
   the second factor, as `(Representation.trivial B G E).tprod ρ`; the source
   leaves this action implicit. The formula for the inverse through the
   idempotent `e_K` is not stated. The source's proof uses `V^K` only for
   compact open `K`, and so does the statement.
2. `FlatnessCriterionStatement`. The Remark reads: "`V` est plat en tant que
   `B`-module si et seulement si tous les `V^K` le sont, lorsque `K` décrit
   l'ensemble des sous-groupes ouverts compacts de `G`". Its hypotheses are
   those of the Proposition: a smooth representation and a commuting
   `B`-module structure, with no flatness.
3. `AdmissibilityCriterionStatement`. The Proposition reads: "`V` est un
   `(G, B)`-module admissible si et seulement si pour tout sous-groupe ouvert
   compact `K` de `G`, `V^K` est un `B`-module projectif de type fini". The left
   side spells out "admissible `(G, B)`-module" for the given smooth `ρ`: `V` is
   flat and every compact-open `V^K` is finitely generated (`Module.Finite`).
4. `SpecializationAdmissibilityStatement`. The source identifies points
   `χ ∈ S` with unital algebra morphisms `B → C`, defines the specialization
   `V_χ = V ⊗_B B/I_χ = V ⊗_B C_{Ψ_χ}`, where `b · z = Ψ_χ(b) z`, and says that
   it is still a smooth representation of `G`. The Lemma reads: "Si `V` est un
   `(G, B)`-module admissible, alors pour tout `χ ∈ S`, `V_χ` est une
   représentation admissible de `G`". In Lean the point is `χ : B →ₐ[ℂ] ℂ`.
   The local instance `χ.toRingHom.toAlgebra` makes `b • z = χ b * z` on `ℂ`,
   which is `C_{Ψ_χ}`. The fiber is `ℂ ⊗[B] V`, with the factors in the opposite
   order to the source's `V ⊗_B C_{Ψ_χ}`; the two are isomorphic by the
   commutativity of the tensor product. Its complex structure comes from the
   factor `ℂ`, and `g` acts by `Module.End.baseChangeHom B ℂ V (ρ g)`, that is
   `v ⊗ z ↦ ρ(g) v ⊗ z` in the source's order.
   The conclusion `Langlands.IsAdmissible` consists of smoothness and
   finite-dimensionality of the fixed vectors of every open subgroup, not only
   of every compact open subgroup. Here this is the source's notion: in a t.d.
   group every open subgroup `H` contains a compact open subgroup `K`, and then
   `(ℂ ⊗[B] V)^H ⊆ (ℂ ⊗[B] V)^K`. This equivalence is Worker 709's remark and is
   not checked in Lean.
5. `LocalFreeCoverStatement`. The Theorem reads: "Un `B`-module `M` est
   projectif de type fini si et seulement s'il existe des éléments
   `(f_i)_{i=1,…,r}` de `B` engendrant `B` sur lui-même, tels que pour tout
   `i = 1, …, r` la localisation `M_{f_i}` soit un `B_{f_i}`-module libre de
   type fini". "Engendrant `B` sur lui-même" is `Ideal.span (Set.range f) = ⊤`.
   `B_f` is `Localization.Away f`, the localization at the powers of `f`, and
   `M_f` is `LocalizedModule (Submonoid.powers f) M` with its module structure
   over `Localization.Away f`, as in A.III.1, Examples 3 and 4. The paragraph
   before the Theorem introduces `B_f` for nonzero `f`; the Theorem itself does
   not restrict the `f_i`, and neither does the statement. Zero members can be
   dropped from a generating family, and their localizations are zero, so the
   two readings are equivalent.

The source proves the Theorem by citing Bourbaki, *Algèbre commutative*,
Chapter II, §5, Theorem 1 ([8]). The statement keeps the source's hypotheses on
`B`.

## Relation to published work

The published `Langlands.Plancherel.RationalNormalized.flat_of_smooth_fixed_flat`, in
[UnramifiedRationalNormalizedInducedFinitenessProof](../Plancherel/UnramifiedRationalNormalizedInducedFinitenessProof.md),
proves the sufficient direction of `FlatnessCriterionStatement` for a locally
compact nonarchimedean group over any commutative ring. Mathlib's
`Module.finitePresentation_of_finite`,
`Module.Flat.projective_of_finitePresentation`,
`Module.basicOpen_subset_freeLocus_iff` and
`Module.FinitePresentation.exists_free_localizedModule_powers` concern the
algebra behind `AdmissibilityCriterionStatement` and
`LocalFreeCoverStatement`. None of them is any of the five statements, and none
is used here. The VI.8 progress note,
`notes/renard/algebraic-families-progress.md`, lists these assertions as
unpublished items 2, 3, 4 and 8.

## Environment

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`. The project imports are
`Langlands.Representation.Smooth.Definitions` (`fixedVectors`, `IsSmooth`,
`IsAdmissible`) and `Langlands.Topology.LocallyProfinite`
(`IsLocallyProfinite`). No construction or axiom is introduced. Proofs belong
to separate proof tasks, which must prove these declarations unchanged.
