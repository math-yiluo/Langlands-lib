# Unitary constituents of an admissible finite-length character limit

Authors: Worker 607 (draft), Worker 5 (revision).

This module states
`Langlands.UnitaryCharacterLimitSubquotientsStatement.{uG, uV}`
in `Langlands/Representation/Unitary/CharacterLimitSubquotientsStatement.lean`.
**It is not proved here.** It is a Prop-valued definition with no axioms,
no `sorry` and no assumed structure fields. The group universe `uG` and the
carrier universe `uV` are independent level parameters.

## The Lean proposition

The statement quantifies over the following data, in this order.

- A group `G : Type uG` with a topology making it a topological group that
  is Hausdorff (`T2Space`), locally compact, totally disconnected and
  second countable.
- A measurable structure on `G` that is its Borel structure (`BorelSpace`).
- A measure `μ` with `μ.IsHaarMeasure` (a left Haar measure), `μ.Regular`,
  and `Measure.IsMulRightInvariant μ`. So `μ` is a two-sided Haar measure
  and `G` is unimodular.
- A sequence `π : ℕ → SmoothRep.{0, uG, uV} ℂ G` with
  `hπ : ∀ k, IsAdmissible (π k).representation`.
- A representation `ρ : SmoothRep.{0, uG, uV} ℂ G` with
  `hρ : IsAdmissible ρ.representation`.

Under the following hypotheses:

1. every `π k` is irreducible (`Representation.IsIrreducible`);
2. every `π k` is unitarizable (`IsUnitarizable`);
3. `ρ` has finite length (`SmoothRep.HasFiniteLength`);
4. for every `f : SchwartzBruhat G`, the complex numbers
   `Character.distribution μ (π k).representation (hπ k) f` tend to
   `Character.distribution μ ρ.representation hρ f` as `k → ∞`
   (`Tendsto … atTop (𝓝 …)`).

The conclusion is that every `τ : SmoothRep.{0, uG, uV} ℂ G` that is
irreducible and satisfies `SmoothRep.IsSubquotient τ ρ` is unitarizable.

All objects are actual Library objects.

- `SmoothRep.{0, uG, uV} ℂ G` is a smooth complex representation whose
  carrier lies in `Type uV`. The sequence, the limit and the subquotient use
  the same carrier universe. Their carriers need not be equal.
- `IsAdmissible` is the Library's all-open-subgroups convention: the
  representation is smooth and the fixed vectors of every open subgroup form
  a finite-dimensional space.
- `Character.distribution μ σ hσ f` is the trace of the finite-rank
  integrated operator `v ↦ ∫ f(g) σ(g) v dμ(g)`. `SchwartzBruhat G` is the
  space of compactly supported locally constant complex functions on `G`.
- `SmoothRep.HasFiniteLength ρ` is finite composition length of the carrier
  as a module over the group algebra `ℂ[G]`. The carrier itself need not be
  finite-dimensional.
- `SmoothRep.IsSubquotient τ ρ` gives an actual subrepresentation `S` of `ρ`,
  an actual subrepresentation `S'` of `S`, and an isomorphism of smooth
  representations from `τ` to `S / S'`.
- `IsUnitarizable` means that the carrier has a positive definite Hermitian
  form preserved by every `σ(g)`. No completion, norm or topology is chosen.

The statement supplies no Hilbert space, chosen decomposition, selected
constituent or common model for the `π k`.

## Source

Marko Tadic, *Classification of unitary representations in irreducible
representations of general linear group (non-archimedean case)*, Ann. Sci.
ENS (4) 19 (1986), 335–382, registered as `tadic-1986-unitary`. A PDF page
number is the printed page number minus 333.

- §2.6, printed p.346 (PDF p.13). `G` is the group of `F`-rational points of
  a connected reductive linear algebraic group over a nonarchimedean local
  field `F`. `H(G)` is its Hecke algebra and `H(G, K)` its subalgebra of
  `K`-bi-invariant functions. `Ĝ` is the set of classes of irreducible
  unitarizable representations and `G̃` the set of classes of irreducible
  smooth representations. `ch_π` is the character of `π`.
- Theorem 2.7(i), printed pp.346–347 (PDF pp.13–14): "Let `(π_n)` be a
  sequence in `Ĝ` such that for each `f ∈ H(G)` there exists a finite limit
  `lim_n ch_{π_n}(f)` in the complex numbers. Then there exist `n_σ ∈ ℤ₊`,
  `σ ∈ Ĝ`, such that `lim_n ch_{π_n}(f) = Σ_{σ∈Ĝ} n_σ ch_σ(f)` for each
  fixed `f ∈ H(G)`. … If we have numbers `m_σ ∈ ℤ₊`, `σ ∈ G̃`, such that
  `Σ_{σ∈G̃} m_σ ch_σ(f) = Σ_{σ∈Ĝ} n_σ ch_σ(f)` for all `f ∈ H(G)` then
  `m_σ = 0` for `σ ∈ G̃ \ Ĝ`, and `n_σ = m_σ` for `σ ∈ Ĝ`."
- Proof, printed pp.347–350 (PDF pp.14–17). Tadic takes a descending basis
  `(K_m)` of compact open subgroups at the identity. He bounds
  `dim V_n^{K_m}` uniformly in `n` by Bernstein's uniform admissibility. He
  bounds the operator norm of `π_n(f)` on `V_n^{K_m}` by `∫ |f(g)| dg`. He
  passes to a diagonal subsequence of unitary `H(G, K_m)`-modules. The limit
  is an admissible representation with an invariant inner product, since
  `(π(f)v, w) = (v, π(f*)w)` with `f*(g) = conj f(g⁻¹)`. It is therefore a
  direct sum of irreducible unitarizable representations with finite
  multiplicities. Uniqueness uses linear independence of the characters of
  inequivalent `H(G, K)`-modules.
- Remark on p.350 (PDF p.17): D. Milicic's description of the dual topology
  gives unitarizability of the irreducible subquotients at the ends of
  complementary series of reductive groups over any local field.
- Proposition 2.9, p.350 (PDF p.17), for `GL_n`, derives unitarity of all
  composition factors at the end-point `α₀` of a complementary series from
  Bernstein's Proposition 8.3, Theorem 2.7 and Lemma 2.8.

## Comparison with the source

**Agreement on connected reductive groups.** Let `G` be as in Tadic §2.6.
Then the Lean hypotheses on `G` hold. `SchwartzBruhat G` is `H(G)`, and
`Character.distribution μ` is Tadic's `ch` for the Haar measure `μ`. A
sequence `π k` as in the Lean statement is a sequence in `Ĝ`. Its
admissibility is then automatic, because irreducible smooth representations
of such groups are admissible. Hypothesis 4 gives the limit required by
Theorem 2.7(i).

The Lean conclusion follows from the source theorem as follows. Let
`τ_1, …, τ_r` be the composition factors of `ρ`. They are irreducible, so
their classes lie in `G̃`. Characters are additive on short exact sequences
(the Library's `Character.distributionShortExactAdditivity`), so
`ch_ρ = Σ_i ch_{τ_i}`. This is an expansion `Σ_{σ∈G̃} m_σ ch_σ` with
`m_σ ∈ ℤ₊`. The existence part of Theorem 2.7(i) writes the same limit as
`Σ_{σ∈Ĝ} n_σ ch_σ`. The uniqueness part then gives `m_σ = 0` for every
non-unitarizable `σ`, so every `τ_i` is unitarizable. By the Jordan–Hölder
theorem, every irreducible subquotient `τ` of `ρ` is isomorphic to some `τ_i`.

**Differences from the source.**

- *Group scope (derived).* The Lean statement concerns every Hausdorff,
  locally compact, totally disconnected, second countable group with a
  two-sided Haar measure. The source assumes a connected reductive group.
  The next section explains why this derived scope is sound. The source
  citation alone does not establish it.
- *The limit is given.* The source only assumes that the limit exists. The
  Lean statement assumes that the limit is the character of a given admissible
  finite-length `ρ`. So the existence of an expansion
  `Σ n_σ ch_σ`, its local finiteness and Bernstein's uniform admissibility are
  not needed.
- *Explicit admissibility.* Admissibility of the `π k` and of `ρ` is an
  explicit hypothesis. It is needed to define their characters for a general
  group.
- *Narrower conclusion.* The Lean statement asserts only the
  constituent-unitarity consequence above. It claims neither the expansion,
  nor `n_σ = m_σ`, nor 2.7(ii) (subsequence convergence), nor 2.7(iii)
  (finiteness of limits).

## Why the derived scope is sound

The following outline shows that the statement is plausible in its stated
generality. It is not a Lean proof, and the proof is left to a successor task.
It adapts Tadic's proof to one compact open subgroup at a time.

Let `K` be a compact open subgroup of `G`. Such subgroups exist and form a
neighbourhood basis of the identity, by total disconnectedness and local
compactness. Let `e_K = μ(K)⁻¹ 1_K ∈ SchwartzBruhat G`. For admissible `σ`,
`σ(e_K)` is the projection onto `σ^K`. Hence
`Character.distribution μ σ hσ e_K = dim σ^K`. For `f` bi-invariant under
`K`, the character is the trace of `σ(f)` on `σ^K`
(`Character.distribution_eq_fixedVectors`).

1. *Dimensions.* Hypothesis 4 at `e_K` gives `dim (π k)^K → dim ρ^K`. These
   are natural numbers, so `dim (π k)^K = d := dim ρ^K` for all large `k`.
2. *Unitary corners.* Use an invariant form on `π k`. Then `π k(f)` and
   `π k(f*)` are adjoint on `(π k)^K`, where `f*(g) = conj f(g⁻¹)`. This
   uses the right invariance of `μ`. Also the operator norm of `π k(f)` is at
   most `∫ |f| dμ`. Let `H(G, K)` be the algebra of `K`-bi-invariant test
   functions. In orthonormal bases of the `(π k)^K`, for each `f ∈ H(G, K)`
   the matrices of `π k(f)` on `ℂ^d` lie in a compact set independent of
   `k`. By Tychonoff's theorem the sequence has a cluster point `σ_K`.
   It is a unital `*`-representation of `H(G, K)` on `ℂ^d` whose trace is the
   character of `ρ` on `H(G, K)`. Tadic instead uses a diagonal subsequence
   along a countable basis.
3. *Composition factors.* A `*`-representation on a finite-dimensional
   Hilbert space is semisimple. Traces of pairwise non-isomorphic simple
   finite-dimensional modules over a complex algebra are linearly independent
   (density theorem). So the `H(G, K)`-modules `ρ^K` and `σ_K` have the same
   composition factors with multiplicities. Every simple subquotient of
   `ρ^K` therefore carries a positive definite form for which `f*` is
   adjoint to `f`.
4. *Gluing.* Let `τ` be an irreducible subquotient of `ρ`. Taking
   `K`-fixed vectors is exact, so `τ^K` is a subquotient of `ρ^K`. It is zero
   or simple over `H(G, K)`
   (`CompactCoefficientClass.isSimpleModule_fixedVectors`, after
   Bernstein–Zelevinsky 1976, 2.10). By Schur's lemma such a form on a simple
   `τ^K` is unique up to a positive scalar. Fix `K₀` and a nonzero
   `v₀ ∈ τ^{K₀}`. Normalize the forms on `τ^K` for compact open `K ⊆ K₀` by
   `⟨v₀, v₀⟩ = 1`. Uniqueness makes them compatible on the directed union
   `τ = ⋃ τ^K`.
5. *Invariance.* Let `g ∈ G` and `v, w ∈ τ^L` with `L ⊆ K₀` compact open.
   The function `f = μ(L)⁻¹ 1_{gL}` is bi-invariant under
   `L ∩ gLg⁻¹`. It satisfies `τ(f)v = τ(g)v` and, by right invariance,
   `τ(f*)τ(g)w = w`. Apply the adjoint identity on `τ^{L ∩ gLg⁻¹}`. This
   gives `⟨τ(g)v, τ(g)w⟩ = ⟨v, w⟩`, so `τ` is unitarizable.

The outline uses the topological hypotheses, unimodularity, and admissibility
of the `π k` and of `ρ`. It does not use second countability, the regularity
of `μ`, irreducibility of the `π k` or finite length of `ρ`. These hypotheses
are kept because this task fixes the interface. They only narrow the
statement and hold in the intended application.

As in the source, the argument needs **all** irreducible constituents. One
limiting positive semidefinite form on `ρ` would only make one quotient of
`ρ` unitarizable. That does not cover every irreducible subquotient.

Library material for a later proof includes `Hecke.HeckeAlgebra.Corner`,
`Hecke.cornerModule`, `Character.distribution_eq_fixedVectors`,
`CompactCoefficientClass.isSimpleModule_fixedVectors`,
`Character.finiteFamilyLinearIndependence` (Bernstein–Zelevinsky 1976,
Proposition 2.19), `Character.distributionShortExactAdditivity` and
`AdmissibleUnitarySemisimplicityStatement`.

## Applicability to `GL_n` over every `PadicField`

Take `p` prime, `F : PadicField.{uF} p`, `T : F.TopologicalData` and
`G = GeneralLinear (m + 1) F.Carrier` with `T.topology`. Then every
hypothesis on `G` and `μ` is available from the Library.

- Topological group: `T.generalLinearTopologicalGroup`.
- Hausdorff: `T.generalLinearT2Space`.
- Locally compact: `T.generalLinearLocallyCompactSpace`.
- Second countable: `T.generalLinearSecondCountableTopology`.
- Totally disconnected: through the nonarchimedean topology of `F.Carrier`
  and the embedding of `GL` into matrices.
- Measure: the Borel structure, and
  `μ = RankinSelberg.generalLinearHaar F.Carrier m`. This measure is a Haar
  measure, is regular and is right invariant
  (`RankinSelberg.generalLinearHaar_isHaar`,
  `RankinSelberg.generalLinearHaar_regular`,
  `RankinSelberg.generalLinearHaar_isMulRightInvariant`).

The levels `.{uF, max uF uV}` match the carrier universe of
`Classification.ComplementarySeriesUnitarity`. A private development probe
compiled the specialization of
`UnitaryCharacterLimitSubquotientsStatement.{uF, max uF uV}` to these data
for every `p`, `F`, `T` and `m`. It used `lean_check` diagnostic
`6230f014-e20c-473a-bdf8-e8e315626d17`. That consumer uses `GL_(2n)` with
`0 < n`. Any Haar measure may be chosen, since the conclusion does not
mention `μ`.

## Consumer

The intended consumer is the end-point clause of
`Langlands.Classification.ComplementarySeriesUnitarity` (Tadic 1986,
Proposition 2.9). Take parameters `α_k` in the open interval tending to `α₀`.
Let `π k` be the complementary products at `α_k` and `ρ` the product at
`α₀`. The following remain separate obligations of that proof:

- irreducibility and unitarity at the interior parameters (hypothesis and
  first clause of Proposition 2.9);
- admissibility of these products;
- finite length at the end-point;
- convergence of characters (Tadic's Lemma 2.8).

None is inferred here.

## Validation

`lean_check` diagnostic `1e59aebf-96e8-48dc-a2cf-f27386624a34` compiled
this module in place without errors or warnings. It reported a proposition-valued
definition with level parameters `uG` and `uV`. The only axioms were
`propext`, `Classical.choice` and `Quot.sound`. This check provides neither a
proof nor semantic acceptance.
