# Weil restriction of algebraic spaces and rational points

Author: Worker 105.
Markdown correction: Worker 172, following Worker 111's source diagnosis and
published counterexample.

`SpaceWeilRestrictionStatement` states Lemma 5.10, and
`HenselianWeilRestrictionPointHomeomorphStatement` states Proposition 5.11(1), of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
pp.17–18. The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only states
these results and contains no proofs.

## Correction to the literal Proposition 5.11(1)

Conrad's literal Proposition 5.11(1), and the faithfully transcribed
`HenselianWeilRestrictionPointHomeomorphStatement`, are false for some finite
purely inseparable extensions of incomplete henselian valued fields. The
proof on printed p.18 invokes the affine comparison of Example 2.4 (printed
p.3), which assumes the module topology on the finite extension. Henselianity
alone does not provide that hypothesis.

The corrected successor is
[`HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement`](HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement.md).
It adds exactly `IsModuleTopology K K'` to the original hypotheses and retains
the existence of the algebraic-space Weil restriction and the homeomorphism
of its canonical rational-point equivalence for the independently defined
étale-chart topologies. It allows arbitrary finite extensions, archimedean
and nonarchimedean fields, and incomplete fields satisfying that topology
hypothesis. It adds no separability, completeness, local separatedness,
separatedness, smoothness or scheme assumption. Complete `K` supplies
`IsModuleTopology K K'` for finite-dimensional normed extensions, by Mathlib's
`isModuleTopologyOfFiniteDimensional`.

For a concrete obstruction, choose `s ∈ F_p((t))` transcendental over `F_p(t)`,
let `K` be the henselization of `F_p(t,s^p)` inside `F_p((t))`, and put
`L = K(s)`, with restricted `t`-adic norms. Then `[L:K] = p`, both fields
are henselian, and `K` is dense proper in `L`. For `Y' = A¹_L`, the canonical
bijection `Res(Y')(K) = K^p → L` sends `(x_i)` to `Σ_i x_i s^i`. If
Laurent-polynomial truncations `a_n ∈ K` tend to `s`, the vectors
`(-a_n,1,0,...)` do not tend to zero, while their images `s-a_n` do.
The inverse is therefore discontinuous.

The valued-field ingredients are from Michael Temkin, *Valued Fields*
(course notes), Exercise 1.8.11(i)–(ii), printed p.22, and Remark 1.9.6,
printed p.25, together with Lemma 1.9.3(ii), p.24, and Theorem 1.9.5 and
Section 1.9.7, p.25. Registered source:
`temkin-valued-fields-2018-course-notes`, SHA-256
`60cbfd7681abcb39ee111aff005434bd6b11054089cf48a78068c97e3d53abe3`.
The year in the source ID is a registration label; the PDF gives no date.
The counterexample to Weil restriction is a derived application of those
examples, explained in the corrected statement's Markdown and
[Worker 111's obstruction note](../../../notes/conrad-adelic/finite-weil-inseparable-obstruction.md).
It is not a Lean refutation in this module.

This is a Markdown-only correction. `SpaceWeilRestrictionStatement.lean`,
including both proposition definitions, is unchanged. Lemma 5.10's finite
projective ring-map scope and its separate exact-proof obligation in Task 5255
are unaffected. No proof of the false unrestricted proposition is claimed.

## Original source statements

Conrad's Lemma 5.10 (printed p.17) reads: "Let `R → R′` be a finite locally free ring
extension, and `X′` a (quasi-separated) algebraic space of finite type over `R′`. The Weil
restriction `X := Res_{R′/R}(X′)` as a functor on `R`-schemes is a (quasi-separated)
algebraic space of finite type over `R`. If `X′` is separated (resp. of finite
presentation) over `R′` then the same holds for `X` over `R`."

Conrad's Proposition 5.11 (printed p.18) begins: "Let `k′/k` be an extension of henselian
valued fields". Part (1) reads: "If `[k′ : k]` is finite then for any (quasi-separated)
algebraic space `Y′` of finite type over `k′`, the identification of sets
`Res_{k′/k}(Y′)(k) = Y′(k′)` is a homeomorphism."

## Objects

The algebraic spaces are the Library's actual algebraic spaces from
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`. The statements use only
published definitions and Mathlib.

- `ringWeilRestriction R R'` (from `SpaceWeilRestriction.lean`) is the Weil restriction of
  fppf sheaves along `Spec R′ ⟶ Spec R`. It sends `X′` to the sheaf
  `T ↦ X′(T ×_{Spec R} Spec R′)` on schemes over `Spec R`, which is Conrad's functor on
  `R`-schemes. `IsAlgebraicSpace _ ((ringWeilRestriction R R').obj X'.toSheaf)` says that
  this sheaf is an algebraic space (representable diagonal and an étale surjective scheme
  atlas). `ringWeilRestrictionSpace R R' X' h` is the resulting algebraic space over
  `Spec R`.
- `ringWeilRestrictionBasePointsEquiv K K' Y' h` (from `SpaceWeilRestriction.lean`) is the
  identification `Res_{K′/K}(Y′)(K) ≃ Y′(K′)` of rational points. The `K`-points of the
  restriction are the points of `Y′` over `Spec K ×_{Spec K} Spec K′`, which is identified
  with `Spec K′` through `K′ ⊗[K] K ≅ K′`.
- `IsQuasiSeparated` and `IsSeparated` (from `RingPoints.lean`) say that the diagonal is
  representable with quasi-compact represented projections, respectively a representable
  closed immersion.
- `FiniteTypeOverRing C X` (from `Langlands/Global/AdelicSpaceLevelPointsStatement.lean`)
  says that `X` has an étale surjective atlas by an actual scheme locally of finite type and
  quasi-compact over `Spec C`. `FinitePresentationOverRing C X` (from
  `SpaceWeilRestriction.lean`) is the same with "locally of finite presentation" in place
  of "locally of finite type". Together with quasi-separatedness, these express finite type
  and finite presentation over `Spec C`.
- A finite locally free ring map `R → R′` is formalized by `[Module.Finite R R']` and
  `[Module.Projective R R']`: a finite module is locally free exactly when it is finitely
  presented and flat, exactly when it is projective (Stacks Project, Tag 00NX).
- `IsHenselianValuedField K` (from
  `Langlands/AlgebraicGeometry/PointTopology/HenselianEtalePointStatement.lean`) is
  Conrad's henselian valued field (printed p.14): the norm extends uniquely to every
  algebraic extension field. A finite extension `K′/K` of valued fields is a
  `NormedAlgebra K K'` with `FiniteDimensional K K'`, so the norm of `K′` restricts to the
  norm of `K`.
- `etaleChartTopology F Y` (from `EtaleChartTopology.lean`) is the strongest topology on
  `Y(F)` making every map `U(F) → Y(F)` continuous, for étale maps `U → Y` from actual
  schemes of finite type over `F`, where `U(F)` has the scheme point topology. This is the
  topology Conrad constructs in the proof of Proposition 5.4.

## The statements

`SpaceWeilRestrictionStatement` says the following. Let `R`, `R'` be commutative rings
with `R'` a finite projective `R`-algebra, and let `X'` be an algebraic space over
`Spec R'` with `IsQuasiSeparated X'` and `FiniteTypeOverRing R' X'`. Then the sheaf
`(ringWeilRestriction R R').obj X'.toSheaf` is an algebraic space (proof `h`), and the
algebraic space `ringWeilRestrictionSpace R R' X' h`
- is quasi-separated and satisfies `FiniteTypeOverRing R`;
- is separated if `X'` is separated;
- satisfies `FinitePresentationOverRing R` if `X'` satisfies
  `FinitePresentationOverRing R'`.

The following describes the false literal proposition recorded by the unchanged Lean
definition, rather than a proved result.
`HenselianWeilRestrictionPointHomeomorphStatement` says the following. Let `K`, `K'` be
nontrivially normed fields with `NormedAlgebra K K'`, `FiniteDimensional K K'`,
`IsHenselianValuedField K` and `IsHenselianValuedField K'`. Let `Y'` be an algebraic space
over `Spec K'` with `IsQuasiSeparated Y'` and `FiniteTypeOverRing K' Y'`. Then the sheaf
`(ringWeilRestriction K K').obj Y'.toSheaf` is an algebraic space (proof `h`), and
`ringWeilRestrictionBasePointsEquiv K K' Y' h` is a homeomorphism (`IsHomeomorph`) from
`etaleChartTopology K (ringWeilRestrictionSpace K K' Y' h)` to `etaleChartTopology K' Y'`.

## Relation to the source and derived content

Conrad's Proposition 5.11(1) presupposes Lemma 5.10, which makes `Res_{k′/k}(Y′)` an
algebraic space carrying the topology of Proposition 5.4. A field extension of finite
degree is finite free, so Lemma 5.10 applies to its representability. Both the literal and
corrected point propositions include existence of the algebraic-space structure in their
conclusion; that conclusion is not an assumed input. A proof of the corrected proposition
can obtain it from the separate proof of Lemma 5.10. Proof irrelevance makes the resulting
algebraic space independent of the choice of proof `h`. The topological conclusion needs
the module-topology correction explained above.

Conrad's topologies are those of his Proposition 5.4 over `k` and over `k′`. The
statement uses the étale-chart topology instead, as the published statements of
Proposition 5.11(2) and (3) do. Conrad's existence proof of Proposition 5.4 (printed
p.15) asserts that this topology "does the job". That claim is stated separately as
`EtaleChartTopologyAdmissibleStatement`; with it and the uniqueness part of
Proposition 5.4, the étale-chart topology is the topology of Proposition 5.4 on
quasi-separated spaces locally of finite type.

For a finite extension, the hypothesis that `k′` is henselian follows from the one for
`k`. The statement keeps both hypotheses, as Conrad states them. Quasi-separatedness is
Conrad's standing convention for Section 5 (printed p.13). The names of the statements are
also chosen here.

## Not stated here

- Conrad's proof of Lemma 5.10 (printed pp.17–18) uses an étale cover `U′ → X′` by an
  affine scheme, the fact that `Res_{R′/R}(U′)` is an affine scheme of finite type,
  Zariski's Main Theorem for the quasi-affineness of `U′ ×_{X′} U′`, and the stability of
  algebraic spaces under quotients by étale equivalence relations [LMB, Prop. 1.3]. These
  are proof material.
- Conrad's reference [Ols, Thm. 1.5] for more general Weil restrictions of algebraic spaces
  is not formalized.
- Proposition 5.11(2) and (3) are the published `HenselianCompletionPointEmbeddingStatement`
  and `HenselianExtensionPointEmbeddingStatement`.
