# Splitting points and a displacement in general position

Module `Langlands.LinearAlgebra.GMFamilySplittingDisplacement` prepares the use
of the alternate splitting formula
`Langlands.GMFamily.alternateSplittingFormula` (Arthur 2005, Lemma 17.6,
proved in the Library module `GMFamilyAlternateSplittingProof`) in the proof of
Lapid's Lemma 8: it chooses the displacement `ξ`, identifies the main pair of
Levi spaces, and turns the formula, which the Library states off an unspecified
finite set of hyperplanes, into an identity at every point off the walls.

## Splitting points

For Levi spaces `L₁, L₂ ∈ leviSpaces R a` with `dCoeff R a L₁ L₂ ≠ 0` and
`ξ ∈ 𝔞_M^G`, the Library's `exists_unique_splitting_points` gives unique
`ξ₁ ∈ L₁ ∩ 𝔞_G^⊥`, `ξ₂ ∈ L₂ ∩ 𝔞_G^⊥` with `2ξ = ξ₁ − ξ₂`.

- `splitPoint₁`, `splitPoint₂`, `splitPoint_spec`, `splitPoint_eq`: these
  points and their uniqueness.
- `splitPointLinear₁`, `splitPointLinear₂`: by uniqueness they depend linearly
  on `ξ`.
- `splitForm b α`: the linear form `ξ ↦ ⟪α, ξ_i⟫`; `splitForm_ne_zero`: it is
  nonzero when the restriction of `α` to `L_i` is nonzero (evaluate at
  `ξ = ±½ α|_{L_i}`, whose splitting has `ξ_i = α|_{L_i}` and the other
  point `0`). `restrictedRoot_levi_mem` places these restrictions in
  `L_i ∩ 𝔞_G^⊥` and in `𝔞_M^G`.

## The displacement

`exists_generic_displacement`: for every chamber `S₀` there is `ξ ∈ 𝔞_M^G`
with

- `RegularDisplacement R a ξ`, the regularity premise of the alternate
  splitting formula (each `ξ_i` is regular in `L_i`);
- `posSet R (−2ξ) = S₀`;
- `⟪α, ξ⟫ ≠ 0` for every root with nonzero restriction to `a`.

The forms `splitForm` (over all admissible pairs, roots and both sides) and
`⟪α, ·⟫` are finitely many nonzero linear forms, so their common nonvanishing
set is dense (`dense_nonzero_forms` of `GMFamilyRootWalls`). It meets the
nonempty open set of `ξ` with `−2ξ` on the same side as a regular point `h₀`
of `S₀` for every root nonzero on `a`; this set contains
`−½ pr(h₀)`, `pr` the projection to `𝔞_G^⊥`.

## The main pair

- `centralSpace_mem_leviSpaces`, `self_mem_leviSpaces`: `𝔞_G` and `a` are
  members of `leviSpaces R a`.
- `dCoeff_centralSpace_self`: `d_M^G(G, M) = dCoeff R a (centralSpace R) a = 1`.
- `posSet_zero`, `splittingSection_centralSpace_self`: the section of the pair
  `(𝔞_G, a)` is `(∅, posSet R (−2ξ))`, that is `(G, S₀)` for the displacement
  above.
- `splittingSection_fst_face`, `splittingSection_snd_face`: the sections are
  faces `posSet R w` with `w ∈ a`.
- `eq_centralSpace_self_of_section_empty`: if `dCoeff R a L₁ L₂ ≠ 0`, `ξ` is
  a regular displacement and the first section is the empty face, then
  `L₁ = 𝔞_G` and `L₂ = a`. An empty face means that all roots vanish at the
  regular point `ξ₁` of `L₁`, so all roots vanish on `L₁` and `L₁ = 𝔞_G`;
  then `dCoeff ≠ 0` (`measureFactor_ne_zero_iff`) forces `a ∩ L₂^⊥ = 0`, so
  `L₂ = a`.

## The identity off the walls

`alternateSplitting_of_offWalls`: for `(G, M)`-families `c`, `d` with
continuous members, a regular displacement `ξ ∈ 𝔞_M^G` and `y ∈ a` with
`Λ_y = ⟪y, ·⟫` off the walls,

`cM(c d)(Λ_y) = ∑_{L₁, L₂} d_M^G(L₁, L₂) · c_M^{Q₁}(Λ_y) · d_M^{Q₂}(Λ_y)`,

`(Q₁, Q₂) = splittingSection R ξ L₁ L₂`. The Library's formula holds for
`Λ_{y'}` with `y'` off finitely many hyperplanes of `a`, a dense set
(`dense_inner_ne_zero`); both sides are continuous at `y` because all
denominators are nonzero there (`continuousAt_cM_familyMul`,
`continuousAt_cQM_face`, `continuousAt_splittingSum`), so they agree at `y`
(`eq_of_continuousAt_of_dense`). Points of `a` are used instead of all of
`StrongDual ℝ a` to work in the topology of the normed space `a`.

## Provenance

J. Arthur, *An introduction to the trace formula*, §17, Lemma 17.6, printed
p. 101 (`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`), and
J. Arthur, *The invariant trace formula. I. Local theory*, §7, Corollary 7.4,
printed p. 358 (`arthur-1988-invariant-trace-formula-I`, SHA-256
`902db792ffe113507165a252b0c1b8c59f78ab8d04def1c5c39b0372362dc3ac`).
E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), §7, proof of Lemma 8, p. 326
(`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, volume PDF
SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`),
uses that in this product formula the coefficient of a pair `(G, Q)` is `1`
for `Q = P` and `0` otherwise; here this is arranged by the choice of `ξ`
(`posSet R (−2ξ) = S₀`) together with `dCoeff_centralSpace_self` and
`eq_centralSpace_self_of_section_empty`. The general-position argument is
derived directly.
