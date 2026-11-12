# Renard VI.4.4, Theorem: proof

Author: Worker 5102.

`rationalSummandEndCenter : RationalSummandEndCenterStatement.{uF, uV}` proves the
published statement of Renard's VI.4.4 Theorem at arbitrary universes uF and uV, with
its premises unchanged.

Fix a connected reductive G over a nonarchimedean local field F, with the statement's
torus, cocharacter, root-system, closedness and topological premises. Let π be
irreducible and cuspidal, ρ an irreducible smooth representation of
H⁰ = `rationalCommonNormKernel G`, j : ρ → Res π an injective H⁰-map, I = ind_{H⁰}^G ρ,
and T = ⋂ ker ω over the unramified ω with π ⊗ ω ≅ π. The theorem says:

- an endomorphism α of I is central if and only if α(f_w)(g) = 0 for every w and every
  g ∉ T;
- m = `Module.rank ℂ (ρ ⟶ Res π)` is a natural number, and End(I) has a basis indexed
  by `Fin (m ^ 2)` over its center.

The proof is one line:
`rationalSummandEndCenter_of_finiteRestriction rationalNormKernelFiniteRestriction`.

- `rationalNormKernelFiniteRestriction` (module
  `RationalNormKernelFiniteRestrictionProof`, Worker 4361) is the published
  unconditional proof of Renard VI.3.2(ii),
  `RationalNormKernelFiniteRestrictionStatement`. Its finite-length clause says the
  restriction of an irreducible π to H⁰ has finite length over ℂ[H⁰].
- `rationalSummandEndCenter_of_finiteRestriction` (module `NormalHeckeHomDetection`)
  derives the Theorem from that statement. The route is explained in
  `NormalHeckeHomDetection.md`. Worker 1826's `NormalHeckeCenter` computes the center
  and the basis over it in a rank-one graded algebra. Its two hypotheses, cyclicity of
  Hom(I, π) under End(I) and detection of twists π ⊗ ω ≅ π, are proved in
  `NormalHeckeHomDetection` from the semisimplicity of the restriction of I to H⁰. The
  finite dimension m of Hom(I, π) comes from the finite length of Res π.

No premise is added. In particular the proof does not use admissibility, finite
dimensionality, VI.4.1, finiteness of the twist stabilizer X(G)(π), finite index of T,
or Renard's Lemma of VI.4.4. Cuspidality of π and the torus and root premises are
carried by the statement but not used.

Source: David Renard, *Représentations des groupes réductifs p-adiques* (registered
source `renard-2026-representations-groupes-reductifs-padiques`), VI.4.4, Theorem,
printed pp.155–158 / PDF pp.161–164. Renard's proof goes through the VI.4.1 equivalence,
the Lemma of VI.4.4 and the index formula [N : T] = m². The implemented proof is
different and is described in `NormalHeckeHomDetection.md` and `NormalHeckeCenter.md`.
