# Parabolic descent for Harish-Chandra's Theorem 1.1

The module `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierDescentStatement`
defines the conclusion of Harish-Chandra's Theorem 1.1 (local summability) at one element,
`Langlands.HarmonicAnalysis.OrbitalFourierRegularityAt`, and states, as the proposition
`Langlands.HarmonicAnalysis.RegularOrbitalFourierDescentStatement.{u, v}`, its parabolic
descent from the centralizer of an idempotent, for the unit group `Aˣ` of a finite-dimensional
semisimple algebra over a nonarchimedean local field of characteristic zero. The descent
statement is **not** proved here.

## The conclusion at one element

`OrbitalFourierRegularityAt.{u, v} F A X`, for a nonarchimedean local field `F : Type u`
(`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`), a
finite-dimensional `F`-algebra `A : Type v` (`[Ring A] [Algebra F A] [FiniteDimensional F A]`)
and `X : A`, quantifies over

- a topology on `A` that is the module topology (`[IsModuleTopology F A]`; the topological ring
  structure is `IsModuleTopology.isTopologicalRing`, bound with `haveI`), Borel σ-algebras on
  `A` and on `Aˣ`;
- `ψ : UnitaryAdditiveCharacter F`, `B : LinearMap.BilinForm F A` with
  `hB : IsInvariantPairing B`, `μ : AdditiveHaarMeasure A`;
- a Borel σ-algebra on `LeftQuotient (conjugationCentralizer X)`, a Haar measure `μG` on `Aˣ`, a
  right-invariant Haar measure `μH` on `C = conjugationCentralizer X`, a quotient measure `ν`
  with `QuotientIntegration.IsCompatible C μG μH ν`, and `hconv : OrbitalIntegralConverges X ν`,

and asserts that there is `Θ : A → ℂ` with `LocallyIntegrable Θ μ.measure` and
`distributionFourier ψ hB.isSymm hB.nondegenerate μ (orbitalDistribution X ν hconv) f =
∫ Y, Θ Y * f Y ∂μ.measure` for every Schwartz–Bruhat `f`. These are the data and the conclusion
of `RegularOrbitalFourierRegularityStatement` for one element `X`; that statement says that
`OrbitalFourierRegularityAt F A X` holds for every regular `X` of every finite-dimensional
semisimple `A` over every nonarchimedean local field `F` of characteristic zero; the two
differ only in the order of the binders.

## The descent statement

`RegularOrbitalFourierDescentStatement.{u, v}` quantifies over a nonarchimedean local field
`F : Type u` of characteristic zero, a finite-dimensional semisimple `F`-algebra `A : Type v`
(`[IsSemisimpleRing A]`), an idempotent `e : A` (`IsIdempotentElem e`) and an element
`X : Subalgebra.centralizer F {e}` of the centralizer `M` of `e` whose image in `A` is regular,
`(X : A) ∈ regularSet F A`. The claim:

`OrbitalFourierRegularityAt F M X → OrbitalFourierRegularityAt F A X`.

The hypothesis is the conclusion of Theorem 1.1 at `X` for the algebra `M` itself, for all of its
data (topology, character, invariant pairing and Haar measures on `M`, the centralizer of `X` in
`Mˣ` and its coset space); the conclusion is that at `X` for `A`.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15):

- §1.2, printed pp. 6–8 (PDF pp. 21–23): for a p-pair `(P, A)` with `P = MN` and opposite
  `P̄ = MN̄`, `g = n̄ + m + n`, `g_f(Y) = ∫_n f(Y + Z) dZ`, `f_P = g_{f̄}` with `f̄` the
  `K`-average of `f`; Lemma 1.4 (`g_{f̂} = (g_f)^`), Lemma 1.5 (`φ^{G/Γ}_f = φ^{M/Γ}_{f_P}` for a
  Cartan subalgebra `Γ` of `m`), Lemma 1.6 (the integral over `N` of `g(n.Y)`) and Lemma 1.7
  (`(f̂)_P = (f_P)^`, hence `φ^{G/Γ}_{f̂} = φ^{M/Γ}_{(f_P)^}`).
- §1.4, printed pp. 9–10 (PDF pp. 24–25): for a distribution `θ` on `m`, `Θ(f) = θ(f_P)`;
  Lemma 1.12 (`θ` `M`-invariant implies `Θ` `G`-invariant) and Lemma 1.13 ("Suppose `θ` is a
  locally summable, `M`-invariant function on `m`. Then `Θ` is a locally summable,
  `G`-invariant function on `g`", with the formula for `|η|^{1/2} Θ` on each Cartan
  subalgebra).
- §1.4, printed pp. 10–11 (PDF pp. 25–26): the step of the induction in the proof of
  Theorem 1.1. For non-elliptic `h`, with `A = A_h` and `P ∈ 𝒫(A)`, Lemma 1.7 gives
  `φ^{G/h}_{f̂} = φ^{M/h}_{(f_P)^}`; the induction hypothesis gives a locally summable
  `M`-invariant `θ` on `m` representing `g ↦ φ^{M/h}_{ĝ}(H₀)`; "Then the conditions required by
  Theorem 1.1 follow immediately from Lemma 1.13."

The statement is derived from these lemmas, with the following correspondence.

- `G = Aˣ`, `g = A`. If `e` is not central, `S = {t e + s (1 - e) : t, s ∈ Fˣ}` is a split
  torus of `Aˣ` whose centralizer in `A` is `M = e A e ⊕ (1 - e) A (1 - e)`, the centralizer of
  `e`. The group `P = Aˣ ∩ (M ⊕ e A (1 - e))` is a parabolic subgroup with Levi factor `Mˣ` and
  unipotent radical `N = 1 + e A (1 - e)`, so `m = M`, `n = e A (1 - e)`, `n̄ = (1 - e) A e`; with
  `A_M` the split component of `Mˣ`, which contains `S`, `(P, A_M)` is a p-pair. Harish-Chandra's
  Lemmas 1.4–1.7 and 1.12–1.13 are stated for an arbitrary p-pair; his proof applies them to
  `P ∈ 𝒫(A_h)`, the statement here to a parabolic subgroup whose Levi factor contains `h`.
- For regular `X ∈ M` the centralizer `h` of `X` in `A` contains `e` and is commutative, so it
  lies in `M`: it is a Cartan subalgebra of `m`, and the centralizers of `X` in `Aˣ` and in `Mˣ`
  are the same group `hˣ`. By Lemma 1.7 the Fourier transform of the orbital distribution of `X`
  on `A`, applied to `f`, is a positive multiple of that on `M` applied to `f_P` (the multiple
  depends on the normalizations of the measures).
- Let `θ` be a Borel representative of the locally integrable density on `M` supplied by the
  hypothesis. The Fourier orbital distribution is invariant under conjugation by `Mˣ`, because
  the quotient measure is right invariant and conjugation preserves the pairing and additive
  Haar measure. Uniqueness of a density tested on compact open sets gives
  `θ(m Y m⁻¹) = θ(Y)` for almost every `Y`, for each `m ∈ Mˣ`.
  Both Haar measures are σ-finite, so Fubini gives the same equality for Haar-almost every `m`
  for almost every `Y`. Define `θ₀(Y)` as the essential constant of `m ↦ θ(m Y m⁻¹)` if one
  exists, and as zero otherwise. This is measurable. To compute the constant, average on a
  fixed compact open subset of `Mˣ` of finite positive measure where the fiber is integrable.
  Integrability there and agreement of the computed value for almost every `m` in `Mˣ` are
  measurable conditions by Tonelli. Right translation preserves Haar null sets, so conjugating
  `Y` preserves the existence and value of the essential constant. Thus `θ₀` is everywhere
  `Mˣ`-invariant and equals `θ` almost everywhere. Lemma 1.13 then gives a locally integrable
  density on `A` for the distribution `f ↦ θ₀(f_P)`.
- If `e` is central, `M` is all of `A` and the statement transports the conclusion along the
  identification of `M` with `A`.
- The induction hypothesis of Harish-Chandra's proof also asserts the local constancy of `θ` on
  `m'` and the local boundedness of `|η_m|^{1/2} θ`; the statement here concerns local
  summability only.
