# Proof of the Artinian étale criterion

`EtaleCriterion.artinianEtaleCriterion : ArtinianEtaleCriterionStatement.{u}` has no hypotheses and
uses only the standard axioms. Let `P → D` be a local, flat, essentially finite type map of
Artinian local rings with `𝔪_P D = 𝔪_D` and `κ_D/κ_P` separable. We show that `D` is
**standard étale** over `P` (Mathlib's `Algebra.IsStandardEtale`), hence étale, hence smooth. Then
`D` is essentially smooth, as the localization of itself at `⊥` (`IsLocalization.self`).

## Helper lemmas

- `isAdicComplete_of_isNilpotent`: a local ring with nilpotent maximal ideal `𝔪` (`𝔪^N = 0`) is
  `𝔪`-adically complete. It is Hausdorff since `𝔪^N • ⊤ = ⊥`. A Cauchy sequence has limit
  `f N`. Hence it is Henselian (`IsAdicComplete.henselianRing`).
- The imported `Langlands.AlgebraicGeometry.Picard.ArtinianColengthOne.isNilpotent_maximalIdeal`
  supplies nilpotence of the maximal ideal (the Jacobson radical) in an Artinian local ring.
- `eq_top_of_le_sup_smul`: Nakayama for a nilpotent ideal and an arbitrary module. If
  `M = N + I M` and `I` is nilpotent, then `M = N`. By induction, `M = N + I^k M` for all `k`.

## Main argument

1. **Residue field.** `κ_D` is essentially of finite type over `κ_P` (through `D` and `P`). It
   is formally unramified, being separable, hence finite (`FormallyUnramified.finite_of_free`).
   Choose a primitive element `α` with separable minimal polynomial `g`
   (`Field.exists_primitive_element`), and a monic lift `G ∈ P[X]` of `g` of the same degree
   (`Polynomial.lifts_and_natDegree_eq_and_monic`).
2. **Hensel.** For a lift `θ₀ ∈ D` of `α`, `G(θ₀) ∈ 𝔪_D` and the residue of `G'(θ₀)` in `κ_D`
   is a unit (it is `g'(α) ≠ 0`, because `g` is separable). This is the input of
   `HenselianRing.is_henselian`, applied to `G` mapped to `D[X]`. It gives a root `θ` of `G` with
   `θ ≡ θ₀ mod 𝔪_D`, so `θ` lifts `α`, and `G'(θ)` is a unit of `D` (its residue is again
   `g'(α) ≠ 0`). The identity `res(aeval x F) = aeval (res x) (F mod 𝔪_P)` is `hres`.
3. **`ρ : P[X]/(G) → D`, `root ↦ θ`, is bijective.**
   - *Injective.* The powers `θ^i`, `i < deg G`, are linearly independent over `P`. This is
     `Module.IsLocalRing.linearIndependent_of_flat`: `D` is flat, and the images of the `θ^i` in
     `κ_P ⊗_P D` map to the powers `α^i`, which are independent (`linearIndependent_pow`). The
     power basis of `P[X]/(G)` (`AdjoinRoot.powerBasis'`) is sent to these powers.
   - *Surjective.* Every `d ∈ D` is congruent modulo `𝔪_D = 𝔪_P D` to a polynomial in `θ`:
     `res d ∈ κ_P[α]`, and polynomials lift. Then Nakayama for the nilpotent `𝔪_P`
     (`eq_top_of_le_sup_smul`) applies to the `P`-submodule `ρ.range`.
4. **Standard étale presentation.** Take the pair `(f, g) = (G, G')`, with `G'·1 + G·0 = G'¹`. Its
   standard étale algebra `Pr.Ring = P[X][Y]/(G, YG' − 1)` maps to `D` by `X ↦ θ` (`Pr.lift`).
   An inverse is `D ≅ P[X]/(G) → Pr.Ring`, `root ↦ X`. Both composites are the identity by
   `AdjoinRoot.algHom_ext` and `StandardEtalePair.hom_ext`. So `Pr.lift` is bijective, giving a
   `StandardEtalePresentation P D`.

5. **Conclusion.** Mathlib's instances give `Algebra.Smooth P D` from `Algebra.IsStandardEtale P D`
   (through `Algebra.Etale`). `EssentiallySmooth P D` is witnessed by `T = D`, the submonoid
   `M = ⊥`, and `IsLocalization.self bot_le`.

## Relation to the source

The statement's source (Stacks, Smoothing Ring Maps, proof of Lemma 16.11.2, Tag 07FH) first
shows that `P → D` is finite (Algebra, Lemma 10.54.4, Tag 07DT), and then that it is étale
(Algebra, Lemma 10.143.7, Tag 00U6). The Lean proof takes a direct route instead and does not use
these lemmas. It never proves separately that `D` is finite over `P`, although this follows from
`D ≅ P[X]/(G)` with `G` monic. The étale property comes from an explicit standard étale
presentation. Only the hypotheses of `ArtinianEtaleCriterionStatement` are used.

## Status

The module imports the statement and Mathlib, and uses only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). It compiles with no errors or warnings.
