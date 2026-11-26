# Central components lift through actual parabolic induction

Module `Langlands.Representation.CuspidalSupport.LeviCenterComponentsLift`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`
(SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), VI.10.5,
Proposition, printed p.213 / PDF p.219. The module states and proves, conditionally, the part of
that Proposition that asserts the existence of `z_M`. It does not prove
`HarishChandraHomomorphismStatement`; the module
`Langlands.Representation.CuspidalSupport.HarishChandraHomomorphismReduction` combines it with
the published `leviCenterDescent` and a finiteness statement.

## The statement `LeviCenterComponentsLiftStatement`

Data, as in the published `HarishChandraHomomorphismStatement`: a nonarchimedean local field
`k : Type u` (with `[T2Space k]`), a connected reductive group scheme `G` over `Spec k`, with
`G(F)` in the canonical topology `RationalPointFamily.pointTopology`, locally compact and
nonarchimedean, and an actual rational parabolic `P = MN` (`p`, `l`, `r`, `hp`, `hl`, `hr`,
`hmul`), not necessarily standard; `M(F)` carries `leviPointTopology l hl`. Write `I` for the
published normalized induction `leviInductionFunctor.{u, max u v} p l r hp hr hl hmul` between
the categories `SmoothRep.{0, u, max u v}` of smooth complex representations of `M(F)` and
`G(F)` on carriers in the universe `max u v`.

Conclusion: for every `z : CatCenter (SmoothRep.{0, u, max u v} ℂ G(F))` (Mathlib's centre
`End (𝟭 _)` of the category) and every smooth `σ` of `M(F)`, there is `y : σ ⟶ σ` with
`I.map y = z.app (I.obj σ)`.

This is, verbatim after unfolding, the premise `Renard.CenterComponentsLift I` of the published
`leviCenterDescent` (module `Langlands.Representation.CuspidalSupport.LeviCenterDescent`). In
Renard's Proposition it is the existence of `z_M` with `i_P^G(z_M) = z` on every `i_P^G(σ)`:
since `I` is faithful (`leviInductionFunctor_faithful`), the endomorphisms `y` are unique, natural
in `σ`, and form the element `z_M` of the centre of `M(M)`, as `leviCenterDescent` shows.

## The reduction

`LeviCenterComponentsLiftReductionStatement` is the implication

`LeviSecondAdjointnessStatement.{u, v} → JointSpecialCompactBasisExistenceStatement.{u} →
LeviCenterComponentsLiftStatement.{u, v}`,

and `leviCenterComponentsLiftReductionStatement_holds` proves it. Both premises are published
propositions, used unchanged: the second adjointness theorem `i_P^G ⊣ r_{P̄}^G` for opposite
actual rational parabolics (Renard VI.9.6, printed p.201 / PDF p.207), and the joint
special-compact basis (Renard V.5.1–V.5.2), which the Library uses through
`projective_rationalNormKernelSummandInduction_of_jointSpecialCompact` to make `Π_D` projective.
The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

### Provenance and relation to Renard

Renard defines `z ↦ z_M` geometrically: `ℨ(G)` and `ℨ(M)` are the algebras of polynomial
functions on `Ω(G)` and `Ω(M)` (VI.10.4, Theorem), and `z_M` is the pull-back of `z` along the
finite morphism `i_{MG} : Ω(M) → Ω(G)` of VI.7.3; the compatibilities are said to follow from
VI.7.3 and Remark 1 of VI.10.4. The route implemented here avoids the variety structures and the
Bernstein decomposition. It uses the induced progenerators `i_Q^M(Π_D)` of VI.10.1, the second
Lemma of VI.10.4 (`ℨ_Ω ⊂ ℨ_D`) and second adjointness, as follows.

## Declarations and proofs as implemented

### `exists_map_eq_center_app_leviInduction_summandInduction` (lifts on induced summands)

Data: `G`, `P = MU` as above; an actual rational parabolic `Q = LV` of `M` (`q`, `n`, `s`, `hq`,
`hn`, `hs`, `hmulQ`); an irreducible supercuspidal (`IsSupercuspidal`) `τ` of `L(F)` on a carrier
in universe `v`; an irreducible `ρ₀` of `⁰L(F) = Plancherel.rationalCommonNormKernel L` with an
injective `j : ρ₀ ⟶ τ|_{⁰L(F)}`; `Π_D = CuspidalSupport.rationalNormKernelSummandInduction L ρ₀`.
Conclusion: for every `z` in the centre of the smooth category of `G(F)` (carriers `max u v`),
with `X = i_Q^M(Π_D)` (`leviInductionFunctor.{u, max u v} q n s …`), there is `f : X ⟶ X` with
`I.map f = z.app (I.obj X)`.

Proof.
1. The published `LeviParabolicExtensionDatum.ofExtension` gives an actual rational parabolic
   `R` of `G` with Levi `L`, and `LeviParabolicExtensionDatum.leviInduction_iso` (Renard VI.1.4)
   a natural isomorphism `θ : i_R^G ≅ i_Q^M ⋙ I`.
2. `z.app (i_R^G Π_D)` commutes with every endomorphism of `i_R^G Π_D` (naturality of `z`), so it
   lies in `Subring.center (End (i_R^G Π_D))`. The published second Lemma of VI.10.4,
   `inducedProgeneratorCenterInclusion` (for `R`, `τ`, `ρ₀`, `j`), writes it as `i_R^G(ζ)` with
   `ζ` in the centre of `End(Π_D)`.
3. Naturality of `z` along `θ.hom.app Π_D` and naturality of `θ.hom` along `ζ` give
   `θ.hom.app Π_D ≫ I.map (i_Q^M ζ) = θ.hom.app Π_D ≫ z.app (I.obj X)`; cancelling the
   isomorphism, `f = i_Q^M(ζ)`.

### `exists_projective_summandInduction_ne_zero` (detection of irreducibles)

Data: `hSA : LeviSecondAdjointnessStatement.{u, v}`, `hJ : JointSpecialCompactBasisExistenceStatement.{u}`,
a connected reductive `G` with the topological hypotheses above, and an irreducible smooth `D` of
`G(F)` on a carrier in universe `max u v`. Conclusion: there are an actual rational parabolic
`Q = LV` of `G`, an irreducible supercuspidal `τ` of `L(F)`, an irreducible `ρ₀` of `⁰L(F)` and an
injective `j : ρ₀ ⟶ τ|_{⁰L(F)}` (all on carriers in `max u v`) such that `i_Q^G(Π_D)` is projective
and has a nonzero morphism to `D`.

Proof.
1. The proved cuspidal embedding theorem `leviCuspidalEmbedding` (Renard VI.2.1, Corollary)
   gives an actual rational parabolic `Q' = LV'` of `G`, an irreducible `τ` of `L(F)` all of whose
   proper Jacquet modules vanish, which is exactly `IsSupercuspidal τ`, and a surjection
   `r_{Q'}(D) → τ`.
2. `exists_opposite_parabolic` gives the opposite parabolic `Q = LV` of `Q'` with the same Levi,
   and `hSA` applied to the pair `(Q, Q')` gives `i_Q^G ⊣ r_{Q'}^G`. The Jacquet functor
   `r_{Q'}^G` is a left adjoint (`leviFirstAdjunction`), so it preserves epimorphisms and zero
   morphisms.
3. The proved `rationalNormKernelFiniteRestriction` with
   `rationalNormKernelConstituent_of_finiteRestriction` (Renard VI.3.2(ii)) gives an irreducible
   subrepresentation `ρ₀` of `τ|_{⁰L(F)}`, with `j` its inclusion.
4. `Π_D` is projective by `projective_rationalNormKernelSummandInduction_of_jointSpecialCompact`
   (from `hJ`), hence `i_Q^G(Π_D)` is projective (`Adjunction.map_projective`, step 2).
5. Frobenius reciprocity for compact induction (`NormalHecke.inducedHomEquiv`) turns `j` into a
   morphism `φ₁ : Π_D ⟶ τ`, nonzero because `j` is injective and `ρ₀` is nontrivial. Projectivity
   of `Π_D` lifts `φ₁` through the surjection `r_{Q'}(D) → τ` to a nonzero `ψ : Π_D ⟶ r_{Q'}(D)`.
   Its adjunct `i_Q^G(Π_D) ⟶ D` is nonzero, since the adjunction sends it back to `ψ` and
   `r_{Q'}^G` preserves zero morphisms.

### `leviCenterComponentsLiftReductionStatement_holds`

Fix the data, `z` and `σ`.
1. `exists_opposite_parabolic` and `hSA` give `adj : I ⊣ r_{P̄}^G`; `I` is faithful
   (`leviInductionFunctor_faithful`). The general lemma
   `Renard.exists_map_eq_center_app_of_detecting` (module `Langlands.CategoryTheory.AdjointCenterLift`)
   reduces the goal to: every nonzero `φ : σ ⟶ Y` is detected by some `t : X ⟶ σ` from an object `X`
   on which the component of `z` lifts.
2. Let `Qp X` say that `X` is projective and that `z.app (I.obj X)` lifts through `I`. For every
   irreducible `D` of `M(F)`, `exists_projective_summandInduction_ne_zero` (applied to the connected
   reductive `M`) gives `X = i_Q^M(Π_D)` projective with a nonzero map to `D`, and
   `exists_map_eq_center_app_leviInduction_summandInduction` (applied in `G` through `P`) gives the
   lift on `X`; so `Qp X`.
3. The family detector `SmoothRep.exists_comp_ne_zero_of_projective_family` (module
   `Langlands.Representation.Category.ProjectiveFamilyDetection`) then supplies the required `X`
   and `t`.

## Scope

- Only the first assertion of Renard's Proposition, the existence of `z_M`, is concerned. The
  finiteness of `ℨ(M)` over `ℨ(G)` is not addressed here.
- The two premises are hypotheses of the reduction; this module does not prove them.
