# The centre of `R_Ω` lies in the centre of `R_D`: statement

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.InducedProgeneratorCenterInclusionStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.4, second Lemma and the sentence after it, printed p.211 / PDF p.217. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

With `R_D = End_M(Π_D)` identified with a subalgebra of `R_Ω = End_G(i_P^G Π_D)` through `i_P^G` (VI.10.4, printed p.209), Renard proves:

- **Lemma.** The centre `ℨ_Ω` of `R_Ω` is contained in the centre `ℨ_D` of `R_D`. The proof uses the free `ℨ_D`-module structure of `R_Ω` and the generic irreducibility VI.8.5.
- He then refines this to `ℨ_Ω ⊂ ℨ_D^{W(D)}` and records, "en particulier", `ℨ_Ω = 𝒞_{ℨ_D}(R_Ω) = {r ∈ ℨ_D | a r = r a for all a ∈ R_Ω}`.

## The Lean statement

`InducedProgeneratorCenterInclusionStatement` is a statement unit: nothing is proved. Its hypotheses are those of the companion VI.10.4 Lemma statement `InducedProgeneratorEndFreeStatement` (Worker 6, candidate `119058e2-2442-4da8-a92a-44231e3b3453`), without the set `W`:

- a nonarchimedean local field `k : Type u` and a connected reductive `G`, with `G(F)` locally compact and nonarchimedean in the canonical topology;
- an actual rational parabolic `P = MN` (`p`, `l`, `r` with `hp`, `hl`, `hr`, `hmul`);
- `π : SmoothRep.{0, u, v} ℂ (rationalPoints M)`, irreducible and supercuspidal (published `IsSupercuspidal`);
- `ρ₀`, an irreducible representation of `Plancherel.rationalCommonNormKernel M` with an injective morphism into `π|_{⁰M(F)}`.

Then `piD := CuspidalSupport.rationalNormKernelSummandInduction M ρ₀` is `Π_D`, and `I := leviInductionFunctor p l r hp hr hl hmul` is the published normalized induction. The conclusion is the set equality

`(Subring.center (End (I.obj piD)) : Set _) = {x | ∃ z ∈ Subring.center (End piD), x = I.map z ∧ ∀ a, a * x = x * a}`.

That is, the centre of `R_Ω = End(I.obj piD)` consists exactly of the images `i_P^G(z)` of central elements `z ∈ ℨ_D` that commute with all of `R_Ω`. This is `ℨ_Ω = 𝒞_{ℨ_D}(R_Ω)` with `R_D` embedded through `i_P^G`. The inclusion `⊆` is Renard's Lemma; the inclusion `⊇` holds by definition of the centre.

## Remarks

- The intermediate refinement `ℨ_Ω ⊂ ℨ_D^{W(D)}`, the final equality `ℨ_Ω = ℨ_D^{W(D)}` and the identification with polynomial functions on `Ω` (VI.10.4, Theorem) are not stated. They need the action of `W(D)` on `ℨ_D` and the variety structure on `Ω`.
- The parabolic need not be standard.
- The proof is not formalized here.
