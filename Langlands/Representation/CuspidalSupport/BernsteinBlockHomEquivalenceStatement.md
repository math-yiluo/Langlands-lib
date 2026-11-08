# A Bernstein block as a module category: statement

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.BernsteinBlockHomEquivalenceStatement`, namespace `Langlands.CuspidalSupport`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.2, Theorem, printed p.208 / PDF p.214. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

With the notation of VI.10.1, put `R_Ω = End_G(Π_Ω)`. As in VI.4.1, Renard introduces the functors

- `F_{Π_Ω} : M(G)_Ω → M(R_Ω)_d`, `(π, V) ↦ Hom_G(Π_Ω, π)`, and
- `G_{Π_Ω} : M(R_Ω)_d → M(G)_Ω`, `M ↦ M ⊗_{R_Ω} Π_Ω`,

where `M(R_Ω)_d` is the category of unital right `R_Ω`-modules. The theorem reads: these functors are quasi-inverse and give an equivalence of categories between `M(G)_Ω` and `M(R_Ω)_d`. The proof of VI.4.1 is copied verbatim, using that `Π_Ω` is a finitely generated progenerator (VI.10.1, Theorem).

## The Lean statement

`BernsteinBlockHomEquivalenceStatement` is a statement unit: nothing is proved. Its hypotheses and the object `Π_Ω` (`piOmega`) are exactly those of the companion VI.10.1 Theorem statement `BernsteinInducedProgeneratorStatement` (Worker 6, candidate `c8183a09-928c-4f9e-8755-071b330ec5c1`), whose Markdown describes them in full:

- the published standard-family framework: a nonarchimedean local field `F : Type uF`, `G` with `[IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]`, `G(F)` locally compact and nonarchimedean in its canonical topology, `T`, `i`, `ν`, and `family : BernsteinStandardFamily i ν`;
- a cuspidal datum `a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family` and an irreducible `ρ₀` of the common norm kernel of its standard Levi `M`, with an injective morphism into the restriction of `a.representation`;
- `Π_Ω` the published normalized induction, along the standard parabolic of `a.roots`, of the literal-Levi transport of `Π_D = rationalNormKernelSummandInduction M ρ₀`.

The conclusion is: there is a proof `hmem` that `Π_Ω` lies in the published block `BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)`, Renard's `M(G)_Ω`, such that for the object `P = ⟨Π_Ω, hmem⟩` of the block, Mathlib's `preadditiveCoyonedaObj P`, the functor `Hom(P, •)` from the block to `ModuleCat (End P)ᵐᵒᵖ`, satisfies `Functor.IsEquivalence`. This mirrors the published VI.4.1 statement `RationalSummandHomEquivalenceStatement`.

## Comparison with the source

- Modules over `(End P)ᵐᵒᵖ` are exactly right modules over `End P = R_Ω`, and `ModuleCat` consists of unital modules, so the target is Renard's `M(R_Ω)_d`. The `(End P)ᵐᵒᵖ`-module structure on `Hom(P, X)` is precomposition, as in the source.
- Renard's statement names the quasi-inverse `G_{Π_Ω}(M) = M ⊗_{R_Ω} Π_Ω`. The Lean statement asserts only that `F_{Π_Ω}` is an equivalence. A quasi-inverse is then unique up to natural isomorphism, and its identification with the tensor-product functor is not stated.
- The block is the published one, defined with the induction-occurrence support relation. Its comparison with Renard's Jacquet-defined `M(G)_Ω` is the remaining support-uniqueness obligation recorded in `BernsteinBlock`.
- The proof is not formalized here.
