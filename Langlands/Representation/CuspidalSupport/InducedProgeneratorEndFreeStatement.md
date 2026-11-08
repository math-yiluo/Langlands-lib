# The endomorphism ring of the induced progenerator: statement

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.InducedProgeneratorEndFreeStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.4, printed pp.209–210 / PDF pp.215–216: the embedding `i_P^G : R_D → R_Ω` and the first Lemma. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

Let `(M, ρ)` be a cuspidal datum with `M` a standard Levi of the standard parabolic `P`, `D = [M, ρ]_M`, `Π_D` the progenerator of `M(M)_D` of VI.4.1, `Π_Ω = i_P^G(Π_D)`, `R_D = End_M(Π_D)` and `R_Ω = End_G(Π_Ω)`. Renard observes that `φ ↦ i_P^G(φ)` is an algebra morphism `R_D → R_Ω`, injective because `i_P^G` is faithful, so `R_Ω` is an `R_D`-bimodule. With `W(D)` the stabilizer of `D` in `W(A_M) = N_G(M)/M`, the Lemma states: the right `R_D`-module `R_Ω` is free of rank `|W(D)|`, hence free of finite rank over the centre `ℨ_D` of `R_D`. The second assertion follows from Theorem VI.4.4.

## The Lean statement

`InducedProgeneratorEndFreeStatement` states these facts for actual groups. It is a statement unit: nothing is proved.

### Hypotheses

The statement quantifies over the following data, the same as in the published VI.10.3 statement `SupercuspidalInductionLengthStatement` and the VI.10.1 statement `InducedProgeneratorIndependenceStatement`:

- a nonarchimedean local field `k : Type u`;
- a connected reductive group scheme `G` over `Spec k`, with canonical point topology, locally compact and nonarchimedean;
- an actual rational parabolic `P = MN` (`p`, `l`, `r` with `hp`, `hl`, `hr`, `hmul`), not necessarily standard;
- `π : SmoothRep.{0, u, v} ℂ (rationalPoints M)`, irreducible and supercuspidal (published `IsSupercuspidal`). This plays the role of Renard's `ρ`; its inertial class is `D`;
- `ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M)`, irreducible, with an injective morphism into `π|_{⁰M(F)}`.

`Π_D` is `piD := CuspidalSupport.rationalNormKernelSummandInduction M ρ₀`, the published compact induction `ind_{⁰M(F)}^{M(F)} ρ₀` of VI.4.1. `I` is the published normalized induction functor `leviInductionFunctor p l r hp hr hl hmul`. Thus `R_D = End piD` and `R_Ω = End (I.obj piD)` are endomorphism rings in the category of smooth representations.

`W` is the actual-group form of `W(D)` used in `SupercuspidalInductionLengthStatement`, here for `π`. It is the set of double cosets `P(F) w P(F)` containing some `w ∈ G(F)` with an automorphism `φ : M ≅ M` satisfying `φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom` (conjugation by `w` normalizes `M`), whose induced point automorphism `e` makes `SmoothRep.pullback e π` isomorphic to an unramified twist `π ⊗ χ`. The Markdown of that statement explains why `W` is in bijection with `W(D)`; the argument is not formalized.

### Conclusion

Morphisms compose diagrammatically: `f ≫ g` is `g ∘ f`. The conclusion is the conjunction of:

1. `Function.Injective (fun a : piD ⟶ piD => I.map a)`: the map `R_D → R_Ω` is injective. That it is a ring morphism is functoriality of `I` and is not restated.
2. `W.Finite`.
3. There are `b : Fin W.ncard → (I.obj piD ⟶ I.obj piD)` such that every `x : I.obj piD ⟶ I.obj piD` is `∑ i, I.map (a i) ≫ b i`, i.e. `x = ∑ bᵢ ∘ i_P^G(aᵢ)`, for exactly one family `a : Fin W.ncard → (piD ⟶ piD)`. This says `R_Ω` is a free right `R_D`-module with basis `b`, for the right action `x · a = x ∘ i_P^G(a)`, of rank `|W| = |W(D)|`.
4. There are `m : ℕ` and `c : Fin m → (I.obj piD ⟶ I.obj piD)` such that every `x` is `∑ i, I.map (z i) ≫ c i` for exactly one family `z : Fin m → Subring.center (End piD)`. This says `R_Ω` is free of finite rank over the centre `ℨ_D` of `R_D`, through the same right action.

Freeness is expressed by explicit unique expansions in a basis rather than by a `Module` instance on `R_Ω`. This avoids installing an opposite-ring module structure for the right action. The two formulations are equivalent.

## Remarks

- Renard's proof uses second adjointness, `R_Ω ≅ Hom_M(Π_D, r_D i_P^G(Π_D))`, the geometric lemma, and projectivity of the conjugates `w · Π_D ≅ Π_D` to split the filtration. None of this is formalized here.
- The later results of VI.10.4 (`ℨ_Ω ⊂ ℨ_D`, `ℨ_Ω = ℨ_D^{W(D)}`, and the Theorem identifying `ℨ_Ω` with the polynomial functions on `Ω`) are not stated here.
