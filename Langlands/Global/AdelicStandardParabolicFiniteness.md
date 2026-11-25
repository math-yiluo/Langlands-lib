# Finitely many parabolic spectra `L²_P([G])` (finiteness in Getz–Hahn Theorem 10.5.1)

This module covers the algebraic part of
`Langlands.Global.SpectralDecompositionStatement`. It proves the finiteness half of item 1 ("only finitely many subspaces `L²_P([G])`
occur"), given item 3 ("`L²_P([G]) = L²_{P'}([G])` for associate `P`, `P'`"). Everything
here is proved and has no premises. The analytic items are reduced separately in
`AdelicSpectralDecompositionReduction`.

## Statements

All three statements are `Prop` definitions in namespace `Langlands.Global`. Each is proved
by the theorem named after it.

1. `PresentedStandardParabolicRangeFiniteStatement`, proved by
   `presentedStandardParabolicRangeFinite`. Let `G` be connected reductive over a number
   field `F` with `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`, and let
   `p₀ : P₀ → G` be a minimal parabolic (`IsMinimalParabolicSubgroup p₀`). Consider all maps
   `p : P → G` that admit some `ParabolicRootPresentation p l a` and satisfy
   `range p₀ ≤ range p`. Their all-test images `SubgroupFunctor.range p` form a finite set
   of subgroup functors of `G`. No closed-immersion hypothesis is needed.

2. `PresentedStandardParabolicWeylConjugacyStatement`, proved by
   `presentedStandardParabolicWeylConjugacy`. Let `G` be connected reductive over a number
   field with `IsAffineHom G.X.hom`. Let `p : P → G` and `p' : P' → G` be closed immersions
   with presentations `ParabolicRootPresentation p l a` and
   `ParabolicRootPresentation p' l' a'`. If `range p = range p'`, then there are a rational
   point `w` of `G` and `c : M' → M` with `IsWeylConjugation p l p' l' w c`. That is, `c` is
   an isomorphism and `c ≫ l ≫ p = l' ≫ p' ≫ (G.innerIso w).inv`. In words, `P` and `P'`
   are associate in the sense of the target.

3. `StandardParabolicSpectrumFinitenessStatement`, proved by
   `standardParabolicSpectrumFiniteness`. It takes the binders and hypotheses of
   `SpectralDecompositionStatement` up to `IsIwasawaCompact p₀ K`, with `hG` taken
   anonymously, and the same set `S` of subspaces `parabolicSpectrum hK rho hsmooth hcalc
   iU l r hA hT` of presented standard data. Assume the first half of item 3 of the target,
   with its binder lists copied verbatim: for any two presented standard data `(P, …, hK)`
   and `(P', …, hK')`, if `∃ w c, IsWeylConjugation p l p' l' w c`, then their parabolic
   spectra are equal. Then `S.Finite`. This is exactly the first conjunct of item 1 of the
   target, `S.Finite`. Item 3 of the target implies the hypothesis by projecting:
   `((h3 … hK).2 P' … hK').1`. Some hypotheses are not used in the proof:
   `IsMaximalCompactSubgroup`, `IsClosedSubgroup rho`, `IsIwasawaCompact p₀ K` and the
   affineness instances. They are kept so that the statement matches the target literally.

## Auxiliary theorems

- `Langlands.GroupScheme.exists_finite_dynamicParabolics_of_minimal_le`: over any field,
  take `G` connected reductive, a maximal split torus `i : T → G` with a generic
  cocharacter `ν`, and a minimal parabolic `p₀`. Then there is a finite set `R` of subgroup
  functors that contains every dynamic parabolic `Dynamic.parabolic ζ` containing
  `range p₀`.
- `Langlands.GroupScheme.exists_innerIso_levi_conjugation_of_range_eq`: let `p`, `p'` be
  monomorphisms with `p` parabolic, and let `l`, `l'` be rational Levis. If
  `range p = range p'`, then there are a rational point `w` of `G` and an isomorphism
  `c : M' ≅ M` with `c.hom ≫ l ≫ p = l' ≫ p' ≫ (G.innerIso w).inv`.
- `Langlands.Global.finite_of_forall_exists_rel`: a counting principle. Suppose every element
  of `S` is related to an element of a finite set `R`, and every `b : β` is related to at most
  one `a : α`. The uniqueness premise ranges over all of `α` and `β`, not only over `S` and
  `R`. Then `S` is finite.
- `Langlands.Global.exists_isWeylConjugation_of_range_eq`: statement 2 with explicit binders.

## Proofs

*Finitely many dynamic parabolics above `P₀`.* `genericMinimalParabolic` and
`isMinimalParabolicFunctor_iff_exists` give a minimal parabolic `p₁` with
`range p₁ = P(ν)`, where `P(ν) = Dynamic.parabolic (groupHom ν ≫ i)`.
`minimalParabolicConjugacy` gives a rational point `g` with `p₁` and `p₀` conjugate by
`Int(g)`, so `range p₁ = (range p₀).comap Int(g)` (`SubgroupFunctor.range_eq_comap_of_iso_square`).
Take `R` to be the image of the finite set of subsets `J ⊆ Δ(ν)`
(`IsSplitTorus.finite_simpleRelativeRoots`) under `J ↦ (standardParabolic i ν J).comap Int(g)⁻¹`.
Suppose `range p₀ ≤ P(ζ)`. Pulling back along `Int(g)` and using
`Dynamic.parabolic_eq_comap_of_iso` gives `P(ν) ≤ P(ζ ≫ Int(g)⁻¹)`. Then the first clause of
`standardParabolicClassification` writes `P(ζ ≫ Int(g)⁻¹)` as some `standardParabolic i ν J`,
so `P(ζ) ∈ R`.

*Statement 1.* If the set is empty, it is finite. Otherwise one presentation `r₀` supplies a
maximal split torus and a generic cocharacter (`r₀.isCompatible.maximalSplit`,
`.generic`), and the previous lemma gives the finite set `R`. Each presentation `r` realizes
`range p` as a dynamic parabolic (`r.isCompatible.realization`), so the set lies in `R`.

*Levi conjugation.* Since `range p = range p'`, the two monomorphisms represent the same
subgroup functor. `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` gives `e : P' ≅ P`
with `e.hom ≫ p = p'`. Then `l` and `l' ≫ e.hom` are rational Levis of `P`
(`IsRationalLeviSubgroup.comp_iso`). Fix a unipotent radical `iU` of `P`
(`IsRationalLeviSubgroup.exists_unipotentRadical`). `rationalLeviConjugacy` gives a rational
point `q` of `U` and `e' : M ≅ M'` with `l ≫ Int_P(q ≫ iU) = e'.hom ≫ l' ≫ e.hom`. Then
`innerIso_hom_comp_groupHom` turns `Int_P` followed by `p` into `p` followed by `Int_G`. This
gives the identity with `w = q ≫ iU ≫ p` and `c = e'.symm`.

*Statement 2.* `r.isCompatible.parabolic`, `r.isCompatible.levi` and
`r'.isCompatible.levi` supply the hypotheses of the Levi conjugation lemma. The closed
immersions supply the monomorphisms (`Over.mono_of_mono_left`).

*Statement 3.* Apply the counting principle with `R` the finite set of statement 1. Relate
`V` to `H` when some presented standard datum has `range p = H` and
`V = parabolicSpectrum …`. Every `V ∈ S` is related to its own `range p ∈ R`. If any two subspaces `V` and
`V'`, in `S` or not, are related to the same `H`, then their data have equal ranges, and statement 2 gives a
Weyl conjugation. The item-3 hypothesis then gives `V = V'`.

## Provenance

Derived. Getz–Hahn, *An Introduction to Automorphic Representations* (2024), source
`getz-hahn-2024-automorphic-representations`, §10.5, (10.21), printed p.281 (PDF p.293),
describes the decomposition as "the (finite) direct sum … over all association classes 𝒫 of
parabolic subgroups". Theorem 10.5.1, printed p.282 (PDF p.294), is the target. The book does
not prove the finiteness separately. It is the standard consequence of the following facts
in Borel–Tits, *Groupes réductifs* (1965), source `borel-tits-1965-groupes-reductifs`:

- the parabolics containing a minimal one are the finitely many standard ones `P_J`,
  `J ⊆ Δ` (§5.12–5.14, printed pp.99–100);
- minimal parabolics are rationally conjugate (Théorème 4.13(b), printed p.90);
- rational Levi subgroups of a parabolic are conjugate by its unipotent radical
  (Corollaire 3.14, printed p.80).

In the Lean statements, all three facts enter through published Library theorems:
`standardParabolicClassification`, `minimalParabolicConjugacy` and `rationalLeviConjugacy`.
The intermediate statements 1 and 2 and the conditional form of statement 3 are internal
steps of this argument. Statement 3 is phrased with the target's data so that it applies
directly to `SpectralDecompositionStatement`.
