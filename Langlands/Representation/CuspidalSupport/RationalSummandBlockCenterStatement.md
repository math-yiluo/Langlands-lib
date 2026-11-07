# Renard VI.4.5: the center of M(G)[π] is the center of End(ind_{⁰G}^G ρ)

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locator is the paragraph of VI.4.5 that follows the Burnside argument, printed p.160 / PDF p.166 ("L'équivalence de catégories entre M(A)_d et M(G)[π] induit donc un isomorphisme d'algèbres entre Z et le centre Z[π] de la catégorie M(G)[π], que nous notons φ ↦ z_φ"). The same isomorphism is announced in the summary that closes VI.4.4, printed p.159 / PDF p.165. The center of a category is defined in A.X, printed p.269 / PDF p.275, whose Example identifies the center of the category of modules over a ring with the center of the ring. The setting is that of VI.4.1–VI.4.4, printed pp.149–159 / PDF pp.155–165. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

Renard keeps the notation of VI.4.1–VI.4.4: (π,V) is an irreducible supercuspidal representation of G, (ρ,W) is an irreducible summand of the restriction of π to ⁰G, Π = ind_{⁰G}^G ρ, R = End_G(Π), A = H(N,ρ) is the convolution algebra of VI.4.2–VI.4.3, isomorphic to R, and Z is the center of A. By A.X, the center of a category 𝒞 is the ring of endomorphisms of the identity functor: an element z is a family of morphisms z_X : X → X with f ∘ z_X = z_Y ∘ f for every f : X → Y.

In VI.4.5 Renard writes: the equivalence of categories between M(A)_d (right A-modules) and M(G)[π] (the Theorem of VI.4.1, transported along R ≃ A) induces an algebra isomorphism between Z and the center Z[π] of the category M(G)[π], written φ ↦ z_φ. The text gives no further argument; it relies on the invariance of the center under equivalence and on the Example of A.X.

## Lean content

Write H = G(F), with its canonical rational-point topology, and H⁰ = `Plancherel.rationalCommonNormKernel G` for Renard's ⁰G, with the subspace topology.

**`RationalSummandBlockCenterStatement`.** The premises are exactly those of `RationalSummandSmallProgeneratorStatement` and `RationalSummandHomEquivalenceStatement`, the Proposition and the Theorem of VI.4.1, with the maximal split torus renamed S:

- an arbitrary connected reductive G over an arbitrary nonarchimedean local field F, a maximal split torus inclusion i : S → G and a generic cocharacter ν;
- explicit `StandardCocharacterStatement`, relative-root-system and standard-unipotent-closedness premises, from which the finite simple-root index set and the actual semidirect decompositions are derived;
- local compactness, the nonarchimedean group property and Hausdorffness of H;
- π an irreducible actual smooth complex representation of H with carrier in `Type uV`, cuspidal in the sense of the published `Aubert.General.IsCuspidal` (every proper standard normalized Jacquet module vanishes);
- ρ an irreducible actual smooth representation of H⁰ with carrier in `Type uV`, with an injective H⁰-equivariant linear map j : ρ → `SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π`.

Let I be the published `Induction.compactInductionFunctor (rationalCommonNormKernel G)` applied to `SmoothRep.toRep.obj ρ`; this is Renard's Π. The conclusion asserts:

1. a proof `hmem` that I lies in the published full category `RationalInertiaBlock G (rationalInertiaBaseLift G π)`, Renard's M(G)[π];
2. a ring isomorphism e from Mathlib's `CatCenter` of this block onto `Subalgebra.center ℂ (End I)`, the center of R = `End I`, such that e(z) = (z.app ⟨I, hmem⟩).hom for every z, that is, e is the component of z at Π.

## Correspondence and conventions

**The center of the block.** Mathlib's `CatCenter C` is `End (𝟭 C)`, the endomorphisms of the identity functor; this is A.X. Its ring structure is that of Mathlib: addition componentwise, and (x * y).app X = y.app X ≫ x.app X, which equals x.app X ≫ y.app X by naturality. The block is a full subcategory of actual smooth representations, so a morphism ⟨I, hmem⟩ ⟶ ⟨I, hmem⟩ in the block is an endomorphism of I, extracted by `.hom`. In `End I`, multiplication is composition, α * β = β ≫ α. So z ↦ z_Π is compatible with multiplication.

**Direction of the isomorphism.** Renard's map φ ↦ z_φ goes from Z to Z[π]; the Lean e goes from Z[π] to the center of R, and its inverse is Renard's map transported along R ≃ A. The identification of the isomorphism with evaluation at Π is not written out in the source, and it is the reason the Lean statement can name e by a formula. Through the equivalence F_Π = Hom_G(Π, −) of VI.4.1, an element z of Z[π] acts on F_Π(X) by Φ ↦ z_X ∘ Φ, and naturality gives z_X ∘ Φ = Φ ∘ z_Π. So the corresponding element of the center of M(R)_d is right multiplication by z_Π, which by A.X corresponds to z_Π in the center of R. Hence Renard's z_φ is the element of Z[π] whose component at Π is φ. This argument explains the formulation and is not part of the statement.

**R versus A.** Renard states the isomorphism with Z, the center of A = H(N,ρ). The Lean statement uses the center of R = `End I`. The Proposition of VI.4.2 (`RationalNormKernelHeckeStatement`, a separate statement) identifies R with A = H(G,ρ), and VI.4.3 shows that A = H(N,ρ); the present statement does not import or use these.

**Scalars.** e is stated as a ring isomorphism. Since e(z) is the component of z, it commutes with multiplication by complex scalars for the natural ℂ-structures; this is not stated separately.

**The universe lift.** I has carrier in `Type (max uF uV)` and π in `Type uV`. The block is therefore formed from the published `rationalInertiaBaseLift G π`, which applies the published fully faithful `SmoothRep.universeLiftFunctor`, as in the VI.4.1 statements.

**Choice of ρ.** As in the VI.4.1 statements, Renard's ρ is an irreducible summand of Res π, and the Lean statement takes every irreducible ρ with an injective equivariant map into Res π. By VI.3.2 these are, up to isomorphism, the summands.

**Cuspidality.** Renard's π is supercuspidal. As in the VI.4.1 statements and Worker 1758's `RationalUniversalSmallProgeneratorStatement`, cuspidality is measured by the vanishing of every proper standard normalized Jacquet module. Comparing this with cuspidality along all proper rational parabolics is a separate obligation.

**Universes.** π and ρ have carriers in `Type uV`, I and the block have carriers in `Type (max uF uV)`. Coefficients are ℂ in universe zero. Renard has no universe restriction.

There is no splitness, characteristic-zero, admissibility, compactness or finite-dimensionality premise on ρ or π.

## Provenance

The statement is the source assertion with one qualification: it is made for the center of R instead of the center Z of A, the two being identified through the separate VI.4.2 statement. The explicit description of the isomorphism as evaluation at Π is the content of the equivalence argument above and is used by Renard implicitly ("φ ↦ z_φ").

## Scope

This module defines a Prop-valued target only. It does not prove block membership or the isomorphism. The other assertions of VI.4.5 are separate: the description of the center of the block as the algebra of functions on Irr(G)[π] is `RationalInertiaBlockCenterEvaluationStatement`, and the indecomposability of M(G)[π] is `RationalInertiaBlockIndecomposableStatement`. The bijection SpecMax(Z) → Irr(A), I ↦ M_I, the bijection Irr(A) ≃ Irr(G)[π], and the isomorphism Π/IΠ ≃ m π_I are not stated.
