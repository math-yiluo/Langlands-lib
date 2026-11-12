# The quasi-split adjoint sentence of AS 5, reduced to translations

Module `Langlands.Geometry.Building.ValuationQuasiSplitAdjointTranslation`.

KP Axiom 4.1.6, AS 5 (printed p.160 / PDF p.191), ends with this sentence: if `G` is quasi-split and adjoint, the image of
`N(F)` in the affine automorphisms of the apartment is the extended affine Weyl group
`W(Ψ)ᵉˣᵗ`. In the Library this is the field
`range_eq_extendedAffineWeylGroup_of_isQuasiSplit_of_isAdjoint` of
`KPApartmentData.SatisfiesApartmentAxioms`. KP prove it as Proposition 6.6.2 (Kaletha–Prasad,
*Bruhat–Tits theory: a new approach*, printed pp.231–232 / PDF pp.262–263).

This module splits that sentence for a `B : ValuationBuildingData G` into two parts:

- a general group-theoretic reduction, proved here;
- a statement about translations, `ValuationBuildingQuasiSplitAdjointTranslationStatement`,
  which is stated here and **not proved**.

It also proves that the translation statement and the first sentence of AS 5 together give the
quasi-split adjoint sentence.

## The proposition

`ValuationBuildingQuasiSplitAdjointTranslationStatement.{u} : Prop` says the following. Take a
nonarchimedean local field `F : Type u`, a group scheme `G` over `Spec F` with
`[IsAffineHom G.X.hom]`, and `B : ValuationBuildingData G`, and assume `IsQuasiSplit G` and
`IsAdjoint G`. Let `v : TranslationSpace B.i`, that is, an element of `V(S)` modulo the common
kernel of the relative roots. Suppose the translation `AffineEquiv.constVAdd ℝ B.Apartment v`
lies in `AffineRootSystem.rootStabilizer B.affineRoots`, so that composing with it permutes the
affine roots `Ψ` of `B` (KP Definition 6.3.4). Then some `z ∈ Z(F)`, `Z = B.centralizer.Z`,
satisfies `Submodule.Quotient.mk (B.translation z).toAdd = v`. In words, `v` is the class of
`ν(z)`, where `ν = B.translation` is KP's `ν : Z(F) → V(S)` (KP Axiom 4.1.4, A 1).

The hypotheses are the Library's own predicates. `IsQuasiSplit G` asks for a connected reductive
`G` with a subgroup defined over `F` that is a Borel subgroup over the algebraic closure. `IsAdjoint G` asks for a semisimple `G` whose
scheme-theoretic centre is trivial.

### Provenance

The proposition is derived. It is the translation step of KP's proof of Proposition 6.6.2. KP
fix an extra special vertex, write `T = Z` for the maximal torus (`G` is quasi-split), and argue
as follows. If the translation `T_v` lies in `W_ext`, it preserves the affine root system.
Hence `a(v) ∈ e_a⁻¹ ℤ` for every root `a`, and by Lemma 6.4.10 (printed p.227 / PDF p.258)
these `v` form the image of `T_ad(k) → V(S′)`. For adjoint `G`, `T_ad = T = Z`, so every
translation that preserves `Ψ` is the translation by `ν(z)` for some `z ∈ Z(F)`. The
proposition states exactly this conclusion for every `ValuationBuildingData` class. KP state
the conclusion as the equality `W̃_ad = W_ext` and do not isolate it as a separate claim.

The proposition adds no hypothesis beyond the two in AS 5's last sentence. It is an
intermediate result toward the Library target `ValuationBuildingApartmentAxiomsStatement`.
Its proof needs the structure of `Z(F)` for quasi-split adjoint `G` and the jumps of the root
filtrations (KP Lemma 6.4.10, Fact 6.5.1), and is left to a separate task.

## The general reduction

These results live in namespace `AffineRootSystem`. They hold for any set `Ψ` of affine
functions on an affine space `A` over a real vector space `V`.

- The imported `map_affineWeylGroup_linearHom Ψ` from `AffineExtendedWeylTransport`:
  the derivative map `AffineEquiv.linearHom` sends `W(Ψ)`
  onto `W(Φ) = derivativeWeylGroup Ψ`. Both are closures of generating sets, and the derivative
  of each generating affine reflection `affineReflection ψ hv.1` is the generating linear
  reflection `Module.reflection hv.1`. The proof uses `MonoidHom.map_closure` and compares the
  generating sets.
- `exists_eq_constVAdd_of_linear_eq`: an affine automorphism `e` with derivative the identity
  is the translation by `e p -ᵥ p` for any point `p`. The proof writes `x = (x -ᵥ p) +ᵥ p` and
  uses `e.map_vadd`.
- `extendedAffineWeylGroup_le_of_constVAdd_mem`: let `H` be a subgroup that contains `W(Ψ)` and
  every translation in `rootStabilizer Ψ`. Then `H` contains `W(Ψ)ᵉˣᵗ`. For `e ∈ W(Ψ)ᵉˣᵗ`, the
  derivative of `e` lies in `W(Φ)`, so by the first item it is the derivative of some
  `w ∈ W(Ψ)`. Then `w⁻¹ e` has identity derivative, so by the second item it is a
  translation. It preserves `Ψ`, because `W(Ψ) ≤ W(Ψ)ᵉˣᵗ ≤ rootStabilizer Ψ`. Hence
  `w⁻¹ e ∈ H` and `e = w (w⁻¹ e) ∈ H`.
- `eq_extendedAffineWeylGroup_of_constVAdd_mem`: if moreover `H ≤ W(Ψ)ᵉˣᵗ`, then
  `H = W(Ψ)ᵉˣᵗ` (by `le_antisymm`).

This is KP's remark in the proof of Proposition 6.6.2 that it suffices to show that all
translations in `W_ext` lie in the image. The Lean proof avoids KP's special vertex
(Lemma 1.3.42) and uses the derivative map instead.

## The reduction for a building datum

These results live in namespace `ValuationBuildingData`. Here `B : ValuationBuildingData G`,
and the image of `N(F)` is `B.apartment.normalizerAffineEquiv.range`.

- `constVAdd_translation_mem_range B z`: for `z ∈ Z(F)`, the translation by the class of `ν(z)`
  is the action of `z` viewed in `N(F)`. This is the published
  `B.isOmegaCompatible.normalizerAffineEquiv_eq z`.
- `range_eq_extendedAffineWeylGroup_of_translation B hW hle hT`: assume
  `hW : W(Ψ) ≤ range` and `hle : range ≤ W(Ψ)ᵉˣᵗ`, which together are the first sentence of
  AS 5. Assume also `hT`: every translation that preserves `Ψ` is a translation by the class of
  some `ν(z)`. Then `range = W(Ψ)ᵉˣᵗ`. The proof applies
  `eq_extendedAffineWeylGroup_of_constVAdd_mem` with `H = range`; the previous item puts each
  such translation in `H`.
- `range_eq_extendedAffineWeylGroup_of_quasiSplitAdjointTranslation B hQA hW hle hqs had`: from
  `hQA : ValuationBuildingQuasiSplitAdjointTranslationStatement.{u}`, `hW`, `hle`,
  `hqs : IsQuasiSplit G` and `had : IsAdjoint G`, the image is `W(Ψ)ᵉˣᵗ`. This is the
  quasi-split adjoint sentence of AS 5 for `B`, in the form of the field
  `range_eq_extendedAffineWeylGroup_of_isQuasiSplit_of_isAdjoint`. The proof applies the
  previous item with `hT = hQA F G B hqs had`.

Every theorem in the module is proved. The only unproved content is the proposition
`ValuationBuildingQuasiSplitAdjointTranslationStatement`, which appears as the hypothesis
`hQA`.
