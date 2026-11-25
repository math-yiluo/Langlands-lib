/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyMaps
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisInjectiveSectionsExact
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisSectionComparison
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# A section-complex diagram computing étale Mayer–Vietoris pullback

Source: Stacks Project, Tag 0A50, proof; the pullback comparison is the
resolution argument in the parent node, steps 1, 2 and 4.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-section-diagram).
-/

@[expose] public section

universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- A morphism of short exact nonnegative section complexes, with homology
identifications respecting the prescribed restriction and pullback maps.
Source: Stacks Project, Tag 0A50, proof, and the explicit resolution comparison
of the parent node, steps 1, 2 and 4.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-section-diagram)

Proof: Choose nonnegative injective resolutions I of G and J of g⁻¹G. Exact inverse
image preserves the quasi-isomorphism from G to I. The bounded below injective
resolution J is K-injective, so a comparison beta from g⁻¹I to J exists over the
augmentations. The possible homotopy of augmentations has values in degree -1 of J,
which is zero, so it is an equality. On X take the complexes of sections of I on
X, the product of its sections on U and V, and its sections on U ∩ V, with the
restriction pair and difference of restrictions. On Y do the same with J and the
inverse-image opens. The sheaf equalizer property gives exactness at the first two
terms in each degree. Injective restriction surjectivity gives surjectivity of the
difference, as in Tag 0A50. These degreewise exact sequences are short exact complexes.
The unit on sections followed by beta commutes with restriction by naturality, and
with its difference by additivity, and gives the morphism phi of short complexes.

Identify homology of these complexes with the displayed Ext cohomology groups using
Hom from the constant integer sheaf, evaluated at 1. For opens, restriction preserves
injectives by its exact extension-by-zero left adjoint, so the same resolutions compute
the restricted cohomology. The identification for the middle complex uses homology's
preservation of the finite product. The coefficient composition comparison gives the
four asserted horizontal identities. To check the two vertical identities, represent
an Ext class by a cocycle in Hom from the constant integer sheaf to I. Exact inverse
image applies to that cocycle, and precomposition with the constant-sheaf comparison
is the adjunction unit on its section. Composing with beta therefore gives precisely
cohomologyMap g. On U ∩ V the restricted resolution and the pullback-unit identity
identify this with openCohomologyPullback, including its coefficient comparisons.
Thus the same identifications satisfy all six identities simultaneously; mere abstract
existence of unrelated isomorphisms is not being used. Empty opens give zero section
complexes, and for the identity morphism one can choose the same resolution. No
connecting maps or long-exact-sequence assertions are part of this statement. -/
theorem etale_mayerVietoris_section_diagram
    {X Y : Scheme.{u}} (g : Y ⟶ X) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ SX SY : ShortComplex (CochainComplex AddCommGrpCat.{u + 1} ℕ),
    ∃ φ : SX ⟶ SY, SX.ShortExact ∧ SY.ShortExact ∧
    ∃ eAX : ∀ q : ℕ, SX.X₁.homology q ≃+ Sheaf.H G q,
    ∃ eBX : ∀ q : ℕ, SX.X₂.homology q ≃+
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} U.ι).obj G) q ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} V.ι).obj G) q),
    ∃ eCX : ∀ q : ℕ, SX.X₃.homology q ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι).obj G) q,
    ∃ eAY : ∀ q : ℕ, SY.X₁.homology q ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj G) q,
    ∃ eBY : ∀ q : ℕ, SY.X₂.homology q ≃+
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ U).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q ×
       Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ V).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q),
    ∃ eCY : ∀ q : ℕ, SY.X₃.homology q ≃+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ (U ⊓ V)).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q,
    (∀ q x, eBX q (HomologicalComplex.homologyMap SX.f q x) =
      (cohomologyMap U.ι G q (eAX q x), cohomologyMap V.ι G q (eAX q x))) ∧
    (∀ q x, eCX q (HomologicalComplex.homologyMap SX.g q x) =
      openCohomologyRestriction (inf_le_left : U ⊓ V ≤ U) G q (eBX q x).1 -
        openCohomologyRestriction (inf_le_right : U ⊓ V ≤ V) G q (eBX q x).2) ∧
    (∀ q x, eBY q (HomologicalComplex.homologyMap SY.f q x) =
      (cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eAY q x),
       cohomologyMap (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eAY q x))) ∧
    (∀ q x, eCY q (HomologicalComplex.homologyMap SY.g q x) =
      openCohomologyRestriction (g.preimage_mono (inf_le_left : U ⊓ V ≤ U))
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eBY q x).1 -
      openCohomologyRestriction (g.preimage_mono (inf_le_right : U ⊓ V ≤ V))
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eBY q x).2) ∧
    (∀ q x, eAY q (HomologicalComplex.homologyMap φ.τ₁ q x) =
      cohomologyMap g G q (eAX q x)) ∧
    (∀ q x, eCY q (HomologicalComplex.homologyMap φ.τ₃ q x) =
      openCohomologyPullback g (U ⊓ V) G q (eCX q x)) := by
  let I := injectiveResolution G
  let J := injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)
  let SX := etaleSectionShortComplex U V I.cocomplex
  let SY := etaleSectionShortComplex (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) J.cocomplex
  have hSX : SX.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro q
    exact etaleSectionShortComplex_degreewise_shortExact U V hcover I.cocomplex q
  have hcY : (g ⁻¹ᵁ U) ⊔ (g ⁻¹ᵁ V) = ⊤ := by
    rw [← g.preimage_sup, hcover, g.preimage_top]
  have hSY : SY.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro q
    exact etaleSectionShortComplex_degreewise_shortExact
      (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) hcY J.cocomplex q
  obtain ⟨φ, eAX, eBX, eCX, eAY, eBY, eCY, hrX, hdX, hrY, hdY, hpA, hpC⟩ :=
    etaleSectionShortComplex_pullback_comparison g U V G I J
  exact ⟨SX, SY, φ, hSX, hSY, eAX, eBX, eCX, eAY, eBY, eCY,
    hrX, hdX, hrY, hdY, hpA, hpC⟩

end AlgebraicGeometry.Etale
