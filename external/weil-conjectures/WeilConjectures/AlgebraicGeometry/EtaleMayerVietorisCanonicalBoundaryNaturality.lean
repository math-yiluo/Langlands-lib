/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisCanonicalBoundary
public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone
import WeilConjectures.AlgebraicGeometry.EtaleSectionShortComplexCoefficientComparison
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Pullback and coefficient naturality of a fixed resolution boundary

Source: Stacks Project, Tag 0A50, functorial resolution proof, and Tag 01F7.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-canonical-boundary-naturality).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- The constructed boundaries commute with one pullback and coefficient morphism.
Source: Stacks Project, Tag 0A50, functorial resolution proof, and Tag 01F7.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-canonical-boundary-naturality)

Proof: The fixed-comparison coefficient lemma supplies a morphism of the two
section short complexes whose homology maps are the actual whole and open
cohomology maps. The covers make both complexes short exact. Represent x
using the source normalized intersection equivalence. Apply Mathlib's
connecting-map naturality to that representative, then the target global
equivalence. The two comparison identities identify its vertical maps.
The definition of the boundary cancels each inverse comparison and yields
the displayed equality. No choices of boundaries are made here. -/
private theorem etaleMayerVietorisCanonicalBoundary_naturality
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U V : X.Opens) (U' V' : Y.Opens)
    (hcover : U ⊔ V = ⊤) (hcover' : U' ⊔ V' = ⊤)
    (hU : U' = f ⁻¹ᵁ U) (hV : V' = f ⁻¹ᵁ V)
    (k : (U' ⊓ V').toScheme ⟶ (U ⊓ V).toScheme)
    (hk : (U' ⊓ V').ι ≫ f = k ≫ (U ⊓ V).ι)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (cI : ResolutionSectionCanonicalComparison F I)
    (cJ : ResolutionSectionCanonicalComparison G J)
    (q : ℕ) (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι).obj F) q) :
    etaleMayerVietorisCanonicalBoundary U' V' hcover' G J cJ q
      (Sheaf.H.map (openSquareCoefficient f (U ⊓ V).ι (U' ⊓ V').ι k hk F G φ) q
        (cohomologyMap k ((upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι).obj F) q x)) =
      Sheaf.H.map φ (q + 1) (cohomologyMap f F (q + 1)
        (etaleMayerVietorisCanonicalBoundary U V hcover F I cI q x)) := by
  obtain ⟨α, ha, hc⟩ := etaleSectionShortComplex_coefficient_comparison
    f U V U' V' hU hV k hk F G φ I J cI cJ
  let hS := etaleSectionShortComplex_resolution_shortExact U V hcover F I
  let hT := etaleSectionShortComplex_resolution_shortExact U' V' hcover' G J
  obtain ⟨z, rfl⟩ := (cI.openEquiv (U ⊓ V) q).surjective x
  have hb (n : ℕ) (w : (etaleSectionShortComplex U V I.cocomplex).X₃.homology n) :
      etaleMayerVietorisCanonicalBoundary U V hcover F I cI n
        (cI.openEquiv (U ⊓ V) n w) = cI.globalEquiv (n + 1)
          (hS.δ n (n + 1) rfl w) := by
    change cI.globalEquiv (n + 1)
      ((hS.δ n (n + 1) rfl).hom
        ((cI.openEquiv (U ⊓ V) n).symm (cI.openEquiv (U ⊓ V) n w))) = _
    rw [AddEquiv.symm_apply_apply]
  have hb' (n : ℕ) (w : (etaleSectionShortComplex U' V' J.cocomplex).X₃.homology n) :
      etaleMayerVietorisCanonicalBoundary U' V' hcover' G J cJ n
        (cJ.openEquiv (U' ⊓ V') n w) = cJ.globalEquiv (n + 1)
          (hT.δ n (n + 1) rfl w) := by
    change cJ.globalEquiv (n + 1)
      ((hT.δ n (n + 1) rfl).hom
        ((cJ.openEquiv (U' ⊓ V') n).symm (cJ.openEquiv (U' ⊓ V') n w))) = _
    rw [AddEquiv.symm_apply_apply]
  rw [← hc q z, hb', hb]
  have hn : HomologicalComplex.homologyMap α.τ₁ (q + 1) (hS.δ q (q + 1) rfl z) =
      hT.δ q (q + 1) rfl (HomologicalComplex.homologyMap α.τ₃ q z) := by
    exact congrArg (fun t : (etaleSectionShortComplex U V I.cocomplex).X₃.homology q ⟶
      (etaleSectionShortComplex U' V' J.cocomplex).X₁.homology (q + 1) ↦ t z)
      (HomologicalComplex.HomologySequence.δ_naturality α hS hT q (q + 1) rfl)
  rw [← hn, ha]

/-- Naturality with specified source and target intersection opens.
Source: Stacks Project, Tags 0A50 and 01F7, the preceding naturality identity.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-canonical-boundary-naturality)

Proof: Substitute the intersection identifications and apply fixed-boundary naturality.
This transports the domain only; the resolutions and normalized comparisons stay fixed. -/
private theorem etaleMayerVietorisBoundaryOn_naturality
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U V W : X.Opens) (U' V' W' : Y.Opens)
    (hW : W = U ⊓ V) (hW' : W' = U' ⊓ V')
    (hcover : U ⊔ V = ⊤) (hcover' : U' ⊔ V' = ⊤)
    (hU : U' = f ⁻¹ᵁ U) (hV : V' = f ⁻¹ᵁ V)
    (k : W'.toScheme ⟶ W.toScheme) (hk : W'.ι ≫ f = k ≫ W.ι)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (cI : ResolutionSectionCanonicalComparison F I)
    (cJ : ResolutionSectionCanonicalComparison G J)
    (q : ℕ) (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj F) q) :
    etaleMayerVietorisBoundaryOn U' V' W' hW' hcover' G J cJ q
      (Sheaf.H.map (openSquareCoefficient f W.ι W'.ι k hk F G φ) q
        (cohomologyMap k ((upperStar AddCommGrpCat.{u + 1} W.ι).obj F) q x)) =
      Sheaf.H.map φ (q + 1) (cohomologyMap f F (q + 1)
        (etaleMayerVietorisBoundaryOn U V W hW hcover F I cI q x)) := by
  subst W
  subst W'
  exact etaleMayerVietorisCanonicalBoundary_naturality
    f U V U' V' hcover hcover' hU hV k hk F G φ I J cI cJ q x

/-- Naturality of the fixed boundary interface.
Source: Stacks Project, Tags 0A50 and 01F7, functorial resolution argument.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-canonical-boundary-naturality)

Proof: Unfold only the fixed resolution choices and apply named-intersection naturality. -/
theorem etaleMayerVietorisFixedBoundary_naturality
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U V W : X.Opens) (U' V' W' : Y.Opens)
    (hW : W = U ⊓ V) (hW' : W' = U' ⊓ V')
    (hcover : U ⊔ V = ⊤) (hcover' : U' ⊔ V' = ⊤)
    (hU : U' = f ⁻¹ᵁ U) (hV : V' = f ⁻¹ᵁ V)
    (k : W'.toScheme ⟶ W.toScheme) (hk : W'.ι ≫ f = k ≫ W.ι)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G)
    (q : ℕ) (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj F) q) :
    etaleMayerVietorisFixedBoundary U' V' W' hW' hcover' G q
      (Sheaf.H.map (openSquareCoefficient f W.ι W'.ι k hk F G φ) q
        (cohomologyMap k ((upperStar AddCommGrpCat.{u + 1} W.ι).obj F) q x)) =
      Sheaf.H.map φ (q + 1) (cohomologyMap f F (q + 1)
        (etaleMayerVietorisFixedBoundary U V W hW hcover F q x)) := by
  unfold etaleMayerVietorisFixedBoundary
  exact etaleMayerVietorisBoundaryOn_naturality
    f U V W U' V' W' hW hW' hcover hcover' hU hV k hk F G φ _ _ _ _ q x

end AlgebraicGeometry.Etale
