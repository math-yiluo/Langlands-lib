import Langlands.Geometry.Building.ApartmentClassRootComparison
import Langlands.Geometry.Building.GaloisFacetAction
import Langlands.Geometry.Building.IntegerCentralizerRepresentative
import Langlands.Geometry.Building.IntegerOmegaApartmentUniqueness

/-! # Coefficient-stable ordinary chambers under apartment class comparison -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building.AffineRootSystem

namespace Langlands.Geometry.Building

namespace IntegerValuation

variable {L : Type u} [Field L]
  {S : CommGroupScheme (Spec (CommRingCat.of L))}
  {H : GroupScheme (Spec (CommRingCat.of L))}
  {j : S.toGrp ⟶ H} [Mono j.hom.hom.left] [IsAffineHom H.X.hom]
  {v : Valuation L (WithZero (Multiplicative ℤ))}
  {D E : KPApartmentData j (order v)} {C C' : CentralizerDatum j}

/-- Full integer V 6 identifies classes independently of the representative of
its actual centralizer. -/
theorem IsOmegaCompatible.eq_of_isMaximalSplitTorus_of_centralizers
    (hD : IsOmegaCompatible v D C) (hE : IsOmegaCompatible v E C')
    (hH : IsConnectedReductive H) (hj : IsMaximalSplitTorus j) : D = E :=
  hD.eq_of_isMaximalSplitTorus hE.changeCentralizer hH hj

end IntegerValuation

namespace KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

private instance comparisonExtendedAffine :
    IsAffineHom (baseChanged k K G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]
  {ω : Kˣ → ℝ}
  (D E : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i) ω)
  (hDE : D.carrier = E.carrier)

include hDE

/-- Coefficient stability depends only on the complete valuation class. -/
theorem galoisStable_iff_of_carrier_eq :
    GaloisStable k K i D ↔ GaloisStable k K i E := by
  simp only [GaloisStable, hDE]

variable (hD : GaloisStable k K i D) (hE : GaloisStable k K i E)

/-- The identity on valuation families intertwines the actual affine
coefficient actions, independently of the supplied stability proofs. -/
theorem galoisAffineAction_apartmentAffineEquivOfCarrierEq
    (σ : K ≃ₐ[k] K) (x : D.Apartment) :
    apartmentAffineEquivOfCarrierEq D E hDE (galoisAffineAction k K i D hD σ x) =
      galoisAffineAction k K i E hE σ (apartmentAffineEquivOfCarrierEq D E hDE x) := by
  apply Apartment.ext
  rfl

/-- The identity on valuation families transports the entire ordinary facet. -/
theorem image_facet_apartmentAffineEquivOfCarrierEq (x : D.Apartment) :
    apartmentAffineEquivOfCarrierEq D E hDE '' facet D.affineRoots x =
      facet E.affineRoots (apartmentAffineEquivOfCarrierEq D E hDE x) := by
  simpa only [transportedRoots_apartmentAffineEquivOfCarrierEq] using
    image_facet_transportedRoots (apartmentAffineEquivOfCarrierEq D E hDE) D.affineRoots x

/-- Ordinary regularity is preserved and reflected by the actual class
comparison. -/
theorem isRegular_apartmentAffineEquivOfCarrierEq_iff (x : D.Apartment) :
    GalleryGeometry.IsRegular E.affineRoots (apartmentAffineEquivOfCarrierEq D E hDE x) ↔
      GalleryGeometry.IsRegular D.affineRoots x := by
  let e := apartmentAffineEquivOfCarrierEq D E hDE
  constructor
  · intro hx ψ hψ
    have h := hx (affineFunctionalTransport e ψ)
      ((mem_affineRoots_apartmentAffineEquivOfCarrierEq_iff D E hDE ψ).2 hψ)
    simpa only [affineFunctionalTransport_apply, e, AffineEquiv.symm_apply_apply] using h
  · intro hx ψ hψ
    rw [← transportedRoots_apartmentAffineEquivOfCarrierEq D E hDE] at hψ
    obtain ⟨η, hη, rfl⟩ := hψ
    simpa only [affineFunctionalTransport_apply, AffineEquiv.symm_apply_apply] using hx η hη

/-- Images of arbitrary apartment subsets commute with the actual coefficient
maps under the class comparison. -/
theorem image_galois_apartmentAffineEquivOfCarrierEq
    (σ : K ≃ₐ[k] K) (Y : Set D.Apartment) :
    apartmentAffineEquivOfCarrierEq D E hDE ''
        (galoisAffineAction k K i D hD σ '' Y) =
      galoisAffineAction k K i E hE σ ''
        (apartmentAffineEquivOfCarrierEq D E hDE '' Y) := by
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro y _
  exact galoisAffineAction_apartmentAffineEquivOfCarrierEq k K i D E hDE hD hE σ y

/-- Setwise invariance of an arbitrary apartment subset is preserved and
reflected by the coefficient-equivariant class comparison. -/
theorem galoisInvariant_image_iff_of_carrier_eq (Y : Set D.Apartment) :
    (∀ σ : K ≃ₐ[k] K, galoisAffineAction k K i E hE σ ''
        (apartmentAffineEquivOfCarrierEq D E hDE '' Y) =
      apartmentAffineEquivOfCarrierEq D E hDE '' Y) ↔
    (∀ σ : K ≃ₐ[k] K, galoisAffineAction k K i D hD σ '' Y = Y) := by
  apply forall_congr'
  intro σ
  rw [← image_galois_apartmentAffineEquivOfCarrierEq k K i D E hDE hD hE σ Y]
  exact (Set.image_injective.mpr (apartmentAffineEquivOfCarrierEq D E hDE).injective).eq_iff

/-- The actual image map identifies the types of coefficient-stable ordinary
chambers in two equal valuation classes. -/
def galoisStableChamberEquivOfCarrierEq :
    {Ca : Set D.Apartment // IsChamber D.affineRoots Ca ∧
      ∀ σ : K ≃ₐ[k] K, galoisAffineAction k K i D hD σ '' Ca = Ca} ≃
    {Cb : Set E.Apartment // IsChamber E.affineRoots Cb ∧
      ∀ σ : K ≃ₐ[k] K, galoisAffineAction k K i E hE σ '' Cb = Cb} :=
  (apartmentAffineEquivOfCarrierEq D E hDE).toEquiv.setCongr.subtypeEquiv fun Ca => by
    have hchamber := isChamber_image_transportedRoots_iff
      (apartmentAffineEquivOfCarrierEq D E hDE) D.affineRoots Ca
    rw [transportedRoots_apartmentAffineEquivOfCarrierEq D E hDE] at hchamber
    exact (and_congr hchamber
      (galoisInvariant_image_iff_of_carrier_eq k K i D E hDE hD hE Ca)).symm

@[simp] theorem galoisStableChamberEquivOfCarrierEq_apply
    (Ca : {Ca : Set D.Apartment // IsChamber D.affineRoots Ca ∧
      ∀ σ : K ≃ₐ[k] K, galoisAffineAction k K i D hD σ '' Ca = Ca}) :
    (galoisStableChamberEquivOfCarrierEq k K i D E hDE hD hE Ca).val =
      apartmentAffineEquivOfCarrierEq D E hDE '' Ca.val := rfl

/-- Invariance of the entire ordinary facet is preserved and reflected, for
each actual coefficient automorphism. -/
theorem image_facet_galois_eq_iff_of_carrier_eq
    (σ : K ≃ₐ[k] K) (x : D.Apartment) :
    galoisAffineAction k K i E hE σ ''
        facet E.affineRoots (apartmentAffineEquivOfCarrierEq D E hDE x) =
      facet E.affineRoots (apartmentAffineEquivOfCarrierEq D E hDE x) ↔
    galoisAffineAction k K i D hD σ '' facet D.affineRoots x =
      facet D.affineRoots x := by
  let e := apartmentAffineEquivOfCarrierEq D E hDE
  rw [← image_facet_apartmentAffineEquivOfCarrierEq k K i D E hDE x,
    ← image_galois_apartmentAffineEquivOfCarrierEq k K i D E hDE hD hE σ]
  exact (Set.image_injective.mpr e.injective).eq_iff

/-- A coefficient-stable ordinary chamber exists in one class exactly when it
exists in the other class; this uses the original coefficient actions. -/
theorem exists_regular_galois_stable_facet_iff_of_carrier_eq :
    (∃ y : E.Apartment, GalleryGeometry.IsRegular E.affineRoots y ∧
      ∀ σ : K ≃ₐ[k] K,
        galoisAffineAction k K i E hE σ '' facet E.affineRoots y = facet E.affineRoots y) ↔
    (∃ x : D.Apartment, GalleryGeometry.IsRegular D.affineRoots x ∧
      ∀ σ : K ≃ₐ[k] K,
        galoisAffineAction k K i D hD σ '' facet D.affineRoots x = facet D.affineRoots x) := by
  let e := apartmentAffineEquivOfCarrierEq D E hDE
  constructor
  · rintro ⟨y, hy, hstable⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, (isRegular_apartmentAffineEquivOfCarrierEq_iff k K i D E hDE x).1 hy,
      fun σ => (image_facet_galois_eq_iff_of_carrier_eq k K i D E hDE hD hE σ x).1
        (hstable σ)⟩
  · rintro ⟨x, hx, hstable⟩
    exact ⟨e x, (isRegular_apartmentAffineEquivOfCarrierEq_iff k K i D E hDE x).2 hx,
      fun σ => (image_facet_galois_eq_iff_of_carrier_eq k K i D E hDE hD hE σ x).2
        (hstable σ)⟩

end KPApartmentData

end Langlands.Geometry.Building
