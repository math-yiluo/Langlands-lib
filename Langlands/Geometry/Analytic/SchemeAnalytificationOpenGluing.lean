import Langlands.Geometry.Analytic.SchemeAnalytificationRestrictionCoherence
import Langlands.Geometry.Analytic.SchemeAnalytificationBasicOpenRangeProof
import Langlands.Geometry.Analytic.SchemeAnalytificationGluingReduction

/-! # Affine-open restrictions and the analytification gluing -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory Opposite _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification

namespace OpenGluing

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

/-- The localization immersion theorem applies to the algebra structure induced by
any specified algebra map. -/
theorem isOpenEmbedding_baseMap_of_localization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (g : A →ₐ[K] B) (a : A)
    (h : letI := g.toRingHom.toAlgebra; IsLocalization.Away a B) :
    IsOpenEmbedding (AffineAnalytification.baseMap K P Q g) := by
  let : Algebra A B := g.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algHom g
  let : IsLocalization.Away a B := h
  have heq : IsScalarTower.toAlgHom K A B = g := by
    ext b
    rfl
  rw [← heq]
  exact AffineAnalytification.ImmersionComparison.isOpenEmbedding_baseMap_away K P Q a

/-- A restriction to a basic affine open induces an open embedding. -/
theorem isOpenEmbedding_localMap_basicOpen (U : X.affineOpens) (a : Γ(X, (U : X.Opens))) :
    IsOpenEmbedding (localMap K f (X.affineBasicOpen_le a)) :=
  isOpenEmbedding_baseMap_of_localization K
    (chartPresentation K f U) (chartPresentation K f (X.affineBasicOpen a))
    (restriction f (X.affineBasicOpen_le a)) (CenterRange.basicOpenGenerator f U a)
    (CenterRange.isLocalization_restriction_basicOpen f U a)

/-- Basic restrictions and their center-controlled ranges suffice for every
affine-open restriction to be an open embedding. -/
theorem isOpenEmbedding_localMap_of_basic
    (hRange : ∀ (U V : X.affineOpens) (h : (V : X.Opens) ≤ U),
      Set.range (localMap K f h) = localCenter K f U ⁻¹' (V : X.Opens))
    (hBasic : ∀ (U : X.affineOpens) (a : Γ(X, (U : X.Opens))),
      IsOpenEmbedding (localMap K f
        (show (⟨X.basicOpen a, U.2.basicOpen a⟩ : X.affineOpens).1 ≤ U from
          X.basicOpen_le a)))
    {U V : X.affineOpens} (hVU : (V : X.Opens) ≤ U) :
    IsOpenEmbedding (localMap K f hVU) := by
  have hinj : Function.Injective (localMap K f hVU) := by
    intro x y hxy
    have hc : localCenter K f V x = localCenter K f V y := by
      rw [← localCenter_localMap K f hVU x, ← localCenter_localMap K f hVU y, hxy]
    obtain ⟨a, haV, hxa⟩ := U.2.exists_basicOpen_le
      ⟨localCenter K f V x, center_ι_mem K f V x⟩ (hVU (center_ι_mem K f V x))
    let W : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
    have hWU : (W : X.Opens) ≤ U := X.basicOpen_le a
    have hWV : (W : X.Opens) ≤ V := haV
    have hxW : x ∈ Set.range (localMap K f hWV) := by
      rw [hRange V W hWV]
      exact hxa
    have hyW : y ∈ Set.range (localMap K f hWV) := by
      rw [hRange V W hWV]
      change localCenter K f V y ∈ X.basicOpen a
      rw [← hc]
      exact hxa
    obtain ⟨s, hs⟩ := hxW
    obtain ⟨t, ht⟩ := hyW
    have hst : s = t := (hBasic U a).injective (by
      change localMap K f hWU s = localMap K f hWU t
      rw [← localMap_trans K f hVU hWV s, ← localMap_trans K f hVU hWV t, hs, ht]
      exact hxy)
    rw [← hs, ← ht, hst]
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (localMap K f hVU).continuous hinj ?_
  intro S hS
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨a, haV, hxa⟩ := U.2.exists_basicOpen_le
    ⟨localCenter K f V x, center_ι_mem K f V x⟩ (hVU (center_ι_mem K f V x))
  let W : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
  have hWU : (W : X.Opens) ≤ U := X.basicOpen_le a
  have hWV : (W : X.Opens) ≤ V := haV
  have hxW : x ∈ Set.range (localMap K f hWV) := by
    rw [hRange V W hWV]
    exact hxa
  obtain ⟨s, hs⟩ := hxW
  have hO := (hBasic U a).isOpenMap _
    (hS.preimage (localMap K f hWV).continuous)
  have hmem : localMap K f hVU x ∈
      localMap K f hWU '' (localMap K f hWV ⁻¹' S) :=
    ⟨s, by simpa only [Set.mem_preimage, hs] using hx, by
      rw [← localMap_trans K f hVU hWV s, hs]⟩
  refine Filter.mem_of_superset (hO.mem_nhds hmem) ?_
  rintro w ⟨t, ht, rfl⟩
  exact ⟨localMap K f hWV t, ht, localMap_trans K f hVU hWV t⟩

/-- The center range formula implies open embeddings for every affine restriction. -/
theorem isOpenEmbedding_localMap_of_range
    (hRange : ∀ (U V : X.affineOpens) (h : (V : X.Opens) ≤ U),
      Set.range (localMap K f h) = localCenter K f U ⁻¹' (V : X.Opens))
    {U V : X.affineOpens} (hVU : (V : X.Opens) ≤ U) :
    IsOpenEmbedding (localMap K f hVU) :=
  isOpenEmbedding_localMap_of_basic K f hRange
    (fun U a => isOpenEmbedding_localMap_basicOpen K f U a) hVU

/-- Every affine-open restriction has the expected local-center range. -/
theorem range_localMap {U V : X.affineOpens} (hVU : (V : X.Opens) ≤ U) :
    Set.range (localMap K f hVU) = localCenter K f U ⁻¹' (V : Set X) :=
  CenterRange.range_localMap K f (basicOpenRangeData K f) (localMap_trans K f) hVU

/-- Every affine-open restriction induces an open embedding. -/
theorem isOpenEmbedding_localMap {U V : X.affineOpens} (hVU : (V : X.Opens) ≤ U) :
    IsOpenEmbedding (localMap K f hVU) :=
  isOpenEmbedding_localMap_of_range K f
    (fun _ _ h => range_localMap K f h) hVU

/-- The local restriction inputs to the quotient gluing argument hold. -/
theorem restrictionGluingData : GluingReduction.RestrictionGluingData K f :=
  ⟨localMap_refl K f, localMap_trans K f,
    isOpenEmbedding_localMap K f, range_localMap K f⟩

/-- Every affine chart is an open embedding into the analytification quotient. -/
theorem isOpenEmbedding_ι (U : X.affineOpens) :
    IsOpenEmbedding (ι K f U) :=
  GluingReduction.isOpenEmbedding_ι (restrictionGluingData K f) U

/-- The images of two affine charts meet in the charts contained in both. -/
theorem range_ι_inter (U V : X.affineOpens) :
    Set.range (ι K f U) ∩ Set.range (ι K f V) =
      ⋃ (W : X.affineOpens) (_ : (W : X.Opens) ≤ (U : X.Opens) ⊓ V),
        Set.range (ι K f W) :=
  GluingReduction.range_ι_inter (restrictionGluingData K f) U V

/-- For an affine scheme, its top chart is homeomorphic to the quotient space. -/
theorem isHomeomorph_ι_top [IsAffine X] :
    IsHomeomorph (ι K f ⟨⊤, isAffineOpen_top X⟩) :=
  GluingReduction.isHomeomorph_ι_top (restrictionGluingData K f)

/-- The four open gluing properties, without the separate separatedness criterion. -/
def AffineOpenGluing : Prop :=
  (∀ (U V : X.affineOpens) (h : (V : X.Opens) ≤ U),
    IsOpenEmbedding (localMap K f h)) ∧
  (∀ U : X.affineOpens, IsOpenEmbedding (ι K f U)) ∧
  (∀ U V : X.affineOpens, Set.range (ι K f U) ∩ Set.range (ι K f V) =
    ⋃ (W : X.affineOpens) (_ : (W : X.Opens) ≤ (U : X.Opens) ⊓ V),
      Set.range (ι K f W)) ∧
  (∀ [IsAffine X], IsHomeomorph (ι K f ⟨⊤, isAffineOpen_top X⟩))

/-- The scheme analytification satisfies the four open gluing properties. -/
theorem affineOpenGluing : AffineOpenGluing K f :=
  ⟨fun _ _ h => isOpenEmbedding_localMap K f h, isOpenEmbedding_ι K f,
    range_ι_inter K f, isHomeomorph_ι_top K f⟩

end OpenGluing

end Langlands.Analytic.SchemeAnalytification
