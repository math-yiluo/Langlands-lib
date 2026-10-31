import Langlands.Representation.Classification.InductionWeakJacquetBoundsStatement
import Langlands.Representation.Classification.InductionWeakJacquetBoundsSpectral
import Langlands.Representation.Geometric.IntersectionChamberCoordinates
import Langlands.Representation.Parabolic.UpperRefinedJacquetAdmissibilityProof

/-!
# Weak upper Jacquet bounds of induced representations from the geometric lemma

For one pair of standard Levis, the geometric lemma places every standard
Jacquet exponent of an actual normalized induced representation in one graded
piece. That piece is refined induction of a transported refined Jacquet
module, so the exponent is the restriction, along the chamber index, of a
refined exponent of the source representation.
-/

noncomputable section

open CategoryTheory

namespace Langlands

open GeneralLinear Geometric

universe uG uM uF uV

/-- Isomorphic representations have the same generalized eigencharacters
after restriction along a common monoid homomorphism. -/
theorem isGeneralizedEigencharacter_comp_of_iso {G : Type uG} [Monoid G] {M : Type uM}
    [Monoid M] {X Y : Rep.{uV} ℂ G} (e : X ≅ Y) (ι : M →* G) (χ : M →* ℂˣ)
    (h : IsGeneralizedEigencharacter (X.ρ.comp ι) χ) :
    IsGeneralizedEigencharacter (Y.ρ.comp ι) χ := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hk
  let f : Representation.IntertwiningMap (X.ρ.comp ι) (Y.ρ.comp ι) :=
    { toLinearMap := e.hom.hom.toLinearMap
      isIntertwining' := fun m => e.hom.hom.isIntertwining' (ι m) }
  refine isGeneralizedEigencharacter_of_map_ne_zero f χ k hv ?_
  intro h0
  apply hv0
  have h1 : (e.hom ≫ e.inv).hom v = v := by
    rw [e.hom_inv_id]
    rfl
  rw [← h1]
  change e.inv.hom (f v) = 0
  rw [h0, map_zero]

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A standard Jacquet exponent of the induced representation is a generalized
eigencharacter of the block scalars on the value of the composite functor. -/
theorem isGeneralizedEigencharacter_jacquetInductionFunctor {n : ℕ} (B C : BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    ∀ (hσ : IsSmooth σ) (χ : (Fin C.length → F.Carrierˣ) →* ℂˣ),
      T.IsJacquetExponent C (T.normalizedParabolicInduced B σ) χ →
      IsGeneralizedEigencharacter
        (((jacquetInductionFunctor.{uF, uV} T B C).obj (SmoothRep.of σ hσ)).ρ.comp
          (C.blockScalarLevi F.Carrier)) χ := by
  intro _ _ hχ
  exact hχ.2

variable {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
  (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R)

/-- A generalized eigencharacter of the block scalars of `C` on one geometric
piece is the chamber restriction of a generalized eigencharacter of the
flattened block scalars on the refined Jacquet module. -/
theorem isGeneralizedEigencharacter_of_geometricPiece :
    letI := T.topology
    ∀ (σ' : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (χ : (Fin C.length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        (((geometricPieceFunctor T B C w S R hS hR).obj σ').ρ.comp
          (C.blockScalarLevi F.Carrier)) χ →
      IsGeneralizedEigencharacter
        (((T.normalizedRefinedJacquet B S σ'.representation).comp
          (flattenedBlockScalar B S F.Carrier)).comp
            (chamberRestriction B C w S F.Carrier)) χ := by
  let := T.topology
  intro σ' χ h1
  have h2 := isGeneralizedEigencharacter_of_normalizedRefinedInductionFunctorOf C R
    (T.refinedLeviHalfModulus C R) (T.refinedLeviHalfModulus_refinedBlockScalar C R) _ χ h1
  have h3 := (isGeneralizedEigencharacter_subgroupEqualityFunctor _ _ hR _
    (refinedBlockScalar C R) χ).mp h2
  have h4 : IsGeneralizedEigencharacter
      (((subgroupEqualityFunctor _ _ hS.symm).obj
          ((T.normalizedRefinedJacquetFunctor B S).obj σ')).representation.comp
        ((intersectionLeviConjugation F.Carrier B C w).symm.toMonoidHom.comp
        ((MulEquiv.subgroupCongr hR).symm.toMonoidHom.comp (refinedBlockScalar C R)))) χ :=
    h3
  have h5 := (isGeneralizedEigencharacter_subgroupEqualityFunctor _ _ hS.symm _ _ χ).mp h4
  have hcomp : (MulEquiv.subgroupCongr hS.symm).symm.toMonoidHom.comp
      ((intersectionLeviConjugation F.Carrier B C w).symm.toMonoidHom.comp
        ((MulEquiv.subgroupCongr hR).symm.toMonoidHom.comp (refinedBlockScalar C R))) =
      (flattenedBlockScalar B S F.Carrier).comp (chamberRestriction B C w S F.Carrier) := by
    refine MonoidHom.ext fun b => Subtype.ext ?_
    exact intersectionLeviConjugation_symm_blockScalar B C w S F.Carrier hS b _ rfl
  rw [hcomp] at h5
  exact h5

include hS in
/-- The chamber restriction of a refined exponent, evaluated at a globally
increasing scalar tuple, is bounded by the source premise. -/
theorem norm_le_one_of_geometricPiece {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hw : ∀ i, StrictMono (fun a : Fin (B.size i) => w (B.index i a))) :
    letI := T.topology
    IsAdmissible σ →
    (∀ (ψ : (Fin (B.flatten S).length → F.Carrierˣ) →* ℂˣ),
      IsOpen (ψ.ker : Set (Fin (B.flatten S).length → F.Carrierˣ)) →
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet B S σ).comp
          ((flattenedLeviEquiv F.Carrier B S).toMonoidHom.comp
            ((B.flatten S).blockScalarLevi F.Carrier))) ψ →
      ∀ a : Fin (B.flatten S).length → F.Carrierˣ,
        (∀ j : Fin B.length, Monotone (fun i : Fin (S j).length =>
          T.normalizedAbs (a (B.flattenBlockEquiv S ⟨j, i⟩) : F.Carrier))) →
        ‖(ψ a : ℂ)‖ ≤ 1) →
    ∀ (χ : (Fin C.length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        (((T.normalizedRefinedJacquet B S σ).comp (flattenedBlockScalar B S F.Carrier)).comp
          (chamberRestriction B C w S F.Carrier)) χ →
      ∀ a : Fin C.length → F.Carrierˣ,
        Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
        ‖(χ a : ℂ)‖ ≤ 1 := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  intro hadm hprem χ h6 a ha
  obtain ⟨ψ, hψo, hψg, hψβ⟩ := exists_eigencharacter_extension
    (T.normalizedRefinedJacquet B S σ)
    (Parabolic.isAdmissible_normalizedRefinedJacquet F T B S V σ hadm)
    (flattenedBlockScalar B S F.Carrier) (continuous_flattenedBlockScalar B S F.Carrier)
    (flattenedBlockScalar_commute B S F.Carrier)
    (chamberRestriction B C w S F.Carrier) χ h6
  have hmono : ∀ j : Fin B.length, Monotone (fun i : Fin (S j).length =>
      T.normalizedAbs
        (chamberRestriction B C w S F.Carrier a (B.flattenBlockEquiv S ⟨j, i⟩) :
          F.Carrier)) :=
    fun j => ha.comp (monotone_chamberIndex B C w S hS hw j)
  have hbound := hprem ψ hψo hψg _ hmono
  have hχa : χ a = ψ (chamberRestriction B C w S F.Carrier a) := by
    rw [← hψβ]
    rfl
  rw [hχa]
  exact hbound

/-- The weak upper Jacquet bound for one ambient block shape `C`, assuming the
geometric lemma for the pair `B, C`. -/
theorem induction_weakJacquetBound_of_geometricLemma
    (hgeo : GeometricLemmaTheorem.{uF, uV} T B C)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    IsAdmissible σ →
    (∀ (D : BlockRefinement B) (ψ : (Fin (B.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsOpen (ψ.ker : Set (Fin (B.flatten D).length → F.Carrierˣ)) →
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet B D σ).comp
          ((flattenedLeviEquiv F.Carrier B D).toMonoidHom.comp
            ((B.flatten D).blockScalarLevi F.Carrier))) ψ →
      ∀ a : Fin (B.flatten D).length → F.Carrierˣ,
        (∀ j : Fin B.length, Monotone (fun i : Fin (D j).length =>
          T.normalizedAbs (a (B.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) →
        ‖(ψ a : ℂ)‖ ≤ 1) →
    ∀ (χ : (Fin C.length → F.Carrierˣ) →* ℂˣ),
      T.IsJacquetExponent C (T.normalizedParabolicInduced B σ) χ →
      ∀ a : Fin C.length → F.Carrierˣ,
        Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
        ‖(χ a : ℂ)‖ ≤ 1 := by
  let := T.topology
  intro hadm hprem χ hχ a ha
  obtain ⟨S, R, hS, hR, m, e, hglued⟩ := hgeo
  obtain ⟨perm, s, hs⟩ := hglued
  let X : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) := SmoothRep.of σ hadm.1
  have h0 : IsGeneralizedEigencharacter
      (((jacquetInductionFunctor.{uF, uV} T B C).obj X).ρ.comp
        (C.blockScalarLevi F.Carrier)) χ :=
    T.isGeneralizedEigencharacter_jacquetInductionFunctor B C σ hadm.1 χ hχ
  obtain ⟨i, hi⟩ := s.exists_graded_isGeneralizedEigencharacter X
    (C.blockScalarLevi F.Carrier) χ h0
  obtain ⟨w, hw⟩ : ∃ w, w = e (perm i) := ⟨_, rfl⟩
  have iso : Nonempty (s.graded i ≅
      geometricPieceFunctor T B C w.val (S w) (R w) (hS w).2.1 (hR w).2.1) := by
    subst hw
    exact hs i
  have h1 : IsGeneralizedEigencharacter
      (((geometricPieceFunctor T B C w.val (S w) (R w) (hS w).2.1 (hR w).2.1).obj X).ρ.comp
        (C.blockScalarLevi F.Carrier)) χ :=
    isGeneralizedEigencharacter_comp_of_iso (iso.some.app X) _ χ hi
  have h6 := T.isGeneralizedEigencharacter_of_geometricPiece B C w.val (S w) (R w)
    (hS w).2.1 (hR w).2.1 X χ h1
  exact T.norm_le_one_of_geometricPiece B C w.val (S w) (hS w).2.1 σ w.2.1 hadm
    (hprem (S w)) χ h6 a ha

end PadicField.TopologicalData

/-- The weak upper Jacquet bounds of actual normalized induction follow from
the normalized geometric lemma. -/
theorem glInductionWeakJacquetBounds_of_geometricLemma
    (hgeo : PadicGeometricLemmaTheorem.{uF, uV}) :
    GLInductionWeakJacquetBoundsStatement.{uF, uV} := by
  intro p _ F T n hn B V _ _ σ _ hadm hprem C χ hχ a ha
  exact T.induction_weakJacquetBound_of_geometricLemma B C (hgeo p F T n hn B C) σ hadm hprem
    χ hχ a ha

end Langlands
