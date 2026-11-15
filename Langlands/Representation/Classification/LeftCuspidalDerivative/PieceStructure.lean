import Langlands.Representation.Classification.LeftCuspidalDerivative.PieceTools
import Langlands.Representation.Classification.LeftCuspidalDerivative.PieceTransport
import Langlands.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.Geometric.InducedPieceGrothendieck
import Langlands.Representation.Parabolic.FlattenedTensorOccurrences
import Langlands.Representation.Parabolic.RefinedFiniteLengthFunctorProof
import Langlands.Representation.Parabolic.RefinedInductionTensorProof
import Langlands.Representation.Classification.ProductLeviCuspidalJacquetAssembly
import Langlands.Representation.Classification.NormalizedProductFiniteLengthProof
import Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityProof
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
import Langlands.Representation.Smooth.Admissibility.FiniteLengthProof

/-!
# Constituents of one block of a geometric piece

Let `w` be a minimal representative for the block shapes `B` and `C` of `GL_n`, with
intersection refinements `S` of `B` and `R` of `C`, and let `Y` be a family of finite-length
representations of the blocks of `B`. Every irreducible subquotient `ρ` of the restriction to
the block `j₀` of `C` of the geometric piece of index `w`, applied to the external tensor
product of `Y`, is described by a family `X` of irreducible admissible representations of the
blocks of the flattened refinement of `B`:

* for each block `i` of `B`, the tensor product of the factors of `X` in the sub-blocks of `i`
  is a subquotient of the normalized Jacquet module of `Y i` along `S i`;
* `ρ` is a subquotient of the normalized induction along `R j₀` of the tensor product of the
  factors of `X`, relabelled by the block bijection of `w` and rank-cast to the sub-blocks of
  `j₀`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear Geometric CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- The external tensor product of finite-length representations of the blocks of a block
shape of positive rank has finite length. -/
theorem hasFiniteLength_externalSmoothObject (hn : 0 < n) (B : BlockShape n)
    (Y : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hY : letI := T.topology; ∀ i, (Y i).HasFiniteLength) :
    letI := T.topology
    (FiniteTensor.externalSmoothObject Y).HasFiniteLength := by
  let := T.topology
  have ha : ∀ i, (Y i).IsAdmissible := fun i =>
    (finiteLengthAdmissibility.{uF, uV} F T).1 _ (Y i) (hY i)
  obtain ⟨m, s, _, hs, _, _⟩ := FiniteTensor.padicExternalTensorFactors.{uF, uV, uV} p F T n hn
    B Y Y ha ha (fun i => ProductLengthProof.selfMatching_of_finiteLength (hY i))
  exact LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength ⟨s, hs⟩

/-- The action on an object of the normalized refined induction functor is the normalized
refined induced action of the underlying representation. -/
def refinedInductionObjEquiv (C : BlockShape n) (R : BlockRefinement C)
    (σ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier C R)) :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ((T.normalizedRefinedInductionFunctor.{uF, uV} C R).obj σ).representation.Equiv
      (T.normalizedRefinedInduced C R σ.representation) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  exact Representation.Equiv.refl _

set_option maxHeartbeats 1000000 in
/-- **Structure of the block constituents of a geometric piece.** An irreducible subquotient
`ρ` of the restriction to the block `j₀` of the geometric piece of index `w` applied to
`Y₀ ⊗ ⋯ ⊗ Y_{r-1}` is a subquotient of the normalized induction along `R j₀` of relabelled
factors of an irreducible admissible family `X` on the flattened refinement of `B`, whose
regrouped tensors are subquotients of the Jacquet modules of the `Y i` along `S i`. -/
theorem exists_factors_of_isSubquotient_geometricPiece (hn : 0 < n) (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (hmin : IsMinimalRepresentative B C w)
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R)
    (Y : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hY : letI := T.topology; ∀ i, (Y i).HasFiniteLength) (j₀ : Fin C.length)
    (ρ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.size j₀) F.Carrier))
    (hρ : letI := T.topology; ρ.IsIrreducible)
    (h : letI := T.topology
      WeylBranchPieces.IsSubquotient
        (((geometricPieceFunctor.{uF, max uF uV} T B C w S R hS hR).obj
            (FiniteTensor.externalSmoothObject Y)).ρ.comp
          (MonoidHom.mulSingle (fun i => GeneralLinear (C.size i) F.Carrier) j₀))
        ρ.representation) :
    letI := T.topology
    ∃ X : ∀ k : Fin (B.flatten S).length,
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((B.flatten S).size k) F.Carrier),
      (∀ k, (X k).IsIrreducible) ∧ (∀ k, (X k).IsAdmissible) ∧
      (∀ i, SmoothRep.IsSubquotient (Parabolic.flattenedBlockTensor T B S X i)
        ((T.normalizedJacquetFunctor (S i)).obj (Y i))) ∧
      WeylBranchPieces.IsSubquotient
        (T.normalizedParabolicInduced (R j₀)
          (Parabolic.flattenedBlockTensor T C R
            (fun k => T.castRank
              (size_blockEquiv_symm
                (conjugatesLevi_flattened_intersections F.Carrier B C w S R hS hR) k)
              (X ((blockEquiv
                (conjugatesLevi_flattened_intersections F.Carrier B C w S R hS hR)).symm k)))
            j₀).representation)
        ρ.representation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let hw := conjugatesLevi_flattened_intersections F.Carrier B C w S R hS hR
  -- The source: the refined Jacquet module of the external tensor product has finite length.
  have hYext : (FiniteTensor.externalSmoothObject Y).HasFiniteLength :=
    hasFiniteLength_externalSmoothObject T hn B Y hY
  let J := (T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj
    (FiniteTensor.externalSmoothObject Y)
  have hJ : J.HasFiniteLength :=
    (Parabolic.normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).2.1 n B S _ hYext
  -- The rest of the piece, followed by restriction to the block `j₀`, is exact.
  have hcont : Continuous
      (MonoidHom.mulSingle (fun i => GeneralLinear (C.size i) F.Carrier) j₀) :=
    continuous_mulSingle (A := fun i : Fin C.length => GeneralLinear (C.size i) F.Carrier) j₀
  let Φ := refinedIntersectionTransportFunctor.{uF, max uF uV} F.Carrier B C w S R hS hR ⋙
    T.normalizedRefinedInductionFunctor.{uF, max uF uV} C R ⋙
    restrictionFunctor (MonoidHom.mulSingle (fun i => GeneralLinear (C.size i) F.Carrier) j₀)
      hcont
  have hΦ : SmoothRep.PreservesFiniteLengthShortExact Φ :=
    SmoothRep.PreservesFiniteLengthShortExact.comp
      (refinedIntersectionTransportFunctor_preservesFiniteLength F.Carrier B C w S R hS hR)
      (refinedIntersectionTransportFunctor_preservesShortExact F.Carrier B C w S R hS hR)
      (SmoothRep.PreservesFiniteLengthShortExact.comp
        ((Parabolic.normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).1 n C R)
        ((Parabolic.normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).2.2.1 n C R)
        (restrictionFunctor_preservesFiniteLengthShortExact _ hcont))
  have hpiece : (CuspidalSupport.geometricPieceSmoothFunctor.{uF, max uF uV}
      F T B C w S R hS hR).obj (FiniteTensor.externalSmoothObject Y) =
      (T.normalizedRefinedInductionFunctor.{uF, max uF uV} C R).obj
        ((refinedIntersectionTransportFunctor.{uF, max uF uV} F.Carrier B C w S R hS hR).obj J) :=
    rfl
  have h0 := h
  rw [← CuspidalSupport.geometricPieceSmoothFunctor_obj_toRep, hpiece] at h0
  have h' : SmoothRep.IsSubquotient ρ (Φ.obj J) :=
    SmoothRep.isSubquotient_iff_representation.mpr h0
  obtain ⟨τ, hτ, hτJ, hρτ⟩ := exists_irreducible_of_isSubquotient_map_of_finiteLength hΦ hJ hρ h'
  -- Factor the irreducible constituent `τ` on the flattened Levi.
  let eB := flattenedLeviEquivContinuous F.Carrier B S
  let τ' := SmoothRep.pullback eB τ
  have hτ' : τ'.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff τ.representation eB).mpr hτ
  have hτ'a : τ'.IsAdmissible :=
    CuspidalSupport.irreducibleLeviAdmissibility.{uF, max uF uV} F T _ (B.flatten S) τ' hτ'
  obtain ⟨X, hXi, hXa, ⟨eX⟩⟩ := CuspidalSupport.padicLeviAdmissibleFactorization.{uF, max uF uV}
    p F T n hn (B.flatten S) τ' hτ' hτ'a
  refine ⟨X, hXi, hXa, ?_, ?_⟩
  · -- Source factors: `τ` is the refined tensor of the regrouped factors.
    let e : τ ≅ SmoothRep.pullback (refinedLeviEquivContinuous F.Carrier B S).symm
        (FiniteTensor.externalSmoothObject (Parabolic.flattenedBlockTensor T B S X)) :=
      (SmoothRep.pullbackSymmIso eB τ).symm ≪≫
        SmoothRep.mkIso (B := SmoothRep.pullback eB.symm (FiniteTensor.externalSmoothObject X))
          (FiniteTensorFiltration.compCongr eX eB.symm.toMonoidHom) ≪≫
          Parabolic.flattenedTensorRefinedIso T B S X
    exact Parabolic.subquotient_factor_of_refinedJacquet_external T B S Y
      (Parabolic.flattenedBlockTensor T B S X)
      (Parabolic.flattenedBlockTensor_isIrreducible T B S X hXi hXa) (hτJ.of_iso_left e)
  · -- Transport: the transported constituent is the tensor of the relabelled factors.
    let σ := (refinedIntersectionTransportFunctor.{uF, max uF uV} F.Carrier B C w S R hS hR).obj τ
    let eC := flattenedLeviEquivContinuous F.Carrier C R
    let X' : ∀ k : Fin (C.flatten R).length,
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((C.flatten R).size k) F.Carrier) :=
      fun k => T.castRank (size_blockEquiv_symm hw k) (X ((blockEquiv hw).symm k))
    have e1 := flattenedIntersectionTransportEquiv F.Carrier B C w S R hS hR hw τ
    have e2 : (transport (B.flatten S) (C.flatten R) w hw
        (τ.representation.comp (flattenedLeviEquiv F.Carrier B S).toMonoidHom)).Equiv
        (transport (B.flatten S) (C.flatten R) w hw
          (FiniteTensor.external (fun k => (X k).representation))) :=
      FiniteTensorFiltration.compCongr eX _
    have e3 := transportExternalCastEquiv T (isMinimalRepresentative_flatten S R hmin) hw X
    have eσ : (SmoothRep.pullback eC σ).representation.Equiv
        (FiniteTensor.externalSmoothObject X').representation :=
      e1.trans (e2.trans e3)
    -- Induction: the refined induction of a refined tensor is the tensor of the inductions.
    let A' := Parabolic.flattenedBlockTensor T C R X'
    let eσ' : σ ≅ SmoothRep.pullback (refinedLeviEquivContinuous F.Carrier C R).symm
        (FiniteTensor.externalSmoothObject A') :=
      (SmoothRep.pullbackSymmIso eC σ).symm ≪≫
        SmoothRep.mkIso (B := SmoothRep.pullback eC.symm (FiniteTensor.externalSmoothObject X'))
          (FiniteTensorFiltration.compCongr eσ eC.symm.toMonoidHom) ≪≫
          Parabolic.flattenedTensorRefinedIso T C R X'
    have eI : σ.representation.Equiv
        (Parabolic.RefinedInductionTensor.inducingRepresentation F T C R A') :=
      SmoothRep.equivOfIso eσ'
    obtain ⟨⟨E3, -⟩⟩ := Parabolic.refinedInductionTensor.{uF, max uF uV} p F T n C R A'
    have E : ((T.normalizedRefinedInductionFunctor.{uF, max uF uV} C R).obj σ).representation.Equiv
        (Parabolic.RefinedInductionTensor.externalRepresentation F T C R A') :=
      (refinedInductionObjEquiv T C R σ).trans
        ((ProductLeviCuspidalJacquetAssembly.normalizedRefinedInducedCongr T C R eI).trans E3)
    -- Restriction to the block `j₀`.
    have h1 : WeylBranchPieces.IsSubquotient
        (((T.normalizedRefinedInductionFunctor.{uF, max uF uV} C R).obj σ).representation.comp
          (MonoidHom.mulSingle (fun i => GeneralLinear (C.size i) F.Carrier) j₀))
        ρ.representation :=
      SmoothRep.isSubquotient_iff_representation.mp hρτ
    have h2 := WeylBranchPieces.IsSubquotient.of_equiv_left (FiniteTensorFiltration.compCongr E
      (MonoidHom.mulSingle (fun i => GeneralLinear (C.size i) F.Carrier) j₀)).symm h1
    exact isSubquotient_factor_of_external_comp_mulSingle
      (Parabolic.RefinedInductionTensor.blockRepresentations F T C R A') j₀ ρ.representation hρ h2

end Langlands.Classification.LeftCuspidalDerivative
