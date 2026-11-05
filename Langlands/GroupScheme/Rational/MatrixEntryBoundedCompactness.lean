import Langlands.GroupScheme.Rational.MatrixEntryBoundedCompactnessStatement
import Langlands.GroupScheme.GeneralLinearPointTopology
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedCompactness

/-! # Compactness from uniform matrix-entry bounds -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology MulOpposite
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {N : ℕ}

local instance : IsAffine (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X.left :=
  GeneralLinear.isAffine_groupScheme (Fin N) (CommRingCat.of F)

omit [IsAffine G.X.left] in
/-- Actual rational matrices agree with the canonical point homeomorphisms. -/
theorem rationalMatrix_eq_pointHomeomorph (ρ : MatrixRepresentation G (Fin N))
    (g : rationalPoints G) :
    ρ.rationalMatrix g =
      GeneralLinear.affinePointsHomeomorph (Fin N) (CommRingCat.of F)
        (CommAlgCat.of (CommRingCat.of F) F)
        (rationalPointsAffineHomeomorph (GeneralLinear.groupScheme (Fin N)
          (CommRingCat.of F)) (g ≫ ρ.hom.hom)) := by
  apply Units.ext
  ext i j
  rw [rationalMatrix_apply_apply, GeneralLinear.affinePointsHomeomorph_apply,
    GeneralLinear.affinePointsEquiv_entry_evaluation]
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      ((g ≫ ρ.hom.hom).left.appTop _) =
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      ((rationalPointsAffineHomeomorph _ (g ≫ ρ.hom.hom)).left.appTop _)
  rw [rationalPointsAffineHomeomorph_left]
  rfl

/-- A closed representation is a closed embedding on rational matrices in the
canonical rational-point topology. -/
theorem isClosedEmbedding_rationalMatrix [T2Space F]
    (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsClosedEmbedding ρ.rationalMatrix := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let H := GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)
  let : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
  let : TopologicalSpace (H.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    H.affinePointsTopologicalSpace _
  let e := (rationalPointsAffineHomeomorph H).trans
    (GeneralLinear.affinePointsHomeomorph (Fin N) (CommRingCat.of F)
      (CommAlgCat.of (CommRingCat.of F) F)).toHomeomorph
  have he := e.isClosedEmbedding.comp
    (isClosedEmbedding_rationalPointMap F ρ.hom.hom)
  convert he using 1
  funext g
  exact rationalMatrix_eq_pointHomeomorph ρ g

end MatrixRepresentation

/-- The exact internal compactness and algebraic-boundedness bridge. -/
theorem matrixEntryBoundedCompactness_proof :
    MatrixEntryBoundedCompactnessStatement.{u} := by
  intro F _ _ _ _ G _ N ρ hρ hb
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  obtain ⟨b, hb0, hb⟩ := hb
  let v := ValuativeRel.valuation F
  let K : Set (Matrix (Fin N) (Fin N) F) :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => {x | v x ≤ v b}))
  have hK : IsCompact K := isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall F _
  let e := Units.embedProduct (Matrix (Fin N) (Fin N) F) ∘ ρ.rationalMatrix
  have he : IsClosedEmbedding e :=
    Units.isClosedEmbedding_embedProduct.comp
      (ρ.isClosedEmbedding_rationalMatrix hρ)
  have hprod : IsCompact (K ×ˢ (opHomeomorph '' K)) :=
    hK.prod (hK.image opHomeomorph.continuous)
  have hcompact : IsCompact (Set.univ : Set (rationalPoints G)) := by
    apply (he.isCompact_preimage hprod).of_isClosed_subset isClosed_univ
    intro g hg
    constructor
    · intro i hi j hj
      exact (v.vle_iff_le).mp (hb g i j)
    · refine ⟨(((ρ.rationalMatrix g)⁻¹ : GL (Fin N) F) :
        Matrix (Fin N) (Fin N) F), ?_, rfl⟩
      intro i hi j hj
      have h := hb g⁻¹ i j
      rw [map_inv] at h
      exact (v.vle_iff_le).mp h
  refine ⟨hcompact, ?_⟩
  intro a
  let e₀ := (rationalPointHomeomorph F G.X).trans
    (affineSchemePointHomeomorph F G.X F)
  have hc : Continuous (fun p : rationalPoints G =>
      rationalPointAlgebraHom F G.X p a) :=
    (AlgPoint.continuous_eval a).comp e₀.continuous
  obtain ⟨c, hc0, hc⟩ := IsCompact.exists_valuative_bound (hcompact.image hc)
  exact ⟨c, hc0, fun p hp => hc _ ⟨p, hp, rfl⟩⟩

end Langlands.GroupScheme
