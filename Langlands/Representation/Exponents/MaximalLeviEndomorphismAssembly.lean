import Langlands.Representation.Filtration.HomGluing
import Langlands.Representation.Schur.RationalPoints
import Langlands.Representation.Schur.TwistedPieceHom
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs
import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.Representation.Geometric.SelfIntersectionPiece
import Langlands.Representation.Geometric.IdentityDoubleCoset

/-! Algebraic and adjunction assembly for the maximal-Levi endomorphism dichotomy. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u v

variable (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)

/-- The actual linear endomorphism-to-Jacquet-Hom equivalence supplied by proved
Frobenius reciprocity, at independent field and carrier universes. -/
def endomorphismReciprocityEquiv :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation.IntertwiningMap
            ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation ≃ₗ[ℂ]
          ((leviJacquetInductionFunctor p l r hp hr hl hmul p l r hp hr hl hmul).obj ρ).ρ.IntertwiningMap
            ρ.representation := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ
  exact (leviFrobeniusReciprocity k G hG P M U p l r hp hl hr hmul
    ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) ρ).choose

/-- The exact endomorphism dichotomy follows from the full represented geometric
lemma. The geometric lemma is an explicit premise of this conditional result. -/
theorem maximalLeviSupercuspidalInductionEndomorphism_of_geometricLemma
    (hgeo : RepresentedGeometricLemmaStatement.{u, v}) :
    MaximalLeviSupercuspidalInductionEndomorphismStatement.{u, v} := by
  classical
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N p l r hp hl hr hmul _hproper _hmax
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hirr hsuper f
  have : ρ.representation.IsIrreducible := hirr
  obtain ⟨n, c, z, hz, D, hglue⟩ :=
    hgeo k G hG P M N P M N p l r hp hl hr hmul p l r hp hl hr hmul
  have hsurj (ψ : M ≅ M) : Function.Surjective (rationalPoints.map ψ.hom) := by
    intro m
    refine ⟨rationalPoints.map ψ.inv m, ?_⟩
    rw [← pointMap_comp_apply, ψ.inv_hom_id]
    simp [rationalPoints.map_apply]
  have hscalar : ∀ a : ρ.representation.IntertwiningMap ρ.representation,
      ∃ b : ℂ, a = b • Representation.IntertwiningMap.id ρ.representation :=
    fun a => (Schur.leviPoint_scalarEndomorphism k l hl ρ hirr a).exists
  have hone : ∀ i : Fin n,
      HomSpace.length ((D i).pieceFunctor.obj ρ).ρ ρ.representation ≤ 1 := by
    intro i
    rcases (D i).subsingleton_or_exists_selfPieceEquiv ρ hsuper with
      hzero | ⟨_, ψ, _, T, hT⟩
    · have := hzero
      have hz : ∀ a : ((D i).pieceFunctor.obj ρ).ρ.IntertwiningMap ρ.representation,
          a = 0 := by
        intro a
        ext x
        change a.toLinearMap x = 0
        have hx : x = 0 := Subsingleton.elim _ _
        simp only [hx, map_zero]
      have : Subsingleton
          (((D i).pieceFunctor.obj ρ).ρ.IntertwiningMap ρ.representation) :=
        ⟨fun a b => (hz a).trans (hz b).symm⟩
      change Module.length ℂ _ ≤ 1
      simp only [Module.length_eq_zero, zero_le]
    · exact Schur.length_hom_le_one_of_twistedPiece
        ((D i).pieceFunctor.obj ρ).ρ ρ.representation
        (rationalPoints.map ψ.hom) (hsurj ψ) T hT hscalar
  let i₀ := identityDoubleCosetIndex (pointImage p) c
  rcases HomSpace.scalar_or_exists_off_piece_of_isGluedFrom
      ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation
      hglue ρ ρ.representation
      (endomorphismReciprocityEquiv k G hG P M N p l r hp hl hr hmul ρ)
      i₀ (hone i₀) (SmoothRep.hom f) with hscalarf | ⟨i, hi, S, hS⟩
  · left
    obtain ⟨a, ha⟩ := hscalarf
    refine ⟨a, fun x => ?_⟩
    have hx := congrArg (fun t => t x) ha
    exact hx
  · rcases (D i).subsingleton_or_exists_selfPieceEquiv ρ hsuper with
      hzero | ⟨_, ψ, hψ, T, hT⟩
    · exfalso
      apply hS
      ext x
      change S.toLinearMap x = 0
      have := hzero
      have hx : x = 0 := Subsingleton.elim _ _
      simp only [hx, map_zero]
    · right
      let E := Schur.inverseTwistedPieceEquiv ((D i).pieceFunctor.obj ρ).ρ
        ρ.representation (rationalPoints.map ψ.hom) (hsurj ψ) T hT S hS
      refine ⟨z i, ψ, hψ,
        (not_mem_pointImage_levi_of_ne_identityDoubleCosetIndex p l c z hz hi).1,
        E.toLinearEquiv, ?_⟩
      intro m x
      exact Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap m x

end Langlands.Aubert.General.RepresentedParabolic
