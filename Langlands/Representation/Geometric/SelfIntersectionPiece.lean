import Langlands.Representation.Geometric.SelfIntersectionLevi
import Langlands.Representation.Geometric.DegenerateJacquetPieces
import Langlands.Representation.Exponents.IsoParabolicInduction

/-! # The identity piece of the geometric lemma for a full self-intersection

For one represented parabolic `P = MN` and a double coset `P z P` whose intersection
`P' = M ∩ zPz⁻¹` is all of `M`, the graded piece `i^M_{Q'} ∘ ι ∘ r^M_{P'}` of the geometric
lemma (Renard VI.5.1) is the twist of `ρ` by conjugation by `z`: the Jacquet restriction
along `P' = M` and the induction along `Q' = M` are both trivial, so only the restriction `ι`
along conjugation by `z` survives.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance selfPieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}

namespace GeometricLemmaIntersectionDatum

variable {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z)

/-- For a self-intersection datum at `P z P` with `P' = M`, the graded piece
`D.pieceFunctor.obj ρ` is linearly equivalent to `ρ`: the inverse of evaluation at `1` on
the induction along `Q' = M`, followed by the identification of the Jacquet module along
`P' = M` with `ρ`. -/
def selfPieceEquiv [IsIso D.p']
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    D.pieceFunctor.obj ρ ≃ₗ[ℂ] ρ :=
  haveI := hl.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  haveI := leviPoints_locallyCompactSpace p l hp hl
  haveI := leviPoints_nonarchimedeanGroup p l hp hl
  letI := leviPointTopology D.l' D.hl'
  letI := leviPointTopology D.lQ' D.hlQ'
  haveI := D.isIso_l'_of_isIso_p'
  haveI := D.isIso_q'_of_isIso_p'
  haveI := D.isIso_lQ'_of_isIso_p'
  (isoParabolicInductionEquiv D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ' D.hmulQ'
      ((SmoothRep.pullbackFunctor D.e).obj
        ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ))).trans
    (fullLeviJacquetEquiv D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' ρ)

/-- The equivalence `selfPieceEquiv` intertwines the action of `m ∈ M(F)` on the graded piece
with the action on `ρ` of the image of `m` under conjugation by `z`. -/
theorem selfPieceEquiv_representation [IsIso D.p']
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (m : rationalPoints M) (x : D.pieceFunctor.obj ρ) :
    letI := leviPointTopology l hl
    D.selfPieceEquiv ρ ((D.pieceFunctor.obj ρ).ρ m x) =
      ρ.representation (rationalPoints.map D.selfConjugation.hom m) (D.selfPieceEquiv ρ x) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  have := D.isIso_l'_of_isIso_p'
  have := D.isIso_q'_of_isIso_p'
  have := D.isIso_lQ'_of_isIso_p'
  obtain ⟨a, rfl⟩ : ∃ a, rationalPoints.map (D.lQ' ≫ D.q') a = m :=
    ⟨rationalPoints.map (inv (D.lQ' ≫ D.q')) m, by
      rw [← pointMap_comp_apply, IsIso.inv_hom_id]
      simp [rationalPoints.map_apply]⟩
  rw [D.selfConjugation_map_rationalPoints, ← D.e_apply]
  exact (congrArg (fullLeviJacquetEquiv D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' ρ)
    (isoParabolicInductionEquiv_map D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ' D.hmulQ' _ a x)).trans
      (fullLeviJacquetEquiv_representation D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' ρ (D.e a) _)

/-- The identity piece of the geometric lemma for a full self-intersection: if
`P' = M ∩ zPz⁻¹` is all of `M`, there is an automorphism `ψ` of `M` that is conjugation by `z`
inside `G`, and the graded piece `D.pieceFunctor.obj ρ` is linearly equivalent to `ρ` by an
equivalence intertwining the action of `m ∈ M(F)` with the action of `ψ(m)`. -/
theorem exists_selfPieceEquiv [IsIso D.p']
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    ∃ ψ : M ≅ M, ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom ∧
      ∃ T : D.pieceFunctor.obj ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : D.pieceFunctor.obj ρ),
        T ((D.pieceFunctor.obj ρ).ρ m x) =
          ρ.representation (rationalPoints.map ψ.hom m) (T x) :=
  ⟨D.selfConjugation, D.selfConjugation_comp, D.selfPieceEquiv ρ,
    D.selfPieceEquiv_representation ρ⟩

/-- For a supercuspidal `ρ` (its Jacquet modules along proper parabolics of `M` vanish), a
graded piece of the geometric lemma at a self-intersection datum either vanishes, or
`P' = M ∩ zPz⁻¹` is all of `M` and the piece is the twist of `ρ` by conjugation by `z`. -/
theorem subsingleton_or_exists_selfPieceEquiv
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hρ : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
        (hmul' : IsIso (subgroupMultiplication l' r')),
        ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) :
    letI := leviPointTopology l hl
    Subsingleton (D.pieceFunctor.obj ρ) ∨
      (IsIso D.p' ∧ ∃ ψ : M ≅ M, ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom ∧
        ∃ T : D.pieceFunctor.obj ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : D.pieceFunctor.obj ρ),
          T ((D.pieceFunctor.obj ρ).ρ m x) =
            ρ.representation (rationalPoints.map ψ.hom m) (T x)) := by
  by_cases h : IsIso D.p'
  · exact Or.inr ⟨h, D.exists_selfPieceEquiv ρ⟩
  · exact Or.inl (D.subsingleton_pieceFunctor_obj ρ
      (hρ _ _ _ D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' h))

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
