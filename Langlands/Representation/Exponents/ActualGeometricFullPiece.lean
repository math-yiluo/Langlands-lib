import Langlands.Representation.Exponents.FullParabolicLeviFunctors
import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Mathlib.RepresentationTheory.Irreducible

/-! # Conjugacy recovered from an actual full geometric piece -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance fullPieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)

/-- The full ambient Levi isomorphism supplied by the original intersection
isomorphism when both represented intersection parabolics are full. -/
def fullLeviConjugacy [IsIso D.p'] [IsIso D.q'] :
    {ε : M ≅ L // ε.hom ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso z⁻¹).hom} := by
  let ε := rationalLeviConjugacyOfFullParabolics D.hl' D.hlQ'
    hl.isConnectedReductive hlQ.isConnectedReductive
    (l ≫ p) (lQ ≫ q) (G.innerIso z) D.φ D.φ_comp
  refine ⟨ε.val, ?_⟩
  simpa only [innerIso_inv_hom, Category.assoc] using ε.property

/-- The corresponding topological equivalence of the original Levi point groups. -/
def fullLeviPointsEquiv [IsIso D.p'] [IsIso D.q'] :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    rationalPoints M ≃ₜ* rationalPoints L := by
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  exact ((fullParabolicLeviPointsEquiv D.p' D.l' D.hp' D.hl'
    hl.isConnectedReductive).symm.trans D.e.symm).trans
      (fullParabolicLeviPointsEquiv D.q' D.lQ' D.hq' D.hlQ'
        hlQ.isConnectedReductive)

omit [T2Space k] [IsAffineHom G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The topological equivalence is the point map of the constructed scheme
isomorphism, rather than an unrelated isomorphism of abstract point groups. -/
@[simp] theorem fullLeviPointsEquiv_apply [IsIso D.p'] [IsIso D.q']
    (m : rationalPoints M) :
    D.fullLeviPointsEquiv m = rationalPoints.map D.fullLeviConjugacy.val.hom m := by
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  let α := fullParabolicLeviPointsEquiv D.p' D.l' D.hp' D.hl' hl.isConnectedReductive
  let β := fullParabolicLeviPointsEquiv D.q' D.lQ' D.hq' D.hlQ' hlQ.isConnectedReductive
  let A := D.hl'.isoOfIsIsoParabolic (p := D.p') hl.isConnectedReductive
  let B := D.hlQ'.isoOfIsIsoParabolic (p := D.q') hlQ.isConnectedReductive
  have hα : α.symm m = rationalPoints.map A.inv m := by
    apply α.injective
    rw [α.apply_symm_apply]
    change m = rationalPoints.map A.hom (rationalPoints.map A.inv m)
    rw [← pointMap_comp_apply, Iso.inv_hom_id]
    rfl
  have he (x : rationalPoints D.M') :
      D.e.symm x = rationalPoints.map D.φ.inv x := by
    apply D.e.injective
    rw [D.e.apply_symm_apply, D.e_apply, ← pointMap_comp_apply, Iso.inv_hom_id]
    rfl
  change β (D.e.symm (α.symm m)) =
    rationalPoints.map ((A.inv ≫ D.φ.inv) ≫ B.hom) m
  rw [hα, he, fullParabolicLeviPointsEquiv_apply]
  change rationalPoints.map (D.lQ' ≫ D.q')
      (rationalPoints.map D.φ.inv (rationalPoints.map A.inv m)) =
    rationalPoints.map ((A.inv ≫ D.φ.inv) ≫ (D.lQ' ≫ D.q')) m
  simp only [pointMap_comp_apply]

set_option maxHeartbeats 800000 in
/-- The actual geometric-lemma piece for full intersection parabolics is the
original representation transported along the recovered Levi conjugacy. -/
def fullPieceEquiv [IsIso D.p'] [IsIso D.q']
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    (D.pieceFunctor.obj σ).ρ.Equiv
      (σ.representation.comp D.fullLeviPointsEquiv.symm.toMonoidHom) := by
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  let J := (leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ
  let eJ := fullParabolicLeviJacquetEquiv D.p' D.l' D.hp' D.hl'
    hl.isConnectedReductive D.r' D.hr' D.hmul' σ
  let eI := fullParabolicLeviInductionEquiv D.q' D.lQ' D.hq' D.hlQ'
    hlQ.isConnectedReductive D.rQ' D.hrQ' D.hmulQ' (SmoothRep.pullback D.e J)
  refine Representation.Equiv.mk (eI.toLinearEquiv.trans eJ.toLinearEquiv) ?_
  intro x
  ext f
  change ((leviInductionFunctor D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ'
    D.hmulQ').obj (SmoothRep.pullback D.e J)) at f
  change eJ (eI
      (((leviInductionFunctor D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ'
        D.hmulQ').obj (SmoothRep.pullback D.e J)).representation x f)) =
    σ.representation (D.fullLeviPointsEquiv.symm x) (eJ (eI f))
  erw [eI.toIntertwiningMap.isIntertwining]
  exact Representation.IntertwiningMap.isIntertwining
    (ρ := J.representation)
    (σ := σ.representation.comp (rationalPoints.map (D.l' ≫ D.p')))
    eJ.toIntertwiningMap _ _

/-- Actual data in the final conjugacy conclusion: the scheme isomorphism,
the ambient equation and a linear equivalence with the original point action. -/
structure FullPieceConjugacy
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (τ : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, w} ℂ (rationalPoints L)) where
  leviIso : M ≅ L
  conjugacy : leviIso.hom ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso z⁻¹).hom
  linearEquiv : σ ≃ₗ[ℂ] τ
  intertwines : letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    ∀ (m : rationalPoints M) (x : σ),
    linearEquiv (σ.representation m x) =
      τ.representation (rationalPoints.map leviIso.hom m) (linearEquiv x)

set_option maxHeartbeats 800000 in
/-- A nonzero map from an actual full geometric piece to an irreducible
representation recovers the precise conjugacy of the two original Levi data.
Fullness is an input, with no claim that a geometric intersection is full. -/
def fullPieceConjugacyOfNonzeroMap [IsIso D.p'] [IsIso D.q']
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (τ : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, w} ℂ (rationalPoints L))
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hτ : letI := leviPointTopology lQ hlQ; τ.IsIrreducible)
    (F : letI := leviPointTopology l hl
      letI := leviPointTopology lQ hlQ
      (D.pieceFunctor.obj σ).ρ.IntertwiningMap τ.representation) (hF : F ≠ 0) :
    FullPieceConjugacy (p := p) (l := l) (q := q) (lQ := lQ)
      (hl := hl) (hlQ := hlQ) (z := z) σ τ := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  let e := D.fullLeviPointsEquiv
  let E := D.fullPieceEquiv σ
  let f := F.comp E.symm.toIntertwiningMap
  have hf : f ≠ 0 := by
    intro hzero
    apply hF
    ext x
    have h := congrArg (fun t : Representation.IntertwiningMap
      (σ.representation.comp e.symm.toMonoidHom)
      τ.representation => t (E x)) hzero
    change F (E.symm (E x)) = 0 at h
    change F x = 0
    simpa only [Representation.Equiv.symm_apply_apply] using h
  let O : Subrepresentation (σ.representation.comp e.symm.toMonoidHom) ≃o
      Subrepresentation σ.representation :=
    { toFun := fun S => ⟨S.toSubmodule, fun m x hx => by
        have h := S.apply_mem_toSubmodule (e m) hx
        change σ.representation (e.symm (e m)) x ∈ S.toSubmodule at h
        simpa only [e.symm_apply_apply] using h⟩
      invFun := fun S => ⟨S.toSubmodule, fun m x hx =>
        S.apply_mem_toSubmodule (e.symm m) hx⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  letI : σ.representation.IsIrreducible := hσ
  letI : τ.representation.IsIrreducible := hτ
  letI : Representation.IsIrreducible
    (σ.representation.comp e.symm.toMonoidHom) := O.isSimpleOrder
  let T := f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)
  refine ⟨D.fullLeviConjugacy.val, D.fullLeviConjugacy.property, T.toLinearEquiv, ?_⟩
  intro m x
  change T (σ.representation m x) =
    τ.representation (rationalPoints.map D.fullLeviConjugacy.val.hom m) (T x)
  have h := Representation.IntertwiningMap.isIntertwining
    (ρ := σ.representation.comp e.symm.toMonoidHom)
    (σ := τ.representation) f (e m) x
  change T (σ.representation (e.symm (e m)) x) = τ.representation (e m) (T x) at h
  rw [e.symm_apply_apply] at h
  simpa only [e, D.fullLeviPointsEquiv_apply] using h

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
