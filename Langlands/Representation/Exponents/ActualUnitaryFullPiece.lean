import Langlands.Representation.Exponents.ActualGeometricFullPiece
import Langlands.Representation.Exponents.TemperedGeometricLemmaStatement

/-! # Conjugacy from an actual full unitary geometric piece -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitaryFullPieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
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
  [IsIso D.p'] [IsIso D.q']
  {A' : CommGroupScheme (Spec (CommRingCat.of k))} {a' : A'.toGrp ⟶ D.M'}
  (ha' : IsSplitComponent a')
  (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))

set_option maxHeartbeats 800000 in
/-- Evaluation, inclusion of the actual unitary Jacquet part, and the full
Jacquet equivalence give an injective map to the original transported action. -/
def unitaryFullPieceEmbedding :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    {j : Representation.IntertwiningMap (D.unitaryPieceRep ha' σ).ρ
      (σ.representation.comp D.fullLeviPointsEquiv.symm.toMonoidHom) //
      Function.Injective j} := by
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
  let J₀ := leviUnitaryJacquetModule D.p' D.l' D.r' D.hp' D.hl'
    D.hr' D.hmul' ha' σ
  let i := SmoothRep.hom (leviUnitaryJacquetModuleι D.p' D.l' D.r'
    D.hp' D.hl' D.hr' D.hmul' ha' σ)
  let eJ := fullParabolicLeviJacquetEquiv D.p' D.l' D.hp' D.hl'
    hl.isConnectedReductive D.r' D.hr' D.hmul' σ
  let eI := fullParabolicLeviInductionEquiv D.q' D.lQ' D.hq' D.hlQ'
    hlQ.isConnectedReductive D.rQ' D.hrQ' D.hmulQ' (SmoothRep.pullback D.e J₀)
  let j : Representation.IntertwiningMap (D.unitaryPieceRep ha' σ).ρ
      (σ.representation.comp D.fullLeviPointsEquiv.symm.toMonoidHom) :=
    { toLinearMap := eJ.toLinearMap.comp (i.toLinearMap.comp eI.toLinearMap)
      isIntertwining' := by
        intro x
        ext f
        change ((leviInductionFunctor D.q' D.lQ' D.rQ' D.hq' D.hrQ'
          D.hlQ' D.hmulQ').obj (SmoothRep.pullback D.e J₀)) at f
        change eJ (i (eI
            (((leviInductionFunctor D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ'
              D.hmulQ').obj (SmoothRep.pullback D.e J₀)).representation x f))) =
          σ.representation (D.fullLeviPointsEquiv.symm x) (eJ (i (eI f)))
        erw [eI.toIntertwiningMap.isIntertwining]
        erw [i.isIntertwining]
        exact Representation.IntertwiningMap.isIntertwining
          (ρ := ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj
            σ).representation)
          (σ := σ.representation.comp (rationalPoints.map (D.l' ≫ D.p')))
          eJ.toIntertwiningMap _ _ }
  refine ⟨j, ?_⟩
  exact eJ.injective.comp
    ((leviUnitaryJacquetModuleι_injective D.p' D.l' D.r' D.hp'
      D.hl' D.hr' D.hmul' ha' σ).comp eI.injective)

set_option maxHeartbeats 800000 in
/-- A nonzero map from the actual unitary piece of full intersections yields
the precise conjugacy. Irreducibility makes the embedded unitary piece full. -/
def unitaryFullPieceConjugacyOfNonzeroMap
    (τ : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, w} ℂ (rationalPoints L))
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hτ : letI := leviPointTopology lQ hlQ; τ.IsIrreducible)
    (F : letI := leviPointTopology l hl
      letI := leviPointTopology lQ hlQ
      Representation.IntertwiningMap (D.unitaryPieceRep ha' σ).ρ τ.representation)
    (hF : F ≠ 0) :
    FullPieceConjugacy (p := p) (l := l) (q := q) (lQ := lQ)
      (hl := hl) (hlQ := hlQ) (z := z) σ τ := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  let e := D.fullLeviPointsEquiv
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
  letI : Representation.IsIrreducible
    (σ.representation.comp e.symm.toMonoidHom) := O.isSimpleOrder
  let j := D.unitaryFullPieceEmbedding ha' σ
  have hj : j.val ≠ 0 := by
    intro hjzero
    apply hF
    ext x
    have hx : x = 0 := j.property (by
      rw [hjzero]
      rfl)
    change F x = 0
    rw [hx, map_zero]
  have honto : Function.Surjective j.val :=
    (Representation.IsIrreducible.surjective_or_eq_zero j.val).resolve_right hj
  let E := j.val.ofBijective ⟨j.property, honto⟩
  let Efull := D.fullPieceEquiv σ
  let Ffull := F.comp (E.symm.toIntertwiningMap.comp Efull.toIntertwiningMap)
  have hFfull : Ffull ≠ 0 := by
    intro hz
    apply hF
    ext x
    have h := congrArg (fun t : Representation.IntertwiningMap
      (D.pieceFunctor.obj σ).ρ τ.representation => t (Efull.symm (E x))) hz
    change F (E.symm (Efull (Efull.symm (E x)))) = 0 at h
    change F x = 0
    simpa only [Representation.Equiv.apply_symm_apply,
      Representation.Equiv.symm_apply_apply] using h
  exact D.fullPieceConjugacyOfNonzeroMap σ τ hσ hτ Ffull hFfull

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
