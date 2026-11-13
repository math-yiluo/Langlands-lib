import Langlands.Representation.Exponents.ActualGeometricFullPiece

/-! # Naturality of the full-piece identification -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance fullPieceNaturalityAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
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

set_option maxHeartbeats 800000 in
/-- The identification of a full geometric-lemma piece with the transported representation
is natural: it intertwines the piece functor's map with the original morphism. -/
theorem fullPieceEquiv_naturality [IsIso D.p'] [IsIso D.q']
    {σ σ' : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    (a : σ ⟶ σ') (y : D.pieceFunctor.obj σ) :
    letI := leviPointTopology l hl
    D.fullPieceEquiv σ' ((D.pieceFunctor.map a).hom y) =
      SmoothRep.hom a (D.fullPieceEquiv σ y) := by
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
  let Jf := leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul'
  let eJ := fullParabolicLeviJacquetEquiv D.p' D.l' D.hp' D.hl'
    hl.isConnectedReductive D.r' D.hr' D.hmul' σ
  let eJ' := fullParabolicLeviJacquetEquiv D.p' D.l' D.hp' D.hl'
    hl.isConnectedReductive D.r' D.hr' D.hmul' σ'
  have hJ : ∀ w : Jf.obj σ, eJ' (SmoothRep.hom (Jf.map a) w) = SmoothRep.hom a (eJ w) := by
    intro w
    obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective σ.representation
      (pointImage (D.r' ≫ D.p')) 1 w
    change eJ' (Jacquet.Localization.mk σ'.representation (pointImage (D.r' ≫ D.p')) 1
      (SmoothRep.hom a x)) = SmoothRep.hom a (eJ (Jacquet.Localization.mk σ.representation
        (pointImage (D.r' ≫ D.p')) 1 x))
    simp only [eJ, eJ', fullParabolicLeviJacquetEquiv_mk]
  exact hJ (y.1.1 1)

/-- The full-piece identifications of all representations `σ`, packaged with their
naturality: a family of linear equivalences `D.pieceFunctor.obj σ ≃ σ` (intertwining
through the recovered Levi conjugacy) that commutes with every morphism `σ ⟶ σ'`. -/
def naturalFullPieceEquiv [IsIso D.p'] [IsIso D.q'] :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    {E : ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        (D.pieceFunctor.obj σ).ρ.Equiv
          (σ.representation.comp D.fullLeviPointsEquiv.symm.toMonoidHom) //
      ∀ {σ σ' : SmoothRep.{0, u, v} ℂ (rationalPoints M)} (a : σ ⟶ σ')
        (y : D.pieceFunctor.obj σ),
        E σ' ((D.pieceFunctor.map a).hom y) = SmoothRep.hom a (E σ y)} :=
  ⟨D.fullPieceEquiv, fun a y => D.fullPieceEquiv_naturality a y⟩

@[simp] theorem naturalFullPieceEquiv_val [IsIso D.p'] [IsIso D.q'] :
    D.naturalFullPieceEquiv.val = D.fullPieceEquiv := rfl

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
