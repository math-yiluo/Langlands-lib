import Langlands.GroupScheme.Commutative.MultiplicativePartHopf
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry

/-! # The multiplicative part of a commutative algebraic group (Milne 16.17): proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot

namespace MultiplicativePart

variable {k : Type u} [Field k]

/-- A connected group scheme over a field stays connected over every field extension: its unit
section makes it geometrically connected. -/
theorem connectedSpace_baseChange (G : GroupScheme (Spec (CommRingCat.of k)))
    [ConnectedSpace G.X.left] (K : Type u) [Field K] [Algebra k K] :
    ConnectedSpace ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.left := by
  have : GeometricallyConnected G.X.hom :=
    Langlands.AlgebraicGeometry.geometricallyConnected_of_connected_section G.X.hom
      η[G.X].left (Over.w η[G.X])
  exact DynamicBaseSmoothConnected.connectedSpace_baseChange _

/-- Smoothness and connectedness of the multiplicative part, by passage to an algebraic closure
and the character-lifting argument of `MultiplicativePartHopf`. -/
theorem smooth_connected {G S Q : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsCommMonObj G.X]
    [IsAffineHom Q.X.hom] (s : S ⟶ G) (q : G ⟶ Q) (hs : IsClosedSubgroup s)
    (hS : IsMultiplicativeType S) (hq : IsFppfQuotient (SubgroupFunctor.range s) q)
    (hQ : IsUnipotent Q) :
    (Smooth G.X.hom → Smooth S.X.hom) ∧ (ConnectedSpace G.X.left → ConnectedSpace S.X.left) := by
  let L := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  obtain ⟨h₁, h₂, h₃⟩ := fieldExtension_fpqc k L
  have : Surjective b := h₁
  have : Flat b := h₂
  have : QuasiCompact b := h₃
  let F := GroupScheme.baseChange b
  have hSL : IsMultiplicativeType (F.obj S) := isMultiplicativeType_baseChange hS L
  obtain ⟨N, hN, hNfg, ⟨eS0⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed (F.obj S) hSL
  have : IsAffineHom (F.obj G).X.hom := DynamicBaseSmoothConnected.isAffineHom_baseChange b
  have : IsAffineHom (F.obj Q).X.hom := DynamicBaseSmoothConnected.isAffineHom_baseChange b
  have : IsAffine (F.obj G).X.left := isAffine_of_isAffineHom (F.obj G).X.hom
  have : IsAffine (F.obj Q).X.left := isAffine_of_isAffineHom (F.obj Q).X.hom
  have : IsCommMonObj (F.obj G).X := Functor.isCommMonObj_obj (F := Over.pullback b) (M := G.X)
  have hsL : IsClosedSubgroup (F.map s) := hs.baseChange b
  have hqL : IsFppfQuotient (SubgroupFunctor.range (F.map s)) (F.map q) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b
  have hQL : IsUnipotent (F.obj Q) := hQ.baseChange
  let p := ringExpChar L
  -- transport of smoothness and connectedness from `D(N)` to `S_L`
  let eX : (F.obj S).X.left ≅ (Diagonalizable.groupScheme (CommRingCat.of L) N).toGrp.X.left :=
    (Over.forget _).mapIso ((Grp.forget _).mapIso eS0)
  have hw : (F.obj S).X.hom =
      eX.hom ≫ (Diagonalizable.groupScheme (CommRingCat.of L) N).toGrp.X.hom :=
    (Over.w eS0.hom.hom.hom).symm
  obtain ⟨hconn, hsmooth, -⟩ :=
    Diagonalizable.diagonalizableSmoothConnectedCriteria L p N
  refine ⟨fun hG => ?_, fun hG => ?_⟩
  · have : Smooth (F.obj G).X.hom := DynamicBaseSmoothConnected.smooth_baseChange b
    have hD : Smooth (Diagonalizable.groupScheme (CommRingCat.of L) N).X.hom :=
      hsmooth.mpr (eq_zero_of_smooth eS0 (F.map s) hsL (F.map q) hqL hQL p)
    have hD' : Smooth (Diagonalizable.groupScheme (CommRingCat.of L) N).toGrp.X.hom := hD
    have hSL' : Smooth (F.obj S).X.hom := by
      rw [hw]
      infer_instance
    exact smooth_of_baseChange b S hSL'
  · have : ConnectedSpace (F.obj G).X.left := connectedSpace_baseChange G L
    have hD : ConnectedSpace (Diagonalizable.groupScheme (CommRingCat.of L) N).X.left :=
      hconn.mpr (exists_pow_nsmul_eq_zero_of_connected eS0 (F.map s) hsL (F.map q) hqL hQL p)
    have hD' : ConnectedSpace (Diagonalizable.groupScheme (CommRingCat.of L) N).toGrp.X.left :=
      hD
    have hSL' : ConnectedSpace (F.obj S).X.left :=
      eX.inv.homeomorph.surjective.connectedSpace eX.inv.continuous
    exact connectedSpace_of_baseChange b S hSL'

end MultiplicativePart

open MultiplicativePart in
/-- **Milne, Note 16.17 and the remark after Theorem 16.13.** For a commutative affine algebraic
group `G` over a field with a closed subgroup `S` of multiplicative type and an fppf quotient
`G ⟶ Q` by `S` onto a unipotent group, `S` is the largest closed subgroup of multiplicative type,
the smallest closed subgroup with unipotent fppf quotient, its formation commutes with field
extension, and it is smooth or connected when `G` is. -/
theorem commutativeMultiplicativePartCharacterization :
    CommutativeMultiplicativePartCharacterizationStatement.{u} := by
  intro k _ G _ _ _ S Q s q hs hS hq hQ
  obtain ⟨hQa, -⟩ := quotient_affine_finiteType s hs hq
  refine ⟨fun H h _ hH => range_le_of_isUnipotent_quotient h hH s q hq hQ, ?_, ?_,
    (smooth_connected s q hs hS hq hQ).1, (smooth_connected s q hs hS hq hQ).2⟩
  · intro H Q' h q' hh hq' hQ'
    obtain ⟨hQ'a, -⟩ := quotient_affine_finiteType h hh hq'
    exact range_le_of_isUnipotent_quotient s hS h q' hq' hQ'
  · intro K _ _
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    refine ⟨isMultiplicativeType_baseChange hS K, fun H h _ hH => ?_⟩
    have hqK : IsFppfQuotient (SubgroupFunctor.range ((GroupScheme.baseChange b).map s))
        ((GroupScheme.baseChange b).map q) := by
      rw [SubgroupFunctor.range_baseChangeHom]
      exact hq.baseChange b
    have : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom :=
      DynamicBaseSmoothConnected.isAffineHom_baseChange b
    exact range_le_of_isUnipotent_quotient h hH _ _ hqK hQ.baseChange

end Langlands.GroupScheme
