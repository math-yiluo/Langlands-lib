import Langlands.GroupScheme.Reductive.PinningNumberingBaseChange
import Langlands.GroupScheme.Reductive.AlignedPinningBaseChange
import Langlands.GroupScheme.Torus.NumberedCharacterDescent
import Langlands.GroupScheme.OrthogonalMatrix.NumberedCoverVectorStatement

/-! # Descent of a supplied numbered vector eigenbasis -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

local instance numberedDescentAffine {S T : Scheme.{u}} (b : T ⟶ S)
    (G : GroupScheme S) [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  exact MorphismProperty.pullback_snd _ _ inferInstance

namespace SplitPinning

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- The three type-D root equations for an actual numbered split pinning. -/
def NumberedRootFamily (p : SplitPinning G) {n : ℕ} (hn : 2 ≤ n)
    (e : p.base.support ≃ Fin n) (eps : Fin n → characterLattice p.torus) : Prop :=
  (∀ (a : p.base.support) (h : (e a).val + 1 < n),
    p.rootDatum.root a.val = eps (e a) - eps ⟨(e a).val + 1, h⟩) ∧
  (∀ (a : p.base.support) (h : (e a).val + 1 = n),
    p.rootDatum.root a.val = eps ⟨n - 2, by omega⟩ + eps ⟨n - 1, by omega⟩) ∧
  (∀ i j : Fin n, i ≠ j → ∀ s t : ℤˣ, ∃ a : p.rootIndex,
    p.rootDatum.root a = (s : ℤ) • eps i + (t : ℤ) • eps j)

variable {L : Type u} [Field L] [Algebra F L] [Algebra.IsAlgebraic F L]

/-- Reindex the scalar-extended root equations by the actual simple-vertex
comparison, then descend them by the split-torus character equivalence. -/
theorem numberedRootFamily_descend (p : SplitPinning G) {n : ℕ} (hn : 2 ≤ n)
    (e : p.base.support ≃ Fin n)
    (eps : Fin n → characterLattice (p.baseChange (F := L)).torus)
    (h : (p.baseChange (F := L)).NumberedRootFamily hn
      (p.baseChangeNumbering (L := L) e) eps) :
    p.NumberedRootFamily hn e
      (characterLattice.descendFamily (algebraBaseMap F L) p.torus
        p.isSplitTorus eps) := by
  have hs : ∀ (a : p.base.support) (h : (e a).val + 1 < n),
      (SplitRootDatum.baseChange (algebraBaseMap F L) p.torus p.isSplitTorus
        p.rootDatum).root a.val = eps (e a) - eps ⟨(e a).val + 1, h⟩ := by
    intro a ha
    have h' := h.1 (p.baseChangeSimpleEquiv (F := L) a)
      (by simpa only [baseChangeNumbering_apply] using ha)
    change (SplitRootDatum.baseChange (algebraBaseMap F L) p.torus p.isSplitTorus
      p.rootDatum).root a.val = _ at h'
    simpa only [baseChangeNumbering_apply] using h' 
  have hl : ∀ (a : p.base.support) (h : (e a).val + 1 = n),
      (SplitRootDatum.baseChange (algebraBaseMap F L) p.torus p.isSplitTorus
        p.rootDatum).root a.val =
          eps ⟨n - 2, by omega⟩ + eps ⟨n - 1, by omega⟩ := by
    intro a ha
    have h' := h.2.1 (p.baseChangeSimpleEquiv (F := L) a)
      (by simpa only [baseChangeNumbering_apply] using ha)
    change (SplitRootDatum.baseChange (algebraBaseMap F L) p.torus p.isSplitTorus
      p.rootDatum).root a.val = _ at h'
    exact h' 
  exact SplitRootDatum.numbered_roots_descend (algebraBaseMap F L)
    p.torus p.isSplitTorus p.rootDatum p.base hn e eps hs hl h.2.2

end SplitPinning

namespace OrthogonalMatrix

variable {L : Type u} [Field L] {n : ℕ}
  {T : CommGroupScheme (Spec (CommRingCat.of L))}

/-- An actual inverse-right row eigenbasis, over every coefficient algebra. -/
def IsCharacterEigenbasis
    (rho : T.toGrp ⟶ groupScheme (Fin n) (CommRingCat.of L))
    {I : Type*} (chi : I → characterLattice T)
    (b : Basis I L ((Fin n ⊕ Fin n) → L)) : Prop :=
  ∀ (R : CommAlgCat.{u} (CommRingCat.of L))
    (t : GroupScheme.affinePoints T.toGrp R) (a : I),
    Matrix.vecMul (fun x => algebraMap L R (b a x))
      ((MatrixRepresentation.affineMatrix (inclusion (Fin n) (CommRingCat.of L))
        R (t ≫ rho.hom.hom))⁻¹ :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) =
      ((Gm.affineUnitsEquiv (CommRingCat.of L) R
        (t ≫ (CommGroupScheme.groupHom (chi a)).hom.hom) : Rˣ) : R) •
          (fun x => algebraMap L R (b a x))

end OrthogonalMatrix

namespace SplitPinning

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Algebra.IsAlgebraic F L]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (p : SplitPinning G) {n : ℕ}

local instance numberedDescentOrthogonalSmooth :
    Smooth (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).X.hom :=
  OrthogonalMatrix.smooth_groupScheme (Fin n) (CommRingCat.of L)

local instance numberedDescentOrthogonalAffine :
    IsAffineHom (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).X.hom :=
  OrthogonalMatrix.isAffineHom_groupScheme (Fin n) (CommRingCat.of L)

/-- The numbered-cover input gives descended roots and a full character
basis over an algebraic extension. The input itself is retained as a premise. -/
theorem numberedVectorBasis_baseChange_of_statement
    (hNumbered : OrthogonalMatrix.NumberedCoverVectorStatement.{u})
    (hn : 4 ≤ n)
    (hsc : IsSimplyConnected ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (pi : (GroupScheme.baseChange (algebraBaseMap F L)).obj G ⟶
      identityComponent (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)))
    (hpi : IsCentralIsogeny pi) (e : p.base.support ≃ Fin n)
    (hcartan : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.D n (e a) (e b))
    (halign : ∀ v : (p.baseChange (F := L)).base.support,
      (p.baseChangeNumbering (L := L) e v).val = 0 →
      (p.baseChange (F := L)).FundamentalWeightTrivialOnKernel v pi) :
    ∃ eps : Fin n → characterLattice (p.baseChange (F := L)).torus,
      p.NumberedRootFamily (by omega : 2 ≤ n) e
        (characterLattice.descendFamily (algebraBaseMap F L) p.torus p.isSplitTorus eps) ∧
      ∃ b : Basis (Fin n × ℤˣ) L ((Fin n ⊕ Fin n) → L),
        OrthogonalMatrix.IsCharacterEigenbasis
          ((p.baseChange (F := L)).inclusion ≫ pi ≫ identityComponentι
            (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)))
          (fun a : Fin n × ℤˣ => (a.2 : ℤ) • eps a.1) b := by
  obtain ⟨eps, hs, hl, hr, b, hb⟩ := hNumbered L n hn _
    (p.baseChange (F := L)) hsc pi hpi (p.baseChangeNumbering (L := L) e)
    (p.baseChangeNumbering_cartan e hcartan) halign
  refine ⟨eps, p.numberedRootFamily_descend (by omega) e eps ⟨hs, hl, hr⟩, b, ?_⟩
  intro R t a
  have hm : MatrixRepresentation.affineMatrix
      (pi ≫ identityComponentι
        (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)) ≫
          OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L)) R
      (t ≫ (p.baseChange (F := L)).inclusion.hom.hom) =
      MatrixRepresentation.affineMatrix
        (OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L)) R
        (t ≫ ((p.baseChange (F := L)).inclusion ≫ pi ≫ identityComponentι
          (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L))).hom.hom) := by
    change GeneralLinear.affinePointsEquiv _ _ R _ =
      GeneralLinear.affinePointsEquiv _ _ R _
    congr 1
  have h := hb R t a
  rw [hm] at h
  exact h

end SplitPinning
end Langlands.GroupScheme
