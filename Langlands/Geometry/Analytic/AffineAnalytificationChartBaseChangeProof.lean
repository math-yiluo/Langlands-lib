import Langlands.Geometry.Analytic.AffineAnalytificationChartBaseChangeStatement

/-! # The fixed-radius comparison of affine charts under ground field extension -/

noncomputable section

universe u u' v w

namespace Langlands.Analytic.AffineAnalytification

open GeneralizedTateAlgebra PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension
open scoped TensorProduct

section LiftChart

variable {F : Type u} [NormedField F] [IsUltrametricDist F]
  {A : Type v} [CommRing A] [Algebra F A] (P : FinitePolynomialPresentation F A)
  (r : PositivePolyradius (Fin P.arity))
  {E : Type w} [NormedCommRing E] [NormedAlgebra F E] [IsUltrametricDist E] [CompleteSpace E]
  (g : A →ₐ[F] E)
  (hg : HasBoundedMonomials r E (fun i => g (P.map (MvPolynomial.X i))))

include hg in
private theorem eval_poly (p : MvPolynomial (Fin P.arity) F) :
    evaluate r F E (fun i => g (P.map (MvPolynomial.X i)))
      (GeneralizedTateAlgebra.polynomialMap r F p) = g (P.map p) := by
  have h : (evaluateHom r F E (fun i => g (P.map (MvPolynomial.X i))) hg).toAlgHom.comp
      (GeneralizedTateAlgebra.polynomialMap r F) = g.comp P.map := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, GeneralizedTateAlgebra.polynomialMap, MvPolynomial.aeval_X]
    exact evaluate_X r F E _ i
  exact DFunLike.congr_fun h p

private def liftChart : BoundedAlgHom F (PolynomialLocus.chart P r) E :=
  evaluateRelations F E P.arity r (PolynomialLocus.relations P r)
    (fun i => g (P.map (MvPolynomial.X i))) hg (by
      rintro _ ⟨p, hp, rfl⟩
      change P.map p = 0 at hp
      rw [eval_poly P r g hg, hp, map_zero])

private theorem liftChart_algebraMap (a : A) :
    liftChart P r g hg (PolynomialLocus.algebraMap P r a) = g a := by
  obtain ⟨p, rfl⟩ := P.surjective a
  rw [PolynomialLocus.algebraMap_map]
  exact eval_poly P r g hg p

end LiftChart

set_option maxHeartbeats 1200000 in
/-- The ground field extension of each fixed-radius affine chart is the chart of
the algebraic base change at the same radius. -/
theorem affineAnalytificationChartBaseChange :
    AffineAnalytificationChartBaseChangeStatement.{u, u', v} := by
  intro K _ _ _ L _ _ _ _ A _ _ P r
  let Q := baseChangePresentation K L P
  let B := PolynomialLocus.chart P r
  let BL := PresentedAffinoidAlgebra.GroundFieldExtension.algebra K L B
  let C := PolynomialLocus.chart Q r
  let : NormedAlgebra K C := NormedAlgebra.restrictScalars K L C
  let : IsScalarTower K L C := IsScalarTower.of_algebraMap_eq' rfl
  let q : A →ₐ[K] C :=
    ((PolynomialLocus.algebraMap Q r).restrictScalars K).comp Algebra.TensorProduct.includeRight
  let p : A →ₐ[K] BL := (iota K L B).toAlgHom.comp (PolynomialLocus.algebraMap P r)
  let pL : L ⊗[K] A →ₐ[L] BL := Algebra.TensorProduct.liftEquivRight K L A BL p
  have hP (i : Fin P.arity) :
      PolynomialLocus.algebraMap P r (P.map (MvPolynomial.X i)) = coordinate K B i :=
    (PolynomialLocus.algebraMap_map P r (MvPolynomial.X i)).trans
      (PolynomialLocus.polynomialMap_X P r i)
  have hQ (i : Fin Q.arity) :
      PolynomialLocus.algebraMap Q r (Q.map (MvPolynomial.X i)) = coordinate L C i :=
    (PolynomialLocus.algebraMap_map Q r (MvPolynomial.X i)).trans
      (PolynomialLocus.polynomialMap_X Q r i)
  have hq (i : Fin P.arity) : q (P.map (MvPolynomial.X i)) = coordinate L C i :=
    (congrArg (fun a : L ⊗[K] A => PolynomialLocus.algebraMap Q r a)
      (baseChangePresentation_map_X K L P i).symm).trans (hQ i)
  have hiota (i : Fin P.arity) :
      iota K L B (PolynomialLocus.algebraMap P r (P.map (MvPolynomial.X i))) = coordinate L BL i :=
    (congrArg (fun x : B => iota K L B x) (hP i)).trans (iota_coordinate K L B i)
  have hp (i : Fin Q.arity) : pL (Q.map (MvPolynomial.X i)) = coordinate L BL i := by
    refine (congrArg (fun b : L ⊗[K] A => pL b) (baseChangePresentation_map_X K L P i)).trans ?_
    change algebraMap L BL 1 * p (P.map (MvPolynomial.X i)) = _
    rw [map_one, one_mul]
    exact hiota i
  have hqM : HasBoundedMonomials r C (fun i => q (P.map (MvPolynomial.X i))) := by
    refine ⟨1, one_pos, fun d => ?_⟩
    rw [one_mul]
    exact monomialValue_norm_le_weight r C (norm_one_le L C) _
      (fun i => (congrArg norm (hq i)).trans_le (norm_coordinate_le L C i)) d
  have hpM : HasBoundedMonomials r BL (fun i => pL (Q.map (MvPolynomial.X i))) := by
    refine ⟨1, one_pos, fun d => ?_⟩
    rw [one_mul]
    exact monomialValue_norm_le_weight r BL (norm_one_le L BL) _
      (fun i => (congrArg norm (hp i)).trans_le (norm_coordinate_le L BL i)) d
  let qB : BoundedAlgHom K B C := liftChart P r q hqM
  let f : BoundedAlgHom L BL C := PresentedAffinoidAlgebra.GroundFieldExtension.lift K L B C qB
  let g : BoundedAlgHom L C BL := liftChart Q r pL hpM
  have hf (a : A) : f (iota K L B (PolynomialLocus.algebraMap P r a)) = q a := by
    exact (lift_iota K L B C qB _).trans (liftChart_algebraMap P r q hqM a)
  have hfC (i : Fin P.arity) : f (coordinate L BL i) = coordinate L C i :=
    (congrArg (fun x : BL => f x) (hiota i)).symm.trans ((hf _).trans (hq i))
  have hgC (i : Fin P.arity) : g (coordinate L C i) = coordinate L BL i :=
    (congrArg (fun x : C => g x) (hQ i)).symm.trans
      ((liftChart_algebraMap Q r pL hpM (Q.map (MvPolynomial.X i))).trans (hp i))
  have hgf : g.comp f = BoundedAlgHom.id L BL := by
    apply hom_ext_coordinate L BL BL
    intro i
    exact (congrArg (fun x : C => g x) (hfC i)).trans (hgC i)
  have hfg : f.comp g = BoundedAlgHom.id L C := by
    apply hom_ext_coordinate L C C
    intro i
    exact (congrArg (fun x : BL => f x) (hgC i)).trans (hfC i)
  refine ⟨BoundedAlgEquiv.ofHomInv f g (fun x => congrArg (fun m : BoundedAlgHom L BL BL => m x) hgf)
    (fun x => congrArg (fun m : BoundedAlgHom L C C => m x) hfg), ?_⟩
  exact hf

end Langlands.Analytic.AffineAnalytification
