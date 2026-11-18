import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Maps
import Langlands.GroupScheme.GeneratedFamily
import Langlands.GroupScheme.Lie.SmoothOpenSubgroup
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.Rational.VectorGroupDimension
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Smoothness of the split Cayley automorphism group scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitCayley

open GeneralLinear.DualNumber

/-! ### Dual-number matrices of root and torus elements -/

section DualMatrices

variable {A B : Type u} [CommRing A] [CommRing B]

theorem map_rootDerFun (f : A →+* B) (α : Root) (x : Fin 8 → A) :
    (fun i => f (rootDerFun α x i)) = rootDerFun α (fun i => f (x i)) := by
  cases α <;> funext i <;> fin_cases i <;>
    simp only [rootDerFun, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, map_sub, map_neg, map_zero]

theorem rootDer_map (f : A →+* B) (α : Root) : (rootDer α).map f = rootDer α := by
  ext i j
  rw [Matrix.map_apply, rootDer_apply, rootDer_apply,
    congrFun (map_rootDerFun f α (Pi.single j 1)) i]
  congr 1
  funext k
  by_cases hk : k = j
  · subst hk
    simp
  · simp [hk]

/-- At the dual-number parameter `ε`, every root element is `1 + εX_α`. -/
theorem rootMatrix_eps (α : Root) :
    rootMatrix α (DualNumber.eps : DualNumber A) = 1 + epsilonMatrix (rootDer α) := by
  refine Matrix.ext fun i j => ?_
  rw [rootMatrix, LinearMap.toMatrix'_apply]
  change rootFun α (DualNumber.eps : DualNumber A) (Pi.single j (1 : DualNumber A)) i = _
  rw [rootFun_eq, Matrix.add_apply, epsilonMatrix_apply]
  have hsq : (DualNumber.eps : DualNumber A) ^ 2 = 0 := by
    rw [pow_two, DualNumber.eps_mul_eps]
  have hD : rootDerFun α (Pi.single j (1 : DualNumber A)) i =
      TrivSqZeroExt.inl (rootDer (A := A) α i j) := by
    have h := congrFun (map_rootDerFun (TrivSqZeroExt.inlHom A A) α (Pi.single j 1)) i
    rw [← rootDer_apply] at h
    have hs : (Pi.single j (1 : DualNumber A) : Fin 8 → DualNumber A) =
        fun k => TrivSqZeroExt.inlHom A A ((Pi.single j (1 : A) : Fin 8 → A) k) := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [hk]
    rw [hs]
    exact h.symm
  simp only [hsq, zero_smul, add_zero, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
    hD]
  congr 1
  · by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Matrix.one_apply_ne hij]
  · refine TrivSqZeroExt.ext ?_ ?_ <;> simp

/-- The dual-number unit `1 + ε`. -/
def epsUnit : (DualNumber A)ˣ where
  val := 1 + DualNumber.eps
  inv := 1 - DualNumber.eps
  val_inv := by
    rw [mul_sub, add_mul, add_mul, one_mul, mul_one, one_mul, DualNumber.eps_mul_eps]
    abel
  inv_val := by
    rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, DualNumber.eps_mul_eps]
    abel

theorem epsUnit_inv_val : (((epsUnit (A := A))⁻¹ : (DualNumber A)ˣ) : DualNumber A) =
    1 - DualNumber.eps := rfl

theorem epsUnit_val : ((epsUnit (A := A) : (DualNumber A)ˣ) : DualNumber A) =
    1 + DualNumber.eps := rfl

/-- The torus element with parameters `(1 + ε, 1)` is `1 + εH₁`. -/
theorem torusGL_epsUnit_one :
    ((torusGL epsUnit 1 : GL (Fin 8) (DualNumber A)) : Matrix (Fin 8) (Fin 8) (DualNumber A)) =
      1 + epsilonMatrix (torusDer 1 0) := by
  rw [torusGL_val, torusDer, ← Matrix.diagonal_one]
  refine Matrix.ext fun i j => ?_
  rw [Matrix.add_apply, epsilonMatrix_apply, Matrix.diagonal_apply, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    fin_cases i <;>
      refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp [torusEntries, epsUnit_val, epsUnit_inv_val]
  · simp [hij]

/-- The torus element with parameters `(1, 1 + ε)` is `1 + εH₂`. -/
theorem torusGL_one_epsUnit :
    ((torusGL 1 epsUnit : GL (Fin 8) (DualNumber A)) : Matrix (Fin 8) (Fin 8) (DualNumber A)) =
      1 + epsilonMatrix (torusDer 0 1) := by
  rw [torusGL_val, torusDer, ← Matrix.diagonal_one]
  refine Matrix.ext fun i j => ?_
  rw [Matrix.add_apply, epsilonMatrix_apply, Matrix.diagonal_apply, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    fin_cases i <;>
      refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp [torusEntries, epsUnit_val, epsUnit_inv_val]
  · simp [hij]

end DualMatrices

variable {K : Type u} [Field K]

attribute [local instance] isAffineHom_generalLinear

/-! ### Lifting Lie elements along a monomorphism -/

section Lift

variable {H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H.X.hom]
  (f : H ⟶ (CayleyDatum.split K).automorphismGroup) [Mono f.hom.hom]

/-- The coordinate matrices of the Lie elements coming from `H`. -/
def liftRange : Submodule K (Matrix (Fin 8) (Fin 8) K) :=
  LinearMap.range ((lieMatrix (K := K) (A := K)).comp (Lie.targetMapLinear f K))

/-- A dual-number point of `H` whose image is `1 + εD` contributes `D` to `liftRange`. -/
theorem mem_liftRange_of_point (q : Lie.AffinePoints H (DualNumber K))
    (D : Matrix (Fin 8) (Fin 8) K)
    (hq : ((affinePointsEquiv K (CommAlgCat.of (CommRingCat.of K) (DualNumber K))
        (q ≫ f.hom.hom) : GL (Fin 8) (DualNumber K)) : Matrix (Fin 8) (Fin 8) (DualNumber K)) =
      1 + epsilonMatrix D) :
    D ∈ liftRange f := by
  have haut := (mem_automorphismSubgroup_split_iff _ _).mp
    (affinePointsEquiv K (CommAlgCat.of (CommRingCat.of K) (DualNumber K))
      (q ≫ f.hom.hom)).property
  rw [hq, isAutomorphism_one_add_epsilonMatrix_iff] at haut
  obtain ⟨X, hX⟩ := exists_lieMatrix_eq (K := K) D haut.1 haut.2
  have hXq : X.toMul.val = q ≫ f.hom.hom := by
    apply (affinePointsEquiv K (CommAlgCat.of (CommRingCat.of K) (DualNumber K))).injective
    apply Subtype.ext
    apply Units.ext
    rw [affinePointsEquiv_lieKernel, hX, hq]
  have hmem : q ∈ (Lie.reduction H (A := K)).ker := by
    apply mem_lieKernel_of_comp f q
    rw [← hXq]
    exact X.toMul.property
  refine ⟨Additive.ofMul ⟨q, hmem⟩, ?_⟩
  have hT : Lie.targetMapLinear f K (Additive.ofMul ⟨q, hmem⟩) = X := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hXq.symm
  change lieMatrix (Lie.targetMapLinear f K (Additive.ofMul ⟨q, hmem⟩)) = D
  rw [hT, hX]

omit [Mono f.hom.hom] in
/-- If all root and torus derivations come from `H`, then every Lie element of the automorphism
group lifts to `H`. -/
theorem lift_of_mem_liftRange (hroot : ∀ α : Root, rootDer α ∈ liftRange f)
    (h₁ : torusDer 1 0 ∈ liftRange f) (h₂ : torusDer 0 1 ∈ liftRange f)
    (X : lieKernel (CayleyDatum.split K).automorphismGroup K) :
    ∃ Y : lieKernel H K, Y.val ≫ f.hom.hom = X.val := by
  have hD := lieMatrix_mulVec_unit_and_isDerivation (K := K) (Additive.ofMul X)
  have hcomb := eq_derivCombination hD.2
  have hmem : lieMatrix (Additive.ofMul X) ∈ liftRange f := by
    rw [hcomb, derivCombination, torusDer_eq]
    refine add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem
      (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_)
      (add_mem (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)) <;>
    exact Submodule.smul_mem _ _ (hroot _)
  obtain ⟨Y, hY⟩ := hmem
  have hYX : Lie.targetMapLinear f K Y = Additive.ofMul X := lieMatrix_injective hY
  exact ⟨Y.toMul, congrArg (fun z => z.toMul.val) hYX⟩

end Lift

/-! ### The generating family -/

section Family

variable (K)

/-- The source group schemes of the generating family: one additive group per root and the
rank-two split torus. -/
def genGroup : Root ⊕ Unit → GroupScheme (Spec (CommRingCat.of K))
  | .inl _ => VectorGroup.groupScheme (CommRingCat.of K) 1
  | .inr _ => (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift.{u} (Fin 2))).toGrp

/-- The generating homomorphisms into the automorphism group scheme. -/
def genMap : ∀ j : Root ⊕ Unit, genGroup K j ⟶ (CayleyDatum.split K).automorphismGroup
  | .inl α => rootMap K α
  | .inr _ => torusMap K

variable {K}

theorem genGroup_hyp (j : Root ⊕ Unit) :
    Smooth (genGroup K j).X.hom ∧ IsAffineHom (genGroup K j).X.hom ∧
      ConnectedSpace (genGroup K j).X.left := by
  rcases j with α | _
  · refine ⟨?_, ?_, ?_⟩
    · show Smooth (VectorGroup.groupScheme (CommRingCat.of K) 1).X.hom
      have : SmoothOfRelativeDimension 1
          (VectorGroup.groupScheme (CommRingCat.of K) 1).X.hom :=
        VectorGroup.smoothOfRelativeDimension _ _
      exact SmoothOfRelativeDimension.smooth 1 _
    · change IsAffineHom
        (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 1) K))))
      infer_instance
    · change ConnectedSpace (Spec (CommRingCat.of (MvPolynomial (Fin 1) K)))
      infer_instance
  · exact ⟨smooth_splitTorus _, isAffineHom_splitTorus_spec _ _,
      IdentityComponent.connectedSpace_splitTorus _⟩

end Family

/-! ### Smoothness -/

/-- The automorphism group scheme of Zorn's split Cayley algebra over a field is smooth. -/
theorem smooth_automorphismGroup : Smooth (CayleyDatum.split K).automorphismGroup.X.hom := by
  have : Smooth (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X.hom :=
    GeneralLinear.smoothStatement _ _
  let incl := (CayleyDatum.split K).automorphismInclusion
  obtain ⟨H, i, hsm, haff, _, hgen⟩ := FiniteGeneration.exists_smooth_generated_family
    (A := genGroup K) (a := fun j => genMap K j ≫ incl) genGroup_hyp
  have : Smooth H.X.hom := hsm
  have : IsAffineHom H.X.hom := haff
  have hincl : IsClosedSubgroup incl :=
    Corepresented.isClosedSubgroup_cutHom (CayleyDatum.split K).isCutOutBy_automorphismIdeal
  have hle := hgen.2.2 _ incl hincl
    (fun j => ⟨(genMap K j).hom.hom, (Grp.comp_hom_hom _ _).symm⟩)
  have hrep : (SubgroupFunctor.range incl).IsRepresentedBy incl :=
    ⟨mono_automorphismInclusion, rfl⟩
  let f : H ⟶ (CayleyDatum.split K).automorphismGroup := hrep.factorHom i hle
  have hf : f ≫ incl = i := hrep.factorHom_comp i hle
  have hclosed : IsClosedSubgroup f :=
    IsClosedSubgroup.of_comp hincl (by rw [hf]; exact hgen.1)
  have : IsClosedImmersion f.hom.hom.left := hclosed
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  -- the matrix of a dual-number point of `H` through `f`
  have hpt : ∀ q : Lie.AffinePoints H (DualNumber K),
      ((affinePointsEquiv K (CommAlgCat.of (CommRingCat.of K) (DualNumber K))
        (q ≫ f.hom.hom) : GL (Fin 8) (DualNumber K)) : Matrix (Fin 8) (Fin 8) (DualNumber K)) =
      (GeneralLinear.affinePointsEquiv (Fin 8) (CommRingCat.of K)
        (CommAlgCat.of (CommRingCat.of K) (DualNumber K)) (q ≫ i.hom.hom) :
          Matrix (Fin 8) (Fin 8) (DualNumber K)) := by
    intro q
    rw [← hf, Grp.comp_hom_hom, ← Category.assoc, affinePointsEquiv_inclusion]
  refine smooth_of_fullLie_closed_subgroup _ H f hclosed
    (lift_of_mem_liftRange f ?_ ?_ ?_)
  · intro α
    obtain ⟨b, hb⟩ : FactorsThrough (rootMap K α ≫ incl).hom.hom i := hgen.2.1 (.inl α)
    refine mem_liftRange_of_point f (VectorGroup.affinePoint _ ![DualNumber.eps] ≫ b) _ ?_
    rw [hpt, Category.assoc, hb, affinePointsEquiv_rootMap_inclusion]
    exact rootMatrix_eps α
  · obtain ⟨b, hb⟩ : FactorsThrough (torusMap K ≫ incl).hom.hom i := hgen.2.1 (.inr ())
    refine mem_liftRange_of_point f
      (GeneralLinear.affineTorusPoint (R := CommRingCat.of K) (A := DualNumber K)
        (fun c => ![epsUnit, 1] c.down) ≫ b) _ ?_
    rw [hpt, Category.assoc, hb, affinePointsEquiv_torusMap, GeneralLinear.torusCoords_affineTorusPoint]
    exact torusGL_epsUnit_one
  · obtain ⟨b, hb⟩ : FactorsThrough (torusMap K ≫ incl).hom.hom i := hgen.2.1 (.inr ())
    refine mem_liftRange_of_point f
      (GeneralLinear.affineTorusPoint (R := CommRingCat.of K) (A := DualNumber K)
        (fun c => ![1, epsUnit] c.down) ≫ b) _ ?_
    rw [hpt, Category.assoc, hb, affinePointsEquiv_torusMap, GeneralLinear.torusCoords_affineTorusPoint]
    exact torusGL_one_epsUnit

end SplitCayley

end Langlands.GroupScheme
