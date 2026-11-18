import Langlands.GroupScheme.Composition.CayleyGrading
import Langlands.GroupScheme.Torus.RingRepresentationWeights
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Upper bound for the split rank of Cayley automorphism group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix

namespace Langlands.GroupScheme.CayleyDatum

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type u} [Field K] (c : CayleyDatum K)

/-! ### Change of coefficients -/

section Coefficients

variable {A B : Type u} [CommRing A] [CommRing B]

theorem map_mulVec_comp (ψ : A →+* B) (M : Matrix (Fin 8) (Fin 8) A) (v : Fin 8 → A) :
    M.map ψ *ᵥ (ψ ∘ v) = ψ ∘ (M *ᵥ v) := by
  funext i
  exact (RingHom.map_mulVec ψ M v i).symm

/-- The extended multiplication commutes with a further change of coefficients. -/
theorem multiplicationOver_comp (φ : K →+* A) (ψ : A →+* B) (x y : CayleyVector A) :
    c.multiplicationOver (ψ.comp φ) (ψ ∘ x) (ψ ∘ y) = ψ ∘ c.multiplicationOver φ x y := by
  funext i
  simp only [multiplicationOver, Function.comp_apply, map_sum, map_mul, RingHom.comp_apply]

theorem unitOver_eq (φ : K →+* A) : c.unitOver φ = fun i => φ (c.unit i) := rfl

theorem unitOver_comp (φ : K →+* A) (ψ : A →+* B) :
    c.unitOver (ψ.comp φ) = ψ ∘ c.unitOver φ := rfl

/-- The extended multiplication of vectors with coefficients in `K`. -/
theorem multiplicationOver_algebraMap (φ : K →+* A) (x y : CayleyVector K) :
    c.multiplicationOver φ (fun i => φ (x i)) (fun i => φ (y i)) =
      fun i => φ (c.multiplication x y i) := by
  have h := c.multiplicationOver_comp (RingHom.id K) φ x y
  rw [RingHom.comp_id, multiplicationOver_self] at h
  exact h

/-- Automorphism matrices descend along injective coefficient maps. -/
theorem IsAutomorphismMatrix.of_map {φ : K →+* A} {ψ : A →+* B} (hψ : Function.Injective ψ)
    {g : GL (Fin 8) A}
    (h : c.IsAutomorphismMatrix (ψ.comp φ) (Matrix.GeneralLinearGroup.map ψ g)) :
    c.IsAutomorphismMatrix φ g := by
  have hg : ((Matrix.GeneralLinearGroup.map ψ g : GL (Fin 8) B) : Matrix (Fin 8) (Fin 8) B) =
      (g : Matrix (Fin 8) (Fin 8) A).map ψ := rfl
  have hinj : ∀ v w : Fin 8 → A, ψ ∘ v = ψ ∘ w → v = w := fun v w hvw =>
    funext fun i => hψ (congrFun hvw i)
  refine ⟨hinj _ _ ?_, fun x y => hinj _ _ ?_⟩
  · have h1 := h.1
    rw [hg, c.unitOver_comp, map_mulVec_comp] at h1
    exact h1
  · have h2 := h.2 (ψ ∘ x) (ψ ∘ y)
    rw [hg, c.multiplicationOver_comp, map_mulVec_comp, map_mulVec_comp, map_mulVec_comp,
      c.multiplicationOver_comp] at h2
    exact h2

end Coefficients

/-! ### Homogeneous monomials in the group algebra -/

section Monomials

variable {M : Type u} [AddCommGroup M] [DecidableEq M]

omit [DecidableEq M] in
theorem algebraMap_addMonoidAlgebra (r : K) :
    algebraMap K (AddMonoidAlgebra K M) r = AddMonoidAlgebra.single 0 r := rfl

/-- The extended product of two homogeneous vectors of degrees `a` and `b` is homogeneous of
degree `a + b`. -/
theorem multiplicationOver_single (a b : M) (x y : CayleyVector K) :
    c.multiplicationOver (algebraMap K (AddMonoidAlgebra K M))
        (fun i => AddMonoidAlgebra.single a (x i)) (fun i => AddMonoidAlgebra.single b (y i)) =
      fun i => AddMonoidAlgebra.single (a + b) (c.multiplication x y i) := by
  funext i
  apply AddMonoidAlgebra.coeff_injective
  ext n
  rw [c.multiplication_apply_eq_sum]
  simp only [multiplicationOver, algebraMap_addMonoidAlgebra, AddMonoidAlgebra.single_mul_single,
    zero_add, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  split_ifs <;> simp

end Monomials

/-! ### The weight grading of a split torus -/

section Universal

open SplitTorusRepresentationWeights splitTorus

variable {c} {H : GroupScheme (Spec (CommRingCat.of K))}
  {iH : H ⟶ GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)}
  (hrep : c.IsAutomorphismRepresentation iH)
  (I : Type u) [Fintype I] [DecidableEq I]
  (j : splitTorus (Spec (CommRingCat.of K)) I ⟶ H)

include hrep in
/-- The matrix of the universal torus point is an automorphism matrix over `K[ℤ^I]`. -/
theorem isAutomorphismMatrix_universalMatrix :
    c.IsAutomorphismMatrix (algebraMap K (AddMonoidAlgebra K (I → ℤ)))
      (universalMatrix iH I j) := by
  let S : CommAlgCat (CommRingCat.of K) :=
    CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K (I → ℤ))
  let x : (algSpec (CommRingCat.of K)).obj (op S) ⟶
      (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X :=
    universalPoint (R := CommRingCat.of K) I ≫ j.hom.hom ≫ iH.hom.hom
  have hx : x ∈ (SubgroupFunctor.range iH).carrier ((algSpec (CommRingCat.of K)).obj (op S)) :=
    SubgroupFunctor.mem_range.mpr
      ⟨universalPoint (R := CommRingCat.of K) I ≫ j.hom.hom, Category.assoc _ _ _⟩
  have h := (hrep.2 _ x).mp hx
  rw [GeneralLinear.pointsEquiv_eq_affinePointsEquiv] at h
  let ψ := (Corepresented.affineSectionsIso S).inv.hom
  have hψ : Function.Injective ψ :=
    (ConcreteCategory.bijective_of_isIso (Corepresented.affineSectionsIso S).inv).1
  refine IsAutomorphismMatrix.of_map c (ψ := ψ.toRingHom) hψ ?_
  have hφ : ψ.toRingHom.comp (algebraMap K (AddMonoidAlgebra K (I → ℤ))) =
      algebraMap (CommRingCat.of K)
        ((algΓ (CommRingCat.of K)).obj ((algSpec (CommRingCat.of K)).obj (op S))).unop :=
    ψ.comp_algebraMap
  rw [hφ]
  exact h

/-- The coefficient of `m` in the universal matrix applied to a constant vector is the weight
projector of `m` applied to that vector. -/
theorem coeff_universalMatrix_mulVec (v : CayleyVector K) (n : I → ℤ) (i : Fin 8) :
    (((universalMatrix iH I j : Matrix (Fin 8) (Fin 8) (AddMonoidAlgebra K (I → ℤ))) *ᵥ
      fun b => algebraMap K (AddMonoidAlgebra K (I → ℤ)) (v b)) i).coeff n =
      (weight iH I j n *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Algebra.commutes, ← Algebra.smul_def, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    smul_eq_mul, mul_comm]
  rfl

/-- A vector of weight `a` becomes the monomial of degree `a` under the universal matrix. -/
theorem universalMatrix_mulVec_of_weight {a : I → ℤ} {x : CayleyVector K}
    (hx : weight iH I j a *ᵥ x = x) :
    ((universalMatrix iH I j : Matrix (Fin 8) (Fin 8) (AddMonoidAlgebra K (I → ℤ))) *ᵥ
      fun b => algebraMap K (AddMonoidAlgebra K (I → ℤ)) (x b)) =
      fun i => AddMonoidAlgebra.single a (x i) := by
  funext i
  apply AddMonoidAlgebra.coeff_injective
  ext n
  rw [coeff_universalMatrix_mulVec, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : a = n
  · subst h
    rw [hx, ite_eq_left rfl]
  · rw [ite_eq_right h, ← hx, Matrix.mulVec_mulVec, weight_mul_weight, ite_eq_right (Ne.symm h),
      Matrix.zero_mulVec]
    rfl

include hrep in
/-- The weight grading of the Cayley datum defined by a split torus of the automorphism
group scheme. -/
def weightGrading : c.Grading (I → ℤ) where
  proj := weight iH I j
  support := weightSupport iH I j
  mem_support := mem_weightSupport iH I j
  sum_proj := sum_weight iH I j
  proj_mul_proj := weight_mul_weight iH I j
  proj_unit := by
    funext i
    have h := congrArg (fun v : CayleyVector (AddMonoidAlgebra K (I → ℤ)) => (v i).coeff 0)
      (isAutomorphismMatrix_universalMatrix hrep I j).1
    rw [unitOver_eq, coeff_universalMatrix_mulVec] at h
    rw [h]
    show (algebraMap K (AddMonoidAlgebra K (I → ℤ)) (c.unit i)).coeff 0 = c.unit i
    rw [algebraMap_addMonoidAlgebra, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  proj_mul := by
    intro a b x y hx hy
    have h := (isAutomorphismMatrix_universalMatrix hrep I j).2
      (fun i => algebraMap K (AddMonoidAlgebra K (I → ℤ)) (x i))
      (fun i => algebraMap K (AddMonoidAlgebra K (I → ℤ)) (y i))
    rw [universalMatrix_mulVec_of_weight I j hx, universalMatrix_mulVec_of_weight I j hy,
      multiplicationOver_single, multiplicationOver_algebraMap] at h
    funext i
    have h' := congrArg
      (fun v : CayleyVector (AddMonoidAlgebra K (I → ℤ)) => (v i).coeff (a + b)) h
    rw [coeff_universalMatrix_mulVec, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same] at h'
    exact h'

include hrep in
/-- **Upper bound.** A closed split torus `𝔾ₘ^I` in the automorphism group scheme of a Cayley
datum has `|I| ≤ 2`. -/
theorem card_le_two_of_isClosedSubgroup (hj : IsClosedSubgroup j) : Fintype.card I ≤ 2 := by
  refine (weightGrading hrep I j).card_le_two ?_
  have hmono : Mono (j.hom.hom ≫ iH.hom.hom).left := by
    have h1 : IsClosedImmersion j.hom.hom.left := hj
    have h2 : IsClosedImmersion iH.hom.hom.left := hrep.1
    have m1 : Mono j.hom.hom.left := inferInstance
    have m2 : Mono iH.hom.hom.left := inferInstance
    show Mono (j.hom.hom.left ≫ iH.hom.hom.left)
    exact mono_comp _ _
  have h := closure_weights_eq_top iH I j hmono
  have hs : {m : I → ℤ | weight iH I j m ≠ 0} = (weightSupport iH I j : Set (I → ℤ)) := by
    ext m
    exact (mem_weightSupport _ _ _ m).symm
  rw [hs] at h
  exact h

end Universal

variable {c}

/-- **Upper bound for the split rank.** The automorphism group scheme of a Cayley datum has
split rank at most two. -/
theorem splitRank_le_two {H : GroupScheme (Spec (CommRingCat.of K))}
    {iH : H ⟶ GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)}
    (hrep : c.IsAutomorphismRepresentation iH) : splitRank H ≤ 2 := by
  refine iSup_le fun I => iSup_le fun hI => iSup_le fun j => iSup_le fun hj => ?_
  classical
  have := Fintype.ofFinite I
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast card_le_two_of_isClosedSubgroup hrep I j hj

end Langlands.GroupScheme.CayleyDatum
