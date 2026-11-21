import Langlands.GroupScheme.CliffordSpin.AffineModel

/-! # Isometric coordinate transport for affine Clifford lifts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CliffordAlgebra
open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.CliffordSpin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {F V W : Type u} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] {n : ℕ}
  {Q : QuadraticForm F V} {P : QuadraticForm F W}
  (e : Q.IsometryEquiv P)

/-- The isometry-induced homomorphism on Clifford coefficients. -/
abbrev isometryTensorMap (A : Type u) [CommRing A] [Algebra F A] :
    A ⊗[F] CliffordAlgebra Q →ₐ[F] A ⊗[F] CliffordAlgebra P :=
  Algebra.TensorProduct.map (AlgHom.id F A) (CliffordAlgebra.equivOfIsometry e).toAlgHom

private theorem isometry_grade_reverse (c : CliffordAlgebra Q) :
    involute (equivOfIsometry e c) = equivOfIsometry e (involute c) ∧
      reverse (equivOfIsometry e c) = equivOfIsometry e (reverse c) := by
  induction c using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | mul x y hx hy => simp only [map_mul, reverse.map_mul, hx.1, hx.2, hy.1, hy.2, and_self]
  | add x y hx hy => simp only [map_add, hx.1, hx.2, hy.1, hy.2, and_self]

variable {A : Type u} [CommRing A] [Algebra F A]

private theorem isometryTensor_grade_reverse (a : A ⊗[F] CliffordAlgebra Q) :
    TensorProduct.map LinearMap.id involute.toLinearMap (isometryTensorMap e A a) =
        isometryTensorMap e A (TensorProduct.map LinearMap.id involute.toLinearMap a) ∧
      TensorProduct.map LinearMap.id reverse (isometryTensorMap e A a) =
        isometryTensorMap e A (TensorProduct.map LinearMap.id reverse a) := by
  induction a using TensorProduct.inductionOn with
  | tmul r c =>
    obtain ⟨hg, hr⟩ := isometry_grade_reverse e c
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom, hg, hr, and_self]
  | add a c ha hc => simp only [map_add, ha.1, ha.2, hc.1, hc.2, and_self]

private theorem isometryTensor_symm_apply (a : A ⊗[F] CliffordAlgebra Q) :
    isometryTensorMap e.symm A (isometryTensorMap e A a) = a := by
  induction a using TensorProduct.inductionOn with
  | tmul r c => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom,
      ← equivOfIsometry_symm, AlgEquiv.symm_apply_apply]
  | add a c ha hc => simp only [map_add, ha, hc]

variable [Invertible (2 : F)] {b : Module.Basis (Fin n) F V} {d : Module.Basis (Fin n) F W}
  (he : ∀ i, e (b i) = d i)

include he

omit [Invertible (2 : F)] in
private theorem isometryTensor_actionDefect (a : A ⊗[F] CliffordAlgebra Q) (g : GL (Fin n) A) (i : Fin n) :
    isometryTensorMap e A (actionDefect Q b A a g i) =
      actionDefect P d A (isometryTensorMap e A a) g i := by
  simp only [actionDefect, map_sub, map_mul, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    AlgEquiv.coe_toAlgHom, equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
  exact congrArg₂ (fun x y => isometryTensorMap e A a * x - y * isometryTensorMap e A a)
    (by rw [show e.toIsometry (b i) = d i from he i])
    (Finset.sum_congr rfl fun j _ => by rw [show e.toIsometry (b j) = d j from he j])

private def isometryPairMap (A : Type u) [CommRing A] [Algebra F A] :
    coefficientSubgroup Q b A →* coefficientSubgroup P d A := by
  let f := (Units.map (isometryTensorMap e A).toMonoidHom).prodMap (MonoidHom.id (GL (Fin n) A))
  refine (f.comp (coefficientSubgroup Q b A).subtype).codRestrict _ fun x => ?_
  obtain ⟨hg, hn, hd, ha⟩ := (mem_coefficientSubgroup_iff Q b x.val.1 x.val.2).mp x.property
  rw [mem_coefficientSubgroup_iff]
  change gradeDefect P A (isometryTensorMap e A x.val.1) = 0 ∧
    normDefect P A (isometryTensorMap e A x.val.1) = 0 ∧
    Matrix.GeneralLinearGroup.det x.val.2 = 1 ∧
    ∀ i, actionDefect P d A (isometryTensorMap e A x.val.1) x.val.2 i = 0
  let J := isometryTensorMap e A
  refine ⟨?_, ?_, hd, fun i => ?_⟩
  · rw [gradeDefect, (isometryTensor_grade_reverse e (x.val.1 : A ⊗[F] CliffordAlgebra Q)).1,
      ← map_sub]
    exact (congrArg J hg).trans (map_zero J)
  · rw [normDefect, (isometryTensor_grade_reverse e (x.val.1 : A ⊗[F] CliffordAlgebra Q)).2,
      ← map_mul, ← map_one J, ← map_sub]
    exact (congrArg J hn).trans (map_zero J)
  · rw [← isometryTensor_actionDefect e he, ha i, map_zero]

private theorem isometryPairMap_val (x : coefficientSubgroup Q b A) :
    (isometryPairMap e he A x).val =
      (Units.map (isometryTensorMap e A).toMonoidHom x.val.1, x.val.2) :=
  rfl

omit he [Invertible (2 : F)] in
private theorem isometryPairMap_naturality {B : Type u} [CommRing B] [Algebra F B]
    (f : A →ₐ[F] B) (a : A ⊗[F] CliffordAlgebra Q) :
    tensorMap P f (isometryTensorMap e A a) = isometryTensorMap e B (tensorMap Q f a) := by
  induction a using TensorProduct.inductionOn with
  | tmul r c => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  | add a c ha hc => simp only [map_add, ha, hc]

private def transportNat : Corepresented.cutFunctor (isCutOutBy Q b) ⟶
    Corepresented.cutFunctor (isCutOutBy P d) where
  app A := GrpCat.ofHom (isometryPairMap e he A)
  naturality {A B} f := by
    ext x
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      exact (isometryPairMap_naturality e f.hom _).symm
    · rfl

/-- The group-scheme homomorphism induced by an isometry matching the chosen bases. -/
def isometryTransport : groupScheme Q b ⟶ groupScheme P d :=
  Corepresented.groupSchemeMap (Corepresented.cutCorepresentableBy (isCutOutBy Q b))
    (Corepresented.cutCorepresentableBy (isCutOutBy P d)) (transportNat e he)

/-- Isometric transport changes the Clifford coordinates and retains the action matrix. -/
theorem affinePairEquiv_isometryTransport (A : CommAlgCat.{u} (CommRingCat.of F))
    (x : (groupScheme Q b).affinePoints A) :
    (affinePairEquiv P d A (x ≫ (isometryTransport e he).hom.hom)).val =
      (Units.map (isometryTensorMap e A).toMonoidHom (affinePairEquiv Q b A x).val.1,
        (affinePairEquiv Q b A x).val.2) := by
  rw [show affinePairEquiv P d A (x ≫ (isometryTransport e he).hom.hom) =
      isometryPairMap e he A (affinePairEquiv Q b A x) from
    Corepresented.groupSchemeMap_affinePoints (Corepresented.cutCorepresentableBy (isCutOutBy Q b))
      (Corepresented.cutCorepresentableBy (isCutOutBy P d)) (transportNat e he) x,
    isometryPairMap_val]

private theorem isometryTransport_comp_symm (hs : ∀ i, e.symm (d i) = b i) :
    isometryTransport e he ≫ isometryTransport e.symm hs = 𝟙 _ := by
  apply Corepresented.hom_ext_affinePoints
  intro A x
  apply Subtype.ext
  change (affinePairEquiv Q b A (x ≫ (isometryTransport e he ≫
    isometryTransport e.symm hs).hom.hom)).val = (affinePairEquiv Q b A (x ≫ 𝟙 _)).val
  rw [Grp.comp_hom_hom, ← Category.assoc, Category.comp_id,
    affinePairEquiv_isometryTransport, affinePairEquiv_isometryTransport]
  apply Prod.ext
  · apply Units.ext
    exact isometryTensor_symm_apply e _
  · rfl

/-- Isometric forms with matching coordinate bases give isomorphic affine lift schemes. -/
def isometryTransportIso : groupScheme Q b ≅ groupScheme P d := by
  have hs (i : Fin n) : e.symm (d i) = b i := by
    rw [← he i]
    exact e.toLinearEquiv.symm_apply_apply _
  exact ⟨isometryTransport e he, isometryTransport e.symm hs, isometryTransport_comp_symm e he hs,
    isometryTransport_comp_symm e.symm hs he⟩

/-- An isometry carrying one basis to the other gives the corresponding Clifford
  coordinate isomorphism, with the same action matrix on each affine test. -/
def CliffordSpinAffineIsometryTransportStatement : Prop :=
  ∀ (F : Type u) [Field F] [Invertible (2 : F)]
    (V W : Type u) [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (Q : QuadraticForm F V) (P : QuadraticForm F W) (n : ℕ)
    (b : Module.Basis (Fin n) F V) (d : Module.Basis (Fin n) F W)
    (e : Q.IsometryEquiv P), (∀ i, e (b i) = d i) →
    ∃ f : groupScheme Q b ≅ groupScheme P d,
      ∀ (A : CommAlgCat.{u} (CommRingCat.of F)) (x : (groupScheme Q b).affinePoints A),
        (affinePairEquiv P d A (x ≫ f.hom.hom.hom)).val =
          (Units.map (isometryTensorMap e A).toMonoidHom (affinePairEquiv Q b A x).val.1,
            (affinePairEquiv Q b A x).val.2)

omit he [Invertible (2 : F)] in
theorem cliffordSpinAffineIsometryTransport : CliffordSpinAffineIsometryTransportStatement.{u} := by
  intro F _ _ V W _ _ _ _ Q P n b d e he
  exact ⟨isometryTransportIso e he, affinePairEquiv_isometryTransport e he⟩

end Langlands.GroupScheme.CliffordSpin
