import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluate Mathlib's nested continuous functions on a finite tuple. -/
def nestedEval (A : TopRep.{u} k G) :
    (n : ℕ) → TopRep.resolutionX A n →ₗ[k] ((Fin n → G) → A)
  | 0 =>
      { toFun := fun a _ => a
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  | n + 1 =>
      { toFun := fun f x => nestedEval A n (f (x 0)) (Fin.tail x)
        map_add' f g := by
          funext x
          exact congrFun ((nestedEval A n).map_add (f (x 0)) (g (x 0))) (Fin.tail x)
        map_smul' c f := by
          funext x
          exact congrFun ((nestedEval A n).map_smul c (f (x 0))) (Fin.tail x) }

theorem nestedEval_action (A : TopRep.{u} k G) (n : ℕ) (g : G)
    (f : TopRep.resolutionX A n) (x : Fin n → G) :
    nestedEval A n ((TopRep.resolutionX A n).ρ g f) x =
      A.ρ g (nestedEval A n f (fun i => g⁻¹ * x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change nestedEval A n ((TopRep.resolutionX A n).ρ g (f (g⁻¹ * x 0))) (Fin.tail x) = _
    rw [ih]
    rfl

/-- Covariant functions on finite tuples with the diagonal group action. -/
def covariantFunctions (A : TopRep.{u} k G) (n : ℕ) :
    Submodule k ((Fin n → G) → A) where
  carrier := { f | ∀ (g : G) (x : Fin n → G), f (fun i => g * x i) = A.ρ g (f x) }
  zero_mem' := by
    intro g x
    exact (map_zero (A.ρ g)).symm
  add_mem' hf hh := by
    intro g x
    simp only [Pi.add_apply, map_add]
    rw [hf g x, hh g x]
  smul_mem' c f hf := by
    intro g x
    simp only [Pi.smul_apply, map_smul]
    rw [hf g x]

theorem nestedEval_invariant (A : TopRep.{u} k G) (n : ℕ)
    (f : (TopRep.resolutionX A n).ρ.invariants) :
    nestedEval A n f.1 ∈ covariantFunctions A n := by
  intro g x
  have h := congrArg (fun v => nestedEval A n v (fun i => g * x i)) (f.property g)
  simpa only [nestedEval_action, inv_mul_cancel_left] using h.symm

@[simp]
theorem nestedEval_cons (A : TopRep.{u} k G) (n : ℕ)
    (f : TopRep.resolutionX A (n + 1)) (g : G) (x : Fin n → G) :
    nestedEval A (n + 1) f (Fin.cons g x) = nestedEval A n (f g) x := by
  simp only [nestedEval, LinearMap.coe_mk, AddHom.coe_mk, Fin.cons_zero, Fin.tail_cons]

/-- The actual nested differential is the alternating deletion differential. -/
theorem nestedEval_d (A : TopRep.{u} k G) (n : ℕ)
    (f : TopRep.resolutionX A n) (x : Fin (n + 1) → G) :
    nestedEval A (n + 1) ((TopRep.d A n).hom f) x =
      ∑ i : Fin (n + 1), (-1 : k) ^ i.val • nestedEval A n f (x ∘ i.succAbove) := by
  induction n with
  | zero =>
    change f = ∑ i : Fin 1, (-1 : k) ^ i.val • f
    simp
  | succ n ih =>
    change nestedEval A (n + 1) (f - (TopRep.d A n).hom (f (x 0))) (Fin.tail x) = _
    simp only [map_sub, Pi.sub_apply]
    rw [ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    have hp (i : Fin (n + 1)) :
        x ∘ i.succ.succAbove = Fin.cons (x 0) (Fin.tail x ∘ i.succAbove) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.tail, Function.comp_def]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero]
    change _ - _ = nestedEval A (n + 1) f (Fin.tail x) + _
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hp, nestedEval_cons]
    simp [pow_succ, neg_smul]

/-- Linear extension of a covariant tuple function to the diagonal permutation module. -/
noncomputable def covariantToRepHom (A : TopRep.{u} k G) (n : ℕ)
    (f : covariantFunctions A n) :
    Rep.diagonal k G n ⟶ Rep.of A.ρ.toRepresentation :=
  Rep.ofHom
    { toLinearMap := Finsupp.lift A k (Fin n → G) f ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
      isIntertwining' g := by
        ext x
        simpa [Pi.smul_def, smul_eq_mul, ContRepresentation.toMonoidHom_apply]
          using f.property g x }

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem covariantToRepHom_single (A : TopRep.{u} k G) (n : ℕ)
    (f : covariantFunctions A n) (x : Fin n → G) (r : k) :
    (covariantToRepHom A n f).hom (.single x r) = r • f.1 x := by
  simp [covariantToRepHom]

/-- Restrict an equivariant linear map to the basis of tuple generators. -/
noncomputable def repHomToCovariant (A : TopRep.{u} k G) (n : ℕ)
    (f : Rep.diagonal k G n ⟶ Rep.of A.ρ.toRepresentation) :
    covariantFunctions A n :=
  ⟨fun x => f.hom (.single x 1), by
    intro g x
    simpa [Pi.smul_def, smul_eq_mul, ContRepresentation.toMonoidHom_apply]
      using Rep.hom_comm_apply f g (.single x 1)⟩

/-- The genuine linear extension/restriction equivalence for homogeneous cochains. -/
noncomputable def covariantHomEquiv (A : TopRep.{u} k G) (n : ℕ) :
    covariantFunctions A n ≃ₗ[k] (Rep.diagonal k G n ⟶ Rep.of A.ρ.toRepresentation) where
  toFun := covariantToRepHom A n
  invFun := repHomToCovariant A n
  left_inv f := by
    ext x
    simp [covariantToRepHom]
  right_inv f := by
    ext x
    simp [repHomToCovariant, covariantToRepHom]
  map_add' f h := by
    ext x
    change (covariantToRepHom A n (f + h)).hom (.single x 1) =
      (covariantToRepHom A n f).hom (.single x 1) +
        (covariantToRepHom A n h).hom (.single x 1)
    simp [covariantToRepHom]
  map_smul' c f := by
    ext x
    change (covariantToRepHom A n (c • f)).hom (.single x 1) =
      c • (covariantToRepHom A n f).hom (.single x 1)
    simp [covariantToRepHom]

/-- Evaluate an invariant nested cochain and extend linearly on tuple generators. -/
noncomputable def homogeneousTermMap (A : TopRep.{u} k G) (n : ℕ) :
    (TopRep.homogeneousCochains A).X n →ₗ[k]
      (Rep.diagonal k G (n + 1) ⟶ Rep.of A.ρ.toRepresentation) :=
  (covariantHomEquiv A (n + 1)).toLinearMap.comp
    (show (TopRep.homogeneousCochains A).X n →ₗ[k] covariantFunctions A (n + 1) from
    { toFun f := ⟨nestedEval A (n + 1) f.1, nestedEval_invariant A (n + 1) f⟩
      map_add' f h := Subtype.ext ((nestedEval A (n + 1)).map_add f.1 h.1)
      map_smul' r f := Subtype.ext ((nestedEval A (n + 1)).map_smul r f.1) })

@[simp]
theorem homogeneousTermMap_single (A : TopRep.{u} k G) (n : ℕ)
    (f : (TopRep.homogeneousCochains A).X n) (x : Fin (n + 1) → G) (r : k) :
    (homogeneousTermMap A n f).hom (.single x r) = r • nestedEval A (n + 1) f.1 x := by
  change (covariantToRepHom A (n + 1) _).hom (.single x r) = _
  rw [covariantToRepHom_single]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical cochain map from nested continuous to standard homogeneous cochains. -/
noncomputable def homogeneousComparison (A : TopRep.{u} k G) :
    ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (TopRep.homogeneousCochains A) ⟶
      (Rep.standardComplex k G).linearYonedaObj k (Rep.of A.ρ.toRepresentation) where
  f n := ModuleCat.ofHom (homogeneousTermMap A n)
  comm' := by
    rintro i j (rfl : i + 1 = j)
    ext f
    change (Rep.standardComplex k G).d (i + 1) i ≫ homogeneousTermMap A i f =
      homogeneousTermMap A (i + 1) ((TopRep.homogeneousCochains A).d i (i + 1) f)
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro x
    change Fin (i + 1 + 1) → G at x
    apply LinearMap.ext_ring
    change (homogeneousTermMap A i f).hom
        (((Rep.standardComplex k G).d (i + 1) i).hom (.single x 1)) =
      (homogeneousTermMap A (i + 1)
        ((TopRep.homogeneousCochains A).d i (i + 1) f)).hom (.single x 1)
    rw [Rep.standardComplex.d_apply, Rep.standardComplex.d_of, map_sum]
    simp only [homogeneousTermMap_single A, one_smul]
    rw [TopRep.homogeneousCochains.d_apply]
    exact (nestedEval_d A (i + 1) f.1 x).symm

/-- Use Mathlib's standard-to-bar resolution isomorphism and its ordinary cochain model. -/
noncomputable def standardToInhomogeneousIso (A : TopRep.{u} k G) :
    (Rep.standardComplex k G).linearYonedaObj k (Rep.of A.ρ.toRepresentation) ≅
      groupCohomology.inhomogeneousCochains (Rep.of A.ρ.toRepresentation) :=
  (HomologicalComplex.unopFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ)).mapIso
    ((((((linearYoneda k (Rep.{u} k G)).obj (Rep.of A.ρ.toRepresentation)).rightOp).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapIso
        (Rep.barComplex.isoStandardComplex k G)).op) ≪≫
    (groupCohomology.inhomogeneousCochainsIso (Rep.of A.ρ.toRepresentation)).symm

/-- Forget continuity and convert homogeneous coordinates to ordinary inhomogeneous cochains. -/
noncomputable def continuousToOrdinaryCochains (A : TopRep.{u} k G) :
    ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (TopRep.homogeneousCochains A) ⟶
      groupCohomology.inhomogeneousCochains (Rep.of A.ρ.toRepresentation) :=
  homogeneousComparison A ≫ (standardToInhomogeneousIso A).hom

/-- The actual homology map from continuous cohomology to ordinary group cohomology. -/
noncomputable def continuousToOrdinary (A : TopRep.{u} k G) (q : ℕ) :
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj (continuousCohomology q A) ⟶
      groupCohomology (Rep.of A.ρ.toRepresentation) q :=
  (((TopRep.homogeneousCochains A).sc q).mapHomologyIso
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).inv ≫
    HomologicalComplex.homologyMap (continuousToOrdinaryCochains A) q

end Langlands.Continuous
