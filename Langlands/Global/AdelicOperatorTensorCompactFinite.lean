import Langlands.Global.AdelicOperatorTensorJointAdmissibility
import Langlands.Representation.KFiniteDual
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-! # Compact finite vectors and semisimplicity of the adelic tensor -/

noncomputable section

open scoped Classical MonoidAlgebra TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Global.AdelicOperatorTensor

open NumberField Langlands.FiniteVectors

section FiniteCompactTensor

variable {I K : Type*} [Group K]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (ρ : ∀ i, Representation ℂ K (V i))

private def diagonalTensor : Representation ℂ K (⨂[ℂ] i, V i) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi ρ)

private theorem diagonalTensor_tprod (k : K) (w : ∀ i, V i) :
    diagonalTensor ρ k (PiTensorProduct.tprod ℂ w) = PiTensorProduct.tprod ℂ (fun i => ρ i k (w i)) :=
  PiTensorProduct.map_tprod _ _

variable [Fintype I]

private theorem finiteVector_tprod (w : ∀ i, V i) (hfin : ∀ i, IsFiniteVector (ρ i) (w i)) :
    IsFiniteVector (diagonalTensor ρ) (PiTensorProduct.tprod ℂ w) := by
  let U (i : I) := orbitSpan (ρ i) (w i)
  let : ∀ i, Module.Finite ℂ (U i) := hfin
  let j := PiTensorProduct.map (fun i => (U i).subtype)
  apply Submodule.finiteDimensional_of_le (S₂ := j.range)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let z (i : I) : U i := ⟨ρ i k (w i), action_mem_orbitSpan (ρ i) k (w i)⟩
  refine ⟨PiTensorProduct.tprod ℂ z, ?_⟩
  change j (PiTensorProduct.tprod ℂ z) = diagonalTensor ρ k (PiTensorProduct.tprod ℂ w)
  rw [diagonalTensor_tprod]
  exact PiTensorProduct.map_tprod _ _

variable [TopologicalSpace K]

private theorem continuous_tprod_coefficient (w : ∀ i, V i)
    (hfin : ∀ i, IsFiniteVector (ρ i) (w i))
    (hcont : ∀ i (ℓ : V i →ₗ[ℂ] ℂ), Continuous (fun k => ℓ (ρ i k (w i))))
    (ℓ : (⨂[ℂ] i, V i) →ₗ[ℂ] ℂ) :
    Continuous (fun k => ℓ (diagonalTensor ρ k (PiTensorProduct.tprod ℂ w))) := by
  let U (i : I) := orbitSpan (ρ i) (w i)
  let : ∀ i, Module.Finite ℂ (U i) := hfin
  let d (i : I) := Module.finrank ℂ (U i)
  let b (i : I) : Module.Basis (Fin (d i)) ℂ (U i) := Module.finBasis ℂ (U i)
  have hex (i : I) (j : Fin (d i)) :
      ∃ e : V i →ₗ[ℂ] ℂ, e.comp (U i).subtype = (b i).coord j :=
    (b i).coord j |>.exists_extend
  choose e he using hex
  let basisVector (i : I) (j : Fin (d i)) : V i := (b i j).val
  have hsum (k : K) (i : I) :
      (∑ j, e i j (ρ i k (w i)) • basisVector i j) = ρ i k (w i) := by
    let z : U i := ⟨ρ i k (w i), action_mem_orbitSpan (ρ i) k (w i)⟩
    have hz (j : Fin (d i)) : e i j (ρ i k (w i)) = (b i).repr z j :=
      LinearMap.congr_fun (he i j) z
    simpa only [hz, basisVector, Submodule.coe_sum, Submodule.coe_smul] using
      congrArg Subtype.val ((b i).sum_repr z)
  let S (k : K) := ∑ j : ∀ i, Fin (d i),
    (∏ i, e i (j i) (ρ i k (w i))) * ℓ (PiTensorProduct.tprod ℂ (fun i => basisVector i (j i)))
  have hS : Continuous S := continuous_finsetSum _ fun j _ =>
    (continuous_finsetProd _ fun i _ => hcont i (e i (j i))).mul continuous_const
  refine hS.congr fun k => ?_
  have hcoord : (fun i => ∑ j, e i j (ρ i k (w i)) • basisVector i j) =
      (fun i => ρ i k (w i)) := funext (hsum k)
  rw [diagonalTensor_tprod, ← hcoord]
  change S k = (ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ))
    (fun i => ∑ j, e i j (ρ i k (w i)) • basisVector i j)
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [MultilinearMap.map_smul_univ]
  rfl

private theorem finite_continuous_diagonalTensor (hfin : ∀ i w, IsFiniteVector (ρ i) w)
    (hcont : ∀ i w (ℓ : V i →ₗ[ℂ] ℂ), Continuous (fun k => ℓ (ρ i k w)))
    (x : ⨂[ℂ] i, V i) :
    IsFiniteVector (diagonalTensor ρ) x ∧
      ∀ ℓ : (⨂[ℂ] i, V i) →ₗ[ℂ] ℂ, Continuous (fun k => ℓ (diagonalTensor ρ k x)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    refine ⟨(finiteVector_tprod ρ w fun i => hfin i (w i)).smul c, fun ℓ => ?_⟩
    have hconst : Continuous (fun _ : K => c) := continuous_const
    refine (hconst.mul (continuous_tprod_coefficient ρ w
      (fun i => hfin i (w i)) (fun i => hcont i (w i)) ℓ)).congr fun k => ?_
    change c * ℓ (diagonalTensor ρ k (PiTensorProduct.tprod ℂ w)) =
      ℓ (diagonalTensor ρ k (c • PiTensorProduct.tprod ℂ w))
    rw [map_smul, map_smul, smul_eq_mul]
  | add x y hx hy =>
    refine ⟨hx.1.add hy.1, fun ℓ => ?_⟩
    refine ((hx.2 ℓ).add (hy.2 ℓ)).congr fun k => ?_
    change ℓ (diagonalTensor ρ k x) + ℓ (diagonalTensor ρ k y) =
      ℓ (diagonalTensor ρ k (x + y))
    rw [map_add, map_add]

end FiniteCompactTensor

universe u

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "Factors" => ArchimedeanCompactFactors F n
local notation "Compact" => standardInfiniteCompact F n

private def toCompact : Factors ≃* Compact :=
  MulEquiv.ofBijective (ArchimedeanCompactFactors.toStandardCompact F n).toMonoidHom
    ⟨ArchimedeanCompactFactors.toStandardCompact_injective F n,
      ArchimedeanCompactFactors.toStandardCompact_surjective F n⟩

omit [NumberField F] in
private theorem continuous_fromCompact : Continuous (toCompact F n).symm := by
  have h : Continuous (toCompact F n).toEquiv := (ArchimedeanCompactFactors.toStandardCompact F n).continuous
  exact h.continuous_symm_of_equiv_compact_to_t2

variable {Vf : Type u}
  {Vr : {v : InfinitePlace F // InfinitePlace.IsReal v} → Type}
  {Vc : {v : InfinitePlace F // InfinitePlace.IsComplex v} → Type}
  [AddCommGroup Vf] [Module ℂ Vf]
  [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
  [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
  (κr : ∀ v, Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (Vr v))
  (κc : ∀ v, Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) (Vc v))

private def slotCompact (i : Slot F) : Representation ℂ Factors (SlotSpace F Vf Vr Vc i) :=
  match i with
  | .inl _ => 1
  | .inr (.inl v) => (ULift.moduleEquiv.symm.conjAlgEquiv ℂ).toAlgHom.toMonoidHom.comp
      ((κr v).comp ((Pi.evalMonoidHom (fun _ : RP => RK) v).comp (MonoidHom.fst _ _)))
  | .inr (.inr v) => (ULift.moduleEquiv.symm.conjAlgEquiv ℂ).toAlgHom.toMonoidHom.comp
      ((κc v).comp ((Pi.evalMonoidHom (fun _ : CP => CK) v).comp (MonoidHom.snd _ _)))

/-- Each slot uses its compact coordinate, and the compact acts trivially on the finite slot. -/
def compactPlaceAction (i : Slot F) : Representation ℂ Compact (SlotSpace F Vf Vr Vc i) :=
  (slotCompact F n κr κc i).comp (toCompact F n).symm.toMonoidHom

private theorem finiteVector_of_coordinate {G H V W : Type*} [Group G] [Group H]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (g : H → G) (e : V ≃ₗ[ℂ] W)
    (he : ∀ h v, σ h (e v) = e (ρ (g h) v)) (v : V) (hv : IsFiniteVector ρ v) :
    IsFiniteVector σ (e v) := by
  let U := orbitSpan ρ v
  let : Module.Finite ℂ U := hv
  apply Submodule.finiteDimensional_of_le (S₂ := U.map e.toLinearMap)
  apply Submodule.span_le.mpr
  rintro _ ⟨h, rfl⟩
  exact ⟨ρ (g h) v, action_mem_orbitSpan ρ (g h) v, (he h v).symm⟩

set_option maxHeartbeats 1400000 in
/-- The actual compact tensor action is locally finite and has continuous
coefficients when its archimedean factors have both properties. -/
theorem tensorCompactAction_finite_continuous
    (hfr : ∀ v w, IsFiniteVector (κr v) w)
    (hfc : ∀ v w, IsFiniteVector (κc v) w)
    (hcr : ∀ v w (ℓ : Vr v →ₗ[ℂ] ℂ), Continuous (fun k => ℓ (κr v k w)))
    (hcc : ∀ v w (ℓ : Vc v →ₗ[ℂ] ℂ), Continuous (fun k => ℓ (κc v k w)))
    (x : Space F Vf Vr Vc) :
    IsFiniteVector (tensorCompactAction F n κr κc) x ∧
      ∀ ℓ : Space F Vf Vr Vc →ₗ[ℂ] ℂ,
        Continuous (fun k => ℓ (tensorCompactAction F n κr κc k x)) := by
  let a := compactPlaceAction F n (Vf := Vf) κr κc
  change IsFiniteVector (diagonalTensor a) x ∧ _
  refine finite_continuous_diagonalTensor a ?_ ?_ x
  · rintro (i | v | v) w
    · apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {w})
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span (Set.mem_singleton w)
    · exact finiteVector_of_coordinate (κr v) (a (.inr (.inl v)))
        (fun k => ((toCompact F n).symm k).1 v)
        ULift.moduleEquiv.symm (fun _ _ => rfl) w.down (hfr v w.down)
    · exact finiteVector_of_coordinate (κc v) (a (.inr (.inr v)))
        (fun k => ((toCompact F n).symm k).2 v)
        ULift.moduleEquiv.symm (fun _ _ => rfl) w.down (hfc v w.down)
  · rintro (i | v | v) w ℓ
    · change Continuous (fun _ : Compact => ℓ w)
      exact continuous_const
    · exact (hcr v w.down (ℓ.comp ULift.moduleEquiv.symm.toLinearMap)).comp
        ((continuous_apply v).comp (continuous_fst.comp (continuous_fromCompact F n)))
    · exact (hcc v w.down (ℓ.comp ULift.moduleEquiv.symm.toLinearMap)).comp
        ((continuous_apply v).comp (continuous_snd.comp (continuous_fromCompact F n)))

open Langlands.FiniteTensor

/-- The finite translations commute with the full compact action on the tensor. -/
theorem tensorFiniteAction_compact_commute (fin : Representation ℂ (FiniteAdelicGL F n) Vf)
    (g : FiniteAdelicGL F n) (k : Compact) (w : Space F Vf Vr Vc) :
    tensorFiniteAction F n fin g (tensorCompactAction F n κr κc k w) =
      tensorCompactAction F n κr κc k (tensorFiniteAction F n fin g w) := by
  let a := compactPlaceAction F n (Vf := Vf) κr κc
  let b := slot (V := SlotSpace F Vf Vr Vc) (.inl ()) (fin g)
  change (PiTensorProduct.map b) (PiTensorProduct.map (fun i => a i k) w) =
    (PiTensorProduct.map (fun i => a i k)) (PiTensorProduct.map b w)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 2
  funext i
  rcases i with (⟨⟩ | i)
  · change (b (.inl ())).comp 1 = (1 : Module.End ℂ Vf).comp (b (.inl ()))
    simp [Module.End.one_eq_id]
  · simp [b, slot]

/-- Smoothness of the grouped finite slot gives smoothness under finite
translation on the adelic tensor. -/
theorem tensorFiniteAction_isSmooth (fin : Representation ℂ (FiniteAdelicGL F n) Vf)
    (hfin : IsSmooth fin) : IsSmooth (tensorFiniteAction F n (Vr := Vr) (Vc := Vc) fin) := by
  intro x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    obtain ⟨L, hL⟩ := hfin (w (.inl ()))
    refine ⟨L, fun g => ?_⟩
    change (PiTensorProduct.map (slot (.inl ()) (fin g.val))) (c • PiTensorProduct.tprod ℂ w) =
      c • PiTensorProduct.tprod ℂ w
    rw [map_smul, PiTensorProduct.map_tprod]
    congr 2
    funext i
    rcases i with i | i
    · have hi : i = () := Subsingleton.elim _ _
      subst i
      simp only [slot, Function.update_self]
      change fin g.val (w (.inl ())) = w (.inl ())
      exact hL g
    · simp [slot]
  | add x y hx hy =>
    obtain ⟨L, hL⟩ := hx
    obtain ⟨M, hM⟩ := hy
    refine ⟨L ⊓ M, fun g => ?_⟩
    change tensorFiniteAction F n fin g.val (x + y) = x + y
    have hx' : tensorFiniteAction F n fin g.val x = x := hL ⟨g.val, g.property.1⟩
    have hy' : tensorFiniteAction F n fin g.val y = y := hM ⟨g.val, g.property.2⟩
    rw [map_add, hx', hy']

end Langlands.Global.AdelicOperatorTensor
