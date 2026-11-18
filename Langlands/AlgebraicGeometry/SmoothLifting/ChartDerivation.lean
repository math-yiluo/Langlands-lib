import Langlands.AlgebraicGeometry.SmoothLifting.QuasiCoherent
import Langlands.AlgebraicGeometry.SmoothLifting.DerivationBaseChange

/-! # Lifts on a single chart are derivations

Suppose that the element `g` of a chart is a unit in `C`. Then the chart covers all of `Spec C`,
and global lifts based at `e` correspond to derivations `Γ(X, U) → I` over `Γ(S, V)`. Here
`Γ(X, U)` acts on `I` through the chart representative of `e`. The correspondence sends a lift
to the difference of chart representatives and is `C`-linear.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AlgebraicGeometry.SmoothLifting

variable {X S : Scheme.{u}} {f : X ⟶ S} {C : CommRingCat.{u}} {I : Ideal C}
  {x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X} {s : Spec C ⟶ S}

theorem restrC_self (y : Spec C ⟶ X) : restrC (C := C) C y = y := by
  rw [restrC, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  exact Category.id_comp y

/-- A lift on `C` itself is a global lift. -/
theorem isGlobalLift_of_isLift_self {z : Spec C ⟶ X} (hz : IsLift f I x₀ s C z) :
    IsGlobalLift f I x₀ s z := by
  have hstr : Spec.map (strMap (C := C) C) = 𝟙 _ := by
    rw [strMap, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have hI : I = redIdeal I C := (Ideal.map_id I).symm
  let ε : C ⧸ I ≃+* C ⧸ redIdeal I C := Ideal.quotEquivOfEq hI
  have hε : redStruct I C = (RingEquiv.toCommRingCatIso ε).hom := by
    ext x
    rfl
  have hiso : IsIso (Spec.map (redStruct I C)) := by rw [hε]; infer_instance
  refine ⟨?_, ?_⟩
  · rw [← cancel_epi (Spec.map (redStruct I C)), ← hz.1, ← Category.assoc, ← Spec.map_comp,
      ← strMap_redMap, Spec.map_comp, hstr, Category.comp_id]
  · rw [hz.2, hstr]
    exact Category.id_comp s

section ChartDer

variable (hI : SqZero I) (e : GLift f I x₀ s) (ch : Chart f I x₀ s)
  (hg : IsUnit (algebraMap C C ch.g))

theorem Chart.rep_θ_apply {y : Spec C ⟶ X} (hy : IsGlobalLift f I x₀ s y) (a : Γ(S, ch.V)) :
    (ch.rep C hI hg (restrC C y) (hy.isLift C)).hom (ch.θ.hom a) = (ch.ψ C hg).hom a :=
  congrArg (fun F => CommRingCat.Hom.hom F a) (ch.rep_θ C hI hg _ (hy.isLift C))

theorem Chart.grep_sub_mem (y : GLift f I x₀ s) (b : Γ(X, ch.U)) :
    ch.grep hI C hg y.2 b - ch.grep hI C hg e.2 b ∈ redIdeal I C :=
  ch.rep_sub_mem C hI hg _ _ (e.2.isLift C) (y.2.isLift C) b

variable [Algebra Γ(S, ch.V) Γ(X, ch.U)] [Algebra Γ(X, ch.U) C] [Algebra Γ(S, ch.V) C]
  [IsScalarTower Γ(S, ch.V) Γ(X, ch.U) C]

theorem Chart.algebraMap_base (hθ : algebraMap Γ(S, ch.V) Γ(X, ch.U) = ch.θ.hom)
    (hφ : ∀ b, algebraMap Γ(X, ch.U) C b = ch.grep hI C hg e.2 b) (a : Γ(S, ch.V)) :
    algebraMap Γ(S, ch.V) C a = (ch.ψ C hg).hom a := by
  rw [IsScalarTower.algebraMap_apply Γ(S, ch.V) Γ(X, ch.U) C, hθ, hφ]
  exact ch.rep_θ_apply hI hg e.2 a

/-- The difference of chart representatives, as a linear map into the ideal. -/
def Chart.derLin (hθ : algebraMap Γ(S, ch.V) Γ(X, ch.U) = ch.θ.hom)
    (hφ : ∀ b, algebraMap Γ(X, ch.U) C b = ch.grep hI C hg e.2 b) (y : GLift f I x₀ s) :
    Γ(X, ch.U) →ₗ[Γ(S, ch.V)] redIdeal I C where
  toFun b := ⟨ch.grep hI C hg y.2 b - ch.grep hI C hg e.2 b, ch.grep_sub_mem hI e hg y b⟩
  map_add' b b' := by
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' a b := by
    rw [RingHom.id_apply]
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def a b, Algebra.smul_def,
      ch.algebraMap_base hI e hg hθ hφ, hθ]
    change (ch.rep C hI hg _ (y.2.isLift C)).hom (ch.θ.hom a * b) -
      (ch.rep C hI hg _ (e.2.isLift C)).hom (ch.θ.hom a * b) = _
    rw [map_mul, map_mul, ch.rep_θ_apply hI hg y.2 a, ch.rep_θ_apply hI hg e.2 a]
    ring

/-- The derivation attached to a lift: the difference of chart representatives. -/
def Chart.der (hθ : algebraMap Γ(S, ch.V) Γ(X, ch.U) = ch.θ.hom)
    (hφ : ∀ b, algebraMap Γ(X, ch.U) C b = ch.grep hI C hg e.2 b) (y : GLift f I x₀ s) :
    Derivation Γ(S, ch.V) Γ(X, ch.U) (redIdeal I C) :=
  Derivation.mk' (ch.derLin hI e hg hθ hφ y) fun a b => by
    apply Subtype.ext
    have h0 := (hI.map (algebraMap C C)) _ (ch.grep_sub_mem hI e hg y a) _
      (ch.grep_sub_mem hI e hg y b)
    rw [Submodule.coe_add, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower,
      Algebra.smul_def, Algebra.smul_def, hφ, hφ]
    change (ch.rep C hI hg _ (y.2.isLift C)).hom (a * b) -
      (ch.rep C hI hg _ (e.2.isLift C)).hom (a * b) = _
    rw [map_mul, map_mul]
    change _ = _ * (ch.grep hI C hg y.2 b - ch.grep hI C hg e.2 b) +
      _ * (ch.grep hI C hg y.2 a - ch.grep hI C hg e.2 a)
    linear_combination h0

@[simp] theorem Chart.der_apply_val (hθ : algebraMap Γ(S, ch.V) Γ(X, ch.U) = ch.θ.hom)
    (hφ : ∀ b, algebraMap Γ(X, ch.U) C b = ch.grep hI C hg e.2 b) (y : GLift f I x₀ s)
    (b : Γ(X, ch.U)) :
    (ch.der hI e hg hθ hφ y b : C) = ch.grep hI C hg y.2 b - ch.grep hI C hg e.2 b := rfl

/-- The ring map `b ↦ e(b) + d(b)` attached to a derivation. -/
def Chart.homOfDer (d : Derivation Γ(S, ch.V) Γ(X, ch.U) (redIdeal I C)) :
    Γ(X, ch.U) ⟶ CommRingCat.of C :=
  CommRingCat.ofHom
    { toFun b := algebraMap Γ(X, ch.U) C b + (d b : C)
      map_one' := by rw [map_one, Derivation.map_one_eq_zero, Submodule.coe_zero, add_zero]
      map_mul' a b := by
        have h0 := (hI.map (algebraMap C C)) _ (d a).2 _ (d b).2
        rw [Derivation.leibniz, Submodule.coe_add, Submodule.coe_smul_of_tower,
          Submodule.coe_smul_of_tower, Algebra.smul_def, Algebra.smul_def, map_mul]
        linear_combination (-1 : C) * h0
      map_zero' := by rw [map_zero, map_zero, Submodule.coe_zero, add_zero]
      map_add' a b := by
        rw [map_add, map_add, Submodule.coe_add]
        ring }

omit [IsScalarTower Γ(S, ch.V) Γ(X, ch.U) C] in
theorem Chart.homOfDer_apply (d : Derivation Γ(S, ch.V) Γ(X, ch.U) (redIdeal I C))
    (b : Γ(X, ch.U)) : (ch.homOfDer hI d).hom b = algebraMap Γ(X, ch.U) C b + (d b : C) := rfl

theorem Chart.homOfDer_θ (hθ : algebraMap Γ(S, ch.V) Γ(X, ch.U) = ch.θ.hom)
    (hφ : ∀ b, algebraMap Γ(X, ch.U) C b = ch.grep hI C hg e.2 b)
    (d : Derivation Γ(S, ch.V) Γ(X, ch.U) (redIdeal I C)) :
    ch.θ ≫ ch.homOfDer hI d = ch.ψ C hg := by
  ext a
  change (ch.homOfDer hI d).hom (ch.θ.hom a) = _
  rw [Chart.homOfDer_apply, ← hθ, Derivation.map_algebraMap, Submodule.coe_zero, add_zero,
    ← IsScalarTower.algebraMap_apply]
  exact ch.algebraMap_base hI e hg hθ hφ a

omit [IsScalarTower Γ(S, ch.V) Γ(X, ch.U) C] in
theorem Chart.homOfDer_red (hφ : ∀ b, algebraMap Γ(X, ch.U) C b = ch.grep hI C hg e.2 b)
    (d : Derivation Γ(S, ch.V) Γ(X, ch.U) (redIdeal I C)) :
    ch.homOfDer hI d ≫ redMap I C = ch.φ₀ C hg := by
  ext b
  change Ideal.Quotient.mk _ ((ch.homOfDer hI d).hom b) = _
  rw [Chart.homOfDer_apply, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (d b).2, add_zero, hφ]
  exact congrArg (fun F => CommRingCat.Hom.hom F b) (ch.rep_red C hI hg _ (e.2.isLift C))

/-- The global lift attached to a derivation. -/
def Chart.liftOfDer (hθ : algebraMap Γ(S, ch.V) Γ(X, ch.U) = ch.θ.hom)
    (hφ : ∀ b, algebraMap Γ(X, ch.U) C b = ch.grep hI C hg e.2 b)
    (d : Derivation Γ(S, ch.V) Γ(X, ch.U) (redIdeal I C)) : GLift f I x₀ s :=
  ⟨Spec.map (ch.homOfDer hI d) ≫ ch.hU.fromSpec, isGlobalLift_of_isLift_self
    (ch.isLift_of_hom C hg _ (ch.homOfDer_θ hI e hg hθ hφ d) (ch.homOfDer_red hI e hg hφ d))⟩

theorem Chart.grep_liftOfDer (hθ : algebraMap Γ(S, ch.V) Γ(X, ch.U) = ch.θ.hom)
    (hφ : ∀ b, algebraMap Γ(X, ch.U) C b = ch.grep hI C hg e.2 b)
    (d : Derivation Γ(S, ch.V) Γ(X, ch.U) (redIdeal I C)) (b : Γ(X, ch.U)) :
    ch.grep hI C hg (ch.liftOfDer hI e hg hθ hφ d).2 b =
      algebraMap Γ(X, ch.U) C b + (d b : C) := by
  have h : ch.rep C hI hg (restrC C (ch.liftOfDer hI e hg hθ hφ d).1)
      ((ch.liftOfDer hI e hg hθ hφ d).2.isLift C) = ch.homOfDer hI d :=
    chartRep_eq _ _ _ (restrC_self _).symm
  exact congrArg (fun F => CommRingCat.Hom.hom F b) h

/-- **Lifts on a chart with invertible element are derivations**, `C`-linearly. -/
def Chart.derEquiv (hθ : algebraMap Γ(S, ch.V) Γ(X, ch.U) = ch.θ.hom)
    (hφ : ∀ b, algebraMap Γ(X, ch.U) C b = ch.grep hI C hg e.2 b) :
    LiftModule hI e ≃ₗ[C] Derivation Γ(S, ch.V) Γ(X, ch.U) (redIdeal I C) where
  toFun y := ch.der hI e hg hθ hφ y
  invFun d := LiftModule.of hI e (ch.liftOfDer hI e hg hθ hφ d)
  left_inv y := by
    apply Subtype.ext
    have key : restrC C (ch.liftOfDer hI e hg hθ hφ (ch.der hI e hg hθ hφ y)).1 =
        restrC C (y : GLift f I x₀ s).1 :=
      ch.eq_of_rep hI hg ((ch.liftOfDer hI e hg hθ hφ _).2.isLift C)
        ((y : GLift f I x₀ s).2.isLift C) fun b => by
          refine (ch.grep_liftOfDer hI e hg hθ hφ _ b).trans ?_
          change algebraMap _ C b + (ch.grep hI C hg (y : GLift f I x₀ s).2 b -
            ch.grep hI C hg e.2 b) = ch.grep hI C hg (y : GLift f I x₀ s).2 b
          rw [hφ]
          ring
    rwa [restrC_self, restrC_self] at key
  right_inv d := by
    ext b
    change ch.grep hI C hg (ch.liftOfDer hI e hg hθ hφ d).2 b - ch.grep hI C hg e.2 b =
      (d b : C)
    rw [ch.grep_liftOfDer hI e hg hθ hφ d b, hφ]
    ring
  map_add' x y := by
    ext b
    change ch.grep hI C hg (LiftModule.lin hI e x y 1 1).2 b - ch.grep hI C hg e.2 b =
      (ch.grep hI C hg (x : GLift f I x₀ s).2 b - ch.grep hI C hg e.2 b) +
        (ch.grep hI C hg (y : GLift f I x₀ s).2 b - ch.grep hI C hg e.2 b)
    refine (congrArg (· - ch.grep hI C hg e.2 b)
      (LiftModule.grep_lin hI e ch C hg x y 1 1 b)).trans ?_
    simp only [map_one, one_mul]
    ring
  map_smul' c x := by
    ext b
    change ch.grep hI C hg (LiftModule.lin hI e x e c 0).2 b - ch.grep hI C hg e.2 b =
      c * (ch.grep hI C hg (x : GLift f I x₀ s).2 b - ch.grep hI C hg e.2 b)
    refine (congrArg (· - ch.grep hI C hg e.2 b)
      (LiftModule.grep_lin hI e ch C hg x e c 0 b)).trans ?_
    simp only [map_zero, zero_mul, add_zero, Algebra.algebraMap_self, RingHom.id_apply]
    ring

@[simp] theorem Chart.derEquiv_apply_val (hθ : algebraMap Γ(S, ch.V) Γ(X, ch.U) = ch.θ.hom)
    (hφ : ∀ b, algebraMap Γ(X, ch.U) C b = ch.grep hI C hg e.2 b) (y : LiftModule hI e)
    (b : Γ(X, ch.U)) :
    (ch.derEquiv hI e hg hθ hφ y b : C) =
      ch.grep hI C hg (y : GLift f I x₀ s).2 b - ch.grep hI C hg e.2 b := rfl

end ChartDer

/-! ### Flat base change on a chart -/

section ChartBaseChange

variable (hI : SqZero I) (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C C ch.g))
  (T : Type u) [CommRing T] [Algebra C T]

include hg in
theorem Chart.isUnit_bc :
    IsUnit (algebraMap (CommRingCat.of T) (CommRingCat.of T) (ch.bc T).g) := by
  have h := hg.map (algebraMap C T)
  rw [Algebra.algebraMap_self, RingHom.id_apply] at h ⊢
  exact h

/-- Chart representatives of restricted global lifts. -/
theorem Chart.grep_bc_res {y : Spec C ⟶ X} (hy : IsGlobalLift f I x₀ s y) (b : Γ(X, ch.U)) :
    (ch.bc T).grep (hI.map (algebraMap C T)) T (ch.isUnit_bc hg T) (hy.res T) b =
      algebraMap C T (ch.grep hI C hg hy b) := by
  have hgT : IsUnit (algebraMap C T ch.g) := by
    have h := hg.map (algebraMap C T)
    rwa [Algebra.algebraMap_self, RingHom.id_apply] at h
  let ρ : (C : Type u) →ₐ[C] T := Algebra.ofId C T
  have hz : IsLift f I x₀ s T (restrC (C := CommRingCat.of T) T (restrC T y)) := by
    rw [restrC_self (C := CommRingCat.of T)]
    exact hy.isLift T
  have e1 := congrArg (fun F => CommRingCat.Hom.hom F b)
    ((ch.rep_bc T hI hgT (ch.isUnit_bc hg T) hz ((hy.res T).isLift T)))
  refine e1.trans ?_
  have e2 : restrC (C := CommRingCat.of T) T (restrC T y) =
      Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ restrC C y := by
    rw [restrC_self (C := CommRingCat.of T), restrC_self]
    rfl
  refine (ch.rep_congr hI hgT hz ((hy.isLift C).restrict ρ) e2 b).trans ?_
  exact congrArg (fun F => CommRingCat.Hom.hom F b) (ch.rep_restrict hI ρ hg hgT (hy.isLift C))

include hg in
/-- **Flat base change on a chart**: if the chart element is a unit in `C`, restriction of lifts
to a flat `C`-algebra `T` is a base change. -/
theorem Chart.isBaseChange_resLin [Smooth f] (e : GLift f I x₀ s) [Module.Flat C T] :
    IsBaseChange T (LiftModule.resLin T hI e) := by
  let iAP : Algebra Γ(S, ch.V) Γ(X, ch.U) := ch.θ.hom.toAlgebra
  have : Algebra.Smooth Γ(S, ch.V) Γ(X, ch.U) := Smooth.smooth_appLE f ch.hV ch.hU ch.hUV
  let iPC : Algebra Γ(X, ch.U) C :=
    (ch.rep C hI hg (restrC C e.1) (e.2.isLift C)).hom.toAlgebra
  let iAC : Algebra Γ(S, ch.V) C :=
    ((algebraMap Γ(X, ch.U) C).comp (algebraMap Γ(S, ch.V) Γ(X, ch.U))).toAlgebra
  have : IsScalarTower Γ(S, ch.V) Γ(X, ch.U) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hgT := ch.isUnit_bc hg T
  let iPT : Algebra Γ(X, ch.U) T := ((ch.bc T).rep T (hI.map (algebraMap C T)) hgT
    (restrC (C := CommRingCat.of T) T (GLift.res T e).1)
    ((GLift.res T e).2.isLift T)).hom.toAlgebra
  let iAT : Algebra Γ(S, ch.V) T :=
    ((algebraMap Γ(X, ch.U) T).comp (algebraMap Γ(S, ch.V) Γ(X, ch.U))).toAlgebra
  have : IsScalarTower Γ(S, ch.V) Γ(X, ch.U) T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hPCT : ∀ b, algebraMap Γ(X, ch.U) T b = algebraMap C T (algebraMap Γ(X, ch.U) C b) :=
    fun b => ch.grep_bc_res hI hg T e.2 b
  have : IsScalarTower Γ(X, ch.U) C T := IsScalarTower.of_algebraMap_eq hPCT
  have : IsScalarTower Γ(S, ch.V) C T := IsScalarTower.of_algebraMap_eq fun _ => hPCT _
  let EC := ch.derEquiv hI e hg rfl (fun _ => rfl)
  let _ : Algebra Γ(S, (ch.bc T).V) Γ(X, (ch.bc T).U) := iAP
  let _ : Algebra Γ(X, (ch.bc T).U) T := iPT
  let _ : Algebra Γ(S, (ch.bc T).V) T := iAT
  have : IsScalarTower Γ(S, (ch.bc T).V) Γ(X, (ch.bc T).U) T :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ET := (ch.bc T).derEquiv (hI.map (algebraMap C T)) (GLift.res T e) hgT rfl (fun _ => rfl)
  have hJ : (redIdeal I C).map (algebraMap C T) =
      redIdeal (bcI (I := I) T) (CommRingCat.of T) := by
    change (I.map (algebraMap C C)).map (algebraMap C T) =
      (I.map (algebraMap C T)).map (algebraMap T T)
    rw [Ideal.map_map, Ideal.map_map, Algebra.algebraMap_self, Algebra.algebraMap_self,
      RingHom.comp_id, RingHom.id_comp]
  let ET' : LiftModule (hI.map (algebraMap C T)) (GLift.res T e) ≃ₗ[T]
      Derivation Γ(S, ch.V) Γ(X, ch.U) (redIdeal (bcI (I := I) T) (CommRingCat.of T)) := ET
  have hD := isBaseChange_derMap (A := Γ(S, ch.V)) (P := Γ(X, ch.U)) (C := C) (T := T)
    (redIdeal I C) _ hJ
  have hnat : ∀ x, ET' (LiftModule.resLin T hI e x) =
      derMap Γ(S, ch.V) Γ(X, ch.U) _ _ hJ (EC x) := by
    intro x
    ext b
    change (ch.bc T).grep _ T hgT ((x : GLift f I x₀ s).2.res T) b -
        (ch.bc T).grep _ T hgT (e.2.res T) b =
      algebraMap C T (ch.grep hI C hg (x : GLift f I x₀ s).2 b - ch.grep hI C hg e.2 b)
    rw [map_sub]
    exact congrArg₂ (· - ·) (ch.grep_bc_res hI hg T (x : GLift f I x₀ s).2 b)
      (ch.grep_bc_res hI hg T e.2 b)
  refine IsBaseChange.of_equiv (((EC.baseChange C T _ _).trans hD.equiv).trans ET'.symm)
    fun x => ?_
  have h1 : ((EC.baseChange C T _ _).trans hD.equiv) (1 ⊗ₜ x) =
      derMap Γ(S, ch.V) Γ(X, ch.U) _ _ hJ (EC x) := by
    rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, one_smul]
  rw [LinearEquiv.trans_apply, h1, ← hnat, LinearEquiv.symm_apply_apply]

end ChartBaseChange

end Langlands.AlgebraicGeometry.SmoothLifting
