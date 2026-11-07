import Langlands.Algebra.HopfPointExtension
import Langlands.Algebra.FiniteSubcomodule
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Support
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Weight projectors of a finite comodule and openness of weight windows -/

noncomputable section

open TensorProduct Coalgebra

namespace Langlands.Algebra.HopfPointWeightWindow

open HopfPointExtension

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {C : Type*} [CommRing C] [Algebra R C] {M : Type*} [AddCommGroup M]

/-- The coefficient of `X^l` of an algebra map into a group algebra, as a linear form. -/
def coeffForm (β : A →ₐ[R] AddMonoidAlgebra C M) (l : M) : A →ₗ[R] C where
  toFun a := (β a).coeff l
  map_add' a b := by rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' r a := by
    rw [map_smul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, RingHom.id_apply]

@[simp] theorem coeffForm_apply (β : A →ₐ[R] AddMonoidAlgebra C M) (l : M) (a : A) :
    coeffForm β l a = (β a).coeff l := rfl

theorem coeff_inlMap_mul_inrMap (x y : AddMonoidAlgebra C M) (l μ : M) :
    (inlMap R C M x * inrMap R C M y).coeff (l, μ) = x.coeff l * y.coeff μ := by
  classical
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, add_mul, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hx, hx']
  | single a c =>
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, mul_add, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, hy, hy']
    | single b d =>
      simp only [inlMap, inrMap, AddMonoidAlgebra.mapDomainAlgHom_apply,
        AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single,
        AddMonoidAlgebra.coeff_single, Finsupp.single_apply, AddMonoidHom.inl_apply,
        AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.injEq]
      by_cases ha : a = l <;> by_cases hb : b = μ <;> simp [ha, hb]

/-- The coefficient `(l, l)` of the exterior square equals the convolution square. -/
theorem coeff_pairMap (β : A →ₐ[R] AddMonoidAlgebra C M) (l : M) (t : A ⊗[R] A) :
    (pairMap β t).coeff (l, l) =
      LinearMap.mul' R C (TensorProduct.map (coeffForm β l) (coeffForm β l) t) := by
  induction t with
  | tmul a b =>
    simp only [pairMap, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
      TensorProduct.map_tmul, LinearMap.mul'_apply, coeffForm_apply]
    exact coeff_inlMap_mul_inrMap _ _ l l
  | add a b ha hb => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb]

/-- For a Hopf point, the coefficient forms are idempotent for convolution. -/
theorem mul'_map_coeffForm_comul {β : A →ₐ[R] AddMonoidAlgebra C M} (hβ : IsHopfPoint β)
    (l : M) :
    LinearMap.mul' R C ∘ₗ TensorProduct.map (coeffForm β l) (coeffForm β l) ∘ₗ
      (comul (R := R) (A := A)) = coeffForm β l := by
  ext a
  simp only [LinearMap.comp_apply]
  rw [← coeff_pairMap]
  have h := congrArg (fun F => (F a).coeff (l, l)) hβ.comul
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at h
  rw [h, coeffForm_apply, diagMap, AddMonoidAlgebra.mapDomainAlgHom_apply]
  change (Finsupp.mapDomain _ (β a).coeff) (l, l) = _
  exact Finsupp.mapDomain_apply_of_injective (fun x y h => congrArg Prod.fst h) _ l

section Projector

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- A right coaction of the bialgebra `A` on `V` is coassociative. -/
def IsCoassoc (δ : V →ₗ[R] V ⊗[R] A) : Prop :=
  TensorProduct.assoc R V A A ∘ₗ δ.rTensor A ∘ₗ δ = (comul (R := R) (A := A)).lTensor V ∘ₗ δ

variable (δ : V →ₗ[R] V ⊗[R] A) (β : A →ₐ[R] AddMonoidAlgebra C M) (l : M)

/-- The `R`-linear map `V ⊗ A → C ⊗ V`, `v ⊗ a ↦ β(a)_l ⊗ v`. -/
def coeffSwap : V ⊗[R] A →ₗ[R] C ⊗[R] V :=
  (TensorProduct.comm R V C).toLinearMap ∘ₗ (coeffForm β l).lTensor V

@[simp] theorem coeffSwap_tmul (v : V) (a : A) :
    coeffSwap (V := V) β l (v ⊗ₜ a) = (β a).coeff l ⊗ₜ v := rfl

/-- The weight projector of `C ⊗ V` attached to the Hopf point `β` and the weight `l`. -/
def proj : C ⊗[R] V →ₗ[C] C ⊗[R] V :=
  LinearMap.liftBaseChange C (coeffSwap β l ∘ₗ δ)

theorem proj_tmul (c : C) (v : V) : proj δ β l (c ⊗ₜ v) = c • coeffSwap β l (δ v) := rfl

/-- The `R`-linear map `V ⊗ (A ⊗ A) → C ⊗ V`, `v ⊗ a ⊗ b ↦ β(a)_l β(b)_l ⊗ v`. -/
def convSwap : V ⊗[R] (A ⊗[R] A) →ₗ[R] C ⊗[R] V :=
  (TensorProduct.comm R V C).toLinearMap ∘ₗ
    (LinearMap.mul' R C ∘ₗ TensorProduct.map (coeffForm β l) (coeffForm β l)).lTensor V

theorem proj_coeffSwap (w : V ⊗[R] A) :
    proj δ β l (coeffSwap β l w) =
      convSwap β l (TensorProduct.assoc R V A A (δ.rTensor A w)) := by
  induction w with
  | tmul v a =>
    simp only [coeffSwap_tmul, proj_tmul, LinearMap.rTensor_tmul]
    induction δ v with
    | tmul v' a' =>
      simp only [coeffSwap_tmul, TensorProduct.smul_tmul', smul_eq_mul,
        TensorProduct.assoc_tmul, convSwap, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
        coeffForm_apply, TensorProduct.comm_tmul, mul_comm]
    | add x y hx hy => simp only [map_add, smul_add, add_tmul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The weight projector is idempotent. -/
theorem proj_proj (hδ : IsCoassoc δ) (hβ : IsHopfPoint β) (x : C ⊗[R] V) :
    proj δ β l (proj δ β l x) = proj δ β l x := by
  induction x with
  | tmul c v =>
    rw [proj_tmul, map_smul, proj_coeffSwap]
    congr 1
    have h1 : TensorProduct.assoc R V A A (δ.rTensor A (δ v)) =
        (comul (R := R) (A := A)).lTensor V (δ v) := congrArg (fun F => F v) hδ
    rw [h1]
    have h2 : convSwap β l ∘ₗ (comul (R := R) (A := A)).lTensor V = coeffSwap β l := by
      rw [convSwap, coeffSwap, LinearMap.comp_assoc, ← LinearMap.lTensor_comp,
        LinearMap.comp_assoc, mul'_map_coeffForm_comul hβ]
    exact congrArg (fun F => F (δ v)) h2
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The counit of `C ⊗ V` induced by a comodule map `ι : V → A`. -/
def counitV (ι : V →ₗ[R] A) : C ⊗[R] V →ₗ[C] C :=
  LinearMap.liftBaseChange C (Algebra.linearMap R C ∘ₗ counit ∘ₗ ι)

/-- The coefficients of `β` on `ι V` are read off from the weight projectors. -/
theorem counitV_proj (ι : V →ₗ[R] A)
    (hι : (comul (R := R) (A := A)) ∘ₗ ι = ι.rTensor A ∘ₗ δ) (v : V) :
    counitV (C := C) ι (proj δ β l (1 ⊗ₜ v)) = (β (ι v)).coeff l := by
  rw [proj_tmul, one_smul]
  have key : ∀ w : V ⊗[R] A, counitV (C := C) ι (coeffSwap β l w) =
      coeffForm β l (TensorProduct.lid R A ((counit (R := R) (A := A) ∘ₗ ι).rTensor A w)) := by
    intro w
    induction w with
    | tmul v' a =>
      simp only [coeffSwap_tmul, counitV, LinearMap.liftBaseChange_tmul,
        LinearMap.comp_apply, Algebra.linearMap_apply, LinearMap.rTensor_tmul,
        TensorProduct.lid_tmul, LinearMap.map_smul, smul_eq_mul]
      rw [Algebra.smul_def, mul_comm, coeffForm_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [key]
  have h2 : (counit (R := R) (A := A) ∘ₗ ι).rTensor A (δ v) =
      (counit (R := R) (A := A)).rTensor A (comul (R := R) (A := A) (ι v)) := by
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply]
    exact congrArg _ (congrArg (fun F => F v) hι).symm
  rw [h2, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul, coeffForm_apply]

end Projector

section BaseChange

variable {V : Type*} [AddCommGroup V] [Module R V]
  (δ : V →ₗ[R] V ⊗[R] A) (β : A →ₐ[R] AddMonoidAlgebra C M) (l : M)
  {D : Type*} [CommRing D] [Algebra R D] (ψ : C →ₐ[R] D)

/-- Weight projectors commute with change of coefficients. -/
theorem rTensor_proj (x : C ⊗[R] V) :
    (ψ.toLinearMap.rTensor V) (proj δ β l x) =
      proj δ ((AddMonoidAlgebra.mapAlgHom M ψ).comp β) l ((ψ.toLinearMap.rTensor V) x) := by
  induction x with
  | tmul c v =>
    rw [proj_tmul, LinearMap.rTensor_tmul, proj_tmul]
    induction δ v with
    | tmul v' a =>
      simp only [coeffSwap_tmul, TensorProduct.smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul,
        AlgHom.toLinearMap_apply, map_mul, AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom]
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end BaseChange

section Openness

/-- An idempotent endomorphism of a finite module that vanishes after tensoring
with the residue field at `p` is killed by an element outside `p`. -/
theorem exists_smul_eq_zero_of_idempotent {N : Type*} [AddCommGroup N] [Module C N]
    [Module.Finite C N] (e : N →ₗ[C] N) (he : ∀ x, e (e x) = e x) (p : Ideal C) [p.IsPrime]
    (h : e.lTensor p.ResidueField = 0) : ∃ f ∉ p, ∀ x, f • e x = 0 := by
  let K := p.ResidueField
  let P := LinearMap.range e
  let i := P.subtype
  let r := e.rangeRestrict
  have hri : r ∘ₗ i = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨y, x, rfl⟩
    exact Subtype.ext (he x)
  have hir : i ∘ₗ r = e := e.subtype_comp_rangeRestrict
  have hsub : Subsingleton (K ⊗[C] P) := by
    refine ⟨fun y y' => ?_⟩
    have key : ∀ z : K ⊗[C] P, z = 0 := by
      intro z
      have h1 : z = (r.lTensor K) ((i.lTensor K) z) := by
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hri, LinearMap.lTensor_id,
          LinearMap.id_apply]
      have h2 : (i.lTensor K) z = (e.lTensor K) ((i.lTensor K) z) := by
        conv_lhs => rw [h1]
        rw [← LinearMap.comp_apply (i.lTensor K), ← LinearMap.lTensor_comp, hir]
      rw [h, LinearMap.zero_apply] at h2
      rw [h1, h2, map_zero]
    rw [key y, key y']
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum C) ∉ Module.support C P := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr hsub
  rw [Module.mem_support_iff_of_finite] at hnot
  obtain ⟨f, hf, hfp⟩ := Set.not_subset.mp hnot
  refine ⟨f, hfp, fun x => ?_⟩
  have := Module.mem_annihilator.mp hf (r x)
  exact congrArg Subtype.val this

variable {V : Type*} [AddCommGroup V] [Module R V]
  (δ : V →ₗ[R] V ⊗[R] A) (β : A →ₐ[R] AddMonoidAlgebra C M) (l : M)

theorem cancelBaseChange_tmul_eq (p : Ideal C) [p.IsPrime] (k : p.ResidueField)
    (z : C ⊗[R] V) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R C p.ResidueField p.ResidueField V
        (k ⊗ₜ z) =
      k • ((IsScalarTower.toAlgHom R C p.ResidueField).toLinearMap.rTensor V z) := by
  induction z with
  | tmul c v =>
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul,
      TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul, mul_comm]
    rfl
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add, smul_add]

/-- Openness of the weight window: if the weight projector for `l` vanishes at
the residue field of `p`, then some element outside `p` kills all
`l`-coefficients of `β` on `ι V`. -/
theorem exists_mul_coeff_eq_zero [Module.Finite R V] (hδ : IsCoassoc δ) (hβ : IsHopfPoint β)
    (ι : V →ₗ[R] A) (hι : (comul (R := R) (A := A)) ∘ₗ ι = ι.rTensor A ∘ₗ δ)
    (p : Ideal C) [p.IsPrime]
    (h : ∀ x, proj δ ((AddMonoidAlgebra.mapAlgHom M
      (IsScalarTower.toAlgHom R C p.ResidueField)).comp β) l x = 0) :
    ∃ f ∉ p, ∀ v, f * (β (ι v)).coeff l = 0 := by
  let K := p.ResidueField
  let e := proj δ β l
  have he : ∀ x, e (e x) = e x := proj_proj δ β l hδ hβ
  have hzero : e.lTensor K = 0 := by
    apply LinearMap.ext
    intro y
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange R C K K V).injective
    rw [LinearMap.zero_apply, map_zero]
    induction y with
    | tmul k z =>
      rw [LinearMap.lTensor_tmul, cancelBaseChange_tmul_eq, rTensor_proj, h, smul_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  obtain ⟨f, hfp, hf⟩ := exists_smul_eq_zero_of_idempotent e he p hzero
  refine ⟨f, hfp, fun v => ?_⟩
  rw [← counitV_proj δ β l ι hι v, ← smul_eq_mul, ← map_smul, hf, map_zero]

end Openness

section Coaction

open FiniteSubcomodule

/-- A right subcomodule of a flat bialgebra carries a unique coassociative
coaction lifting the comultiplication. -/
theorem exists_coaction [Module.Flat R A] (V : Submodule R A) (hV : IsRightSubcomodule V) :
    ∃ δ : V →ₗ[R] V ⊗[R] A, IsCoassoc δ ∧
      (comul (R := R) (A := A)) ∘ₗ V.subtype = V.subtype.rTensor A ∘ₗ δ := by
  let j : V ⊗[R] A →ₗ[R] A ⊗[R] A := V.subtype.rTensor A
  have hj : Function.Injective j :=
    Module.Flat.rTensor_preserves_injective_linearMap V.subtype V.injective_subtype
  let δ : V →ₗ[R] V ⊗[R] A := (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ
    ((comul (R := R) (A := A)) ∘ₗ V.subtype).codRestrict (LinearMap.range j)
      (fun x => hV x x.2)
  have hjδ : ∀ x : V, j (δ x) = comul (R := R) (A := A) (x : A) := fun x =>
    LinearEquiv.ofInjective_symm_apply (f := j) (h := hj)
      (⟨comul (R := R) (A := A) (x : A), hV x x.2⟩ : LinearMap.range j)
  have hcomp : (comul (R := R) (A := A)) ∘ₗ V.subtype = V.subtype.rTensor A ∘ₗ δ :=
    LinearMap.ext fun x => (hjδ x).symm
  refine ⟨δ, ?_, hcomp⟩
  -- coassociativity, checked after the injective map into `A ⊗ (A ⊗ A)`
  let J : V ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] (A ⊗[R] A) := V.subtype.rTensor (A ⊗[R] A)
  have hJ : Function.Injective J :=
    Module.Flat.rTensor_preserves_injective_linearMap V.subtype V.injective_subtype
  have h1 : ∀ w : V ⊗[R] A, J ((comul (R := R) (A := A)).lTensor V w) =
      (comul (R := R) (A := A)).lTensor A (j w) := by
    intro w
    induction w with
    | tmul v a => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have key : ∀ (w : V ⊗[R] A) (a : A), J (TensorProduct.assoc R V A A (w ⊗ₜ a)) =
      TensorProduct.assoc R A A A (j w ⊗ₜ a) := by
    intro w a
    induction w with
    | tmul v' a' => rfl
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  have h2 : ∀ w : V ⊗[R] A, J (TensorProduct.assoc R V A A (δ.rTensor A w)) =
      TensorProduct.assoc R A A A ((comul (R := R) (A := A)).rTensor A (j w)) := by
    intro w
    induction w with
    | tmul v a =>
      rw [LinearMap.rTensor_tmul, key, hjδ]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply LinearMap.ext
  intro x
  apply hJ
  show J (TensorProduct.assoc R V A A (δ.rTensor A (δ x))) =
    J ((comul (R := R) (A := A)).lTensor V (δ x))
  rw [h2, h1, hjδ]
  exact Coalgebra.coassoc_apply (R := R) (A := A) (x : A)

end Coaction

section Weights

variable {V : Type*} [AddCommGroup V] [Module R V]
  (δ : V →ₗ[R] V ⊗[R] A) (β : A →ₐ[R] AddMonoidAlgebra C M)

/-- The weights of `β` on the comodule `V` lie in `T`: every weight projector
outside `T` vanishes. -/
def WeightsIn (T : Set M) : Prop :=
  ∀ l ∉ T, ∀ x, proj δ β l x = 0

/-- For a finitely generated comodule, only finitely many weight projectors are
nonzero. -/
theorem exists_finite_weightsIn [Module.Finite R V] :
    ∃ T : Finset M, WeightsIn δ β (T : Set M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := V)
  -- the supports of the coefficients occurring in `δ v` for generators `v`
  have hfin : ∀ v : V, ∃ T : Finset M, ∀ l ∉ T, coeffSwap β l (δ v) = 0 := by
    intro v
    obtain ⟨S, hS⟩ := TensorProduct.exists_finset (δ v)
    refine ⟨S.biUnion fun p => (β p.2).coeff.support, fun l hl => ?_⟩
    rw [hS, map_sum]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [coeffSwap_tmul]
    have : (β p.2).coeff l = 0 := by
      by_contra hne
      exact hl (Finset.mem_biUnion.mpr ⟨p, hp, Finsupp.mem_support_iff.mpr hne⟩)
    rw [this, TensorProduct.zero_tmul]
  choose T hT using hfin
  refine ⟨s.biUnion T, fun l hl x => ?_⟩
  have hgen : ∀ v ∈ s, coeffSwap β l (δ v) = 0 := fun v hv =>
    hT v l (fun h => hl (Finset.mem_biUnion.mpr ⟨v, hv, h⟩))
  have hall : ∀ v : V, coeffSwap β l (δ v) = 0 := by
    intro v
    have hv : v ∈ Submodule.span R (s : Set V) := hs ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem v hv => exact hgen v hv
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb, add_zero]
    | smul r a _ ha => rw [map_smul, map_smul, ha, smul_zero]
  induction x with
  | tmul c v => rw [proj_tmul, hall v, smul_zero]
  | add a b ha hb => rw [map_add, ha, hb, add_zero]

/-- Weights in `T` force the coefficients on `ι V` to be supported in `T`. -/
theorem support_subset_of_weightsIn {V : Type*} [AddCommGroup V] [Module R V]
    (δ : V →ₗ[R] V ⊗[R] A) (β : A →ₐ[R] AddMonoidAlgebra C M) {T : Set M}
    (hT : WeightsIn δ β T) (ι : V →ₗ[R] A)
    (hι : (comul (R := R) (A := A)) ∘ₗ ι = ι.rTensor A ∘ₗ δ) (v : V) :
    ↑(β (ι v)).coeff.support ⊆ T := by
  intro l hl
  by_contra hlT
  apply Finsupp.mem_support_iff.mp hl
  rw [← counitV_proj δ β l ι hι v, hT l hlT, map_zero]

end Weights

section Pushforward

variable {V : Type*} [AddCommGroup V] [Module R V]
  (δ : V →ₗ[R] V ⊗[R] A) {M' : Type*} [AddCommGroup M']

theorem coeff_mapDomain_eq_sum [DecidableEq M'] (π : M →+ M') (x : AddMonoidAlgebra C M)
    (l : M') (S : Finset M) (hS : x.coeff.support ⊆ S) :
    (AddMonoidAlgebra.mapDomainAlgHom R C π x).coeff l =
      ∑ χ ∈ S, if π χ = l then x.coeff χ else 0 := by
  classical
  rw [HopfPointExtension.coeff_mapDomainAlgHom, Finsupp.mapDomain, Finsupp.sum_apply]
  rw [Finsupp.sum, Finset.sum_subset hS]
  · refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finsupp.single_apply]
  · intro χ _ hχ
    rw [Finsupp.notMem_support_iff.mp hχ, Finsupp.single_zero, Finsupp.zero_apply]

/-- Pushing a Hopf point forward along `π` pushes its weights forward. -/
theorem weightsIn_mapDomain [DecidableEq M] [DecidableEq M'] (π : M →+ M')
    {β : A →ₐ[R] AddMonoidAlgebra C M} {T : Set M} (hT : WeightsIn δ β T) :
    WeightsIn δ ((AddMonoidAlgebra.mapDomainAlgHom R C π).comp β) (π '' T) := by
  intro l hl x
  induction x with
  | tmul c v =>
    rw [proj_tmul]
    obtain ⟨S, hS⟩ := TensorProduct.exists_finset (δ v)
    let U : Finset M := S.biUnion fun p => (β p.2).coeff.support
    have hsub : ∀ p ∈ S, (β p.2).coeff.support ⊆ U := fun p hp =>
      Finset.subset_biUnion_of_mem (fun p => (β p.2).coeff.support) hp
    have key : coeffSwap ((AddMonoidAlgebra.mapDomainAlgHom R C π).comp β) l (δ v) =
        ∑ χ ∈ U, if π χ = l then coeffSwap β χ (δ v) else 0 := by
      have hp : ∀ p ∈ S, coeffSwap ((AddMonoidAlgebra.mapDomainAlgHom R C π).comp β) l
          (p.1 ⊗ₜ p.2) = ∑ χ ∈ U, if π χ = l then coeffSwap β χ (p.1 ⊗ₜ p.2) else 0 := by
        intro p hp
        rw [coeffSwap_tmul, AlgHom.comp_apply, coeff_mapDomain_eq_sum π (β p.2) l U (hsub p hp),
          TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun χ _ => ?_
        split_ifs
        · rw [coeffSwap_tmul]
        · rw [TensorProduct.zero_tmul]
      rw [hS, map_sum, Finset.sum_congr rfl hp, Finset.sum_comm]
      refine Finset.sum_congr rfl fun χ _ => ?_
      split_ifs
      · rw [map_sum]
      · rw [Finset.sum_const_zero]
    rw [key, Finset.sum_eq_zero, smul_zero]
    intro χ _
    split_ifs with hχ
    · have hχT : χ ∉ T := fun h => hl ⟨χ, h, hχ⟩
      have := hT χ hχT (1 ⊗ₜ v)
      rwa [proj_tmul, one_smul] at this
    · rfl
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

end Pushforward

end Langlands.Algebra.HopfPointWeightWindow
