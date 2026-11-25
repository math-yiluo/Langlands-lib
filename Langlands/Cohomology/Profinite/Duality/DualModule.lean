import Langlands.Cohomology.Profinite.ClassFormation.Corestriction
import Langlands.Cohomology.Profinite.Cup.Pairing
import Langlands.Cohomology.Profinite.TorsionDual

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory

universe u

section Iso

variable {k G : Type*} [CommRing k] [Monoid G]

def repIsoOfBijective {A B : Rep.{u} k G} (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    A ≅ B :=
  Rep.mkIso (Representation.IntertwiningMap.ofBijective f.hom hf)

@[simp]
theorem repIsoOfBijective_hom {A B : Rep.{u} k G} (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    (repIsoOfBijective f hf).hom = f :=
  rfl

end Iso

section ZMod

variable (G : Type*) [Monoid G]

abbrev zmodRep (n : ℕ) : Rep.{u} (ULift.{u} ℤ) G :=
  Rep.trivial (ULift.{u} ℤ) G (ULift.{u} (ZMod n))

end ZMod

section ULiftInt


variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module (ULift.{u} ℤ) A]
  [Module (ULift.{u} ℤ) B]

variable (A B) in

def uliftIntLinearEquivAddHom : (A →ₗ[ULift.{u} ℤ] B) ≃+ (A →+ B) where
  toFun f := f.toAddMonoidHom
  invFun g :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r a => by
        obtain ⟨k⟩ := r
        have h : (ULift.up k : ULift.{u} ℤ) = ((k : ℤ) : ULift.{u} ℤ) := by
          ext
          simp
        rw [RingHom.id_apply, h, Int.cast_smul_eq_zsmul (ULift.{u} ℤ) k a,
          Int.cast_smul_eq_zsmul (ULift.{u} ℤ) k (g a)]
        exact map_zsmul g k a }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem uliftIntLinearEquivAddHom_apply (f : A →ₗ[ULift.{u} ℤ] B) (a : A) :
    uliftIntLinearEquivAddHom A B f a = f a :=
  rfl

@[simp]
theorem uliftIntLinearEquivAddHom_symm_apply (g : A →+ B) (a : A) :
    (uliftIntLinearEquivAddHom A B).symm g a = g a :=
  rfl

end ULiftInt

section ZMod

theorem nsmul_zmodRep_eq_zero (G : Type*) [Monoid G] (n : ℕ) (x : zmodRep.{u} G n) : n • x = 0 := by
  obtain ⟨z⟩ := x
  apply ULift.ext
  change n • z = 0
  have := AddMonoid.exponent_nsmul_eq_zero z
  rwa [ZMod.exponent] at this

theorem exponent_zmodRep (G : Type*) [Monoid G] (n : ℕ) :
    AddMonoid.exponent (zmodRep.{u} G n) = n := by
  change AddMonoid.exponent (ULift.{u} (ZMod n)) = n
  rw [AddMonoid.exponent_eq_of_addEquiv AddEquiv.ulift, ZMod.exponent]

instance finite_zmodRep (G : Type*) [Monoid G] (n : ℕ) [NeZero n] : Finite (zmodRep.{u} G n) :=
  inferInstanceAs (Finite (ULift.{u} (ZMod n)))

theorem zmodRep_eq_zsmul (G : Type*) [Monoid G] (n : ℕ) (k : ℤ) :
    (ULift.up (k : ZMod n) : zmodRep.{u} G n) = k • (ULift.up 1 : zmodRep.{u} G n) := by
  apply ULift.ext
  change (k : ZMod n) = k • (1 : ZMod n)
  rw [zsmul_one]

end ZMod

section ZModRes

variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
  [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G ≃ₜ* G')

/-- `ℤ/n` restricted along an isomorphism is `ℤ/n`. -/
def zmodRepResIso (n : ℕ) : Rep.res (θ : G →* G') (zmodRep.{u} G' n) ≅ zmodRep.{u} G n where
  hom := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  inv := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

end ZModRes

section H0

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[reassoc]
theorem cocyclesIso₀_hom_comp_f (A : Rep.{u} k G) [IsSmoothRep A] :
    (cocyclesIso₀ A).hom ≫ (shortComplexH0 A).f = (cochains A).iCycles 0 := by
  rw [cocyclesIso₀, Limits.KernelFork.mapIsoOfIsLimit_hom]
  exact (Limits.KernelFork.mapOfIsLimit_ι _ _ _).trans (Category.comp_id _)

theorem shortComplexH0_f_zeroIso_hom (A : Rep.{u} k G) [IsSmoothRep A] (y : cohomology A 0) :
    (shortComplexH0 A).f.hom ((zeroIso A).hom.hom y) =
      ((cochains A).iCycles 0).hom ((cochains A).isoHomologyπ₀.inv.hom y) :=
  congrArg (fun φ => φ.hom ((cochains A).isoHomologyπ₀.inv.hom y))
    (cocyclesIso₀_hom_comp_f A)

/-- The invariant vector of the class of a `0`-cocycle is the value of the cocycle at the empty
tuple. -/
theorem zeroIso_hom_cohomology_class_zero (A : Rep.{u} k G) [IsSmoothRep A] (z : cocycles A 0) :
    (((zeroIso A).hom.hom (cohomologyπ A 0 z) : A.ρ.invariants) : A) =
      cochainOf A (cocycleι A 0 z) Fin.elim0 := by
  have h1 : (CochainComplex.isoHomologyπ₀ (cochains A)).inv.hom (cohomologyπ A 0 z) = z := by
    exact congrArg (fun φ => φ.hom z) (CochainComplex.isoHomologyπ₀ (cochains A)).hom_inv_id
  have h2 := congrArg (fun φ => φ.hom z) (cocyclesIso₀_hom_comp_f A)
  change (shortComplexH0 A).f.hom ((cocyclesIso₀ A).hom.hom z) = cocycleι A 0 z at h2
  change (((cocyclesIso₀ A).hom.hom ((CochainComplex.isoHomologyπ₀ (cochains A)).inv.hom
    (cohomologyπ A 0 z)) : A.ρ.invariants) : A) = _
  rw [h1, ← h2]
  rfl

theorem zeroIso_inv_hom_apply (A : Rep.{u} k G) [IsSmoothRep A] (y : cohomology A 0) :
    (zeroIso A).inv.hom ((zeroIso A).hom.hom y) = y :=
  congrArg (fun φ => φ.hom y) (zeroIso A).hom_inv_id

theorem zeroIso_hom_inv_apply (A : Rep.{u} k G) [IsSmoothRep A] (v : A.ρ.invariants) :
    (zeroIso A).hom.hom ((zeroIso A).inv.hom v) = v :=
  congrArg (fun φ => φ.hom v) (zeroIso A).inv_hom_id

theorem cohomologyMap_zero_comp_zeroIso_hom {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    (f : A ⟶ B) :
    coeffMap f 0 ≫ (zeroIso B).hom = (zeroIso A).hom ≫ (Rep.invariantsFunctor k G).map f := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  apply (ModuleCat.mono_iff_injective (shortComplexH0 B).f).1 inferInstance
  change (shortComplexH0 B).f.hom ((zeroIso B).hom.hom ((coeffMap f 0).hom x)) =
    (shortComplexH0 B).f.hom (((Rep.invariantsFunctor k G).map f).hom ((zeroIso A).hom.hom x))
  rw [shortComplexH0_f_zeroIso_hom]
  have e1 := congrArg (fun φ => φ.hom x)
    (CochainComplex.isoHomologyπ₀_inv_naturality (coeffCochainsMap f))
  have e2 := congrArg (fun φ => φ.hom ((cochains A).isoHomologyπ₀.inv.hom x))
    (HomologicalComplex.cyclesMap_i (coeffCochainsMap f) 0)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  change ((cochains B).iCycles 0).hom ((cochains B).isoHomologyπ₀.inv.hom
    ((HomologicalComplex.homologyMap (coeffCochainsMap f) 0).hom x)) = _
  exact (congrArg ((cochains B).iCycles 0).hom e1).trans (e2.trans
    (congrArg ((coeffCochainsMap f).f 0).hom (shortComplexH0_f_zeroIso_hom A x).symm))

end H0

section Bijective

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A bijective map of coefficients is injective on cohomology. -/
theorem injective_coeffMap_of_bijective {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    (f : A ⟶ B) (hf : Function.Bijective f.hom) (n : ℕ) :
    Function.Injective (coeffMap f n).hom := by
  let e := repIsoOfBijective f hf
  refine Function.LeftInverse.injective (g := (coeffMap e.inv n).hom) fun z => ?_
  rw [← ModuleCat.comp_apply, ← coeffMap_comp, show f ≫ e.inv = 𝟙 A from e.hom_inv_id, coeffMap_id]
  rfl

end Bijective

end Langlands.ProfiniteCohomology

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory

universe u

section Dual

variable {k G : Type u} [CommRing k] [Group G]

abbrev dualRep (D M : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (Representation.linHom M.ρ D.ρ)

theorem dualRep_eq_ihom (D M : Rep.{u} k G) : dualRep D M = (Rep.ihom M).obj D :=
  rfl

theorem dualRep_ρ_apply (D M : Rep.{u} k G) (σ : G) (f : M →ₗ[k] D) (m : M) :
    ((dualRep D M).ρ σ f : M →ₗ[k] D) m = D.ρ σ (f (M.ρ σ⁻¹ m)) :=
  rfl

def dualMap (D : Rep.{u} k G) {A B : Rep.{u} k G} (φ : A ⟶ B) : dualRep D B ⟶ dualRep D A :=
  Rep.ofHom ⟨{ toFun := fun f => f ∘ₗ φ.hom.toLinearMap
               map_add' := fun f g => rfl
               map_smul' := fun r f => rfl }, fun σ => by
    refine LinearMap.ext fun f => LinearMap.ext fun a => ?_
    change D.ρ σ (f (B.ρ σ⁻¹ (φ.hom a))) = D.ρ σ (f (φ.hom (A.ρ σ⁻¹ a)))
    rw [Rep.hom_comm_apply]⟩

@[simp]
theorem dualMap_hom_apply (D : Rep.{u} k G) {A B : Rep.{u} k G} (φ : A ⟶ B) (f : B →ₗ[k] D)
    (a : A) : ((dualMap D φ).hom f : A →ₗ[k] D) a = f (φ.hom a) :=
  rfl

theorem dualMap_id (D A : Rep.{u} k G) : dualMap D (𝟙 A) = 𝟙 (dualRep D A) :=
  rfl

theorem dualMap_comp (D : Rep.{u} k G) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    dualMap D (φ ≫ ψ) = dualMap D ψ ≫ dualMap D φ :=
  rfl

def dualEvalBilin (D M : Rep.{u} k G) : M →ₗ[k] (M →ₗ[k] D) →ₗ[k] D where
  toFun m :=
    { toFun := fun f => f m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' a b := LinearMap.ext fun f => f.map_add a b
  map_smul' r a := LinearMap.ext fun f => f.map_smul r a

def evalPairing (D M : Rep.{u} k G) : M ⊗ dualRep D M ⟶ D :=
  pairingHom (dualEvalBilin D M) fun σ m f => by
    change D.ρ σ (f (M.ρ σ⁻¹ (M.ρ σ m))) = D.ρ σ (f m)
    rw [Representation.inv_self_apply]

@[simp]
theorem evalPairing_tmul (D M : Rep.{u} k G) (m : M) (f : M →ₗ[k] D) :
    (evalPairing D M).hom (m ⊗ₜ[k] (f : dualRep D M) : (M ⊗ dualRep D M : Rep k G)) = f m :=
  pairingHom_tmul (A := M) (B := dualRep D M) (dualEvalBilin D M) _ m f

theorem tensorHom_evalPairing (D : Rep.{u} k G) {A B : Rep.{u} k G} (φ : A ⟶ B) :
    (φ ⊗ₘ 𝟙 (dualRep D B)) ≫ evalPairing D B = (𝟙 A ⊗ₘ dualMap D φ) ≫ evalPairing D A := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def toDualDual (D M : Rep.{u} k G) : M ⟶ dualRep D (dualRep D M) :=
  Rep.ofHom ⟨dualEvalBilin D M, fun σ => by
    refine LinearMap.ext fun m => LinearMap.ext fun f => ?_
    change f (M.ρ σ m) = D.ρ σ (D.ρ σ⁻¹ (f (M.ρ σ⁻¹⁻¹ m)))
    rw [inv_inv, Representation.self_inv_apply]⟩

@[simp]
theorem toDualDual_hom_apply (D M : Rep.{u} k G) (m : M) (f : M →ₗ[k] D) :
    ((toDualDual D M).hom m : (M →ₗ[k] D) →ₗ[k] D) f = f m :=
  rfl

end Dual

section Discrete

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance isSmoothRep_dualRep (D M : Rep.{u} k G) [IsSmoothRep D] [IsSmoothRep M]
    [Finite M] : IsSmoothRep (dualRep D M) := by
  refine IsSmoothRep.of_isOpen_stabilizer _ fun f => Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hmem : (⋂ m : M, ((vectorStabilizer M.ρ m : Set G) ∩ (vectorStabilizer D.ρ (f m) : Set G))) ∈
      nhds (1 : G) :=
    Filter.iInter_mem.2 fun m => Filter.inter_mem
      ((IsSmoothRep.isOpen_stabilizer M m).mem_nhds (one_mem _))
      ((IsSmoothRep.isOpen_stabilizer D (f m)).mem_nhds (one_mem _))
  refine Filter.mem_of_superset hmem fun σ hσ => ?_
  simp only [Set.mem_iInter, Set.mem_inter_iff, SetLike.mem_coe, mem_vectorStabilizer] at hσ
  change (dualRep D M).ρ σ f = f
  refine LinearMap.ext fun m => ?_
  have hm : M.ρ σ⁻¹ m = m := (vectorStabilizer M.ρ m).inv_mem (hσ m).1
  rw [dualRep_ρ_apply, hm, (hσ m).2]

end Discrete

section Pairing

variable {k : Type u} [CommRing k]

def bilinAddHom {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Module k X]
    [Module k Y] [Module k Z] (β : X →ₗ[k] Y →ₗ[k] Z) : X →+ Y →+ Z where
  toFun x := (β x).toAddMonoidHom
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem bilinAddHom_apply {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module k X] [Module k Y] [Module k Z] (β : X →ₗ[k] Y →ₗ[k] Z) (x : X) (y : Y) :
    bilinAddHom β x y = β x y :=
  rfl

def IsPerfectPairing {n : ℕ} {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (β : X →+ Y →+ Z) (t : Z →+ ZMod n) : Prop :=
  Function.Bijective (fun x : X => t.comp (β x)) ∧
    Function.Bijective (fun y : Y => t.comp (β.flip y))

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def dualityMap (D : Rep.{u} k G) [IsSmoothRep D] {n m r s : ℕ} (h : r + s = m)
    (t : cohomology D m →+ ZMod n) (M : Rep.{u} k G) [IsSmoothRep M]
    [IsSmoothRep (dualRep D M)] :
    cohomology M r →+ (cohomology (dualRep D M) s →+ ZMod n) where
  toFun x := t.comp (bilinAddHom (cupPairing (evalPairing D M) h) x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem dualityMap_apply (D : Rep.{u} k G) [IsSmoothRep D] {n m r s : ℕ} (h : r + s = m)
    (t : cohomology D m →+ ZMod n) (M : Rep.{u} k G) [IsSmoothRep M]
    [IsSmoothRep (dualRep D M)] (x : cohomology M r) (y : cohomology (dualRep D M) s) :
    dualityMap D h t M x y = t (cupPairing (evalPairing D M) h x y) :=
  rfl

end Pairing

section ZModMul

variable {G : Type u} [Group G]

theorem nsmul_eq_zero_of_nonempty_addEquiv {n : ℕ} {D : Type*} [AddCommGroup D]
    (h : Nonempty (D ≃+ ZMod n)) (d : D) : n • d = 0 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_nsmul, map_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem zsmul_eq_zsmul_of_intCast_eq {n : ℕ} {D : Type*} [AddCommGroup D]
    (hD : ∀ d : D, n • d = 0) {a b : ℤ} (h : (a : ZMod n) = b) (d : D) : a • d = b • d := by
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a n).1 h.symm
  have h0 : (a - b) • d = 0 := by
    rw [hc, mul_comm, mul_zsmul, natCast_zsmul, hD, zsmul_zero]
  rwa [sub_smul, sub_eq_zero] at h0

def zmodMulAddHom (n : ℕ) {D : Type*} [AddCommGroup D] (hD : ∀ d : D, n • d = 0) :
    ZMod n →+ D →+ D where
  toFun a :=
    { toFun := fun d => (ZMod.cast a : ℤ) • d
      map_zero' := zsmul_zero _
      map_add' := fun d d' => zsmul_add _ _ _ }
  map_zero' := by
    ext d
    simp
  map_add' a b := by
    ext d
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply, ← add_zsmul]
    exact zsmul_eq_zsmul_of_intCast_eq hD (by push_cast; simp) d

theorem zmodMulAddHom_apply (n : ℕ) {D : Type*} [AddCommGroup D] (hD : ∀ d : D, n • d = 0)
    (a : ZMod n) (d : D) : zmodMulAddHom n hD a d = (ZMod.cast a : ℤ) • d :=
  rfl

def bilinOfAddHom {k : Type*} [CommRing k] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module k A] [Module k B] [Module k C] (f : A →+ B →+ C)
    (h₁ : ∀ (c : k) (a : A) (b : B), f (c • a) b = c • f a b)
    (h₂ : ∀ (c : k) (a : A) (b : B), f a (c • b) = c • f a b) : A →ₗ[k] B →ₗ[k] C :=
  LinearMap.mk₂ k (fun a b => f a b) (fun a a' b => by simp) h₁ (fun a b b' => by simp) h₂

def zmodMulPairing (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) G) (hD : ∀ d : D, n • d = 0) :
    zmodRep.{u} G n ⊗ D ⟶ D :=
  pairingHom
    (bilinOfAddHom ((zmodMulAddHom n hD).comp
      ((AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n).toAddMonoidHom.comp
        (AddMonoidHom.id (zmodRep.{u} G n))))
      (fun c a d => by
        obtain ⟨c⟩ := c
        have h : (ULift.up c : ULift.{u} ℤ) = ((c : ℤ) : ULift.{u} ℤ) := by
          ext
          simp
        rw [h, Int.cast_smul_eq_zsmul (ULift.{u} ℤ), Int.cast_smul_eq_zsmul (ULift.{u} ℤ),
          map_zsmul, AddMonoidHom.zsmul_apply])
      (fun c a d => by
        obtain ⟨c⟩ := c
        have h : (ULift.up c : ULift.{u} ℤ) = ((c : ℤ) : ULift.{u} ℤ) := by
          ext
          simp
        rw [h, Int.cast_smul_eq_zsmul (ULift.{u} ℤ), Int.cast_smul_eq_zsmul (ULift.{u} ℤ),
          map_zsmul]))
    fun σ a d => by
      change zmodMulAddHom n hD (ULift.down (a : ULift.{u} (ZMod n))) (D.ρ σ d) =
        D.ρ σ (zmodMulAddHom n hD (ULift.down (a : ULift.{u} (ZMod n))) d)
      rw [zmodMulAddHom_apply, zmodMulAddHom_apply, map_zsmul]

@[simp]
theorem zmodMulPairing_tmul (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) G) (hD : ∀ d : D, n • d = 0)
    (a : ZMod n) (d : D) :
    (zmodMulPairing n D hD).hom ((ULift.up a : zmodRep.{u} G n) ⊗ₜ[ULift.{u} ℤ] d :
      (zmodRep.{u} G n ⊗ D : Rep _ _)) = (ZMod.cast a : ℤ) • d :=
  by
    rw [zmodMulPairing, pairingHom_tmul]
    rfl

end ZModMul

section Hypotheses

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

structure DualizingData (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D] where

  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)

  finite_cohomology : ∀ (U : OpenSubgroup G) (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup G))
    [IsSmoothRep M] [Finite M], (∀ m : M, n • m = 0) → ∀ r ≤ 2, Finite (cohomology M r)

  subsingleton_cohomology_three : ∀ (U : OpenSubgroup G)
    (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup G)) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (cohomology M 3)

  t : ∀ U : OpenSubgroup G, cohomology (Rep.res (U : Subgroup G).subtype D) 2 ≃+ ZMod n

  t_cores : ∀ (U V : OpenSubgroup G) (h : V ≤ U)
    (x : cohomology (Rep.res (V : Subgroup G).subtype D) 2),
    t U (coresOfLE D h 2 x) = t V x

  isPerfectPairing : ∀ U : OpenSubgroup G,
    IsPerfectPairing
      (bilinAddHom (cupPairing (zmodMulPairing n (Rep.res (U : Subgroup G).subtype D)
        (nsmul_eq_zero_of_nonempty_addEquiv nonempty_addEquiv)) (show 1 + 1 = 2 from rfl)))
      (t U).toAddMonoidHom

end Hypotheses

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open Function

variable {n : ℕ}

variable (n) in

noncomputable def zmodToQZ : ZMod n →+ QZ :=
  ZMod.lift n ⟨zmultiplesHom QZ (QZ.mk (1 / n)), by
    rw [zmultiplesHom_apply, ← QZ.mk_zsmul, QZ.mk_eq_zero_iff]
    by_cases hn : n = 0
    · exact ⟨0, by simp [hn]⟩
    · have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
      exact ⟨1, by rw [zsmul_eq_mul, Int.cast_natCast, mul_one_div, div_self hn', Int.cast_one]⟩⟩

theorem zmodToQZ_intCast (m : ℤ) : zmodToQZ n (m : ZMod n) = QZ.mk (m / n) := by
  rw [zmodToQZ, ZMod.lift_coe, zmultiplesHom_apply, ← QZ.mk_zsmul, zsmul_eq_mul, mul_one_div]

variable [NeZero n]

theorem zmodToQZ_injective : Injective (zmodToQZ n) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
  rw [zmodToQZ_intCast, QZ.mk_eq_zero_iff] at ha
  obtain ⟨z, hz⟩ := ha
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨z, ?_⟩
  have : (m : ℚ) = n * z := by
    rw [hz]
    field_simp
  exact_mod_cast this

theorem exists_zmodToQZ_eq {x : QZ} (hx : n • x = 0) : ∃ a : ZMod n, zmodToQZ n a = x := by
  obtain ⟨q, rfl⟩ := QZ.mk_surjective x
  have h : QZ.mk ((n : ℤ) • q) = 0 := by
    rw [QZ.mk_zsmul, natCast_zsmul, hx]
  obtain ⟨z, hz⟩ := (QZ.mk_eq_zero_iff _).1 h
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  refine ⟨(z : ZMod n), ?_⟩
  rw [zmodToQZ_intCast, hz, zsmul_eq_mul]
  congr 1
  push_cast
  field_simp

section Lift

variable {A : Type*} [AddCommGroup A]

noncomputable def zmodOfQZ (f : A →+ QZ) (hf : ∀ a, n • f a = 0) : A →+ ZMod n where
  toFun a := Classical.choose (exists_zmodToQZ_eq (hf a))
  map_zero' := zmodToQZ_injective (by
    rw [Classical.choose_spec (exists_zmodToQZ_eq (hf 0)), map_zero, map_zero])
  map_add' a b := zmodToQZ_injective (by
    rw [Classical.choose_spec (exists_zmodToQZ_eq (hf (a + b))), map_add, map_add,
      Classical.choose_spec (exists_zmodToQZ_eq (hf a)),
      Classical.choose_spec (exists_zmodToQZ_eq (hf b))])

theorem zmodToQZ_zmodOfQZ (f : A →+ QZ) (hf : ∀ a, n • f a = 0) (a : A) :
    zmodToQZ n (zmodOfQZ f hf a) = f a :=
  Classical.choose_spec (exists_zmodToQZ_eq (hf a))

end Lift

theorem zmod_exists_comp_eq_of_ker_le {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (hC : ∀ c : C, n • c = 0) (h : B →+ C) (χ : B →+ ZMod n) (hχ : h.ker ≤ χ.ker) :
    ∃ ψ : C →+ ZMod n, ψ.comp h = χ := by
  obtain ⟨ψ₀, hψ₀⟩ := QZ.exists_comp_eq_of_ker_le h ((zmodToQZ n).comp χ) fun b hb => by
    rw [AddMonoidHom.mem_ker] at hb ⊢
    rw [AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).1 (hχ hb), map_zero]
  have hψ₀' : ∀ c, n • ψ₀ c = 0 := fun c => by rw [← map_nsmul, hC, map_zero]
  refine ⟨zmodOfQZ ψ₀ hψ₀', AddMonoidHom.ext fun b => zmodToQZ_injective ?_⟩
  rw [AddMonoidHom.comp_apply, zmodToQZ_zmodOfQZ]
  exact DFunLike.congr_fun hψ₀ b

theorem zmod_exists_apply_ne_zero {A : Type*} [AddCommGroup A] (hA : ∀ a : A, n • a = 0)
    {a : A} (ha : a ≠ 0) : ∃ χ : A →+ ZMod n, χ a ≠ 0 := by
  obtain ⟨f, hf⟩ := QZ.exists_apply_ne_zero ha
  have hf' : ∀ x, n • f x = 0 := fun x => by rw [← map_nsmul, hA, map_zero]
  refine ⟨zmodOfQZ f hf', fun h => hf ?_⟩
  rw [← zmodToQZ_zmodOfQZ f hf' a, h, map_zero]

theorem comp_zmodToQZ_injective {A : Type*} [AddCommGroup A] :
    Injective fun χ : A →+ ZMod n => (zmodToQZ n).comp χ := fun _ _ h =>
  AddMonoidHom.ext fun a => zmodToQZ_injective (DFunLike.congr_fun h a)

instance finite_addMonoidHom_zmod {A : Type*} [AddCommGroup A] [Finite A] :
    Finite (A →+ ZMod n) :=
  Finite.of_injective _ comp_zmodToQZ_injective

theorem card_addMonoidHom_zmod_le {A : Type*} [AddCommGroup A] [Finite A] :
    Nat.card (A →+ ZMod n) ≤ Nat.card A :=
  (Nat.card_le_card_of_injective _ comp_zmodToQZ_injective).trans QZ.card_hom_le

theorem bijective_of_bijective_flip {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Finite X] (hX : ∀ x : X, n • x = 0) (β : X →+ Y →+ Z) (t : Z →+ ZMod n)
    (h : Bijective fun y : Y => t.comp (β.flip y)) : Bijective fun x : X => t.comp (β x) := by
  let ψ : Y →+ (X →+ ZMod n) :=
    { toFun := fun y => t.comp (β.flip y)
      map_zero' := by ext; simp
      map_add' := fun y y' => by ext; simp }
  let φ : X →+ (Y →+ ZMod n) :=
    { toFun := fun x => t.comp (β x)
      map_zero' := by ext; simp
      map_add' := fun x x' => by ext; simp }
  let e : Y ≃+ (X →+ ZMod n) := AddEquiv.ofBijective ψ h
  let e' : (Y →+ ZMod n) ≃ ((X →+ ZMod n) →+ ZMod n) :=
    { toFun := fun f => f.comp e.symm.toAddMonoidHom
      invFun := fun g => g.comp e.toAddMonoidHom
      left_inv := fun f => by ext; simp
      right_inv := fun g => by ext; simp }
  have : Finite (Y →+ ZMod n) := Finite.of_equiv _ e'.symm
  have hinj : Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hX hne
    obtain ⟨y, hy⟩ := h.2 χ
    apply hχ
    rw [← hy]
    exact DFunLike.congr_fun hx y
  refine hinj.bijective_of_nat_card_le ?_
  calc Nat.card (Y →+ ZMod n) = Nat.card ((X →+ ZMod n) →+ ZMod n) := Nat.card_congr e'
    _ ≤ Nat.card (X →+ ZMod n) := card_addMonoidHom_zmod_le
    _ ≤ Nat.card X := card_addMonoidHom_zmod_le

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

section Algebra

/-- A group `B` with maps `g : A → B`, `f : B → C` from and to finite groups is finite when the
kernel of `f` lies in the range of `g`. -/
theorem finite_of_exact_of_finite {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Finite A] [Finite C] (g : A →+ B) (f : B →+ C)
    (hex : ∀ b, f b = 0 → ∃ a, g a = b) : Finite B := by
  rw [f.finite_iff_finite_ker_range]
  refine ⟨?_, inferInstance⟩
  have hsub : (f.ker : Set B) ⊆ Set.range g := fun b hb => hex b hb
  exact ((Set.finite_range g).subset hsub).to_subtype

variable {n : ℕ}

/-- If `f = c • g` with `f` surjective onto `ℤ/n`, then `c` is a unit. -/
theorem isUnit_of_surjective_of_eq_mul {Y : Type*} [AddCommGroup Y] (f g : Y →+ ZMod n)
    (hf : Function.Surjective f) (c : ZMod n) (hfg : ∀ y, f y = c * g y) : IsUnit c := by
  obtain ⟨y, hy⟩ := hf 1
  exact IsUnit.of_mul_eq_one (g y) ((hfg y).symm.trans hy)

end Algebra

section PerfectPairing

variable {n : ℕ} [NeZero n]

/-- A finite group killed by `n` has as many characters with values in `ℤ/n` as elements. -/
theorem card_addMonoidHom_zmod_of_nsmul {B : Type*} [AddCommGroup B] [Finite B]
    (hB : ∀ b : B, n • b = 0) : Nat.card (B →+ ZMod n) = Nat.card B := by
  refine le_antisymm card_addMonoidHom_zmod_le ?_
  have : Finite (B →+ ZMod n) :=
    Finite.of_injective (fun f : B →+ ZMod n => (f : B → ZMod n)) DFunLike.coe_injective
  let ev : B →+ ((B →+ ZMod n) →+ ZMod n) :=
    AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun f => f b) fun f g => rfl)
      fun b c => by ext f; simp
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra h
    obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hB h
    exact hχ (DFunLike.congr_fun hb χ)
  exact (Nat.card_le_card_of_injective _ hinj).trans card_addMonoidHom_zmod_le

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

/-- The homomorphisms vanishing on `S` are the homomorphisms from `Y/S`. -/
def annihilatorEquiv (S : AddSubgroup Y) :
    {f : Y →+ ZMod n // ∀ y ∈ S, f y = 0} ≃ (Y ⧸ S →+ ZMod n) where
  toFun f := QuotientAddGroup.lift S f.1 fun y hy => f.2 y hy
  invFun g := ⟨g.comp (QuotientAddGroup.mk' S), fun y hy => by
    simp [(QuotientAddGroup.eq_zero_iff y).2 hy]⟩
  left_inv f := Subtype.ext (AddMonoidHom.ext fun y => rfl)
  right_inv g := by
    refine AddMonoidHom.ext fun q => ?_
    induction q using QuotientAddGroup.induction_on
    rfl

/-- In a perfect pairing `X × Y → ℤ/n` of finite groups with `Y` killed by `n`, the annihilator of
`S ⊆ Y` has `|Y|/|S|` elements. -/
theorem card_annihilator_left [Finite Y] (hY : ∀ y : Y, n • y = 0) {β : X →+ Y →+ Z}
    {t : Z →+ ZMod n} (hP : IsPerfectPairing β t) (S : AddSubgroup Y) :
    Nat.card {x : X // ∀ y ∈ S, t (β x y) = 0} * Nat.card S = Nat.card Y := by
  have e1 : {x : X // ∀ y ∈ S, t (β x y) = 0} ≃ {f : Y →+ ZMod n // ∀ y ∈ S, f y = 0} :=
    (Equiv.ofBijective _ hP.1).subtypeEquiv fun x => Iff.rfl
  have hQ : ∀ q : Y ⧸ S, n • q = 0 := fun q => by
    induction q using QuotientAddGroup.induction_on with
    | H y => rw [← QuotientAddGroup.mk_nsmul, hY, QuotientAddGroup.mk_zero]
  rw [Nat.card_congr (e1.trans (annihilatorEquiv S)), card_addMonoidHom_zmod_of_nsmul hQ,
    ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]

/-- The same on the other side. -/
theorem card_annihilator_right [Finite X] (hX : ∀ x : X, n • x = 0) {β : X →+ Y →+ Z}
    {t : Z →+ ZMod n} (hP : IsPerfectPairing β t) (A : AddSubgroup X) :
    Nat.card {y : Y // ∀ x ∈ A, t (β x y) = 0} * Nat.card A = Nat.card X := by
  have e1 : {y : Y // ∀ x ∈ A, t (β x y) = 0} ≃ {f : X →+ ZMod n // ∀ x ∈ A, f x = 0} :=
    (Equiv.ofBijective _ hP.2).subtypeEquiv fun y => Iff.rfl
  have hQ : ∀ q : X ⧸ A, n • q = 0 := fun q => by
    induction q using QuotientAddGroup.induction_on with
    | H x => rw [← QuotientAddGroup.mk_nsmul, hX, QuotientAddGroup.mk_zero]
  rw [Nat.card_congr (e1.trans (annihilatorEquiv A)), card_addMonoidHom_zmod_of_nsmul hQ,
    ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]

/-- The annihilator in `X` of a subgroup of `Y`, as a subgroup. -/
def leftAnnihilator (β : X →+ Y →+ Z) (t : Z →+ ZMod n) (S : AddSubgroup Y) : AddSubgroup X where
  carrier := {x | ∀ y ∈ S, t (β x y) = 0}
  add_mem' ha hb y hy := by rw [map_add, AddMonoidHom.add_apply, map_add, ha y hy, hb y hy,
    add_zero]
  zero_mem' y _ := by rw [map_zero, AddMonoidHom.zero_apply, map_zero]
  neg_mem' ha y hy := by rw [map_neg, AddMonoidHom.neg_apply, map_neg, ha y hy, neg_zero]

/-- In a perfect pairing of finite groups killed by `n`, a subgroup of `Y` is the annihilator of
its annihilator. -/
theorem mem_of_forall_leftAnnihilator [Finite X] [Finite Y] (hX : ∀ x : X, n • x = 0)
    (hY : ∀ y : Y, n • y = 0) {β : X →+ Y →+ Z} {t : Z →+ ZMod n} (hP : IsPerfectPairing β t)
    (S : AddSubgroup Y) {y : Y} (hy : ∀ x ∈ leftAnnihilator β t S, t (β x y) = 0) : y ∈ S := by
  set A := leftAnnihilator β t S
  let B : AddSubgroup Y :=
    { carrier := {y | ∀ x ∈ A, t (β x y) = 0}
      add_mem' := fun ha hb x hx => by rw [map_add, map_add, ha x hx, hb x hx, add_zero]
      zero_mem' := fun x _ => by rw [map_zero, map_zero]
      neg_mem' := fun ha x hx => by rw [map_neg, map_neg, ha x hx, neg_zero] }
  have hSB : S ≤ B := fun y hy x hx => hx y hy
  have h1 : Nat.card B * Nat.card A = Nat.card X := card_annihilator_right hX hP A
  have h2 : Nat.card A * Nat.card S = Nat.card Y := card_annihilator_left hY hP S
  have hXY : Nat.card X = Nat.card Y := by
    rw [Nat.card_congr (Equiv.ofBijective _ hP.1), card_addMonoidHom_zmod_of_nsmul hY]
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hcard : Nat.card B = Nat.card S := by
    rw [hXY, ← h2, mul_comm (Nat.card A)] at h1
    exact Nat.eq_of_mul_eq_mul_right hApos h1
  have : Finite B := Finite.of_injective _ Subtype.val_injective
  have hBS : S = B := AddSubgroup.eq_of_le_of_card_ge hSB hcard.le
  rw [hBS]
  exact hy

/-- If `N` is the common kernel of a finite group `A` of characters `G → ℤ/n` (given as a pairing
`c`), then `|G/N| ≤ |A|`: `G/N` embeds into `Hom(A, ℤ/n)`. -/
theorem card_quotient_le_of_pairing {G : Type*} [Group G] {X : Type*} [AddCommGroup X]
    (A : AddSubgroup X) [Finite A] (c : X → G → ZMod n)
    (hadd : ∀ x y g, c (x + y) g = c x g + c y g) (hmul : ∀ x g h, c x (g * h) = c x g + c x h)
    (N : Subgroup G) (hN : ∀ g, g ∈ N ↔ ∀ x ∈ A, c x g = 0) :
    Nat.card (G ⧸ N) ≤ Nat.card A := by
  have hone : ∀ x, c x 1 = 0 := fun x => by
    have h := hmul x 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  let φ : G →* Multiplicative (A →+ ZMod n) :=
    { toFun := fun g => Multiplicative.ofAdd
        (AddMonoidHom.mk' (fun x : A => c (x : X) g) fun x y => by
          rw [AddSubgroup.coe_add]
          exact hadd _ _ g)
      map_one' := by
        apply Multiplicative.toAdd.injective
        refine AddMonoidHom.ext fun x => ?_
        exact hone _
      map_mul' := fun g h => by
        apply Multiplicative.toAdd.injective
        refine AddMonoidHom.ext fun x => ?_
        exact hmul _ g h }
  have hker : φ.ker = N := by
    ext g
    rw [MonoidHom.mem_ker, hN]
    constructor
    · intro h x hx
      exact congrArg (fun f : Multiplicative (A →+ ZMod n) => Multiplicative.toAdd f ⟨x, hx⟩) h
    · intro h
      apply Multiplicative.toAdd.injective
      refine AddMonoidHom.ext fun x => ?_
      exact h x x.2
  rw [← hker]
  calc Nat.card (G ⧸ φ.ker) ≤ Nat.card (Multiplicative (A →+ ZMod n)) :=
        Nat.card_le_card_of_injective _ (QuotientGroup.kerLift_injective φ)
    _ = Nat.card (A →+ ZMod n) := rfl
    _ ≤ Nat.card A := card_addMonoidHom_zmod_le

end PerfectPairing

end Langlands.ProfiniteCohomology

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory

universe u

abbrev zmodULiftModule (n : ℕ) : Module (ULift.{u} ℤ) (ULift.{u} (ZMod n)) :=
  (zmodRep.{u} PUnit.{u + 1} n).hV2


variable {G : Type u} [Group G] {n : ℕ}

section Basic

variable {D M : Rep.{u} (ULift.{u} ℤ) G}

theorem nsmul_dualRep_eq_zero (hD : ∀ d : D, n • d = 0) (f : dualRep D M) : n • f = 0 := by
  let f' : M →ₗ[ULift.{u} ℤ] D := f
  change n • f' = 0
  refine LinearMap.ext fun m => ?_
  rw [LinearMap.smul_apply, hD, LinearMap.zero_apply]

theorem finite_of_nonempty_addEquiv [NeZero n] (hD : Nonempty (D ≃+ ZMod n)) : Finite D := by
  obtain ⟨e⟩ := hD
  exact Finite.of_equiv _ e.symm.toEquiv

instance finite_dualRep [Finite D] [Finite M] : Finite (dualRep D M) :=
  Finite.of_injective (fun f : M →ₗ[ULift.{u} ℤ] D => (f : M → D)) DFunLike.coe_injective

theorem card_dualRep_le [NeZero n] (hD : Nonempty (D ≃+ ZMod n)) [Finite M] :
    Nat.card (dualRep D M) ≤ Nat.card M := by
  obtain ⟨e⟩ := hD
  let F : (M →ₗ[ULift.{u} ℤ] D) → (M →+ ZMod n) := fun f => e.toAddMonoidHom.comp f.toAddMonoidHom
  have hF : Function.Injective F := fun f f' h => LinearMap.ext fun m =>
    e.injective (DFunLike.congr_fun h m)
  exact (Nat.card_le_card_of_injective F hF).trans card_addMonoidHom_zmod_le

theorem exists_dualRep_apply_ne_zero [NeZero n] (hD : Nonempty (D ≃+ ZMod n))
    (hM : ∀ m : M, n • m = 0) {m : M} (hm : m ≠ 0) :
    ∃ f : M →ₗ[ULift.{u} ℤ] D, f m ≠ 0 := by
  obtain ⟨e⟩ := hD
  obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hM hm
  refine ⟨(uliftIntLinearEquivAddHom M D).symm (e.symm.toAddMonoidHom.comp χ), fun h => hχ ?_⟩
  rw [uliftIntLinearEquivAddHom_symm_apply, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.map_eq_zero_iff] at h
  exact h

theorem bijective_toDualDual [NeZero n] (hD : Nonempty (D ≃+ ZMod n)) [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Bijective (toDualDual D M).hom := by
  have : Finite D := finite_of_nonempty_addEquiv hD
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (dualRep D (dualRep D M)) := finite_dualRep
  refine Function.Injective.bijective_of_nat_card_le ?_
    ((card_dualRep_le hD).trans (card_dualRep_le hD))
  rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra hne
  obtain ⟨f, hf⟩ := exists_dualRep_apply_ne_zero hD hM hne
  exact hf (DFunLike.congr_fun hm f)

end Basic

section EvalAt

variable {k : Type u} [CommRing k]

private theorem dualMap_zero (D : Rep.{u} k G) {A B : Rep.{u} k G} : dualMap D (0 : A ⟶ B) = 0 := by
  ext f a
  change f ((0 : A ⟶ B).hom a) = 0
  rw [Rep.zero_hom]
  exact map_zero f

def dualEvalAt (D X : Rep.{u} k G) (x : X) (hx : ∀ g : G, X.ρ g x = x) : dualRep D X ⟶ D :=
  Rep.ofHom ⟨{ toFun := fun ν => (ν : X →ₗ[k] D) x
               map_add' := fun _ _ => rfl
               map_smul' := fun _ _ => rfl }, fun σ => LinearMap.ext fun ν => by
    change D.ρ σ ((ν : X →ₗ[k] D) (X.ρ σ⁻¹ x)) = D.ρ σ ((ν : X →ₗ[k] D) x)
    rw [hx]⟩

theorem tensorHom_dualEvalAt (D X : Rep.{u} k G) (x : X) (hx : ∀ g : G, X.ρ g x = x)
    (μ : X ⊗ D ⟶ D) (h : ∀ (a : X) (ν : X →ₗ[k] D), μ.hom (a ⊗ₜ[k] ν x : (X ⊗ D : Rep k G)) = ν a) :
    (𝟙 X ⊗ₘ dualEvalAt D X x hx) ≫ μ = evalPairing D X := by
  ext y
  induction y using TensorProduct.inductionOn with
  | tmul a ν =>
    change μ.hom (a ⊗ₜ[k] (ν : X →ₗ[k] D) x : (X ⊗ D : Rep k G)) = (ν : X →ₗ[k] D) a
    exact h a ν
  | add y z hy hz => simp only [map_add, hy, hz]

end EvalAt

section Exact

attribute [local instance 3000] Submodule.Quotient.module

variable (D : Rep.{u} (ULift.{u} ℤ) G)

abbrev dualShortComplex (S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)) :
    ShortComplex (Rep.{u} (ULift.{u} ℤ) G) :=
  ShortComplex.mk (dualMap D S.g) (dualMap D S.f) (by
    rw [← dualMap_comp, S.zero, dualMap_zero])

variable {D}

theorem dualShortComplex_injective_f {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)}
    (hS : S.ShortExact) : Function.Injective (dualShortComplex D S).f.hom := by
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  intro f₁ f₂ h
  refine LinearMap.ext fun c => ?_
  obtain ⟨b, rfl⟩ := hg c
  exact LinearMap.congr_fun h b

theorem dualShortComplex_exact {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)}
    (hS : S.ShortExact) : (dualShortComplex D S).Exact := by
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex : ∀ b : S.X₂, S.g.hom b = 0 → ∃ a : S.X₁, S.f.hom a = b := by
    have := (ShortComplex.exact_map_iff_of_faithful _
      (forget₂ (Rep.{u} (ULift.{u} ℤ) G) (ModuleCat.{u} (ULift.{u} ℤ)))).2 hS.exact
    exact (ShortComplex.moduleCat_exact_iff _).1 this
  rw [← ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (Rep.{u} (ULift.{u} ℤ) G) (ModuleCat.{u} (ULift.{u} ℤ))),
    ShortComplex.moduleCat_exact_iff]
  intro φ₀ hφ₀
  let φ : S.X₂ →ₗ[ULift.{u} ℤ] D := φ₀
  have hφ : ∀ a : S.X₁, φ (S.f.hom a) = 0 := fun a => LinearMap.congr_fun hφ₀ a
  let g : S.X₂ →ₗ[ULift.{u} ℤ] S.X₃ := S.g.hom.toLinearMap
  have hker : LinearMap.ker g ≤ LinearMap.ker φ := by
    intro b hb
    obtain ⟨a, rfl⟩ := hex b hb
    exact hφ a
  let ψ : S.X₃ →ₗ[ULift.{u} ℤ] D :=
    ((LinearMap.ker g).liftQ φ hker).comp (g.quotKerEquivOfSurjective hg).symm.toLinearMap
  refine ⟨ψ, LinearMap.ext fun b => ?_⟩
  change ψ (g b) = φ b
  simp only [ψ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

theorem dualShortComplex_surjective_g [NeZero n] (hD : Nonempty (D ≃+ ZMod n))
    {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} (hS : S.ShortExact)
    (hn : ∀ x : S.X₂, n • x = 0) : Function.Surjective (dualShortComplex D S).g.hom := by
  obtain ⟨e⟩ := hD
  have hf : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  intro ψ₀
  let ψ : S.X₁ →ₗ[ULift.{u} ℤ] D := ψ₀
  let h : S.X₁ →+ S.X₂ := S.f.hom.toLinearMap.toAddMonoidHom
  obtain ⟨Φ, hΦ⟩ := zmod_exists_comp_eq_of_ker_le hn h (e.toAddMonoidHom.comp ψ.toAddMonoidHom)
    (fun a ha => by
      rw [AddMonoidHom.mem_ker] at ha ⊢
      have : a = 0 := hf (by rw [map_zero]; exact ha)
      rw [this, map_zero])
  refine ⟨(uliftIntLinearEquivAddHom S.X₂ D).symm (e.symm.toAddMonoidHom.comp Φ),
    LinearMap.ext fun a => ?_⟩
  change e.symm (Φ (S.f.hom a)) = ψ a
  have := DFunLike.congr_fun hΦ a
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom] at this
  change e.symm (Φ (h a)) = ψ a
  rw [this, AddEquiv.symm_apply_apply]
  rfl

theorem dualShortComplex_shortExact [NeZero n] (hD : Nonempty (D ≃+ ZMod n))
    {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} (hS : S.ShortExact)
    (hn : ∀ x : S.X₂, n • x = 0) : (dualShortComplex D S).ShortExact where
  exact := dualShortComplex_exact hS
  mono_f := (Rep.mono_iff_injective _).2 (dualShortComplex_injective_f hS)
  epi_g := (Rep.epi_iff_surjective _).2 (dualShortComplex_surjective_g hD hS hn)

end Exact

section ZModDual

variable (n) (D : Rep.{u} (ULift.{u} ℤ) G) (hD : ∀ d : D, n • d = 0)

def zmodDualHom : dualRep D (zmodRep.{u} G n) ⟶ D :=
  dualEvalAt D (zmodRep.{u} G n) (ULift.up 1) fun _ => rfl

theorem zmodDualHom_hom_apply (ν : dualRep D (zmodRep.{u} G n)) :
    (zmodDualHom n D).hom ν = ν (ULift.up 1 : zmodRep.{u} G n) :=
  rfl

theorem dualRep_zmodRep_apply (ν : dualRep D (zmodRep.{u} G n)) (a : ZMod n) :
    ν (ULift.up a : zmodRep.{u} G n) = (ZMod.cast a : ℤ) • ν (ULift.up 1 : zmodRep.{u} G n) := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast a]
  rw [zmodRep_eq_zsmul G n, map_zsmul]

include hD in
theorem bijective_zmodDualHom : Function.Bijective (zmodDualHom n D).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ν hν
    rw [zmodDualHom_hom_apply] at hν
    refine DFunLike.ext _ _ fun a => ?_
    obtain ⟨a⟩ := a
    rw [dualRep_zmodRep_apply, hν, zsmul_zero]
    rfl
  · intro d
    refine ⟨(uliftIntLinearEquivAddHom (zmodRep.{u} G n) D).symm
      ((zmodMulAddHom n hD).flip d |>.comp
        ((AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n).toAddMonoidHom.comp
          (AddMonoidHom.id (zmodRep.{u} G n)))), ?_⟩
    change (zmodMulAddHom n hD) 1 d = d
    rw [zmodMulAddHom_apply]
    rw [zsmul_eq_zsmul_of_intCast_eq hD (b := 1) (by simp) d, one_zsmul]

def zmodDualIso : dualRep D (zmodRep.{u} G n) ≅ D :=
  repIsoOfBijective (zmodDualHom n D) (bijective_zmodDualHom n D hD)

theorem tensorHom_zmodDualIso_zmodMulPairing :
    (𝟙 (zmodRep.{u} G n) ⊗ₘ (zmodDualIso n D hD).hom) ≫ zmodMulPairing n D hD =
      evalPairing D (zmodRep.{u} G n) :=
  tensorHom_dualEvalAt D (zmodRep.{u} G n) (ULift.up 1) (fun _ => rfl) _ fun a ν => by
    obtain ⟨a⟩ := a
    change zmodMulAddHom n hD a (ν (ULift.up 1)) = ν (ULift.up a)
    rw [zmodMulAddHom_apply]
    exact (dualRep_zmodRep_apply n D ν a).symm

end ZModDual

end Langlands.ProfiniteCohomology
