import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Lifting right resolutions into complexes of injective objects

Let `C` be an abelian category and `ε : A[0] ⟶ K` a right resolution of an object `A`: a
quasi-isomorphism from `A` placed in degree zero to a cochain complex `K` indexed by `ℕ`.
The terms of `K` are arbitrary. This module constructs the comparison of Cartan–Eilenberg,
Chapter V, Proposition 1.1a, for such resolutions.

* `lift ε f η : K ⟶ L` is a cochain map over `f : A ⟶ B` into a complex `L` of injective
  objects with an augmentation `η : B[0] ⟶ L`, and `comp_lift` says
  `ε ≫ lift ε f η = (single₀ C).map f ≫ η`. For an injective resolution `J` of `B`,
  take `η := J.ι`.
* `homotopyOfComp ε φ ψ h` is a homotopy between two cochain maps `φ ψ : K ⟶ L` into a
  complex of injective objects such that `ε ≫ φ = ε ≫ ψ`. The target `L` needs no
  augmentation and need not be exact.

The construction copies Mathlib's `InjectiveResolution.desc` and
`InjectiveResolution.descHomotopyZero`. These use only the exactness of the source
resolution and the injectivity of the target terms. Here the source is any right
resolution instead of an injective one. Exactness of `K` comes from `ε` being a
quasi-isomorphism: `K` is exact in positive degrees (`exactAt_succ`), and `A` is the
kernel of `K⁰ ⟶ K¹` (`isLimitKernelFork`).
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

noncomputable section

namespace Langlands.Cohomology.AcyclicResolution

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A : C} {K : CochainComplex C ℕ} (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]

include ε in
/-- The target of a right resolution is exact in every positive degree. -/
lemma exactAt_succ (n : ℕ) : K.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt ε (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

include ε in
/-- The short complex `Kⁿ ⟶ Kⁿ⁺¹ ⟶ Kⁿ⁺²` of a right resolution is exact. -/
lemma exact_succ (n : ℕ) :
    (ShortComplex.mk _ _ (K.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (exactAt_succ ε n)

omit [QuasiIso ε] in
set_option backward.isDefEq.respectTransparency false in
/-- The augmentation composed with the first differential is zero. -/
@[reassoc]
lemma f_zero_comp_d : ε.f 0 ≫ K.d 0 1 = 0 := by
  rw [ε.comm]
  simp

/-- The kernel fork `A ⟶ K⁰ ⟶ K¹`. -/
abbrev kernelFork : KernelFork (K.d 0 1) :=
  KernelFork.ofι _ (f_zero_comp_d ε)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `A` is the kernel of `K⁰ ⟶ K¹`. -/
def isLimitKernelFork : IsLimit (kernelFork ε) := by
  refine IsLimit.ofIsoLimit (K.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt ε 0 ≪≫ K.isoHomologyπ₀.symm) ?_
  rw [← cancel_epi (singleObjHomologySelfIso (ComplexShape.up ℕ) _ _).hom,
    ← cancel_epi (isoHomologyπ₀ _).hom,
    ← cancel_epi (singleObjCyclesSelfIso (ComplexShape.up ℕ) _ _).inv]
  simp

/-- The short complex `A ⟶ K⁰ ⟶ K¹` is exact. -/
lemma exact₀ : (ShortComplex.mk _ _ (f_zero_comp_d ε)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitKernelFork ε)

/-- The augmentation `A ⟶ K⁰` is a monomorphism. -/
instance mono_f_zero : Mono (ε.f 0) :=
  mono_of_isLimit_fork (isLimitKernelFork ε)

variable {L : CochainComplex C ℕ} [∀ n, Injective (L.X n)]
  {B : C} (f : A ⟶ B) (η : (CochainComplex.single₀ C).obj B ⟶ L)

/-- Degree-zero component of the lift. -/
def liftFZero : K.X 0 ⟶ L.X 0 :=
  Injective.factorThru (((CochainComplex.single₀ C).map f ≫ η).f 0) (ε.f 0)

@[reassoc (attr := simp)]
lemma f_zero_comp_liftFZero :
    ε.f 0 ≫ liftFZero ε f η = ((CochainComplex.single₀ C).map f ≫ η).f 0 :=
  Injective.comp_factorThru _ _

/-- Degree-one component of the lift. -/
def liftFOne : K.X 1 ⟶ L.X 1 :=
  (exact₀ ε).descToInjective (liftFZero ε f η ≫ L.d 0 1) (by
    change ε.f 0 ≫ liftFZero ε f η ≫ L.d 0 1 = 0
    rw [f_zero_comp_liftFZero_assoc, HomologicalComplex.comp_f, Category.assoc,
      f_zero_comp_d η, Limits.comp_zero])

lemma d_comp_liftFOne :
    K.d 0 1 ≫ liftFOne ε f η = liftFZero ε f η ≫ L.d 0 1 :=
  (exact₀ ε).comp_descToInjective _ _

variable (L) in
/-- Inductive step of the lift. -/
def liftFSucc (n : ℕ) (g : K.X n ⟶ L.X n) (g' : K.X (n + 1) ⟶ L.X (n + 1))
    (w : K.d n (n + 1) ≫ g' = g ≫ L.d n (n + 1)) :
    Σ' g'' : K.X (n + 2) ⟶ L.X (n + 2),
      K.d (n + 1) (n + 2) ≫ g'' = g' ≫ L.d (n + 1) (n + 2) :=
  ⟨(exact_succ ε n).descToInjective
    (g' ≫ L.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
      (exact_succ ε n).comp_descToInjective _ _⟩

/-- A cochain map from the right resolution `K` of `A` to a complex `L` of injective
objects with augmentation `η` from `B`, lying over `f : A ⟶ B`. -/
def lift : K ⟶ L :=
  CochainComplex.mkHom _ _ (liftFZero ε f η) (liftFOne ε f η) (d_comp_liftFOne ε f η).symm
    fun n ⟨g, g', w⟩ =>
      ⟨(liftFSucc ε L n g g' w.symm).1, (liftFSucc ε L n g g' w.symm).2.symm⟩

/-- The lift lies over `f`. -/
lemma comp_lift : ε ≫ lift ε f η = (CochainComplex.single₀ C).map f ≫ η := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  cases n with
  | zero =>
    change ε.f 0 ≫ (lift ε f η).f 0 = ((CochainComplex.single₀ C).map f ≫ η).f 0
    rw [lift, CochainComplex.mkHom_f_0]
    exact f_zero_comp_liftFZero ε f η
  | succ n =>
    exact (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_src _ _

variable {ε}

/-- Auxiliary degree-zero homotopy component. -/
def homotopyZeroZero (χ : K ⟶ L) (comm : ε ≫ χ = 0) :
    K.X 1 ⟶ L.X 0 :=
  (exact₀ ε).descToInjective (χ.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
lemma comp_homotopyZeroZero (χ : K ⟶ L) (comm : ε ≫ χ = 0) :
    K.d 0 1 ≫ homotopyZeroZero χ comm = χ.f 0 :=
  (exact₀ ε).comp_descToInjective _ _

/-- Auxiliary degree-one homotopy component. -/
def homotopyZeroOne (χ : K ⟶ L) (comm : ε ≫ χ = 0) :
    K.X 2 ⟶ L.X 1 :=
  (exact_succ ε 0).descToInjective (χ.f 1 - homotopyZeroZero χ comm ≫ L.d 0 1)
    (by rw [Preadditive.comp_sub, comp_homotopyZeroZero_assoc χ comm,
          HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]
lemma comp_homotopyZeroOne (χ : K ⟶ L) (comm : ε ≫ χ = 0) :
    K.d 1 2 ≫ homotopyZeroOne χ comm =
      χ.f 1 - homotopyZeroZero χ comm ≫ L.d 0 1 :=
  (exact_succ ε 0).comp_descToInjective _ _

variable (ε) in
/-- Inductive homotopy component. -/
def homotopyZeroSucc (χ : K ⟶ L) (n : ℕ) (g : K.X (n + 1) ⟶ L.X n)
    (g' : K.X (n + 2) ⟶ L.X (n + 1))
    (w : χ.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ L.d n (n + 1)) :
    K.X (n + 3) ⟶ L.X (n + 2) :=
  (exact_succ ε (n + 1)).descToInjective (χ.f (n + 2) - g' ≫ L.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
        Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, Limits.comp_zero,
        add_zero, sub_self])

variable (ε) in
@[reassoc (attr := simp)]
lemma comp_homotopyZeroSucc (χ : K ⟶ L) (n : ℕ)
    (g : K.X (n + 1) ⟶ L.X n) (g' : K.X (n + 2) ⟶ L.X (n + 1))
    (w : χ.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ L.d n (n + 1)) :
    K.d (n + 2) (n + 3) ≫ homotopyZeroSucc ε χ n g g' w =
      χ.f (n + 2) - g' ≫ L.d _ _ :=
  (exact_succ ε (n + 1)).comp_descToInjective _ _

/-- A cochain map from a right resolution into a complex of injective objects that is
killed by the augmentation is null-homotopic. -/
def homotopyZero (χ : K ⟶ L) (comm : ε ≫ χ = 0) : Homotopy χ 0 :=
  Homotopy.mkCoinductive _ (homotopyZeroZero χ comm) (by simp)
    (homotopyZeroOne χ comm) (by simp) (fun n ⟨g, g', w⟩ =>
    ⟨homotopyZeroSucc ε χ n g g' (by simp only [w, add_comm]), by simp⟩)

variable (ε) in
/-- Two cochain maps from a right resolution into a complex of injective objects that
agree after the augmentation are homotopic. -/
def homotopyOfComp (φ ψ : K ⟶ L) (h : ε ≫ φ = ε ≫ ψ) : Homotopy φ ψ :=
  Homotopy.equivSubZero.invFun
    (homotopyZero (φ - ψ) (by rw [Preadditive.comp_sub, h, sub_self]))

end Langlands.Cohomology.AcyclicResolution

end
