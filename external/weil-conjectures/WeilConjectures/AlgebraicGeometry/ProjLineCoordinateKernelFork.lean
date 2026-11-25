/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! The kernel of the coordinate quotient on the polynomial projective line.

The explicit signed coordinate lift is a kernel on each of the two standard charts.
Restriction preserves kernels, and stalkwise bijectivity identifies it with a global kernel.
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem mapped_biprod_hom_ext
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {B : C} [HasBinaryBiproduct B B]
    {W : D} {a b : W ⟶ F.obj (B ⊞ B)}
    (h₀ : a ≫ F.map biprod.fst = b ≫ F.map biprod.fst)
    (h₁ : a ≫ F.map biprod.snd = b ≫ F.map biprod.snd) : a = b := by
  have ht : F.map biprod.fst ≫ F.map biprod.inl +
      F.map biprod.snd ≫ F.map biprod.inr = 𝟙 (F.obj (B ⊞ B)) := by
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
  calc
    a = a ≫ (F.map biprod.fst ≫ F.map biprod.inl +
        F.map biprod.snd ≫ F.map biprod.inr) := by rw [ht, Category.comp_id]
    _ = b ≫ (F.map biprod.fst ≫ F.map biprod.inl +
        F.map biprod.snd ≫ F.map biprod.inr) := by
      simp only [Preadditive.comp_add, ← Category.assoc, h₀, h₁]
    _ = b := by rw [ht, Category.comp_id]

private noncomputable def kernel_of_invertible_component
    {C : Type*} [Category C] [Preadditive C]
    {A E B T : C} (f : A ⟶ E) (g : E ⟶ T) (p q : E ⟶ B)
    (c d : B ⟶ T) (h : f ≫ g = 0) (hg : g = p ≫ c + q ≫ d)
    (hext : ∀ {W : C} (a b : W ⟶ E), a ≫ p = b ≫ p → a ≫ q = b ≫ q → a = b)
    [IsIso (f ≫ q)] [IsIso c] : IsLimit (KernelFork.ofι f h) := by
  let lift {W : C} (a : W ⟶ E) := a ≫ q ≫ inv (f ≫ q)
  have hq {W : C} (a : W ⟶ E) : lift a ≫ f ≫ q = a ≫ q := by
    simp [lift]
  have cancel {W : C} (a b : W ⟶ E) (ha : a ≫ g = 0) (hb : b ≫ g = 0)
      (hab : a ≫ q = b ≫ q) : a = b := by
    apply hext a b _ hab
    apply (cancel_mono c).mp
    have hsum : a ≫ p ≫ c + a ≫ q ≫ d = b ≫ p ≫ c + b ≫ q ≫ d := by
      simpa only [hg, Preadditive.comp_add, Category.assoc] using ha.trans hb.symm
    simp only [← Category.assoc, hab] at hsum
    exact add_right_cancel hsum
  refine KernelFork.IsLimit.ofι f h (fun a _ ↦ lift a) (fun a ha ↦ ?_) ?_
  · apply cancel _ _ _ ha (by simpa only [Category.assoc] using hq a)
    simp [Category.assoc, h]
  · intro W a ha m hm
    change m = a ≫ q ≫ inv (f ≫ q)
    rw [← hm]
    simp only [Category.assoc, ← Category.assoc f q, IsIso.hom_inv_id, Category.comp_id]

private theorem mapped_signed_lift_component_isos
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {A B T : C} [HasBinaryBiproduct B B]
    (a b : A ⟶ B) (c d : B ⟶ T)
    (hi : (IsIso (F.map b) ∧ IsIso (F.map c)) ∨
      (IsIso (F.map a) ∧ IsIso (F.map d))) :
    (IsIso (F.map (biprod.lift (-a) b) ≫ F.map biprod.snd) ∧ IsIso (F.map c)) ∨
      (IsIso (F.map (biprod.lift (-a) b) ≫ F.map biprod.fst) ∧ IsIso (F.map d)) := by
  rcases hi with ⟨hb, hc⟩ | ⟨ha, hd⟩
  · left
    refine ⟨?_, hc⟩
    rw [← F.map_comp, biprod.lift_snd]
    exact hb
  · right
    refine ⟨?_, hd⟩
    rw [← F.map_comp, biprod.lift_fst, F.map_neg]
    exact inferInstanceAs (IsIso ((-asIso (F.map a)).hom))

private theorem mapped_kernel_of_component_isos
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {A B T : C} [HasBinaryBiproduct B B]
    (f : A ⟶ B ⊞ B) (c d : B ⟶ T) (h : f ≫ biprod.desc c d = 0)
    (hi : (IsIso (F.map f ≫ F.map biprod.snd) ∧ IsIso (F.map c)) ∨
      (IsIso (F.map f ≫ F.map biprod.fst) ∧ IsIso (F.map d))) :
    Nonempty (IsLimit (KernelFork.ofι (F.map f)
      (by rw [← F.map_comp, h, F.map_zero]))) := by
  rcases hi with ⟨hq, hc⟩ | ⟨hq, hd⟩
  · refine ⟨?_⟩
    apply kernel_of_invertible_component (F.map f) (F.map (biprod.desc c d))
      (F.map biprod.fst) (F.map biprod.snd) (F.map c) (F.map d)
      (by rw [← F.map_comp, h, F.map_zero])
      (by simp only [biprod.desc_eq, F.map_add, F.map_comp])
    intro W a b h₀ h₁
    exact mapped_biprod_hom_ext F h₀ h₁
  · refine ⟨?_⟩
    apply kernel_of_invertible_component (F.map f) (F.map (biprod.desc c d))
      (F.map biprod.snd) (F.map biprod.fst) (F.map d) (F.map c)
      (by rw [← F.map_comp, h, F.map_zero])
      (by
        simp only [biprod.desc_eq, F.map_add, F.map_comp]
        exact add_comm _ _)
    intro W a b h₀ h₁
    exact mapped_biprod_hom_ext F h₁ h₀

private theorem isIso_map_fork_lift
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]
    {A B T : C} (f : A ⟶ B) (g : B ⟶ T) (h : f ≫ g = 0)
    (s : KernelFork g) (hs : IsLimit s) [PreservesLimit (parallelPair g 0) F]
    (hf : IsLimit (KernelFork.ofι (F.map f) (by rw [← F.map_comp, h, F.map_zero]))) :
    IsIso (F.map (hs.lift (KernelFork.ofι f h))) := by
  let hs' := s.mapIsLimit hs F
  let t : KernelFork (F.map g) :=
    KernelFork.ofι (F.map f) (by rw [← F.map_comp, h, F.map_zero])
  have he : F.map (hs.lift (KernelFork.ofι f h)) = hs'.lift t := by
    apply Fork.IsLimit.hom_ext hs'
    calc
      F.map (hs.lift (KernelFork.ofι f h)) ≫ F.map s.ι = F.map f := by
        rw [← F.map_comp, Fork.IsLimit.lift_ι]
        rfl
      _ = _ := (Fork.IsLimit.lift_ι (t := t) hs').symm
  rw [he]
  exact hs'.nonempty_isLimit_iff_isIso_lift.mp ⟨hf⟩

private theorem coordinate_commutes
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (d t : ℤ) (hd : d + (1 : ℕ) = t) :
    (G ◁ Proj.twistMul d
      (MvPolynomial.X_mem_homogeneousSubmodule_one k (1 : Fin 2))) ≫
      eqToHom (congrArg (fun n ↦
        G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) hd) ≫
      (G ◁ Proj.twistMul t
        (MvPolynomial.X_mem_homogeneousSubmodule_one k (0 : Fin 2))) =
    (G ◁ Proj.twistMul d
      (MvPolynomial.X_mem_homogeneousSubmodule_one k (0 : Fin 2))) ≫
      eqToHom (congrArg (fun n ↦
        G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) hd) ≫
      (G ◁ Proj.twistMul t
        (MvPolynomial.X_mem_homogeneousSubmodule_one k (1 : Fin 2))) := by
  subst t
  simp only [eqToHom_refl, Category.id_comp]
  rw [← whiskerLeft_comp, ← whiskerLeft_comp]
  rw [Proj.twistMul_comp_twistMul]

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate morphism admits a kernel fork with source G(z-1).

Source: the two-chart calculation in
`dag/nodes/sec-picard-framework/lem-sc-p1-proj-coordinate-short-exact.json`,
proof steps 1 and 2, and Stacks Project, Tag 01MN for the twisting sheaves.
(blueprint: lem-sc-p1-proj-coordinate-kernel-fork).

Proof: Write μ_i(d) for G whiskered with multiplication by x_i from O(d)
to O(d+1). Define f by its two components -μ_1(z-1) and μ_0(z-1),
transporting (z-1)+1 to z. Commutativity of coordinate multiplication implies
f followed by (μ_0(z), μ_1(z)) is zero. On D+(x_0), multiplication by x_0
is invertible for every twist, and remains invertible after tensoring with G.
For a morphism (a,b) killed by the quotient map, set t=μ_0(z-1)^{-1} b.
The equation μ_0(z)a+μ_1(z)b=0 and commutativity give a=-μ_1(z-1)t;
t is unique because its second component is b. On D+(x_1), instead set
t=-μ_1(z-1)^{-1} a; the same equation gives b=μ_0(z-1)t, uniquely.
These local factorizations agree on overlaps by uniqueness. The sheaf gluing
property therefore gives a unique global factorization for every kernel fork,
which is exactly the universal property IsLimit. No arbitrary witness is
used to define f: it is the displayed binary biproduct lift. Tensoring needs
no flatness because the local inverses still exist. The calculation covers
the zero module, modules with torsion, characteristic two, and every integer z.
-/
theorem exists_proj_coordinate_kernel_fork
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules) (z : ℤ) :
    ∃ (f : G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (z - 1) ⟶
        (G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z) ⊞
        (G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z))
      (h : f ≫ biprod.desc
        (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (0 : Fin 2)))
        (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (1 : Fin 2))) = 0),
      Nonempty (IsLimit (KernelFork.ofι f h)) := by
  let μ (i : Fin 2) (d : ℤ) :=
    G ◁ Proj.twistMul d (MvPolynomial.X_mem_homogeneousSubmodule_one k i)
  have hz : z - 1 + (1 : ℕ) = z := by omega
  let e := eqToIso (congrArg (fun d ↦
    G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d) hz)
  let a (i : Fin 2) := μ i (z - 1) ≫ e.hom
  let f := biprod.lift (-a 1) (a 0)
  let g := biprod.desc (μ 0 z) (μ 1 z)
  have hc : a 1 ≫ μ 0 z = a 0 ≫ μ 1 z := by
    exact coordinate_commutes k G (z - 1) z hz
  have h : f ≫ g = 0 := by
    simp [f, g, Preadditive.neg_comp, hc]
  refine ⟨f, h, ?_⟩
  -- Use an arbitrary existing limit cone, keeping its point abstract rather than unfolding
  -- the concrete categorical kernel. Its universal property determines it up to unique iso.
  obtain ⟨S⟩ := (inferInstance : HasKernel g).exists_limit
  let l := S.isLimit.lift (KernelFork.ofι f h)
  have hlocal (i : Fin 2) : IsIso ((Scheme.Modules.restrictFunctor
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X i)).ι).map l) := by
    let U := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.X i)
    let F := Scheme.Modules.restrictFunctor U.ι
    have hμ (d : ℤ) : IsIso (F.map (μ i d)) := by
      rw [NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι)]
      let P := Scheme.Modules.pullback U.ι
      have ht : IsIso (P.map (Proj.twistMul d
          (MvPolynomial.X_mem_homogeneousSubmodule_one k i))) := by
        rw [← NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι)]
        infer_instance
      rw [Functor.Monoidal.map_whiskerLeft]
      infer_instance
    have ha : IsIso (F.map (a i)) := by
      dsimp only [a]
      rw [F.map_comp]
      infer_instance
    apply isIso_map_fork_lift F f g h S.cone S.isLimit
    apply Nonempty.some
    apply mapped_kernel_of_component_isos F f (μ 0 z) (μ 1 z) h
    apply mapped_signed_lift_component_isos F (a 1) (a 0) (μ 0 z) (μ 1 z)
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with hi | hi
    · left
      exact ⟨Eq.mp (congrArg (fun j ↦ IsIso (F.map (a j))) hi) ha,
        Eq.mp (congrArg (fun j ↦ IsIso (F.map (μ j z))) hi) (hμ z)⟩
    · right
      exact ⟨Eq.mp (congrArg (fun j ↦ IsIso (F.map (a j))) hi) ha,
        Eq.mp (congrArg (fun j ↦ IsIso (F.map (μ j z))) hi) (hμ z)⟩
  have hcover : (⨆ i : Fin 2, Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i)) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top
    rw [MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule]
  have hl : IsIso l := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
      (F := ⟨(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (z - 1)).presheaf, (G ⊗ Proj.twist
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (z - 1)).isSheaf⟩)
      (G := ⟨S.cone.pt.presheaf, S.cone.pt.isSheaf⟩) ⟨l.mapPresheaf⟩ V
      (fun x _ ↦ by
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
          (hcover.ge (Set.mem_univ x))
        have := hlocal i
        exact Scheme.Modules.bijective_stalk_of_isIso_restrict l x hi)
  exact S.isLimit.nonempty_isLimit_iff_isIso_lift.mpr hl

end AlgebraicGeometry
