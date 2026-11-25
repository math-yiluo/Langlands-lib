/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedAlgebraData
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitEpi

/-! # Exactness and degree projections for a graded quotient

Source: Stacks Project, Tag 09MS, direct sum of coherent-equation-ses.
(blueprint: lem-sc-tensor-graded-degree-data).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section
attribute [local irreducible] tensorGradedAlgebraMap tensorGradedUnit
  commAlgebraSheafModule tensorPullback

private theorem tensorGradedUnit_epi {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (M : X.Modules) : Epi (tensorGradedUnit j M) := by
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction j)
  let adj' := Classical.choose (exists_tensorPullbackAdjunction j)
  have : Epi (adj.unit.app M) := closedImmersion_unit_epi j M
  unfold tensorGradedUnit
  rw [← adj.unit_leftAdjointUniq_hom_app adj' M]
  infer_instance

private def kernelCofan {C : Type u} [Category C] [Abelian C]
    [HasColimitsOfShape (Discrete ℕ) C] [HasExactColimitsOfShape (Discrete ℕ) C]
    (F G : ℕ → C) (f : ∀ d, F d ⟶ G d)
    (B Q : C) (b : ∀ d, F d ⟶ B) (c : ∀ d, G d ⟶ Q)
    (hb : IsColimit (Cofan.mk B b)) (hc : IsColimit (Cofan.mk Q c))
    (p : B ⟶ Q) (hp : ∀ d, b d ≫ p = f d ≫ c d) :
    IsColimit (Cofan.mk (kernel p) (fun d ↦
      kernel.lift p (kernel.ι (f d) ≫ b d) (by simp [Category.assoc, hp]))) := by
  let K := fun d ↦ kernel (f d)
  let α : Discrete.functor K ⟶ Discrete.functor F :=
    Discrete.natTrans (fun d ↦ kernel.ι (f d.as))
  let β : Discrete.functor F ⟶ Discrete.functor G := Discrete.natTrans (fun d ↦ f d.as)
  have w : α ≫ β = 0 := by ext d; exact kernel.condition _
  let S := ShortComplex.mk α β w
  have hK : IsLimit (KernelFork.ofι α w) := by
    apply evaluationJointlyReflectsLimits
    intro d
    exact (KernelFork.isLimitMapConeEquiv _ _).symm (kernelIsKernel (f d.as))
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel _ hK
  let v : (∐ K) ⟶ B := Sigma.desc (fun d ↦ kernel.ι (f d) ≫ b d)
  have hv (d : ℕ) : Sigma.ι K d ≫ v = kernel.ι (f d) ≫ b d := Sigma.ι_comp_desc _ _
  have (d : Discrete ℕ) : Mono (α.app d) := by
    change Mono (kernel.ι (f d.as))
    infer_instance
  have hm : Mono α := NatTrans.mono_of_mono_app α
  have hvmono : Mono v := colim.map_mono' α (coproductIsCoproduct K) hb v (fun d ↦ hv d.as)
  let S' := colim.mapShortComplex S (coproductIsCoproduct K)
    (Cofan.mk B b) (Cofan.mk Q c) v p (fun d ↦ hv d.as) (fun d ↦ hp d.as)
  have he : S'.Exact := colim.exact_mapShortComplex hS (coproductIsCoproduct K)
    hb hc v p (fun d ↦ hv d.as) (fun d ↦ hp d.as)
  have : Mono S'.f := hvmono
  let e := he.fIsKernel.conePointUniqueUpToIso (kernelIsKernel p)
  have heι : e.hom ≫ kernel.ι p = v :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  apply IsColimit.ofIsoColimit (coproductIsCoproduct K)
  refine Cofan.ext e ?_
  intro d
  apply (cancel_mono (kernel.ι p)).1
  change (Sigma.ι K d ≫ e.hom) ≫ kernel.ι p = _
  rw [Category.assoc, heι]
  exact (hv d).trans (kernel.lift_ι _ _ _).symm

/-- The canonical kernel sequence of a graded algebra quotient, with its degree maps.
The kernel object and its inclusion are fixed, rather than selected from existence.
Source: Stacks Project, Tag 09MS, direct sum of coherent-equation-ses.
(blueprint: lem-sc-tensor-graded-degree-data). -/
structure TensorGradedDegreeData {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) (A : TensorGradedAlgebraData j L) where
  shortExact : (ShortComplex.kernelSequence (tensorGradedAlgebraMap A.p)).ShortExact
  k : ∀ d : ℕ,
    kernel (tensorGradedUnit j (L.tensorPow d)) ⟶ kernel (tensorGradedAlgebraMap A.p)
  degree : ∀ d : ℕ,
    ShortComplex.kernelSequence (tensorGradedAlgebraMap A.p) ⟶
      ShortComplex.kernelSequence (tensorGradedUnit j (L.tensorPow d))
  q : ∀ d : ℕ, commAlgebraSheafModule X.sheaf A.C ⟶
    (pushforward j).obj ((tensorPullback j).obj (L.tensorPow d))
  degree_quotient : ∀ d : ℕ, (degree d).τ₃ = q d
  k_colimit : IsColimit (Cofan.mk (kernel (tensorGradedAlgebraMap A.p)) k)
  k_inclusion : ∀ d : ℕ, k d ≫ kernel.ι _ = kernel.ι _ ≫ A.b d
  c_projection : ∀ d : ℕ, A.c d ≫ q d = 𝟙 _
  k_projection : ∀ d : ℕ, k d ≫ (degree d).τ₁ = 𝟙 _
  k_orthogonal : ∀ a d : ℕ, a ≠ d → k a ≫ (degree d).τ₁ = 0

/-- Exact coproducts supply the kernel direct sum and all degree projections.
Source: Stacks Project, Tag 09MS, coherent-equation-ses and its direct sum;
Tag 04CJ (1), the closed-immersion module quotient.
Proof: the adjunction unit in each degree is an epimorphism for a closed immersion,
with kernel J L^d. Use the two coproduct universal properties of A to define the
projections r_d from B and q_d from C by identity in degree d and zero otherwise.
The quotient squares imply r_d;eta_d = p;q_d by testing on every b_a. Kernel
functoriality gives the short-complex morphisms degree_d. The square
ker(eta_d) -> L^d -> B, followed by p, is zero, and hence induces k_d into ker(p).
Sheaf coproducts of modules are exact: on stalks these are direct sums of modules,
where an element has finite support and degreewise lifting proves surjectivity.
Consequently p is epi and the sum of the degreewise kernel sequences is its
kernel sequence, proving shortExact and k_colimit. The identities and off-diagonal
zero composites follow by testing the coproduct inclusions and then cancelling
kernel inclusions. No multiplicative property or square-zero hypothesis is used.
(blueprint: lem-sc-tensor-graded-degree-data). -/
theorem tensorGradedDegreeData_exists {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) (A : TensorGradedAlgebraData j L) :
    Nonempty (TensorGradedDegreeData j L A) := by
  classical
  let F := fun d : ℕ ↦ L.tensorPow d
  let G := fun d : ℕ ↦ (pushforward j).obj ((tensorPullback j).obj (F d))
  let η := fun d : ℕ ↦ tensorGradedUnit j (F d)
  let p := tensorGradedAlgebraMap A.p
  let r : ∀ d : ℕ, commAlgebraSheafModule X.sheaf A.B ⟶ F d := fun d ↦
    A.b_colimit.desc (Cofan.mk (F d)
      (fun a ↦ if h : a = d then eqToHom (congrArg F h) else 0))
  let q : ∀ d : ℕ, commAlgebraSheafModule X.sheaf A.C ⟶ G d := fun d ↦
    A.c_colimit.desc (Cofan.mk (G d)
      (fun a ↦ if h : a = d then eqToHom (congrArg G h) else 0))
  have hr (a d : ℕ) : A.b a ≫ r d =
      if h : a = d then eqToHom (congrArg F h) else 0 :=
    A.b_colimit.fac _ (Discrete.mk a)
  have hq (a d : ℕ) : A.c a ≫ q d =
      if h : a = d then eqToHom (congrArg G h) else 0 :=
    A.c_colimit.fac _ (Discrete.mk a)
  have hw (d : ℕ) : p ≫ q d = r d ≫ η d := by
    apply A.b_colimit.hom_ext
    intro a
    change A.b a.as ≫ (p ≫ q d) = A.b a.as ≫ (r d ≫ η d)
    rw [← Category.assoc, A.b_quotient, Category.assoc, hq, ← Category.assoc, hr]
    by_cases h : a.as = d
    · subst d
      simp only [dite_true, eqToHom_refl]
      rfl
    · simp [h]
  let k : ∀ d : ℕ, kernel (η d) ⟶ kernel p := fun d ↦
    kernel.lift p (kernel.ι (η d) ≫ A.b d)
      (by
        change kernel.ι (η d) ≫ (A.b d ≫ tensorGradedAlgebraMap A.p) = 0
        rw [A.b_quotient, ← Category.assoc]
        exact (kernel.condition (η d) ▸ zero_comp))
  let degree : ∀ d : ℕ, ShortComplex.kernelSequence p ⟶
      ShortComplex.kernelSequence (η d) := fun d ↦
    { τ₁ := kernel.map p (η d) (r d) (q d) (hw d)
      τ₂ := r d
      τ₃ := q d }
  have hk (a d : ℕ) : k a ≫ (degree d).τ₁ ≫ kernel.ι (η d) =
      kernel.ι (η a) ≫ (A.b a ≫ r d) := by
    dsimp only [degree]
    rw [kernel.lift_ι, ← Category.assoc]
    dsimp only [k]
    rw [kernel.lift_ι, Category.assoc]
  let β : Discrete.functor F ⟶ Discrete.functor G :=
    Discrete.natTrans (fun a ↦ η a.as)
  have (d : Discrete ℕ) : Epi (β.app d) := tensorGradedUnit_epi j (F d.as)
  have hp : Epi p := colim.map_epi' β
    (Cofan.mk _ A.b) A.c_colimit p (fun d ↦ A.b_quotient d.as)
  let _ : IsGrothendieckAbelian.{u} X.Modules :=
    isGrothendieckAbelian X
  refine ⟨{
    shortExact := { exact := ShortComplex.kernelSequence_exact p, epi_g := hp }
    k := k
    degree := degree
    q := q
    degree_quotient := fun _ ↦ rfl
    k_colimit := kernelCofan F G η _ _ A.b A.c A.b_colimit A.c_colimit p A.b_quotient
    k_inclusion := fun d ↦ kernel.lift_ι _ _ _
    c_projection := ?_
    k_projection := ?_
    k_orthogonal := ?_ }⟩
  · intro d
    simpa using hq d d
  · intro d
    apply (cancel_mono (kernel.ι (η d))).1
    rw [Category.assoc, hk, hr]
    simp
  · intro a d had
    apply (cancel_mono (kernel.ι (η d))).1
    rw [Category.assoc, hk, hr]
    simp [had]

end
end AlgebraicGeometry.Scheme.Modules
