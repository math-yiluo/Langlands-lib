/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.AlgebraicGeometry.FormalModuleQuotientAffineProjection
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FiniteModuleComplete
import Mathlib.RingTheory.AdicCompletion.LocalRing

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The canonical cone from a module to the sections of its sheaf quotient system.
The maps are the tilde/global-sections unit followed by the actual quotient projections.
Source: Stacks Project, Tag 087W, implicit converse (blueprint:
def-weil-pbc-coherent-formal-modules-affine-quotient-cone). 
(blueprint: def-weil-pbc-coherent-formal-modules-affine-quotient-cone)
-/
noncomputable def coherentFormalModules_affine_quotientCone
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (N : ModuleCat.{u} (AdicCompletion I A)) :
    Cone ((formalCompletionFunctor J).obj
      ((tilde.functor (CommRingCat.of A)).obj
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N)) ⋙
      moduleSpecΓFunctor (R := CommRingCat.of A)) where
  pt := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N
  π :=
    { app := fun n ↦ (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app _ ≫
        (moduleSpecΓFunctor (R := CommRingCat.of A)).map
          (formalModuleQuotientπ J (n.unop + 1) _)
      naturality := by
        intro n m f
        dsimp only [Functor.const, Functor.comp, formalCompletionFunctor,
          formalCompletionSystem]
        rw [Category.id_comp, Category.assoc, ← Functor.map_comp]
        congr 1
        simp [formalModuleQuotientπ, formalModuleQuotientMap] }

private theorem isLimit_of_complete_quotient_projections
    {A : Type u} [CommRing A] (I : Ideal A) {D : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (c : Cone D) [IsAdicComplete I c.pt]
    (hp : ∀ n : ℕ, Function.Surjective (c.π.app (op n)) ∧
      LinearMap.ker (c.π.app (op n)).hom = I ^ (n + 1) • (⊤ : Submodule A c.pt)) :
    Nonempty (IsLimit c) := by
  classical
  let e (n : ℕ) :
      (c.pt ⧸ (I ^ (n + 1) • (⊤ : Submodule A c.pt))) ≃ₗ[A] D.obj (op n) :=
    (Submodule.quotEquivOfEq _ _ (hp n).2.symm).trans
      ((c.π.app (op n)).hom.quotKerEquivOfSurjective (hp n).1)
  have he (n : ℕ) (x : c.pt) : e n (Submodule.Quotient.mk x) = c.π.app (op n) x := by
    rfl
  have he' (n : ℕ) (x : c.pt) :
      (e n).symm (c.π.app (op n) x) = Submodule.Quotient.mk x := by
    rw [← he]
    exact (e n).symm_apply_apply _
  let f (s : Cone D) (n : ℕ) :
      s.pt →ₗ[A] c.pt ⧸ (I ^ (n + 1) • (⊤ : Submodule A c.pt)) :=
    (e n).symm.toLinearMap ∘ₗ (s.π.app (op n)).hom
  have hf (s : Cone D) {m : ℕ} :
      Submodule.factorPow I c.pt (Nat.succ_le_succ m.le_succ) ∘ₗ f s (m + 1) = f s m := by
    have ht : Submodule.factorPow I c.pt (Nat.succ_le_succ m.le_succ) ∘ₗ
        (e (m + 1)).symm.toLinearMap = (e m).symm.toLinearMap ∘ₗ
          (D.map (homOfLE m.le_succ).op).hom := by
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := (hp (m + 1)).1 y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he']
      have hw := congrArg (fun g ↦ g x) (c.w (homOfLE m.le_succ).op)
      change D.map (homOfLE m.le_succ).op (c.π.app (op (m + 1)) x) =
        c.π.app (op m) x at hw
      rw [hw, he']
      rfl
    dsimp only [f]
    rw [← LinearMap.comp_assoc, ht, LinearMap.comp_assoc]
    rw [show (D.map (homOfLE m.le_succ).op).hom ∘ₗ
      (s.π.app (op (m + 1))).hom = (s.π.app (op m)).hom from
      congrArg ModuleCat.Hom.hom (s.w (homOfLE m.le_succ).op)]
  have ha : StrictMono (fun n : ℕ ↦ n + 1) := by
    intro m n h
    exact Nat.add_lt_add_right h 1
  let l (s : Cone D) : s.pt →ₗ[A] c.pt :=
    IsAdicComplete.StrictMono.lift I ha (f s) (hf s)
  have hl (s : Cone D) (n : ℕ) (x : s.pt) :
      Submodule.Quotient.mk (p := I ^ (n + 1) • (⊤ : Submodule A c.pt)) (l s x) =
        f s n x :=
    IsAdicComplete.StrictMono.mk_lift I ha (f s) (hf s) (n := n) x
  refine ⟨{
    lift := fun s ↦ ModuleCat.ofHom (l s)
    fac := ?_
    uniq := ?_ }⟩
  · intro s n
    ext x
    apply (e n.unop).symm.injective
    change (e n.unop).symm (c.π.app (op n.unop)
      (l s x)) = _
    rw [he']
    exact hl s n.unop x
  · intro s g hg
    apply ModuleCat.hom_ext
    change g.hom = l s
    apply IsAdicComplete.StrictMono.eq_lift I ha (f s) (hf s) (F := g.hom)
    intro n
    ext x
    have hw := congrArg (fun k ↦ (e n).symm (k x)) (hg (op n))
    change (e n).symm (c.π.app (op n) (g x)) = (e n).symm (s.π.app (op n) x) at hw
    change Submodule.Quotient.mk (g x) = (e n).symm (s.π.app (op n) x)
    simpa only [he'] using hw

/-- The canonical quotient cone of a finite completed module is limiting, and its
projections use the residue of a completed scalar at their level. This assertion
concerns only the explicit quotient construction, not any candidate inverse functor.
Source: Stacks Project, Tag 087W, implicit converse; Algebra Tags 0316, 05GG, 00MA (3).
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-quotient-cone).

Proof: Write B = AdicCompletion I A and K = I B. Since A is Noetherian, I is finitely
generated. The completion quotient formula identifies B/K^m with A/I^m for every
positive m, and B is K-adically complete and Noetherian (0316 and 05GG). The finite
B-module N is K-adically complete: 00MA (3) identifies its completion with
N tensor B-completion, hence with N itself. Restriction of scalars identifies
K^m N with I^m N: expand elements of the extended ideal as finite sums, and use
associativity of scalar multiplication; the reverse inclusion uses the algebra map.
The affine tilde/global-sections unit and ideal-product/cokernel comparison identify
our displayed projections with N -> N/I^(n+1)N and the transitions with reductions.
Completeness therefore supplies exactly the universal property of this cone; dropping
the zero quotient at exponent zero does not change compatible families. Finally, if
r has the residue of a modulo I^(n+1), the completion quotient formula puts
r - algebraMap A B a in K^(n+1). Its product with any x is killed by this quotient
projection, so the projection of r x equals a times the projection of x. The unit
and cokernel comparison transport this equality to the displayed sections maps.
For I = bottom this is the constant module cone; for I = top both B and N are zero. -/
theorem coherentFormalModules_affine_quotientCone_complete
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (N : ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N)) :
    Nonempty (IsLimit (coherentFormalModules_affine_quotientCone A I J N.obj)) ∧
    (∀ (n : ℕ) (r : AdicCompletion I A) (a : A) (x : N.obj),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (coherentFormalModules_affine_quotientCone A I J N.obj).π.app (op n) (r • x) =
        a • (coherentFormalModules_affine_quotientCone A I J N.obj).π.app (op n) x) := by
  let B := AdicCompletion I A
  let M := (ModuleCat.restrictScalars (algebraMap A B)).obj N.obj
  have : IsNoetherianRing B := AdicCompletion.isNoetherianRing I
  have : IsAdicComplete (I.map (algebraMap A B)) B :=
    AdicCompletion.isAdicComplete_self I (IsNoetherian.noetherian I)
  have : Module.Finite B M := N.property
  have : IsAdicComplete (I.map (algebraMap A B)) M :=
    finite_module_complete_over_complete_noetherian B (I.map (algebraMap A B)) M
  have : IsScalarTower A B M := ⟨fun a b x ↦ mul_smul (algebraMap A B a) b x⟩
  have : IsAdicComplete I M := (IsAdicComplete.map_algebraMap_iff (S := B) I M).mp inferInstance
  let c := coherentFormalModules_affine_quotientCone A I J N.obj
  have : IsAdicComplete I c.pt := (show IsAdicComplete I M from inferInstance)
  have hp (n : ℕ) : Function.Surjective (c.π.app (op n)) ∧
      LinearMap.ker (c.π.app (op n)).hom = I ^ (n + 1) • (⊤ : Submodule A M) :=
    formalModuleQuotient_affine_projection A I J hJ M (n + 1) (Nat.succ_pos n)
  refine ⟨isLimit_of_complete_quotient_projections I c hp, ?_⟩
  intro n r a x hr
  have hd : r - algebraMap A B a ∈ I ^ (n + 1) • (⊤ : Submodule A B) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := A) (IsNoetherian.noetherian I)]
    rw [LinearMap.mem_ker]
    apply (Ideal.quotientEquivAlgOfEq A
      (show I ^ (n + 1) • (⊤ : Ideal A) = I ^ (n + 1) by simp)).injective
    change AdicCompletion.evalₐ I (n + 1) (r - algebraMap A B a) = 0
    rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, hr,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  let x' : M := x
  have hdx : (r - algebraMap A B a) • x' ∈ I ^ (n + 1) • (⊤ : Submodule A M) := by
    refine Submodule.smul_induction_on hd (fun b hb y _ ↦ ?_) (fun y z hy hz ↦ ?_)
    · rw [smul_assoc]
      exact Submodule.smul_mem_smul hb (Submodule.mem_top)
    · rw [add_smul]
      exact Submodule.add_mem _ hy hz
  have hz : c.π.app (op n) ((r - algebraMap A B a) • x') = 0 := by
    apply LinearMap.mem_ker.mp
    rw [(hp n).2]
    exact hdx
  rw [sub_smul, map_sub, sub_eq_zero] at hz
  calc
    c.π.app (op n) (r • x') = c.π.app (op n) (algebraMap A B a • x') := hz
    _ = a • c.π.app (op n) x := (c.π.app (op n)).hom.map_smul a x'

end AlgebraicGeometry
