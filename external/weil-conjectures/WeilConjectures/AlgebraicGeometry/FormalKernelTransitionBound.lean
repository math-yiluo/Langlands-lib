/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleShiftedQuotient
public import Mathlib.Algebra.Homology.ShortComplex.Exact

import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelShiftedStalkModel
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Eventual exactness of shifted kernel quotient transitions

Source: Stacks Project, Lemma 087X, proof of claims (a)--(c).
(blueprint: lem-weil-pbc-formal-kernel-quotient-transition-exact-bound).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem idealModuleProduct_mono {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) :
    Mono (Scheme.idealModuleProductι ι F) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  dsimp [Scheme.idealModuleProductι]
  infer_instance

private theorem multiplication_naturality {C : Type*} [Category C] [MonoidalCategory C]
    {J F G : C} (ι : J ⟶ MonoidalCategoryStruct.tensorUnit C) (f : F ⟶ G) :
    (MonoidalCategoryStruct.whiskerRight ι F ≫
      (MonoidalCategoryStruct.leftUnitor F).hom) ≫ f =
      MonoidalCategoryStruct.whiskerLeft J f ≫ (MonoidalCategoryStruct.whiskerRight ι G ≫
        (MonoidalCategoryStruct.leftUnitor G).hom) := by
  rw [Category.assoc, ← MonoidalCategory.leftUnitor_naturality,
    ← MonoidalCategory.whisker_exchange_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem idealModuleProduct_comp_zero_iff {X : Scheme.{u}} {J F G : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (f : F ⟶ G) :
    let _ : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    Scheme.idealModuleProductι ι F ≫ f = 0 ↔
      (MonoidalCategoryStruct.whiskerRight ι F ≫
        (MonoidalCategoryStruct.leftUnitor F).hom) ≫ f = 0 := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := (MonoidalCategoryStruct.whiskerRight ι F) ≫ (MonoidalCategoryStruct.leftUnitor F).hom
  change image.ι a ≫ f = 0 ↔ a ≫ f = 0
  rw [← cancel_epi (factorThruImage a)]
  simp only [← Category.assoc, image.fac, comp_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem idealModuleProduct_quotient_comp_zero_iff {X : Scheme.{u}}
    {J F Q G : X.Modules} (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    (q : F ⟶ Q) [Epi q] (f : Q ⟶ G) :
    Scheme.idealModuleProductι ι Q ≫ f = 0 ↔
      Scheme.idealModuleProductι ι F ≫ q ≫ f = 0 := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let : MonoidalClosed X.Modules := SheafOfModules.monoidalClosed (R := X.sheaf)
  have : Epi ((MonoidalCategory.tensorLeft J).map q) :=
    (MonoidalCategory.tensorLeft J).map_epi q
  have h₁ := idealModuleProduct_comp_zero_iff ι f
  have h₂ := idealModuleProduct_comp_zero_iff ι (q ≫ f)
  dsimp only at h₁ h₂
  rw [h₁, h₂, ← cancel_epi ((MonoidalCategory.tensorLeft J).map q)]
  rw [comp_zero, ← Category.assoc _ _ f]
  change (MonoidalCategoryStruct.whiskerLeft J q ≫
    (MonoidalCategoryStruct.whiskerRight ι Q ≫
      (MonoidalCategoryStruct.leftUnitor Q).hom)) ≫ f = 0 ↔
    (MonoidalCategoryStruct.whiskerRight ι F ≫
      (MonoidalCategoryStruct.leftUnitor F).hom) ≫ q ≫ f = 0
  rw [← multiplication_naturality ι q, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem idealModuleProduct_quotient_zero {X : Scheme.{u}} {J F : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) :
    IsZero (Scheme.idealModuleProduct ι (cokernel (Scheme.idealModuleProductι ι F))) := by
  have := idealModuleProduct_mono ι (cokernel (Scheme.idealModuleProductι ι F))
  apply IsZero.of_mono_eq_zero (Scheme.idealModuleProductι ι _)
  have hz := (idealModuleProduct_quotient_comp_zero_iff ι
    (cokernel.π (Scheme.idealModuleProductι ι F)) (𝟙 _)).mpr (by simp)
  simpa only [Category.comp_id] using hz

private theorem quotient_transition_kernel {R : Type u} [CommRing R]
    (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] (n : ℕ) :
    LinearMap.ker (Submodule.factorPow J M (Nat.le_succ (n + 1))) =
      J ^ (n + 1) • (⊤ : Submodule R (M ⧸ J ^ (n + 2) • (⊤ : Submodule R M))) := by
  let P : Submodule R M := J ^ (n + 2) • ⊤
  have hm : (J ^ (n + 1) • (⊤ : Submodule R M)).map P.mkQ =
      J ^ (n + 1) • (⊤ : Submodule R (M ⧸ P)) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr P.mkQ_surjective]
  rw [← hm]
  ext q
  constructor
  · intro h
    obtain ⟨m, rfl⟩ := P.mkQ_surjective q
    refine ⟨m, ?_, rfl⟩
    simpa [LinearMap.mem_ker, Submodule.factor] using h
  · rintro ⟨m, hm, rfl⟩
    simpa [LinearMap.mem_ker, Submodule.factor] using hm


set_option backward.isDefEq.respectTransparency false in
/-- The kernel of each sufficiently shifted quotient transition is its ideal product.

Source: Stacks Project, Lemma 087X, proof of claims (a)--(c).
(blueprint: lem-weil-pbc-formal-kernel-quotient-transition-exact-bound).

Proof: Restrict to a finite affine cover. The affine formal-module equivalence represents
alpha by a map f : M to N over the Noetherian completed ring. Put L = ker f.
Artin--Rees for im f in N gives a constant a such that
f inverse(I^t N) = L + I^(t-a) f inverse(I^a N) for t >= a.
For l >= m+a, its image modulo I^(m+1) M is therefore the image of L.
Choose l also >= m+c, and use hc to identify the image at m+c with this image.
Thus the eventual kernel image in level m is L/(L intersect I^(m+1) M).
The isomorphisms hS transport this
identification to S_m; the equations with j and its naturality identify the transitions
with the reductions of L. Artin--Rees for L in M supplies a bound b on each affine
with L intersect I^(r+b) M contained in I^r L. Take the maximum on the finite cover.
For d >= max(c,b), the level n shifted quotient is L/I^(n+1) L: the extra intersection
L intersect I^(n+d+1) M is contained in I^(n+1) L. Its transition from n+1 to n
is reduction, whose kernel is I^(n+1)L/I^(n+2)L, the ideal product of its source.
The Lean proof separates the unshifted stalk presentations from their shifted
quotient calculation. It identifies the kernel of a power-quotient reduction
with the power times the source by Submodule.map_smul'' and quotient representatives.
The stalk ideal-product calculation transports this equality to the sheaves.
Exactness is local, giving the asserted short-complex exactness and zero composite.
For I=0 these transitions are identities; for I=O_X or zero modules all terms vanish.
The empty scheme admits bound zero. -/
theorem coherentFormalModule_kernel_quotient_transition_exact_bound
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)))
    (hS : ∀ m : ℕ, ∃ e : S.obj (op m) ≅
      Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op),
      e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) :
    ∃ b : ℕ, ∀ d : ℕ, max c b ≤ d → ∀ n : ℕ,
      ∃ hz : Scheme.idealModuleProductι
          (Scheme.idealSheafPower I.toModulesι (n + 1)).2
          ((formalShiftedQuotient I S d).obj (op (n + 1))) ≫
          (formalShiftedQuotient I S d).map (homOfLE (Nat.le_succ n)).op = 0,
        (ShortComplex.mk
          (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2
            ((formalShiftedQuotient I S d).obj (op (n + 1))))
          ((formalShiftedQuotient I S d).map (homOfLE (Nat.le_succ n)).op) hz).Exact := by
  obtain ⟨b, hb⟩ := coherentFormalModule_kernel_shifted_stalk_model I F H α c S j hc hS
  refine ⟨b, ?_⟩
  intro d hd n
  let Q := formalShiftedQuotient I S d
  let i := Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2
    (Q.obj (op (n + 1)))
  let t := Q.map (homOfLE (Nat.le_succ n)).op
  have htarget : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (Q.obj (op n))) :=
    idealModuleProduct_quotient_zero _
  have hz : i ≫ t = 0 := by
    obtain ⟨k, hk⟩ := formalModuleQuotient_factor I t (Nat.le_refl (n + 1))
    rw [show i ≫ t = k ≫ Scheme.idealModuleProductι
      (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (Q.obj (op n)) from hk,
      htarget.eq_zero_of_src (Scheme.idealModuleProductι
        (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (Q.obj (op n))), comp_zero]
  refine ⟨hz, ?_⟩
  apply ((RingedSpace.module_stalk_exact X.toRingedSpace i).2.2.2.2
    (Q.obj (op n)) i t hz).2
  intro x
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro z hz'
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  change (T.map t).hom z = 0 at hz'
  obtain ⟨e, he, _, _, _, _, hp⟩ := Scheme.ideal_module_product_stalk
    I.toModulesι (Q.obj (op (n + 1))) x
  let J : Ideal (X.presheaf.stalk x) := LinearMap.range (T.map I.toModulesι ≫ e.hom).hom
  obtain ⟨M, E, hE⟩ := hb d hd x e he
  have hr : LinearMap.range (T.map i).hom =
      J ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk x) (T.obj (Q.obj (op (n + 1))))) :=
    (hp (n + 1) (Nat.succ_pos n)).2.1
  have hm : E (n + 1) z ∈ J ^ (n + 1) •
      (⊤ : Submodule (X.presheaf.stalk x) (M ⧸ J ^ (n + 2) • (⊤ : Submodule _ M))) := by
    rw [← quotient_transition_kernel J M n]
    change Submodule.factorPow J M (Nat.le_succ (n + 1)) (E (n + 1) z) = 0
    rw [← hE n z]
    change E n ((T.map t).hom z) = 0
    rw [hz', map_zero]
  have hcomap := Submodule.comap_smul_top_of_surjective (J ^ (n + 1))
    (E (n + 1)).toLinearMap (E (n + 1)).surjective
  rw [LinearMap.ker_eq_bot.mpr (E (n + 1)).injective, sup_bot_eq] at hcomap
  have hm' : z ∈ Submodule.comap (E (n + 1)).toLinearMap
      (J ^ (n + 1) • (⊤ : Submodule _ (M ⧸ J ^ (n + 2) • (⊤ : Submodule _ M)))) := hm
  rw [hcomap, ← hr] at hm'
  exact hm' 

end AlgebraicGeometry
