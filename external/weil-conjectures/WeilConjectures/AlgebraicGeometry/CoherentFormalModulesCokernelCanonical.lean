/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Images of multiplication commute with testing vanishing after an epimorphism.
The tensor functor preserves epimorphisms by its right adjoint. Cancel the image
factorizations and the tensor of the epimorphism, then use unitor naturality. -/
private theorem multiplicationImage_quotient_comp_zero_iff
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C] [MonoidalClosed C]
    {J F Q G : C} (ι : J ⟶ MonoidalCategoryStruct.tensorUnit C)
    (q : F ⟶ Q) [Epi q] (f : Q ⟶ G) :
    image.ι (MonoidalCategoryStruct.whiskerRight ι Q ≫
      (MonoidalCategoryStruct.leftUnitor Q).hom) ≫ f = 0 ↔
    image.ι (MonoidalCategoryStruct.whiskerRight ι F ≫
      (MonoidalCategoryStruct.leftUnitor F).hom) ≫ q ≫ f = 0 := by
  let a := MonoidalCategoryStruct.whiskerRight ι F ≫
    (MonoidalCategoryStruct.leftUnitor F).hom
  let b := MonoidalCategoryStruct.whiskerRight ι Q ≫
    (MonoidalCategoryStruct.leftUnitor Q).hom
  have : Epi ((MonoidalCategory.tensorLeft J).map q) :=
    (MonoidalCategory.tensorLeft J).map_epi q
  change image.ι b ≫ f = 0 ↔ image.ι a ≫ q ≫ f = 0
  rw [← cancel_epi (factorThruImage b), ← cancel_epi (factorThruImage a)]
  simp only [← Category.assoc, image.fac, comp_zero]
  rw [← cancel_epi ((MonoidalCategory.tensorLeft J).map q), comp_zero]
  change MonoidalCategoryStruct.whiskerLeft J q ≫ b ≫ f = 0 ↔ (a ≫ q) ≫ f = 0
  have hn : a ≫ q = MonoidalCategoryStruct.whiskerLeft J q ≫ b := by
    dsimp only [a, b]
    rw [Category.assoc, ← MonoidalCategory.leftUnitor_naturality,
      ← MonoidalCategory.whisker_exchange_assoc]
  rw [← Category.assoc, ← hn]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical ambient cokernel of a map between coherent formal modules is coherent.
Source: Stacks Project, Lemma 087X, termwise cokernel construction
(blueprint: lem-weil-pbc-coherent-formal-cokernel-canonical).

Proof: evaluate the ambient cokernel cofork termwise. Coherence of each term follows
from coherent kernel/cokernel closure. The quotient description on affine sections,
together with the transition quotient isomorphisms and ideal-product formulas, proves
annihilation and the adic transition condition. -/
theorem coherentFormalModules_canonicalCokernel_isCoherent
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    {F G : ℕᵒᵖ ⥤ X.Modules}
    (hF : IsCoherentFormalModule I F) (hG : IsCoherentFormalModule I G)
    (α : F ⟶ G) :
    IsCoherentFormalModule I (cokernel α) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let : MonoidalClosed X.Modules := SheafOfModules.monoidalClosed (R := X.sheaf)
  have hquot {J A B H : X.Modules}
      (j : J ⟶ SheafOfModules.unit X.ringCatSheaf) (q : A ⟶ B) [Epi q]
      (f : B ⟶ H) :
      Scheme.idealModuleProductι j B ≫ f = 0 ↔
        Scheme.idealModuleProductι j A ≫ q ≫ f = 0 :=
    multiplicationImage_quotient_comp_zero_iff j q f
  let Q := cokernel α
  let q := cokernel.π α
  have hq (n : ℕ) : Epi (q.app (op n)) := by
    exact ((evaluation ℕᵒᵖ X.Modules).obj (op n)).map_epi q
  have hc (n : ℕ) : RingedSpace.IsCoherent X.toRingedSpace (Q.obj (op n)) := by
    let e := PreservesCokernel.iso ((evaluation ℕᵒᵖ X.Modules).obj (op n)) α
    have h := ((RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).1
      (F.obj (op n)) (G.obj (op n)) (α.app (op n)) (hF.1 n) (hG.1 n)).2
    exact (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).2.2.2.2
      _ _ e.symm h
  refine ⟨hc, ?_, ?_⟩
  · intro n
    have := hq n
    let j := (Scheme.idealSheafPower I.toModulesι (n + 1)).2
    have hz : Scheme.idealModuleProductι j (G.obj (op n)) = 0 :=
      (hG.2.1 n).eq_zero_of_src _
    have hi : Scheme.idealModuleProductι j (Q.obj (op n)) = 0 := by
      have h := (hquot j (q.app (op n))
        (𝟙 (Q.obj (op n)))).mpr (by simp [hz])
      simpa using h
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    have : Mono (Scheme.idealModuleProductι j (Q.obj (op n))) :=
      inferInstanceAs (Mono (image.ι _))
    exact IsZero.of_mono_eq_zero _ hi
  · intro n
    have := hq n
    have := hq (n + 1)
    let t := (homOfLE (Nat.le_succ n)).op
    obtain ⟨eF, heF⟩ := hF.2.2 n
    obtain ⟨eG, heG⟩ := hG.2.2 n
    let j := (Scheme.idealSheafPower I.toModulesι (n + 1)).2
    let k := Scheme.idealModuleProductι j (Q.obj (op (n + 1)))
    let p := formalModuleQuotientπ I (n + 1) (Q.obj (op (n + 1)))
    have : Epi p := inferInstanceAs (Epi (cokernel.π k))
    have htG : Epi (G.map t) := by
      rw [← heG]
      change Epi (cokernel.π _ ≫ eG.hom)
      infer_instance
    have htF : Epi (F.map t) := by
      rw [← heF]
      change Epi (cokernel.π _ ≫ eF.hom)
      infer_instance
    have hqnat : q.app (op (n + 1)) ≫ Q.map t = G.map t ≫ q.app (op n) :=
      (q.naturality t).symm
    have hαnat : α.app (op (n + 1)) ≫ G.map t = F.map t ≫ α.app (op n) :=
      (α.naturality t).symm
    have hkill : k ≫ Q.map t = 0 := by
      apply (hquot j (q.app (op (n + 1)))
        (Q.map t)).mpr
      rw [hqnat, ← heG]
      change Scheme.idealModuleProductι j (G.obj (op (n + 1))) ≫
        (cokernel.π _ ≫ eG.hom) ≫ q.app (op n) = 0
      simp [j]
    let a := cokernel.desc k (Q.map t) hkill
    have ha : p ≫ a = Q.map t := cokernel.π_desc _ _ _
    have hvzero : Scheme.idealModuleProductι j (G.obj (op (n + 1))) ≫
        q.app (op (n + 1)) ≫ p = 0 :=
      (hquot j (q.app (op (n + 1))) p).mp
        (cokernel.condition k)
    let v := eG.inv ≫ cokernel.desc
      (Scheme.idealModuleProductι j (G.obj (op (n + 1))))
      (q.app (op (n + 1)) ≫ p) hvzero
    have hv : G.map t ≫ v = q.app (op (n + 1)) ≫ p := by
      rw [← heG]
      simp [v, j, formalModuleQuotientπ, Category.assoc]
    have hcond (m : ℕ) : α.app (op m) ≫ q.app (op m) = 0 := by
      simpa only [NatTrans.comp_app, NatTrans.app_zero] using
        congrArg (fun f ↦ f.app (op m)) (cokernel.condition α)
    have hvα : α.app (op n) ≫ v = 0 := by
      apply (cancel_epi (F.map t)).1
      rw [comp_zero, ← Category.assoc, ← hαnat, Category.assoc, hv,
        ← Category.assoc, hcond, zero_comp]
    have hcol : IsColimit (CokernelCofork.ofπ (q.app (op n)) (hcond n)) :=
      isColimitOfHasCokernelOfPreservesColimit ((evaluation ℕᵒᵖ X.Modules).obj (op n)) α
    obtain ⟨b, hb⟩ := CokernelCofork.IsColimit.desc' hcol v hvα
    change q.app (op n) ≫ b = v at hb
    have hab : a ≫ b = 𝟙 _ := by
      apply (cancel_epi p).1
      apply (cancel_epi (q.app (op (n + 1)))).1
      rw [← Category.assoc p, ha, ← Category.assoc, hqnat,
        Category.assoc, hb, hv]
      exact (congrArg (q.app (op (n + 1)) ≫ ·) (Category.comp_id p)).symm
    have hba : b ≫ a = 𝟙 _ := by
      apply (cancel_epi (q.app (op n))).1
      apply (cancel_epi (G.map t)).1
      rw [← Category.assoc (q.app (op n)), hb, ← Category.assoc, hv,
        Category.assoc, ha, hqnat]
      simp
    exact ⟨⟨a, b, hab, hba⟩, ha⟩

end AlgebraicGeometry
