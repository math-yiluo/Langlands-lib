/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import all WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FormalCompletionAffineSections
import Mathlib.RingTheory.AdicCompletion.Exactness

/-! # Vanishing of the completion of a coherent kernel's ideal product

Source: Stacks Project, Tags 088A, 087W and 00MB.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private noncomputable def completionSectionsUnit {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) (U : X.affineOpens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U.1)).obj M ⟶
      limit (formalCompletionSystem I M ⋙
        SheafOfModules.evaluation X.ringCatSheaf (op U.1)) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  refine limit.lift (formalCompletionSystem I M ⋙ E) { pt := E.obj M, π :=
    { app := fun n : ℕᵒᵖ ↦ E.map (formalModuleQuotientπ I (n.unop + 1) M)
      naturality := ?_ } }
  intro n m f
  symm
  change E.map (formalModuleQuotientπ I (n.unop + 1) M) ≫
    E.map (formalModuleQuotientMap I (𝟙 M) (Nat.succ_le_succ (leOfHom f.unop))) = _
  rw [← E.map_comp]
  simp [formalModuleQuotientMap, formalModuleQuotientπ]

set_option backward.isDefEq.respectTransparency false in
private theorem completionSectionsUnit_π {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) (U : X.affineOpens) (n : ℕᵒᵖ) :
    completionSectionsUnit I M U ≫ limit.π _ n =
      (SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map
        (formalModuleQuotientπ I (n.unop + 1) M) := by
  simpa only [completionSectionsUnit] using
    (limit.lift_π (F := formalCompletionSystem I M ⋙
      SheafOfModules.evaluation X.ringCatSheaf (op U.1)) _ n)

set_option backward.isDefEq.respectTransparency false in
private theorem completionSectionsUnit_naturality {X : Scheme.{u}}
    (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) (U : X.affineOpens) :
    completionSectionsUnit I M U ≫ lim.map (Functor.whiskerRight
        (formalCompletionMap I f) (SheafOfModules.evaluation X.ringCatSheaf (op U.1))) =
      (SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map f ≫
        completionSectionsUnit I N U := by
  apply limit.hom_ext
  intro n
  change (completionSectionsUnit I M U ≫ limMap _) ≫ _ = _
  rw [Category.assoc]
  erw [limMap_π]
  rw [ ← Category.assoc, completionSectionsUnit_π,
    Category.assoc, completionSectionsUnit_π]
  change _ ≫ (SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map
    (formalModuleQuotientMap I f (Nat.le_refl _)) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp [formalModuleQuotientMap, formalModuleQuotientπ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completionSections_dictionary {X : Scheme.{u}}
    (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens) :
    let A := Γ(X, U.1)
    let J := I.ideal U
    let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
    ∃ (q : ∀ n : ℕ, ModuleCat.of A
        (Γ(M, U.1) ⧸ (J ^ (n + 1) • (⊤ : Submodule A Γ(M, U.1)))) ≅
          E.obj (formalModuleQuotient I (n + 1) M))
      (e : ModuleCat.of A (AdicCompletion J Γ(M, U.1)) ≅
        limit (formalCompletionSystem I M ⋙ E)),
      (∀ n, ModuleCat.ofHom (Submodule.mkQ (J ^ (n + 1) • ⊤)) ≫ (q n).hom =
        E.map (formalModuleQuotientπ I (n + 1) M)) ∧
      (∀ n, e.hom ≫ limit.π _ (op n) =
        ModuleCat.ofHom (AdicCompletion.eval J Γ(M, U.1) (n + 1)) ≫ (q n).hom) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let S := formalCompletionSystem I M
  obtain ⟨q, hq, e, he⟩ := formalCompletion_affine_sections I M U.1 U.2
  let e' := e ≪≫ preservesLimitIso E S
  have he' (n : ℕ) : e'.hom ≫ limit.π _ (op n) =
      ModuleCat.ofHom (AdicCompletion.eval (I.ideal U) Γ(M, U.1) (n + 1)) ≫
        (q n).hom := by
    dsimp only [e', Iso.trans_hom]
    rw [Category.assoc, preservesLimitIso_hom_π, he]
  exact ⟨q, e', hq, he'⟩

/-- Compatibility with quotient projections determines the map on ideal quotients. -/
private theorem reduceModIdeal_naturality_of_mkQ
    {R M N P Q : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (J : Ideal R) (f : M →ₗ[R] N)
    (pM : M →ₗ[R] P) (pN : N →ₗ[R] Q)
    (qM : (M ⧸ (J • ⊤ : Submodule R M)) →ₗ[R] P)
    (qN : (N ⧸ (J • ⊤ : Submodule R N)) →ₗ[R] Q) (g : P →ₗ[R] Q)
    (hqM : qM.comp (Submodule.mkQ (J • ⊤)) = pM)
    (hqN : qN.comp (Submodule.mkQ (J • ⊤)) = pN)
    (hg : g.comp pM = pN.comp f) (x : M ⧸ (J • ⊤ : Submodule R M)) :
    g (qM x) = qN (f.reduceModIdeal J x) := by
  obtain ⟨y, rfl⟩ := (J • (⊤ : Submodule R M)).mkQ_surjective x
  exact (congrArg g (LinearMap.congr_fun hqM y)).trans
    ((LinearMap.congr_fun hg y).trans (LinearMap.congr_fun hqN (f y)).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completionSections_map_injective {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) [Mono f]
    (U : X.affineOpens) [Module.Finite Γ(X, U.1) Γ(N, U.1)] :
    Function.Injective (lim.map (Functor.whiskerRight (formalCompletionMap I f)
      (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))) := by
  let A := Γ(X, U.1)
  let J := I.ideal U
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let L := (E.map f).hom
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite A (E.obj N) := ‹Module.Finite Γ(X, U.1) Γ(N, U.1)›
  have hinj : Function.Injective L :=
    (ModuleCat.mono_iff_injective _).mp (E.map_mono f)
  obtain ⟨qM, eM, hqM, heM⟩ := completionSections_dictionary I M U
  obtain ⟨qN, eN, hqN, heN⟩ := completionSections_dictionary I N U
  let α := Functor.whiskerRight (formalCompletionMap I f) E
  have hn : eM.hom ≫ lim.map α =
      ModuleCat.ofHom ((AdicCompletion.map J L).restrictScalars A) ≫ eN.hom := by
    apply limit.hom_ext
    intro n
    change (eM.hom ≫ limMap α) ≫ _ = _
    rw [Category.assoc]
    erw [limMap_π]
    rw [← Category.assoc, heM]
    simp only [Category.assoc]
    erw [heN n.unop]
    rw [← Category.assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (E.map (formalModuleQuotientMap I f (Nat.le_refl _)))
      ((qM n.unop).hom (x.val (n.unop + 1))) =
      (qN n.unop).hom (L.reduceModIdeal (J ^ (n.unop + 1)) (x.val (n.unop + 1)))
    apply reduceModIdeal_naturality_of_mkQ (J ^ (n.unop + 1)) L
      (E.map (formalModuleQuotientπ I (n.unop + 1) M)).hom
      (E.map (formalModuleQuotientπ I (n.unop + 1) N)).hom
      (qM n.unop).hom.hom (qN n.unop).hom.hom
      (E.map (formalModuleQuotientMap I f (Nat.le_refl _))).hom
      (congrArg ModuleCat.Hom.hom (hqM n.unop))
      (congrArg ModuleCat.Hom.hom (hqN n.unop))
    have hnatu : formalModuleQuotientπ I (n.unop + 1) M ≫
        formalModuleQuotientMap I f (Nat.le_refl _) =
        f ≫ formalModuleQuotientπ I (n.unop + 1) N := by
      simp only [formalModuleQuotientMap, formalModuleQuotientπ, cokernel.π_desc]
    exact congrArg (fun g ↦ (E.map g).hom) hnatu
  intro x y hxy
  obtain ⟨x', rfl⟩ := eM.toLinearEquiv.surjective x
  obtain ⟨y', rfl⟩ := eM.toLinearEquiv.surjective y
  apply congrArg eM.hom
  apply AdicCompletion.map_injective J hinj
  apply eN.toLinearEquiv.injective
  have hn' := fun z ↦ ConcreteCategory.congr_hom hn z
  exact (hn' x').symm.trans (hxy.trans (hn' y'))

/-- A map into a kernel annihilated by an ideal kills the corresponding ideal product. -/
private theorem linearMap_eq_zero_of_mem_smul_top_of_annihilator
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (J : Ideal R) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ x, f x ∈ LinearMap.ker g)
    (hJ : J ≤ Module.annihilator R (LinearMap.ker g))
    {x : M} (hx : x ∈ J • (⊤ : Submodule R M)) : f x = 0 := by
  refine Submodule.smul_induction_on hx (fun r hr x _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [map_smul]
    exact congrArg Subtype.val (Module.mem_annihilator.mp (hJ hr) ⟨_, hf x⟩)
  · rw [map_add, hx, hy, add_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An affine limit-kernel annihilator makes every reduction of the coherent
ideal product with the original kernel zero.
Source: Stacks Project, Tag 088A, second application of Remark 0888;
Tag 087W and Algebra, Tag 00MB (exactness of finite-module completion).
(blueprint: lem-weil-pbc-coherent-kernel-ideal-product-completion-zero).

Proof:
1. The kernel of a map between coherent modules on a Noetherian scheme is coherent.
The ideal power is quasi-coherent and locally finitely generated. Its product with
this kernel is quasi-coherent and a submodule of a coherent module, hence coherent.
2. On an affine open U, exact affine sections identify the sheaf kernel with the
kernel of the section map and the ideal product with K(U)^t times that kernel.
Finite-module completion is tensoring with the flat completed ring. It therefore
identifies the completion of this kernel with the kernel of the completed map,
and the completion of its ideal product with the image of the completed ideal action.
3. The natural quotient and inverse-limit comparisons identify the completed map
with the inverse limit of the section maps of the quotient system. The stated
annihilator bound makes the image from step 2 zero. Thus the completion of the
ideal product is zero on every affine open.
4. Each positive quotient is a quotient of that finite-module completion, so it
is zero on each affine open. The affine opens form a basis, and sheaf separatedness
makes each quotient zero globally. This includes t = 0, the empty affine, and the
unit completion ideal; no faithfulness of affine completion is used.
-/
theorem coherentKernel_idealProduct_completion_zero
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (F G : CoherentModules X) (a : F ⟶ G) (t : ℕ)
    (h : ∀ U : X.affineOpens,
      K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight ((completion X I).map a).hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom)) :
    RingedSpace.IsCoherent X.toRingedSpace
      (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel a.hom)) ∧
    ∀ n : ℕ, IsZero (formalModuleQuotient I (n + 1)
      (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel a.hom))) := by
  classical
  let L := kernel a.hom
  have hL : RingedSpace.IsCoherent X.toRingedSpace L :=
    ((RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).1
      F.obj G.obj a.hom F.property G.property).1
  have : L.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X L).mp hL).1
  have : (Scheme.idealSheafPower K.toModulesι t).1.IsQuasicoherent :=
    idealSheafPower_quasicoherent K t
  let H := Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2 L
  let i : H ⟶ L := Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι t).2 L
  have hi : Mono i := by dsimp [i, Scheme.idealModuleProductι]; infer_instance
  have : H.IsQuasicoherent := idealModuleProduct_quasicoherent _ L
  have hH : RingedSpace.IsCoherent X.toRingedSpace H :=
    ((Scheme.Modules.isCoherent_kernel_cokernel_biprod_and_submodule X).2
      L H i hL hi inferInstance).1
  refine ⟨hH, ?_⟩
  have hF := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X F.obj).mp F.property
  have : F.obj.IsQuasicoherent := hF.1
  have : F.obj.IsFiniteType := hF.2
  let j : H ⟶ F.obj := i ≫ kernel.ι a.hom
  have : Mono j := by dsimp [j]; infer_instance
  have hz (U : X.affineOpens) (s : Γ(H, U.1)) :
      completionSectionsUnit I H U s = 0 := by
    let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
    have : (F.obj.over U.1).IsFiniteType :=
      Scheme.Modules.isFiniteType_over (_root_.Opens.grothendieckTopology X)
        X.ringCatSheaf F.obj U.1
    have : Module.Finite Γ(X, U.1) Γ(F.obj, U.1) :=
      (((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} X).2 F.obj hF.1).1
        U.1 U.2).1.mp inferInstance
    have hinj := completionSections_map_injective I j U
    apply hinj
    rw [map_zero]
    have hnat := ConcreteCategory.congr_hom (completionSectionsUnit_naturality I j U) s
    change (lim.map (Functor.whiskerRight (formalCompletionMap I j) E))
      (completionSectionsUnit I H U s) =
        completionSectionsUnit I F.obj U (j.app U.1 s) at hnat
    rw [hnat]
    have hk (x : Γ(L, U.1)) :
        completionSectionsUnit I F.obj U ((kernel.ι a.hom).app U.1 x) ∈
          LinearMap.ker (lim.map (Functor.whiskerRight ((completion X I).map a).hom E)).hom := by
      change (lim.map (Functor.whiskerRight (formalCompletionMap I a.hom) E))
        (completionSectionsUnit I F.obj U ((kernel.ι a.hom).app U.1 x)) = 0
      have hn := ConcreteCategory.congr_hom
        (completionSectionsUnit_naturality I a.hom U) ((kernel.ι a.hom).app U.1 x)
      change (lim.map (Functor.whiskerRight (formalCompletionMap I a.hom) E))
        (completionSectionsUnit I F.obj U ((kernel.ι a.hom).app U.1 x)) =
          completionSectionsUnit I G.obj U
            (a.hom.app U.1 ((kernel.ι a.hom).app U.1 x)) at hn
      rw [hn]
      have ha : a.hom.app U.1 ((kernel.ι a.hom).app U.1 x) = 0 :=
        ConcreteCategory.congr_hom (congrArg E.map (kernel.condition a.hom)) x
      change completionSectionsUnit I G.obj U (a.hom.app U.1 _) = 0
      rw [ha, map_zero]
    have hr := Scheme.Modules.multiplication_range
      (Scheme.idealSheafPower K.toModulesι t).2 L U
    have hp : (LinearMap.range
        ((Scheme.idealSheafPower K.toModulesι t).2.val.app (op U.1)).hom :
          Ideal Γ(X, U.1)) = K.ideal U ^ t := by
      cases t with
      | zero =>
        rw [pow_zero, Ideal.one_eq_top]
        change LinearMap.range (LinearMap.id : Γ(X, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1)) = ⊤
        apply LinearMap.range_eq_top.mpr
        exact Function.surjective_id
      | succ t =>
        exact SetLike.coe_injective
          (((Scheme.Modules.ideal_times_quasiCoherent_affine_sections K L).2.2.2.1 U).2.2.2
            (t + 1) (Nat.succ_pos t))
    dsimp only at hr
    rw [hp] at hr
    have hs : i.app U.1 s ∈ K.ideal U ^ t •
        (⊤ : Submodule Γ(X, U.1) Γ(L, U.1)) := by
      have hm : i.app U.1 s ∈ Set.range
          ((Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι t).2 L).app
            U.1) := ⟨s, rfl⟩
      rw [hr] at hm
      exact hm
    change completionSectionsUnit I F.obj U ((kernel.ι a.hom).app U.1 (i.app U.1 s)) = 0
    exact linearMap_eq_zero_of_mem_smul_top_of_annihilator (K.ideal U ^ t)
      ((completionSectionsUnit I F.obj U).hom.comp (E.map (kernel.ι a.hom)).hom)
      (lim.map (Functor.whiskerRight ((completion X I).map a).hom E)).hom hk (h U) hs
  intro n
  have hquot (U : X.affineOpens) (s : Γ(H, U.1)) :
      (formalModuleQuotientπ I (n + 1) H).app U.1 s = 0 := by
    have he := ConcreteCategory.congr_hom (completionSectionsUnit_π I H U (op n)) s
    change (limit.π (formalCompletionSystem I H ⋙
      SheafOfModules.evaluation X.ringCatSheaf (op U.1)) (op n)) (completionSectionsUnit I H U s) =
      (formalModuleQuotientπ I (n + 1) H).app U.1 s at he
    rw [hz U s, map_zero] at he
    exact he.symm
  have hsections (U : X.affineOpens) :
      Subsingleton Γ(formalModuleQuotient I (n + 1) H, U.1) := by
    obtain ⟨q, hq, e, he⟩ := formalCompletion_affine_sections I H U.1 U.2
    have hsurj : Function.Surjective ((formalModuleQuotientπ I (n + 1) H).app U.1) := by
      have hs := (q n).toLinearEquiv.surjective.comp
        ((I.ideal U) ^ (n + 1) • (⊤ : Submodule Γ(X, U.1) Γ(H, U.1))).mkQ_surjective
      have hq' := fun s ↦ ConcreteCategory.congr_hom (hq n) s
      intro x
      obtain ⟨s, hs⟩ := hs x
      exact ⟨s, (hq' s).symm.trans hs⟩
    exact ⟨fun x y ↦ by
      obtain ⟨s, rfl⟩ := hsurj x
      obtain ⟨r, rfl⟩ := hsurj y
      exact (hquot U s).trans (hquot U r).symm⟩
  exact Scheme.Modules.isZero_of_forall_affineOpens _ hsections

end AlgebraicGeometry
