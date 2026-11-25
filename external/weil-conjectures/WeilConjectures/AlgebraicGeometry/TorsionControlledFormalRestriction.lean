/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import all WeilConjectures.AlgebraicGeometry.ModulePullbackIdealPowerProductImage
import WeilConjectures.AlgebraicGeometry.IdealPowerProductRestrictionZero
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The restriction dictionary for torsion-controlled formal maps

Source: Stacks Project, Tags 087X, 0887 and Remark 0888; Modules, Tags 01AG and 01CB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

private theorem restriction_power_image {X : Scheme.{u}} (J : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (n : ℕ) :
    imageSubobject ((Scheme.Modules.restrictFunctor U.ι).map
      (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F)) =
    imageSubobject (Scheme.idealModuleProductι
      (Scheme.idealSheafPower (J.comap U.ι).toModulesι n).2
      ((Scheme.Modules.restrictFunctor U.ι).obj F)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  obtain ⟨e, he⟩ := power_subobject_eq J n
  obtain ⟨e', he'⟩ := power_subobject_eq (J.comap U.ι) n
  obtain ⟨a, ha⟩ := product_iso _ _ e he F
  obtain ⟨b, hb⟩ := product_iso _ _ e' he' (R.obj F)
  calc
    _ = imageSubobject (R.map (Scheme.idealModuleProductι (J ^ n).toModulesι F)) := by
      rw [← ha, R.map_comp]
      exact imageSubobject_iso_comp (R.map a.hom) _
    _ = imageSubobject (Scheme.idealModuleProductι ((J ^ n).comap U.ι).toModulesι
        (R.obj F)) :=
      (Scheme.Modules.ideal_times_quasiCoherent_affine_sections (J ^ n) F).2.2.2.2 U
    _ = imageSubobject (Scheme.idealModuleProductι ((J.comap U.ι) ^ n).toModulesι
        (R.obj F)) := by rw [Scheme.IdealSheafData.comap_pow]
    _ = _ := by
      rw [← hb]
      exact (imageSubobject_iso_comp b.hom _).symm

private def restrictionQuotientIso {X : Scheme.{u}} (J : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (n : ℕ) :
    formalModuleQuotient (J.comap U.ι) n ((Scheme.Modules.restrictFunctor U.ι).obj F) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj (formalModuleQuotient J n F) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let i := Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F
  let k := Scheme.idealModuleProductι
    (Scheme.idealSheafPower (J.comap U.ι).toModulesι n).2 (R.obj F)
  have : Mono k := by dsimp [k, Scheme.idealModuleProductι]; infer_instance
  have he : Subobject.mk k = Subobject.mk (image.ι (R.map i)) := by
    rw [← imageSubobject_mono k]
    exact (restriction_power_image J F U n).symm
  let e := Subobject.isoOfMkEqMk k (image.ι (R.map i)) he
  exact cokernel.mapIso k (image.ι (R.map i)) e (Iso.refl _) (by simp [e]) ≪≫
    cokernelImageι (R.map i) ≪≫ (PreservesCokernel.iso R i).symm

private theorem restrictionQuotientIso_π {X : Scheme.{u}} (J : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (n : ℕ) :
    formalModuleQuotientπ (J.comap U.ι) n ((Scheme.Modules.restrictFunctor U.ι).obj F) ≫
        (restrictionQuotientIso J F U n).hom =
      (Scheme.Modules.restrictFunctor U.ι).map (formalModuleQuotientπ J n F) := by
  dsimp only [restrictionQuotientIso, Iso.trans_hom, Iso.symm_hom]
  rw [PreservesCokernel.iso_inv]
  simp [formalModuleQuotientπ, cokernel.mapIso, cokernelImageι]

private theorem quotientMap_π {X : Scheme.{u}} (J : X.IdealSheafData)
    {F G : X.Modules} (a : F ⟶ G) {m n : ℕ} (h : n ≤ m) :
    formalModuleQuotientπ J m F ≫ formalModuleQuotientMap J a h =
      a ≫ formalModuleQuotientπ J n G := cokernel.π_desc _ _ _

private def restrictionCompletionIso {X : Scheme.{u}} (J : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) :
    formalCompletionSystem (J.comap U.ι) ((Scheme.Modules.restrictFunctor U.ι).obj F) ≅
      formalCompletionSystem J F ⋙ Scheme.Modules.restrictFunctor U.ι := by
  let R := Scheme.Modules.restrictFunctor U.ι
  refine NatIso.ofComponents (fun n ↦ restrictionQuotientIso J F U (n.unop + 1)) ?_
  intro a b f
  change formalModuleQuotientMap (J.comap U.ι) (𝟙 (R.obj F)) (Nat.succ_le_succ (leOfHom f.unop)) ≫
      (restrictionQuotientIso J F U (b.unop + 1)).hom =
    (restrictionQuotientIso J F U (a.unop + 1)).hom ≫
      R.map (formalModuleQuotientMap J (𝟙 F) (Nat.succ_le_succ (leOfHom f.unop)))
  apply (cancel_epi (cokernel.π (Scheme.idealModuleProductι
    (Scheme.idealSheafPower (J.comap U.ι).toModulesι (a.unop + 1)).2 (R.obj F)))).1
  change formalModuleQuotientπ (J.comap U.ι) (a.unop + 1) (R.obj F) ≫ _ =
    formalModuleQuotientπ (J.comap U.ι) (a.unop + 1) (R.obj F) ≫ _
  simp only [← Category.assoc, quotientMap_π, Category.id_comp]
  rw [restrictionQuotientIso_π, restrictionQuotientIso_π,
    ← R.map_comp, quotientMap_π, Category.id_comp]

private theorem restrictionCompletionComparison {X : Scheme.{u}} (J : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (F' : U.toScheme.Modules)
    (h : F' = (Scheme.Modules.restrictFunctor U.ι).obj F) :
    ∃ γ : formalCompletionSystem J F ⋙ Scheme.Modules.restrictFunctor U.ι ≅
        formalCompletionSystem (J.comap U.ι) F',
      ∀ n : ℕ,
        (Scheme.Modules.restrictFunctor U.ι).map (formalModuleQuotientπ J (n + 1) F) ≫
            γ.hom.app (op n) =
          eqToHom h.symm ≫ formalModuleQuotientπ (J.comap U.ι) (n + 1) F' := by
  subst F'
  refine ⟨(restrictionCompletionIso J F U).symm, ?_⟩
  intro n
  simp only [restrictionCompletionIso, Iso.symm_hom, NatIso.ofComponents_inv_app]
  rw [← restrictionQuotientIso_π, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp

private theorem powerProduct_zero_of_iso {X : Scheme.{u}} (J : X.IdealSheafData)
    {F G : X.Modules} (e : F ≅ G) (t : ℕ)
    (hz : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2 G)) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2 F) := by
  obtain ⟨k, hk⟩ := formalModuleQuotient_factor J e.hom (Nat.le_refl t)
  have : Mono (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι t).2 F) := by
    dsimp [Scheme.idealModuleProductι]; infer_instance
  have : Mono (k ≫ Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι t).2 G) :=
    hk ▸ inferInstance
  have : Mono k := mono_of_mono k
    (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι t).2 G)
  exact IsZero.of_mono k hz

private theorem restriction_bound {X : Scheme.{u}} (J : X.IdealSheafData)
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G)
    (U : X.Opens) {G' : U.toScheme.Modules}
    (e : (Scheme.Modules.restrictFunctor U.ι).obj G ≅ G') (t : ℕ)
    (hk : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι t).2 (kernel f)))
    (hc : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι t).2 (cokernel f))) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower (J.comap U.ι).toModulesι t).2
      (kernel ((Scheme.Modules.restrictFunctor U.ι).map f ≫ e.hom))) ∧
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower (J.comap U.ι).toModulesι t).2
      (cokernel ((Scheme.Modules.restrictFunctor U.ι).map f ≫ e.hom))) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  have := Scheme.Modules.isQuasicoherent_kernel f
  have := Scheme.Modules.isQuasicoherent_cokernel f
  have hk' := (Scheme.Modules.idealPowerProduct_restrict_isZero_iff J (kernel f) U t).mp
    (R.map_isZero hk)
  have hc' := (Scheme.Modules.idealPowerProduct_restrict_isZero_iff J (cokernel f) U t).mp
    (R.map_isZero hc)
  exact ⟨powerProduct_zero_of_iso (J.comap U.ι)
      (kernelCompMono (R.map f) e.hom ≪≫ (PreservesKernel.iso R f).symm) t hk',
    powerProduct_zero_of_iso (J.comap U.ι)
      (cokernelCompIsIso (R.map f) e.hom ≪≫ (PreservesCokernel.iso R f).symm) t hc'⟩

/-- The canonical completion comparison on an open, with the original component
annihilation bound transported to the restricted map. The projection equations
specify the comparison, rather than allowing an arbitrary completion automorphism.

Source: Stacks Project, Tags 087X, 0887 and Remark 0888; Modules, Tags 01AG and 01CB.
(blueprint: lem-weil-pbc-torsion-controlled-formal-restriction).

Proof: Restriction to an open is exact and commutes with ideal products and powers.
For each n restrict the cokernel presentation H/J^(n+1)H. Identify the restricted
ideal-product inclusion with that for the comapped ideal. The two cokernel universal
properties give inverse comparison maps; cancelling the quotient epimorphisms
proves their inverse identities and the displayed projection equation. The same
cancellation with the transition maps proves naturality in n, yielding gamma.
Restriction preserves the component kernel and cokernel. Restrict the two zero
products, and use the ideal-power and kernel/cokernel comparisons to obtain their
zero products on U. Postcomposing with gamma at each level changes the kernel and
cokernel only by isomorphism, so the bound is unchanged. The equality hH identifies
the chosen coherent object with the actual restriction; eqToHom records this
identification in the quotient equation. All comparisons are defined by quotient
projections and are unique. Empty opens and zero or unit ideals satisfy the same
universal-property argument. No algebraization or choice of a local triple is used. -/
theorem torsionControlled_formal_restriction
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H) (U : X.Opens)
    (Hlocal : CoherentModules U.toScheme)
    (hH : Hlocal.obj = (Scheme.Modules.restrictFunctor U.ι).obj H.obj)
    (t : ℕ) (hbound : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op n))))) :
    ∃ γ : ((completion X J).obj H).obj ⋙ Scheme.Modules.restrictFunctor U.ι ≅
        formalCompletionSystem (J.comap U.ι) Hlocal.obj,
      (∀ n : ℕ,
        (Scheme.Modules.restrictFunctor U.ι).map
            (formalModuleQuotientπ J (n + 1) H.obj) ≫ γ.hom.app (op n) =
          eqToHom hH.symm ≫ formalModuleQuotientπ (J.comap U.ι) (n + 1) Hlocal.obj) ∧
      (∀ n : ℕ,
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap U.ι).toModulesι t).2
          (kernel ((Functor.whiskerRight δ.hom (Scheme.Modules.restrictFunctor U.ι) ≫
            γ.hom).app (op n)))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap U.ι).toModulesι t).2
          (cokernel ((Functor.whiskerRight δ.hom (Scheme.Modules.restrictFunctor U.ι) ≫
            γ.hom).app (op n))))) := by
  have : H.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X H.obj).mp
      H.property).1
  obtain ⟨γ, hγ⟩ := restrictionCompletionComparison J H.obj U Hlocal.obj hH
  refine ⟨γ, hγ, ?_⟩
  intro n
  have : (N.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (N.property.1 n)).1
  have : (((completion X J).obj H).obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (((completion X J).obj H).property.1 n)).1
  exact restriction_bound J (δ.hom.app (op n)) U (γ.app (op n)) t
    (hbound n).1 (hbound n).2

end
end AlgebraicGeometry
