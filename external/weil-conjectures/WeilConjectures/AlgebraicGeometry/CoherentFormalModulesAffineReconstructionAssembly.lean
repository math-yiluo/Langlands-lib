/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineQuotient
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Natural assembly of affine coherent formal reconstruction

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatible affine reconstruction projections assemble into a natural isomorphism.
Source: Stacks Project, Cohomology of Schemes, Lemma 087W, affine correspondence and
M/I^n M = M_n; Algebra, Lemma 05G8, surjective finite-module endomorphisms.
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-reconstruction-assembly).

Proof: Transpose each projection through the tilde/Gamma adjunction. The target is
annihilated by the required ideal power, so multiplication naturality factors this
transpose through the sheaf quotient. The adjunction triangle says its sections map,
precomposed by the unit and quotient projection, is the given surjection. Hence the
quotient comparison is surjective on sections. The objectwise isomorphism gives a
separate isomorphism between its source and target. Composing the comparison with
that isomorphism's inverse gives a surjective endomorphism of the finite section
module of the coherent target, which is bijective by 05G8. Thus the comparison is
invertible on sections, and the affine counit equation makes it invertible on sheaves.
For transitions and morphisms, precompose with the cokernel projection. The resulting
equalities are respectively naturality of p and hnatural, transported by tilde and
the counit. Cancel the projection and assemble twice with NatIso.ofComponents. -/
theorem coherentFormalModules_affine_reconstruction_assembly
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (L : CoherentFormalModule (Spec (CommRingCat.of A)) J ⥤
    ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N))
    (p : ∀ F : CoherentFormalModule (Spec (CommRingCat.of A)) J,
      (Functor.const ℕᵒᵖ).obj
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
          (L.obj F).obj) ⟶ F.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A))
    (hnatural : (∀ (F G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (f : F ⟶ G)
      (n : ℕ),
      (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map
        (L.map f).hom ≫ (p G).app (op n) =
      (p F).app (op n) ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map (f.hom.app (op n))))
    (hquotient : (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ),
      Function.Surjective ((p F).app (op n)) ∧
      LinearMap.ker ((p F).app (op n)).hom =
        I ^ (n + 1) • (⊤ : Submodule A
          ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
            (L.obj F).obj))))
    (hobj : ∀ F, Nonempty ((L ⋙ coherentFormalModules_affine_quotientFunctor A I J hJ).obj F ≅ F)) :
    Nonempty (L ⋙ coherentFormalModules_affine_quotientFunctor A I J hJ ≅ 𝟭 _) := by
  classical
  let S := ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))
  let T := tilde.functor (CommRingCat.of A)
  let Γ := moduleSpecΓFunctor (R := CommRingCat.of A)
  let ε := Scheme.Modules.fromTildeΓNatTrans (R := CommRingCat.of A)
  have hcomp (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ) :
      ∃ e : formalModuleQuotient J (n + 1) (T.obj (S.obj (L.obj F).obj)) ≅
          F.obj.obj (op n),
        formalModuleQuotientπ J (n + 1) _ ≫ e.hom =
          T.map ((p F).app (op n)) ≫ ε.app (F.obj.obj (op n)) := by
    have : (F.obj.obj (op n)).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp
        (F.property.1 n)).1
    let M := S.obj (L.obj F).obj
    let V := F.obj.obj (op n)
    let t : T.obj M ⟶ V := T.map ((p F).app (op n)) ≫ ε.app V
    obtain ⟨k, hk⟩ := formalModuleQuotient_factor J t (Nat.le_refl (n + 1))
    have hz : Scheme.idealModuleProductι
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2 (T.obj M) ≫ t = 0 := by
      rw [hk, (F.property.2.1 n).eq_zero_of_src
        (Scheme.idealModuleProductι
          (Scheme.idealSheafPower J.toModulesι (n + 1)).2 V), comp_zero]
    let q : formalModuleQuotient J (n + 1) (T.obj M) ⟶ V :=
      cokernel.desc _ t hz
    have hq : formalModuleQuotientπ J (n + 1) (T.obj M) ≫ q = t :=
      cokernel.π_desc _ _ _
    let η := (tilde.adjunction (R := CommRingCat.of A)).unit
    have hp : η.app M ≫ Γ.map t = (p F).app (op n) := by
      dsimp only [t]
      rw [Γ.map_comp, ← Category.assoc]
      have hη := η.naturality ((p F).app (op n))
      change (p F).app (op n) ≫ η.app (Γ.obj V) =
        η.app M ≫ Γ.map (T.map ((p F).app (op n))) at hη
      rw [← hη, Category.assoc]
      have htri := (tilde.adjunction (R := CommRingCat.of A)).right_triangle_components V
      change η.app (Γ.obj V) ≫ Γ.map (ε.app V) = 𝟙 _ at htri
      rw [htri]
      change (p F).app (op n) ≫ 𝟙 _ = (p F).app (op n)
      exact Category.comp_id _
    have : Epi ((p F).app (op n)) :=
      (ModuleCat.epi_iff_surjective _).mpr (hquotient F n).1
    have : Epi (Γ.map t) := epi_of_epi_fac hp
    have : Epi (Γ.map q) := epi_of_epi_fac (by rw [← Γ.map_comp, hq])
    let e₀ := (hobj F).some
    let e₁ : formalModuleQuotient J (n + 1) (T.obj M) ≅ V :=
      ((IsCoherentFormalModule J).ι.mapIso e₀).app (op n)
    let i : Γ.obj (formalModuleQuotient J (n + 1) (T.obj M)) ≅ Γ.obj V := Γ.mapIso e₁
    have : Module.Finite Γ(Spec (.of A), ⊤) Γ(V, ⊤) :=
      Scheme.Modules.coherent_affine_sections_finite _ V (F.property.1 n)
        ⊤ (isAffineOpen_top _)
    have : Module.Finite A (Γ.obj V) := Scheme.Modules.finite_sections_top_of_finite V
    let v : Γ.obj V ⟶ Γ.obj V := i.inv ≫ Γ.map q
    have : Epi v := inferInstanceAs (Epi (i.inv ≫ Γ.map q))
    have hv : Function.Bijective v :=
      OrzechProperty.bijective_of_surjective_endomorphism v.hom
        ((ModuleCat.epi_iff_surjective v).mp inferInstance)
    have : IsIso v := (ConcreteCategory.isIso_iff_bijective v).mpr hv
    have : IsIso (Γ.map q) := (isIso_comp_left_iff i.inv _).mp ‹IsIso v›
    have : IsIso (ε.app V) := by
      dsimp only [ε, Scheme.Modules.fromTildeΓNatTrans]
      exact Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) V
    have hε₀ := ε.naturality e₁.hom
    change T.map (Γ.map e₁.hom) ≫ ε.app V =
      ε.app (formalModuleQuotient J (n + 1) (T.obj M)) ≫ e₁.hom at hε₀
    have : IsIso (ε.app (formalModuleQuotient J (n + 1) (T.obj M))) := by
      apply (isIso_comp_right_iff _ e₁.hom).mp
      rw [← hε₀]
      infer_instance
    have hε := ε.naturality q
    change T.map (Γ.map q) ≫ ε.app V =
      ε.app (formalModuleQuotient J (n + 1) (T.obj M)) ≫ q at hε
    have : IsIso q := by
      apply (isIso_comp_left_iff
        (ε.app (formalModuleQuotient J (n + 1) (T.obj M))) q).mp
      rw [← hε]
      infer_instance
    exact ⟨asIso q, hq⟩
  choose e he using hcomp
  have hπ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ) :
      Epi (formalModuleQuotientπ J (n + 1) (T.obj (S.obj (L.obj F).obj))) := by
    dsimp only [formalModuleQuotientπ]
    infer_instance
  let α (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) :
      (L ⋙ coherentFormalModules_affine_quotientFunctor A I J hJ).obj F ≅ F :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun n ↦ e F n.unop) (by
      intro a b f
      change formalModuleQuotientMap J (𝟙 (T.obj (S.obj (L.obj F).obj)))
        (Nat.succ_le_succ (leOfHom f.unop)) ≫ (e F b.unop).hom =
          (e F a.unop).hom ≫ F.obj.map f
      apply (cancel_epi (formalModuleQuotientπ J (a.unop + 1) _)).mp
      simp only [← Category.assoc, formalModuleQuotientπ, formalModuleQuotientMap,
        cokernel.π_desc, Category.id_comp]
      change formalModuleQuotientπ J (b.unop + 1) _ ≫ (e F b.unop).hom =
        (formalModuleQuotientπ J (a.unop + 1) _ ≫ (e F a.unop).hom) ≫ F.obj.map f
      rw [he, he, Category.assoc]
      have hε := ε.naturality (F.obj.map f)
      change T.map (Γ.map (F.obj.map f)) ≫ ε.app (F.obj.obj b) =
        ε.app (F.obj.obj a) ≫ F.obj.map f at hε
      rw [← hε]
      rw [← Category.assoc, ← T.map_comp]
      have hp := (p F).naturality f
      change (p F).app b = (p F).app a ≫ Γ.map (F.obj.map f) at hp
      rw [← hp]))
  refine ⟨NatIso.ofComponents α ?_⟩
  intro F G f
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  change formalModuleQuotientMap J (T.map (S.map (L.map f).hom))
      (Nat.le_refl (n.unop + 1)) ≫ (e G n.unop).hom =
    (e F n.unop).hom ≫ f.hom.app n
  apply (cancel_epi (formalModuleQuotientπ J (n.unop + 1) _)).mp
  simp only [← Category.assoc, formalModuleQuotientπ, formalModuleQuotientMap,
    cokernel.π_desc]
  change T.map (S.map (L.map f).hom) ≫
      formalModuleQuotientπ J (n.unop + 1) _ ≫ (e G n.unop).hom =
    (formalModuleQuotientπ J (n.unop + 1) _ ≫ (e F n.unop).hom) ≫ f.hom.app n
  rw [he, he, Category.assoc]
  have hε := ε.naturality (f.hom.app n)
  change T.map (Γ.map (f.hom.app n)) ≫ ε.app (G.obj.obj n) =
    ε.app (F.obj.obj n) ≫ f.hom.app n at hε
  rw [← hε]
  simp only [← Category.assoc, ← T.map_comp]
  rw [hnatural F G f n.unop]
end AlgebraicGeometry
