/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineQuotient
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Objectwise reconstruction of affine coherent formal modules

Source: Stacks Project, Lemma 087W and the affine sheaf/module correspondence.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open Scheme Scheme.Modules in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Tilde of the module projection is a cokernel of the sheaf ideal-power inclusion.
Source: Stacks Project, Schemes, Section 01LA, item (8), Lemma 01IC and Lemma 01ID;
Cohomology of Schemes, Lemma 087W, the reduction to module systems.

Proof: On each basic open D(f), tilde sections are localized modules. The ideal
associated to I has localized ideal I_f, and its nth power has ideal (I^n)_f.
Localization commutes with products and images, so the image of the multiplication
inclusion on these sections is (I^n N)_f. Localization is exact, hence the localized
projection N_f -> (N/I^n N)_f is surjective with this kernel. The composite of the
inclusion and projection is therefore zero on the basic-open basis, hence zero as
a sheaf morphism. Given a sheaf morphism from tilde(N) annihilating the inclusion,
its maps on basic-open sections descend uniquely through these quotient projections.
Uniqueness and compatibility of the original maps make these descended maps commute
with restriction; they glue to a unique sheaf morphism from tilde(N/I^n N).
This is exactly the cokernel cofork universal property. -/
private theorem affineIdealPower_tilde_cokernel
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (N : ModuleCat.{u} A) (n : ℕ) (hn : 0 < n) :
    ∃ h : Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2
        ((tilde.functor (CommRingCat.of A)).obj N) ≫
        (tilde.functor (CommRingCat.of A)).map
          (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A N)).mkQ) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((tilde.functor (CommRingCat.of A)).map
          (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A N)).mkQ)) h)) := by
  classical
  let X := Spec (CommRingCat.of A)
  let T := tilde.functor (CommRingCat.of A)
  let M := T.obj N
  let G := moduleSpecΓFunctor (R := CommRingCat.of A)
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let a := (Scheme.idealSheafPower J.toModulesι n).2
  have : M.IsQuasicoherent := by
    change (tilde (R := CommRingCat.of A) N).IsQuasicoherent
    exact (presentationTilde (R := CommRingCat.of A) N Set.univ
      (by simp) _ (Submodule.span_eq _)).isQuasicoherent
  have hp := Scheme.Modules.ideal_times_quasiCoherent_affine_sections J M
  have : (Scheme.idealSheafPower J.toModulesι n).1.IsQuasicoherent := hp.2.2.1 n hn
  have hm := Scheme.Modules.multiplication_range a M U
  have ha : (LinearMap.range (a.val.app (op U.1)).hom : Ideal Γ(X, U.1)) =
      J.ideal U ^ n := by
    apply SetLike.coe_injective
    exact hp.2.2.2.1 U |>.2.2.2 n hn
  dsimp only at hm
  rw [ha] at hm
  have hJtop : J.ideal U = I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
    rw [hJ]
    exact Scheme.IdealSheafData.ideal_top_ofIdealTop _
  rw [hJtop, ← Ideal.map_pow] at hm
  let η := tilde.isoTop (R := CommRingCat.of A) N
  let i := Scheme.idealModuleProductι a M
  let r := G.map i ≫ η.inv
  let φ := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hφ : Function.Surjective φ :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective
  have hη (c : A) (t : Γ(M, U.1)) :
      η.inv.hom (φ c • t) = c • η.inv.hom t := by
    exact η.inv.hom.map_smul c t
  have hη' (c : A) (t : N) : η.hom.hom (c • t) =
      φ c • (show Γ(M, U.1) from η.hom.hom t) := by
    exact η.hom.hom.map_smul c t
  have hr : LinearMap.range r.hom = I ^ n • (⊤ : Submodule A N) := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      have ht : i.app U.1 t ∈ (I ^ n).map φ •
          (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
        exact (Set.ext_iff.mp hm (i.app U.1 t)).mp ⟨t, rfl⟩
      change η.inv.hom (i.app U.1 t) ∈ I ^ n • (⊤ : Submodule A N)
      refine Submodule.smul_induction_on ht ?_ ?_
      · intro c hc z _
        obtain ⟨c', hc', rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hc
        rw [hη]
        exact Submodule.smul_mem_smul hc' (Submodule.mem_top)
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    · intro x hx
      have ht : (show Γ(M, U.1) from η.hom.hom x) ∈ (I ^ n).map φ •
          (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
        refine Submodule.smul_induction_on hx ?_ ?_
        · intro c hc z _
          rw [hη']
          exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem φ hc) (Submodule.mem_top)
        · intro x y hx hy
          rw [map_add]
          exact Submodule.add_mem _ hx hy
      obtain ⟨t, ht⟩ := (Set.ext_iff.mp hm (η.hom.hom x)).mpr ht
      refine ⟨t, ?_⟩
      change η.inv.hom (i.app U.1 t) = x
      rw [ht]
      exact congrArg (fun f ↦ f x) η.hom_inv_id
  have : (Scheme.idealModuleProduct a M).IsQuasicoherent := Scheme.Modules.product_qc a M
  have : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A)
      (Scheme.idealModuleProduct a M)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of A) _
  let eK := asIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A)
    (Scheme.idealModuleProduct a M))
  let S : Submodule A N := I ^ n • ⊤
  let q := ModuleCat.ofHom S.mkQ
  have hrexact : Function.Exact r.hom q.hom := by
    apply LinearMap.exact_iff.mpr
    rw [hr]
    exact Submodule.ker_mkQ S
  have hz : r ≫ q = 0 := by
    ext x
    exact hrexact.apply_apply_eq_zero x
  let c := CokernelCofork.ofπ q hz
  have hc : IsColimit c := ModuleCat.isColimitCokernelCofork r q hrexact S.mkQ_surjective
  have htri : T.map η.hom ≫ Scheme.Modules.fromTildeΓ
      (R := CommRingCat.of A) M = 𝟙 M :=
    (tilde.adjunction (R := CommRingCat.of A)).left_triangle_components N
  have hcounit : Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) M = T.map η.inv := by
    calc
      _ = T.map η.inv ≫ (T.map η.hom ≫
          Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) M) := by
        simp [← Category.assoc, ← T.map_comp]
      _ = _ := by rw [htri, Category.comp_id]
  have hi : eK.hom ≫ i = T.map r := by
    have hh := (Scheme.Modules.fromTildeΓNatTrans
      (R := CommRingCat.of A)).naturality i
    change T.map (G.map i) ≫ Scheme.Modules.fromTildeΓ
      (R := CommRingCat.of A) M = eK.hom ≫ i at hh
    rw [hcounit] at hh
    simpa [r, T.map_comp] using hh.symm
  have : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  have : T.IsLeftAdjoint := (tilde.adjunction (R := CommRingCat.of A)).isLeftAdjoint
  have : PreservesColimitsOfSize.{u, u} T := inferInstance
  have hzero : i ≫ T.map q = 0 := by
    apply (cancel_epi eK.hom).1
    rw [← Category.assoc, hi, ← T.map_comp, hz, Functor.map_zero, comp_zero]
  refine ⟨hzero, ⟨?_⟩⟩
  change IsColimit (CokernelCofork.ofπ (T.map q) hzero)
  exact IsCokernel.ofIso _ (c.mapIsColimit hc T) _ eK (Iso.refl M) (Iso.refl _)
    (hi.trans (Category.comp_id (T.map r)).symm)
    (by simp only [Iso.refl_hom, Category.comp_id]; rfl)


open Scheme Scheme.Modules in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A surjective section map with ideal-power kernel induces the specified quotient
isomorphism at a single level. Source: Stacks Project, Lemma 087W, the reduction to
module systems; Schemes 01I7 and 01IB, and the ideal-product calculation of 01IC.

Proof: The first isomorphism theorem identifies N/(I^n N) with Gamma(F), with its
projection induced by q. The affine ideal-product formula identifies the inclusion
of J^n tilde(N) with the tilde of I^n N, because J is associated to I. Tilde preserves
cokernels, hence identifies the sheaf quotient with tilde(N/(I^n N)). Compose this
comparison with tilde of the first-isomorphism map and the quasi-coherent counit onto
F. Each comparison respects its projection, so their composite has the stated
factorization. This factorization uniquely determines the isomorphism, since the
quotient projection is an epimorphism. -/
private theorem affineFormalQuotient_projection_iso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (N : ModuleCat.{u} A) (F : (Spec (CommRingCat.of A)).Modules)
    [F.IsQuasicoherent] (n : ℕ) (hn : 0 < n)
    (q : N ⟶ (moduleSpecΓFunctor (R := CommRingCat.of A)).obj F)
    (hq : Function.Surjective q)
    (hker : LinearMap.ker q.hom = I ^ n • (⊤ : Submodule A N)) :
    ∃ e : formalModuleQuotient J n ((tilde.functor (CommRingCat.of A)).obj N) ≅ F,
      formalModuleQuotientπ J n ((tilde.functor (CommRingCat.of A)).obj N) ≫ e.hom =
        (tilde.functor (CommRingCat.of A)).map q ≫
          Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) F := by
  classical
  let S : Submodule A N := I ^ n • ⊤
  let T := tilde.functor (CommRingCat.of A)
  let i := Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 (T.obj N)
  obtain ⟨h, ⟨hc⟩⟩ := affineIdealPower_tilde_cokernel A I J hJ N n hn
  let c := CokernelCofork.ofπ (T.map (ModuleCat.ofHom S.mkQ)) h
  let d := (cokernelIsCokernel i).coconePointUniqueUpToIso hc
  let k : ModuleCat.of A (N ⧸ S) ≅ (moduleSpecΓFunctor
      (R := CommRingCat.of A)).obj F :=
    (Submodule.quotEquivOfEq S q.hom.ker hker.symm ≪≫ₗ
      q.hom.quotKerEquivOfSurjective hq).toModuleIso
  have hk : ModuleCat.ofHom S.mkQ ≫ k.hom = q := by
    ext x
    simp [k, S, LinearEquiv.toModuleIso, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  have : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) F) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of A) F
  let e := d ≪≫ T.mapIso k ≪≫ asIso (Scheme.Modules.fromTildeΓ
    (R := CommRingCat.of A) F)
  refine ⟨e, ?_⟩
  have hd : formalModuleQuotientπ J n (T.obj N) ≫ d.hom =
      T.map (ModuleCat.ofHom S.mkQ) := by
    exact (cokernelIsCokernel i).comp_coconePointUniqueUpToIso_hom hc
      WalkingParallelPair.one
  change formalModuleQuotientπ J n (T.obj N) ≫
    (d.hom ≫ T.map k.hom ≫ Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) F) =
      T.map q ≫ Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) F
  rw [← Category.assoc, ← Category.assoc, hd, ← T.map_comp, hk]


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The proof follows the first-isomorphism and affine tilde/Gamma arguments,
then checks transition and map naturality as in Lemma 087W.
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-reconstruction-objectwise).
Proof: apply the corresponding argument to quotient projections and cancel their
surjectivity. -/
theorem coherentFormalModules_affine_reconstruction_objectwise
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
    (hquotient : (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ),
      Function.Surjective ((p F).app (op n)) ∧
      LinearMap.ker ((p F).app (op n)).hom =
        I ^ (n + 1) • (⊤ : Submodule A
          ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
            (L.obj F).obj)))) :
    ∀ F, Nonempty ((L ⋙ coherentFormalModules_affine_quotientFunctor A I J hJ).obj F ≅ F) := by
  classical
  intro F
  let N := ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
    (L.obj F).obj)
  let T := tilde.functor (CommRingCat.of A)
  have hqc (n : ℕ) : (F.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp
      (F.property.1 n)).1
  have he (n : ℕ) : ∃ e : formalModuleQuotient J (n + 1) (T.obj N) ≅
      F.obj.obj (op n), formalModuleQuotientπ J (n + 1) (T.obj N) ≫ e.hom =
        T.map ((p F).app (op n)) ≫
          Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) (F.obj.obj (op n)) := by
    have := hqc n
    exact affineFormalQuotient_projection_iso A I J hJ N _ (n + 1)
      (Nat.zero_lt_succ n) ((p F).app (op n)) (hquotient F n).1 (hquotient F n).2
  choose e he using he
  let E : formalCompletionSystem J (T.obj N) ≅ F.obj :=
    NatIso.ofComponents (fun n ↦ e n.unop) (by
      intro a b f
      apply (cancel_epi (cokernel.π
        (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι
          (a.unop + 1)).2 (T.obj N)))).1
      change formalModuleQuotientπ J (a.unop + 1) (T.obj N) ≫
        formalModuleQuotientMap J (𝟙 (T.obj N))
          (Nat.succ_le_succ (leOfHom f.unop)) ≫ (e b.unop).hom =
        formalModuleQuotientπ J (a.unop + 1) (T.obj N) ≫
          (e a.unop).hom ≫ F.obj.map f
      rw [← Category.assoc]
      simp only [formalModuleQuotientπ, formalModuleQuotientMap, cokernel.π_desc,
        Category.id_comp]
      change formalModuleQuotientπ J (b.unop + 1) (T.obj N) ≫ (e b.unop).hom =
        formalModuleQuotientπ J (a.unop + 1) (T.obj N) ≫
          (e a.unop).hom ≫ F.obj.map f
      rw [he b.unop, ← Category.assoc, he a.unop, Category.assoc]
      have hc := (Scheme.Modules.fromTildeΓNatTrans
        (R := CommRingCat.of A)).naturality (F.obj.map f)
      change T.map ((moduleSpecΓFunctor (R := CommRingCat.of A)).map (F.obj.map f)) ≫
        Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) (F.obj.obj b) =
        Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) (F.obj.obj a) ≫
          F.obj.map f at hc
      rw [← hc]
      rw [← Category.assoc, ← T.map_comp]
      congr 1
      simpa using congrArg T.map ((p F).naturality f))
  exact ⟨(IsCoherentFormalModule J).isoMk E⟩
end AlgebraicGeometry
