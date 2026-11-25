/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Limits
import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineProjections
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # The inverse limit of affine sections of a formal module

Source: Stacks Project, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Sections on U of a module on the open subscheme U, regarded as a Γ(X,U)-module.
Source: Stacks Project, Lemma 087W, affine sections construction.
(blueprint: lem-weil-pbc-formal-affine-section-limit-full). -/
noncomputable def formalAffineSections (X : Scheme.{u}) (U : X.Opens) :
    U.toScheme.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  Scheme.Modules.pushforward U.ι ⋙ SheafOfModules.evaluation X.ringCatSheaf (op U)

/-- The tower of affine sections of an adic system, before taking its limit.
Source: Stacks Project, Lemma 087W.
(blueprint: lem-weil-pbc-formal-affine-section-limit-full). -/
noncomputable def formalAffineSectionTower (X : Scheme.{u}) (U : X.Opens)
    [IsNoetherian U.toScheme] (J : U.toScheme.IdealSheafData) :
    CoherentFormalModule U.toScheme J ⥤ (ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, U)) :=
  ObjectProperty.ι _ ⋙
    (Functor.whiskeringRight ℕᵒᵖ U.toScheme.Modules (ModuleCat.{u} Γ(X, U))).obj
      (formalAffineSections X U)

/-- The actual module limit of the affine section tower; no module witness is chosen.
Source: Stacks Project, Lemma 087W.
(blueprint: lem-weil-pbc-formal-affine-section-limit-full). -/
noncomputable def formalAffineSectionLimit (X : Scheme.{u}) (U : X.Opens)
    [IsNoetherian U.toScheme] (J : U.toScheme.IdealSheafData) :
    CoherentFormalModule U.toScheme J ⥤ ModuleCat.{u} Γ(X, U) :=
  formalAffineSectionTower X U J ⋙ lim

set_option backward.isDefEq.respectTransparency false in
private theorem sections_injective (Y : Scheme.{u}) [IsAffine Y]
    (W : Y.Opens) (hw : W = ⊤) {M N : Y.Modules} [M.IsQuasicoherent]
    {f g : M ⟶ N} (h : (SheafOfModules.evaluation Y.ringCatSheaf (op W)).map f =
      (SheafOfModules.evaluation Y.ringCatSheaf (op W)).map g) : f = g := by
  apply Scheme.Modules.hom_ext_of_isAffine
  have he : ∀ x : Γ(M, W), f.app W x = g.app W x :=
    fun x ↦ congrArg (fun k ↦ k x) h
  rw [← hw]
  exact he

private theorem sections_surjective (Y : Scheme.{u}) [IsAffine Y]
    (W : Y.Opens) (hw : W = ⊤) {M N : Y.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : (SheafOfModules.evaluation Y.ringCatSheaf (op W)).obj M ⟶
      (SheafOfModules.evaluation Y.ringCatSheaf (op W)).obj N) :
    ∃ g : M ⟶ N, (SheafOfModules.evaluation Y.ringCatSheaf (op W)).map g = f := by
  subst W
  obtain ⟨g, hg⟩ := Scheme.Modules.exists_hom_app_top_eq_of_isAffine f.hom
  refine ⟨g, ?_⟩
  ext x
  exact hg x

private theorem quotient_lift {A : Type u} [CommRing A]
    {M N P Q : ModuleCat.{u} A} (I : Ideal A)
    (p : M ⟶ P) (q : N ⟶ Q) (f : M ⟶ N)
    (hp : Function.Surjective p)
    (hpk : LinearMap.ker p.hom = I • (⊤ : Submodule A M))
    (hqk : LinearMap.ker q.hom = I • (⊤ : Submodule A N)) :
    ∃ g : P ⟶ Q, p ≫ g = f ≫ q := by
  have hk : LinearMap.ker p.hom ≤ LinearMap.ker (q.hom.comp f.hom) := by
    rw [hpk, LinearMap.ker_comp, hqk]
    exact Submodule.smul_top_le_comap_smul_top I f.hom
  let e := p.hom.quotKerEquivOfSurjective hp
  let g := (LinearMap.ker p.hom).liftQ (q.hom.comp f.hom) hk
  refine ⟨ModuleCat.ofHom (g.comp e.symm.toLinearMap), ?_⟩
  ext x
  change g (e.symm (p x)) = q (f x)
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On an affine open, the inverse limit of sections is fully faithful on coherent
formal modules. This concerns arbitrary formal systems and does not identify the
completion of any coherent module.

Source: Stacks Project, Lemma 087W, full faithfulness and the formula N/J^(n+1)N = N_n.
(blueprint: lem-weil-pbc-formal-affine-section-limit-full).

Proof: Identify U with Spec Γ(X,U) and its ideal with the ideal of global sections.
Lemma 087W identifies a formal system with a finite module over the completed ring;
its underlying Γ(X,U)-module is the inverse limit of its section tower. The same
lemma identifies the projections as surjections with kernel J^(n+1) times the limit.
Any Γ(X,U)-linear map between two limits preserves these kernels, hence descends
uniquely to maps on every quotient. The affine tilde/sections equivalence turns them
into sheaf maps between the levels. Surjectivity of the projections proves that the
maps commute with transitions. They therefore give a map of formal systems whose
limit is the given linear map. Conversely a map with zero limit has every component
zero, again by surjectivity, and the affine sections equivalence makes the sheaf map
zero. This proves fullness and faithfulness. The zero and unit ideals give respectively
constant and zero towers; the argument also covers the empty affine open. -/
theorem formalAffineSectionLimit_full_faithful (X : Scheme.{u})
    (U : X.Opens) [IsNoetherian U.toScheme] (hU : IsAffineOpen U)
    (J : U.toScheme.IdealSheafData) :
    (formalAffineSectionLimit X U J).Full ∧
      (formalAffineSectionLimit X U J).Faithful := by
  classical
  have : IsAffine U.toScheme := hU
  let W := U.ι ⁻¹ᵁ U
  have hw : W = ⊤ := U.ι_preimage_self
  have hW : IsAffineOpen W := hw.symm ▸ isAffineOpen_top U.toScheme
  let H := SheafOfModules.evaluation U.toScheme.ringCatSheaf (op W)
  let T := ObjectProperty.ι (IsCoherentFormalModule J) ⋙
    (Functor.whiskeringRight ℕᵒᵖ U.toScheme.Modules (ModuleCat.{u} Γ(U.toScheme, W))).obj H
  have hqc (F : CoherentFormalModule U.toScheme J) (n : ℕ) :
      (F.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp
      (F.property.1 n)).1
  have hp (F : CoherentFormalModule U.toScheme J) (n : ℕ) :=
    coherentFormalModule_affine_projections U.toScheme J F ⟨W, hW⟩ n
  have hepi (F : CoherentFormalModule U.toScheme J) (n : ℕ) :
      Epi (limit.π (T.obj F) (op n)) :=
    (ModuleCat.epi_iff_surjective _).mpr (hp F n).1
  have hFF : (T ⋙ lim).Full ∧ (T ⋙ lim).Faithful := by
    constructor
    · constructor
      intro F G f
      have ha (n : ℕ) : ∃ a : (T.obj F).obj (op n) ⟶ (T.obj G).obj (op n),
          limit.π (T.obj F) (op n) ≫ a = f ≫ limit.π (T.obj G) (op n) :=
        quotient_lift _ _ _ f (hp F n).1 (hp F n).2 (hp G n).2
      choose a ha using ha
      have hb (n : ℕ) : ∃ b : F.obj.obj (op n) ⟶ G.obj.obj (op n),
          H.map b = a n := by
        have hF := hqc F n
        have hG := hqc G n
        exact sections_surjective U.toScheme W hw
          (M := F.obj.obj (op n)) (N := G.obj.obj (op n)) (a n)
      choose b hb using hb
      let α : F.obj ⟶ G.obj :=
        { app := fun i ↦ b i.unop
          naturality := by
            intro i j v
            have := hqc F i.unop
            apply sections_injective U.toScheme W hw
            change H.map (F.obj.map v ≫ b j.unop) = H.map (b i.unop ≫ G.obj.map v)
            rw [H.map_comp, H.map_comp, hb, hb]
            have := hepi F i.unop
            apply (cancel_epi (limit.π (T.obj F) i)).1
            change limit.π (T.obj F) i ≫ ((T.obj F).map v ≫ a j.unop) =
              limit.π (T.obj F) i ≫ (a i.unop ≫ (T.obj G).map v)
            rw [← Category.assoc, limit.w, ha, ← Category.assoc, ha,
              Category.assoc, limit.w] }
      refine ⟨ObjectProperty.homMk α, ?_⟩
      apply limit.hom_ext
      intro i
      change limMap (T.map (ObjectProperty.homMk α)) ≫ limit.π (T.obj G) i =
        f ≫ limit.π (T.obj G) i
      rw [limMap_π]
      change limit.π (T.obj F) i ≫ H.map (b i.unop) = _
      rw [hb, ha]
    · constructor
      intro F G f g h
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext i
      have := hqc F i.unop
      apply sections_injective U.toScheme W hw
      have := hepi F i.unop
      apply (cancel_epi (limit.π (T.obj F) i)).1
      change limit.π (T.obj F) i ≫ (T.map f).app i =
        limit.π (T.obj F) i ≫ (T.map g).app i
      rw [← limMap_π, ← limMap_π]
      exact congrArg (fun a ↦ a ≫ limit.π (T.obj G) i) h
  
  have : (T ⋙ lim).Full := hFF.1
  have : (T ⋙ lim).Faithful := hFF.2
  let R := ModuleCat.restrictScalars (U.ι.app U).hom
  have : IsIso (U.ι.app U) := by
    rw [Scheme.Opens.ι_app_self]
    infer_instance
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (asIso (U.ι.app U)).commRingCatIsoToRingEquiv
  have : R.IsEquivalence := E.isEquivalence_functor
  let e : (T ⋙ lim) ⋙ R ≅ formalAffineSectionLimit X U J :=
    Functor.associator T lim R ≪≫ Functor.isoWhiskerLeft T (preservesLimitNatIso R)
  exact ⟨Functor.Full.of_iso e, Functor.Faithful.of_iso e⟩

end AlgebraicGeometry
