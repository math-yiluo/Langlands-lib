/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentStalkMapExtends
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.LocalClosedIdealMapExtension

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem pushforward_ideal_map_eq_zero_of_generic_stalk
    {X W : Scheme.{u}} (i : W ⟶ X) [IsIntegral W]
    (J : W.IdealSheafData) {F : X.Modules}
    (f : F ⟶ (pushforward i).obj J.toModules)
    (hf : (RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint W))).map f = 0) : f = 0 := by
  let O := (SheafOfModules.unit W.ringCatSheaf : W.Modules)
  let g : F ⟶ (pushforward i).obj O := f ≫ (pushforward i).map J.toModulesι
  have hg : (RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint W))).map g = 0 := by
    simp [g, hf]
  have hsec (U : X.Opens) (s : Γ(F, U)) : g.app U s = 0 := by
    apply TopCat.Presheaf.section_ext W.sheaf (i ⁻¹ᵁ U) (g.app U s) 0
    intro z hz
    have hη : genericPoint W ∈ i ⁻¹ᵁ U :=
      ((genericPoint_spec W).mem_open_set_iff (i ⁻¹ᵁ U).isOpen).mpr ⟨z, trivial, hz⟩
    let P : TopCat.Presheaf Ab X.toTopCat := ((pushforward i).obj O).val.presheaf
    have he : P.germ U (i.base (genericPoint W)) hη (g.app U s) = 0 := by
      have he' := congrArg
        (fun k ↦ k.hom (TopCat.Presheaf.germ (X := X.toTopCat)
          F.val.presheaf U (i.base (genericPoint W)) hη s)) hg
      change (TopCat.Presheaf.stalkFunctor Ab (i.base (genericPoint W))).map
        ((PresheafOfModules.toPresheaf _).map g.val) _ = 0 at he'
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at he'
      exact he'
    rw [← map_zero (P.germ U (i.base (genericPoint W)) hη).hom] at he
    obtain ⟨V, hV, iU, iV, heq⟩ := P.germ_eq _ hη hη _ _ he
    change W.presheaf.map ((TopologicalSpace.Opens.map i.base).map iU).op (g.app U s) =
      W.presheaf.map ((TopologicalSpace.Opens.map i.base).map iV).op 0 at heq
    rw [map_zero] at heq
    have hz' : g.app U s = 0 :=
      map_injective_of_isIntegral W ((TopologicalSpace.Opens.map i.base).map iU)
        (H := ⟨⟨genericPoint W, hV⟩⟩) (heq.trans (map_zero _).symm)
    rw [hz', map_zero]
  ext U s
  apply J.injective_toModulesι_app (i ⁻¹ᵁ U)
  change g.app U s = J.toModulesι.app (i ⁻¹ᵁ U) 0
  rw [hsec, map_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem mono_of_pushforward_ideal_generic_injective
    {X W : Scheme.{u}} (i : W ⟶ X) [IsIntegral W]
    (J : W.IdealSheafData) {G : X.Modules}
    (α : (pushforward i).obj J.toModules ⟶ G)
    (hα : Function.Injective ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint W))).map α)) : Mono α := by
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))
  have : Mono (T.map α) := (ModuleCat.mono_iff_injective _).mpr hα
  apply Abelian.mono_of_kernel_ι_eq_zero
  apply pushforward_ideal_map_eq_zero_of_generic_stalk i J
  apply (cancel_mono (T.map α)).mp
  rw [← T.map_comp, CategoryTheory.Limits.kernel.condition, T.map_zero,
    CategoryTheory.Limits.zero_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem coherent_closed_pushforward_unit
    {X W : Scheme.{u}} [IsLocallyNoetherian X]
    (i : W ⟶ X) [IsClosedImmersion i] :
    RingedSpace.IsCoherent X.toRingedSpace
      ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) := by
  have := SheafOfModules.isQuasicoherent_unit (R := W.ringCatSheaf)
  let F := (pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)
  have hq : F.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated i _
  have hs (U : X.affineOpens) : Module.Finite Γ(X, U.1) Γ(F, U.1) := by
    let := (i.app U.1).hom.toAlgebra
    have : Module.Finite Γ(X, U.1) Γ(W, i ⁻¹ᵁ U.1) :=
      Module.Finite.of_surjective (Algebra.linearMap _ _) (i.app_surjective U.1 U.2)
    exact Module.Finite.equiv
      { AddEquiv.refl _ with map_smul' _ _ := rfl :
        Γ(W, i ⁻¹ᵁ U.1) ≃ₗ[Γ(X, U.1)] Γ(F, U.1) }
  have ht : F.IsFiniteType :=
    ((((quasicoherent_finite_type_affine.{u, u} X).2 F hq).2.1)
      X.affineOpens (fun U ↦ U.1) (iSup_affineOpens_eq_top X)
      (fun U ↦ U.2) hs).1
  exact (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mpr ⟨hq, ht⟩

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_map_apply_eq_restrict {X : Scheme.{u}} {F G : X.Modules}
    (α : F ⟶ G) (U : X.Opens) (x : X) (hx : x ∈ U)
    (m : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map α m =
      ConcreteCategory.hom ((restrictStalkNatIso U.ι (⟨x, hx⟩ : (U : Scheme))).hom.app G)
        ((RingedSpace.moduleStalkFunctor (U : Scheme).toRingedSpace
          (⟨x, hx⟩ : (U : Scheme))).map ((restrictFunctor U.ι).map α)
          (ConcreteCategory.hom ((restrictStalkNatIso U.ι
            (⟨x, hx⟩ : (U : Scheme))).inv.app F) m)) := by
  have h := ConcreteCategory.congr_hom
    ((restrictStalkNatIso U.ι (⟨x, hx⟩ : (U : Scheme))).hom.naturality α)
    (ConcreteCategory.hom ((restrictStalkNatIso U.ι
      (⟨x, hx⟩ : (U : Scheme))).inv.app F) m)
  simp only [ConcreteCategory.comp_apply] at h
  have hm := ConcreteCategory.congr_hom
    ((restrictStalkNatIso U.ι (⟨x, hx⟩ : (U : Scheme))).inv_hom_id_app F) m
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hm
  rw [hm] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- A prescribed injective generic stalk map from a closed pushforward of the
structure module extends after restricting its source to a nonzero ideal.
Source: Stacks Project, Tags 01Y4, 01YB and 01YE, extending stalk maps and
clearing denominators in the ideal-lattice construction.
(blueprint: new-generic-ideal-stalk-embedding-extension)

Proof: the closed pushforward of the structure module is coherent because the
closed immersion is finite and X is Noetherian. Extend the prescribed stalk map
on a neighbourhood of the image of the generic point (01Y4). Choose the reduced
ideal of its closed complement and extend the local map from a sufficiently high
power of that ideal times the source (01YB). On affine opens, multiplication of
this ideal with i_*O_W is the pushforward of its image ideal on W; thus the source
is i_*J. Near the generic point the complement ideal is the unit ideal, so J has
full generic stalk and is nonzero. The extension agrees with the prescribed map
on that stalk, giving the displayed equation. Its kernel is a quasi-coherent
submodule of i_*J. The defining ideal of W annihilates this kernel, so it descends
to a quasi-coherent submodule of J on W. Injectivity of the prescribed generic map
makes its generic stalk zero. A quasi-coherent submodule of an ideal on an
integral scheme with zero generic stalk is zero: on every nonempty affine open it
is a submodule of a domain and injects into its fraction field. The kernel is
therefore zero and the extended map is mono. The construction uses no rank or
maximal-ideal-annihilation hypothesis on G. -/
theorem generic_ideal_stalk_embedding_extension {X W : Scheme.{u}} [IsNoetherian X]
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (G : X.Modules) (hGcoh : RingedSpace.IsCoherent X.toRingedSpace G)
    (ψ : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj ((pushforward i).obj
          (SheafOfModules.unit W.ringCatSheaf)) ⟶
      (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G)
    (hψ : Function.Injective ψ) :
    ∃ (J : W.IdealSheafData), J ≠ ⊥ ∧
      ∃ (α : (pushforward i).obj J.toModules ⟶ G), Mono α ∧
        (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).map α =
        (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).map ((pushforward i).map J.toModulesι) ≫ ψ := by
  let H := (pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)
  let x := i.base (genericPoint W)
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  obtain ⟨U, hx, φ, hφ⟩ := exists_open_hom_of_coherent_stalk_map G H hGcoh
    (coherent_closed_pushforward_unit i) x ψ
  obtain ⟨J, hJ, α, hαU⟩ := local_closed_ideal_map_extension i G hGcoh U hx φ
  let j := (pushforward i).map J.toModulesι
  have hα : T.map α = T.map j ≫ ψ := by
    ext m
    rw [stalk_map_apply_eq_restrict α U x hx m, hαU]
    rw [Functor.map_comp]
    simp only [ConcreteCategory.comp_apply]
    change _ = ψ (T.map j m)
    rw [hφ]
    congr 2
    have h := ConcreteCategory.congr_hom
      ((restrictStalkNatIso U.ι (⟨x, hx⟩ : (U : Scheme))).inv.naturality j) m
    simp only [ConcreteCategory.comp_apply] at h
    exact h.symm
  refine ⟨J, hJ, α, ?_, hα⟩
  apply mono_of_pushforward_ideal_generic_injective i J α
  rw [hα]
  apply hψ.comp
  change Function.Injective ((TopCat.Presheaf.stalkFunctor Ab x).map j.mapPresheaf)
  exact TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
    (fun V ↦ J.injective_toModulesι_app (i ⁻¹ᵁ V)) x

end AlgebraicGeometry.Scheme.Modules
