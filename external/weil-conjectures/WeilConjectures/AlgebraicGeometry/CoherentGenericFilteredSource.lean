/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentGenericLocalFreeModel
import WeilConjectures.AlgebraicGeometry.CoherentLocalFreeIdealLattice
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationIdealSumZero
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationBiproductSucc
import WeilConjectures.AlgebraicGeometry.PushforwardFinSumSuccIso
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # A filtered source surjecting at a generic stalk

Source: Stacks Project, Tags 01YE and 01YF, generic ideal inclusion and its source filtration.
(blueprint: lem-pc-s3-coherent-generic-filtered-source)
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
private theorem pushforward_ideal_sum_map_eq_zero_of_generic_stalk
    {X W : Scheme.{u}} (i : W ⟶ X) [IsIntegral W]
    (r : ℕ) (J : W.IdealSheafData) {F : X.Modules}
    (f : F ⟶ (pushforward i).obj (∐ fun _ : Fin r ↦ J.toModules))
    (hf : (RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint W))).map f = 0) : f = 0 := by
  let D : Fin r → W.Modules := fun _ ↦ J.toModules
  have : HasBiproduct D := .of_hasCoproduct _
  have : HasBiproduct ((pushforward i).obj ∘ D) := .of_hasCoproduct _
  have : PreservesBiproductsOfShape (Fin r) (pushforward i) :=
    preservesBiproductsOfShape_of_preservesProductsOfShape (pushforward i)
  let E := (pushforward i).mapIso (biproduct.isoCoproduct D).symm ≪≫
    (pushforward i).mapBiproduct D
  apply (cancel_mono E.hom).mp
  rw [zero_comp]
  apply biproduct.hom_ext
  intro j
  rw [zero_comp]
  let fj := (f ≫ E.hom) ≫ biproduct.π _ j
  have hfj : (RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint W))).map fj = 0 := by
    simp only [fj, Functor.map_comp, hf, zero_comp]
  change fj = 0
  let O := (SheafOfModules.unit W.ringCatSheaf : W.Modules)
  let g : F ⟶ (pushforward i).obj O := fj ≫ (pushforward i).map J.toModulesι
  have hg : (RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint W))).map g = 0 := by
    simp [g, hfj]
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

open CategoryTheory.Limits in
private theorem mono_of_pushforward_ideal_sum_generic_iso
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsIntegral Z]
    (r : ℕ) (I : Z.IdealSheafData) {F : X.Modules}
    (α : (pushforward i).obj (∐ fun _ : Fin r => I.toModules) ⟶ F)
    (hα : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint Z))).map α)) : Mono α := by
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint Z))
  have : IsIso (T.map α) := hα
  apply Abelian.mono_of_kernel_ι_eq_zero
  apply pushforward_ideal_sum_map_eq_zero_of_generic_stalk i r I
  apply (cancel_mono (T.map α)).mp
  rw [← T.map_comp, kernel.condition, T.map_zero, zero_comp]

open CategoryTheory.Limits in
private theorem coherent_ideal_sum_filtration
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : Z.IdealSheafData) (hne : I ≠ ⊥)
    (hI : RingedSpace.IsCoherent Z.toRingedSpace I.toModules)
    (hA : RingedSpace.IsCoherent X.toRingedSpace ((pushforward i).obj I.toModules))
    (r : ℕ) : HasCoherentIntegralFiltration
      ((pushforward i).obj (∐ fun _ : Fin r => I.toModules)) := by
  induction r with
  | zero => exact coherentIntegralFiltration_ideal_sum_zero i I
  | succ r ih =>
    have hAw : ∃ (Z' : Scheme.{u}) (j : Z' ⟶ X),
        IsClosedImmersion j ∧ IsIntegral Z' ∧
        ∃ J : Z'.IdealSheafData, J ≠ ⊥ ∧
          RingedSpace.IsCoherent Z'.toRingedSpace J.toModules ∧
          Nonempty ((pushforward i).obj I.toModules ≅ (pushforward j).obj J.toModules) :=
      ⟨Z, i, inferInstance, inferInstance, I, hne, hI, ⟨Iso.refl _⟩⟩
    obtain ⟨e⟩ := pushforward_fin_sum_succ_iso i r I
    exact hasCoherentIntegralFiltration_of_biproduct _ _ _ ih hA hAw e

/-- Construct only the filtered source of the generic inclusion, without constructing
its cokernel or asserting anything about the target's support.

Source: Stacks Project, Tag 01YE (`lemma-prepare-filter-irreducible`), and Tag 01YF
(`lemma-coherent-filter`), final paragraph.
(blueprint: lem-pc-s3-coherent-generic-filtered-source)

Proof: apply the generic-point ideal inclusion to i and F, obtaining a coherent ideal
I on Z, a finite number r of copies, and a monomorphism from their pushforward to F
which is invertible on an open neighbourhood of i(genericPoint Z). The stalk at this
point is nonzero by hx. If I were zero, its finite sum and pushforward would be zero,
contradicting hx via the bijective generic stalk map. Thus I is nonzero. Finite-sum
coherence and finite closed-pushforward coherence make A coherent. Filter A by the first k summands,
for k = 0,...,r. Each consecutive quotient is the pushforward of I from the integral
closed subscheme Z, so the ideal-sum filtration theorem gives the required coherent
integral filtration. The isomorphism on the neighbourhood induces a bijective stalk
map, and in particular a surjective one. This constructs A and its map; no cokernel,
short exact sequence, support containment, or support induction is used here.

Edge cases: hx excludes a zero target stalk and therefore excludes I = 0 and r = 0.
No assertion that F is supported on the image of i is required: the construction
concerns only its generic stalk, and sections away from that image remain in F. -/
theorem coherent_generic_filtered_source
    {X Z : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hx : ¬ Subsingleton (F.presheaf.stalk (i.base (genericPoint Z))))
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal
      (X.presheaf.stalk (i.base (genericPoint Z))),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint Z))).obj F, a • m = 0) :
    ∃ (A : X.Modules) (f : A ⟶ F), Mono f ∧
      RingedSpace.IsCoherent X.toRingedSpace A ∧ HasCoherentIntegralFiltration A ∧
      Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint Z))).map f) := open CategoryTheory.Limits in by
  obtain ⟨r, U, hxU, ⟨e⟩⟩ := coherent_generic_local_free_model i F hF hkill
  obtain ⟨I, hI, hι, α, hα⟩ :=
    coherent_local_free_ideal_lattice i F hF r U e.hom
  have : IsIso ((restrictFunctor U.ι).map
      ((pushforward i).map (Sigma.desc (fun j : Fin r ↦ I.toModulesι ≫
          Sigma.ι (fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf) j)))) := hι
  have : IsIso ((restrictFunctor U.ι).map α) := by
    rw [hα]
    infer_instance
  have hbij : Function.Bijective ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint Z))).map α) :=
    bijective_stalk_of_isIso_restrict α _ hxU
  have hiso : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint Z))).map α) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hmono := mono_of_pushforward_ideal_sum_generic_iso i r I α hiso
  have hsurj := hbij.2
  have hne : I ≠ ⊥ := by
    intro hbot
    have hzI : IsZero I.toModules := by
      apply isZero_of_forall_affineOpens
      intro V
      refine ⟨fun a b ↦ ?_⟩
      apply I.injective_toModulesι_app V.1
      have zero (a : Γ(I.toModules, V.1)) : I.toModulesι.app V.1 a = 0 := by
        have ha : I.toModulesι.app V.1 a ∈ (I.ideal V : Set Γ(Z, V.1)) := by
          rw [← I.range_toModulesι_app V]
          exact Set.mem_range_self a
        simpa [hbot] using ha
      exact (zero a).trans (zero b).symm
    have hzsum : IsZero (∐ fun _ : Fin r => I.toModules) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply Sigma.hom_ext
      intro j
      exact hzI.eq_of_src _ _
    have hzA := (pushforward i).map_isZero hzsum
    have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint Z))).obj
        ((pushforward i).obj (∐ fun _ : Fin r => I.toModules))) :=
      ModuleCat.subsingleton_of_isZero
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint Z))).map_isZero hzA)
    exact hx hsurj.subsingleton
  have hr : 0 < r := by
    by_contra hn
    have heq : r = 0 := Nat.eq_zero_of_not_pos hn
    have hzsum : IsZero (∐ fun _ : Fin r => I.toModules) := by
      subst r
      apply (IsZero.iff_id_eq_zero _).mpr
      apply Sigma.hom_ext
      intro j
      exact Fin.elim0 j
    have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint Z))).obj
        ((pushforward i).obj (∐ fun _ : Fin r => I.toModules))) :=
      ModuleCat.subsingleton_of_isZero
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint Z))).map_isZero ((pushforward i).map_isZero hzsum))
    exact hx hsurj.subsingleton
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  have : I.toModules.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType Z I.toModules).mp hI).1
  have hq : ((pushforward i).obj I.toModules).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated i I.toModules
  have : Mono α := hmono
  have : HasBiproduct (fun _ : Fin r ↦ I.toModules) := .of_hasCoproduct _
  let j : I.toModules ⟶ (∐ fun _ : Fin r => I.toModules) :=
    Sigma.ι (fun _ : Fin r => I.toModules) ⟨0, hr⟩
  let β := (pushforward i).map j ≫ α
  have hpush : RingedSpace.IsCoherent X.toRingedSpace ((pushforward i).obj I.toModules) :=
    ((isCoherent_kernel_cokernel_biprod_and_submodule X).2 F _ β hF
      inferInstance hq).1
  have hfil := coherent_ideal_sum_filtration i I hne hI hpush r
  have hsource : RingedSpace.IsCoherent X.toRingedSpace
      ((pushforward i).obj (∐ fun _ : Fin r => I.toModules)) := by
    obtain ⟨m, c, _, _, htop, hcc, _⟩ := hfil
    have ht := hcc (Fin.last m)
    rw [htop] at ht
    exact (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).2.2.2.2 _ _
      (asIso (⊤ : Subobject _).arrow) ht
  exact ⟨_, α, hmono, hsource, hfil, hsurj⟩

end AlgebraicGeometry.Scheme.Modules
