/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.CategoryTheory.Subobject.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.IntegralIdealCommonSubmodule
import WeilConjectures.AlgebraicGeometry.FinitePresentationIntegralFiltration
import WeilConjectures.CategoryTheory.FiniteFiltrationRefinement
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Comparing an integral ideal with a module of generic rank one

Source: Stacks Project, Cohomology of Schemes, Tags 01YF and 01YH.
(blueprint: lem-pc-v3-integral-ideal-comparison-filtrations)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The zero ideal gives a zero module: all germs vanish on affine neighborhoods. -/
private theorem ideal_bot_isZero (Z : Scheme.{u}) :
    IsZero (⊥ : Z.IdealSheafData).toModules := by
  let J : Z.IdealSheafData := ⊥
  let F := J.toModules.presheaf
  let T := SheafOfModules.toSheaf Z.ringCatSheaf
  have hz : IsZero (T.obj J.toModules) := by
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro x
    have hzero (m : F.stalk x) : m = 0 := by
      obtain ⟨V, hxV, m, rfl⟩ := F.exists_germ_eq m
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
        Z.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
      have hm : J.toModulesι.app W (F.map (homOfLE hWV).op m) = 0 := by
        have hr : J.toModulesι.app W (F.map (homOfLE hWV).op m) ∈ J.ideal ⟨W, hW⟩ := by
          change _ ∈ (J.ideal ⟨W, hW⟩ : Set Γ(Z, W))
          rw [← J.range_toModulesι_app ⟨W, hW⟩]
          exact ⟨_, rfl⟩
        simpa [J, IdealSheafData.ideal_bot] using hr
      have hm0 := J.injective_toModulesι_app W (hm.trans (map_zero _).symm)
      rw [← F.germ_res_apply (homOfLE hWV) x hxW m]
      exact (congrArg (F.germ W x hxW) hm0).trans (map_zero (F.germ W x hxW).hom)
    have : Subsingleton (F.stalk x) := ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩
    change IsZero (F.stalk x)
    exact AddCommGrpCat.isZero_of_subsingleton _
  rw [IsZero.iff_id_eq_zero]
  apply T.map_injective
  rw [T.map_id, T.map_zero]
  exact hz.eq_of_src _ _

/-- Delete zero factors from the existing finite-presentation integral filtration,
using empty filtrations for zero quotients and finite filtration refinement. -/
private theorem exists_finitePresentation_nonzero_integral_filtration
    (X : Scheme.{u}) [IsNoetherian X] (F : X.Modules)
    [F.IsFinitePresentation] :
    ∃ (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c),
      c 0 = ⊥ ∧ c (Fin.last m) = ⊤ ∧
      ∀ j : Fin m, ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
        IsClosedImmersion i ∧ IsIntegral Z ∧ ∃ I : Z.IdealSheafData,
          I ≠ ⊥ ∧ Nonempty (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
            (hc j.castSucc_le_succ)) ≅ (pushforward i).obj I.toModules) := by
  classical
  let P : X.Modules → Prop := fun Q ↦
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧ IsIntegral Z ∧
      ∃ I : Z.IdealSheafData, I ≠ ⊥ ∧ Nonempty (Q ≅ (pushforward i).obj I.toModules)
  have hP : ∀ (A B : X.Modules), Nonempty (A ≅ B) → P A → P B := by
    rintro A B ⟨e⟩ ⟨Z, i, hi, hZ, I, hI, ⟨f⟩⟩
    exact ⟨Z, i, hi, hZ, I, hI, ⟨e.symm ≪≫ f⟩⟩
  obtain ⟨m, c, hc, hbot, htop, hfactors⟩ :=
    exists_finitePresentation_integral_filtration X F
  apply finite_filtration_refinement P hP F m c hc hbot htop
  intro k
  obtain ⟨Z, i, hi, hZ, I, ⟨e⟩⟩ := hfactors k
  by_cases hI : I = ⊥
  · have hz : IsZero (cokernel (Subobject.ofLE (c k.castSucc) (c k.succ)
        (hc k.castSucc_le_succ))) := by
      apply IsZero.of_iso _ e
      subst I
      exact (pushforward i).map_isZero (ideal_bot_isZero Z)
    have := Subobject.subsingleton_of_isZero hz
    exact Or.inr ⟨0, fun _ ↦ ⊥, monotone_const, rfl,
      Subsingleton.elim _ _, fun j ↦ j.elim0⟩
  · exact Or.inl ⟨Z, i, hi, hZ, I, hI, ⟨e⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero integral-ideal subquotient has its entire closed image in the
support of the ambient coherent module: detect its generic stalk, then specialize. -/
private theorem integral_factor_support_subset (X Z : Scheme.{u}) [IsNoetherian X]
    (Q : X.Modules) (hQ : RingedSpace.IsCoherent X.toRingedSpace Q)
    (A B : Subobject Q) (hAB : A ≤ B) (j : Z ⟶ X)
    [IsClosedImmersion j] [IsIntegral Z] (J : Z.IdealSheafData) (hJ : J ≠ ⊥)
    (e : cokernel (Subobject.ofLE A B hAB) ≅ (pushforward j).obj J.toModules) :
    Set.range j.base ⊆ {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} := by
  classical
  obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X Q).mp hQ
  have := hq
  have := ht
  have hclosed := (finite_type_module_support_closed X Q).2.2.2
  have hgeneric : j.base (genericPoint Z) ∈
      {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} := by
    change ¬ Subsingleton (Q.presheaf.stalk (j.base (genericPoint Z)))
    intro hz
    have := hz
    let S : X.Modules ⥤ Ab.{u} := SheafOfModules.toSheaf X.ringCatSheaf ⋙
      (TopCat.Sheaf.forget Ab.{u} X.toTopCat ⋙
        TopCat.Presheaf.stalkFunctor (X := X.toTopCat) Ab.{u} (j.base (genericPoint Z)))
    have : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) :=
      (moduleSheaves_colimits_forgetful X.ringCatSheaf).2.1
    have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) :=
      (moduleSheaves_colimits_forgetful X.ringCatSheaf).2.2.1
    have : PreservesFiniteLimits
        (TopCat.Sheaf.forget Ab.{u} X.toTopCat ⋙
          TopCat.Presheaf.stalkFunctor (X := X.toTopCat) Ab.{u}
            (j.base (genericPoint Z))) :=
      TopCat.Sheaf.instPreservesFiniteLimitsCompPresheafForgetStalkFunctor _
    have : PreservesFiniteColimits
        (TopCat.Sheaf.forget Ab.{u} X.toTopCat ⋙
          TopCat.Presheaf.stalkFunctor (X := X.toTopCat) Ab.{u}
            (j.base (genericPoint Z))) := inferInstance
    have : PreservesFiniteLimits S := by
      exact comp_preservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf)
        (TopCat.Sheaf.forget Ab.{u} X.toTopCat ⋙
          TopCat.Presheaf.stalkFunctor (X := X.toTopCat) Ab.{u} (j.base (genericPoint Z)))
    have : PreservesFiniteColimits S := by
      exact comp_preservesFiniteColimits (SheafOfModules.toSheaf X.ringCatSheaf)
        (TopCat.Sheaf.forget Ab.{u} X.toTopCat ⋙
          TopCat.Presheaf.stalkFunctor (X := X.toTopCat) Ab.{u} (j.base (genericPoint Z)))
    have : Subsingleton (S.obj Q) := hz
    have hinj : Function.Injective (S.map B.arrow) :=
      (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    have hB : Subsingleton (S.obj (B : X.Modules)) := hinj.subsingleton
    have := hB
    have hsurj : Function.Surjective (S.map (cokernel.π (Subobject.ofLE A B hAB))) :=
      (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
    have hC : Subsingleton (S.obj (cokernel (Subobject.ofLE A B hAB))) :=
      hsurj.subsingleton
    have := hC
    have hP : Subsingleton (((pushforward j).obj J.toModules).presheaf.stalk
        (j.base (genericPoint Z))) :=
      (ConcreteCategory.bijective_of_isIso (S.map e.hom)).2.subsingleton
    have := hP
    change Subsingleton ((TopCat.Presheaf.pushforward Ab.{u} j.base).obj
      J.toModules.presheaf |>.stalk (j.base (genericPoint Z))) at hP
    have := hP
    have hc := ((closedImmersion_pushforward_stalks j j.isClosedEmbedding
      J.toModules).2.1 (genericPoint Z)).1
    have hZ : Subsingleton (J.toModules.presheaf.stalk (genericPoint Z)) :=
      hc.2.subsingleton
    have hn := (integral_ideal_generic_stalk Z J).2.2.2.1.mp hJ
    have : Nontrivial (J.toModules.presheaf.stalk (genericPoint Z)) := hn
    exact not_subsingleton _ hZ
  rintro x ⟨z, rfl⟩
  exact ((genericPoint_specializes z).map j.continuous).mem_closed
    hclosed hgeneric

-- The existential module structure is used implicitly in the finrank expression.
set_option linter.unusedVariables false in
/-- An ideal and a coherent module of generic rank one have a common submodule whose
 two cokernels admit integral-ideal filtrations on strictly smaller closed supports.
 The zero ideal is recorded separately. This statement involves no cohomology property.

Source: Stacks Project, Cohomology of Schemes, Tag 01YH, proof of
`lemma-property-irreducible`, and Tag 01YF, `lemma-coherent-filter`.
(blueprint: lem-pc-v3-integral-ideal-comparison-filtrations)

Proof: Split on whether the ideal pushforward is zero. In the nonzero case,
`exists_integral_ideal_common_submodule` supplies two monomorphisms with coherent
cokernels supported strictly inside the integral closed image. Their canonical
cokernel sequences are short exact in the abelian category of module sheaves.
Apply `exists_finitePresentation_integral_filtration` to each cokernel Q and delete
zero-ideal factors by replacing them with empty chains and using
`finite_filtration_refinement`.
For a factor isomorphic to j_*J with J nonzero, its generic stalk is nontrivial by
`integral_ideal_generic_stalk` and `closedImmersion_pushforward_stalks`. If Q vanished
at that generic point, the stalk of its subobject would vanish by injectivity, and
the factor stalk would vanish by surjectivity of the cokernel projection. Exactness
of the abelian-group stalk functor gives these two properties. This contradiction
places the generic point in the support of Q. That support is closed by coherence
and `finite_type_module_support_closed`, so every specialization of the generic
point also belongs to it. Thus j(W') is contained in Supp Q, which is strictly
contained in i(W); transitivity gives the required strict inclusion. The empty
filtration supplied for a zero cokernel has no factors to check. -/
theorem exists_integral_ideal_comparison_filtrations (X W : Scheme.{u})
    [IsNoetherian X] (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (G : X.Modules) (hGcoh : RingedSpace.IsCoherent X.toRingedSpace G)
    (hGsupp : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base)
    (hGann : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint W))),
      ∀ v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G, a • v = 0)
    (hGrank : ∃ inst : Module (X.residueField (i.base (genericPoint W)))
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G),
      (∀ (a : X.presheaf.stalk (i.base (genericPoint W)))
        (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).obj G),
        a • v = (X.residue (i.base (genericPoint W))) a • v) ∧
      Module.finrank (X.residueField (i.base (genericPoint W)))
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G)
        = 1)
    (I : W.IdealSheafData) :
    IsZero ((pushforward i).obj I.toModules) ∨
      ∃ (K Q₁ Q₂ : X.Modules) (a : K ⟶ G) (b : G ⟶ Q₁) (hab : a ≫ b = 0),
        (ShortComplex.mk a b hab).ShortExact ∧
        ∃ (d : K ⟶ (pushforward i).obj I.toModules)
          (e : (pushforward i).obj I.toModules ⟶ Q₂) (hde : d ≫ e = 0),
          (ShortComplex.mk d e hde).ShortExact ∧
          ∀ Q : X.Modules, Q = Q₁ ∨ Q = Q₂ →
            ∃ (m : ℕ) (c : Fin (m + 1) → Subobject Q) (hc : Monotone c),
              c 0 = ⊥ ∧ c (Fin.last m) = ⊤ ∧
              ∀ k : Fin m, ∃ (W' : Scheme.{u}) (j : W' ⟶ X),
                IsClosedImmersion j ∧ IsIntegral W' ∧
                ∃ J : W'.IdealSheafData, Set.range j.base ⊂ Set.range i.base ∧
                  Nonempty (cokernel (Subobject.ofLE (c k.castSucc) (c k.succ)
                    (hc k.castSucc_le_succ)) ≅ (pushforward j).obj J.toModules) := by
  classical
  by_cases hI : IsZero ((pushforward i).obj I.toModules)
  · exact Or.inl hI
  obtain ⟨K, a, d, ha, hd, hQ₁, hQ₂, hfp₁, hfp₂, hS₁, hS₂⟩ :=
    exists_integral_ideal_common_submodule X W i G hGcoh hGsupp hGann hGrank I hI
  have := ha
  have := hd
  refine Or.inr ⟨K, cokernel a, cokernel d, a, cokernel.π a, cokernel.condition a,
    { exact := ShortComplex.exact_cokernel a }, d, cokernel.π d, cokernel.condition d,
    { exact := ShortComplex.exact_cokernel d }, ?_⟩
  intro Q hQ
  have hcoh : RingedSpace.IsCoherent X.toRingedSpace Q := by
    rcases hQ with rfl | rfl
    · exact hQ₁
    · exact hQ₂
  have hsupp : {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} ⊂ Set.range i.base := by
    rcases hQ with rfl | rfl
    · exact hS₁
    · exact hS₂
  have hfp : Q.IsFinitePresentation := by
    rcases hQ with rfl | rfl
    · exact hfp₁
    · exact hfp₂
  have := hfp
  obtain ⟨m, c, hc, hbot, htop, hfactors⟩ :=
    exists_finitePresentation_nonzero_integral_filtration X Q
  refine ⟨m, c, hc, hbot, htop, ?_⟩
  intro k
  obtain ⟨W', j, hj, hW', J, hJ, ⟨e⟩⟩ := hfactors k
  have := hj
  have := hW'
  refine ⟨W', j, hj, hW', J, ?_, ⟨e⟩⟩
  exact lt_of_le_of_lt
    (integral_factor_support_subset X W' Q hcoh (c k.castSucc) (c k.succ)
      (hc k.castSucc_le_succ) j J hJ e) hsupp

end AlgebraicGeometry.Scheme.Modules
