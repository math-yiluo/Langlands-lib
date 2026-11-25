/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SectionBoundaryExact
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

/-! # Canonical comparison maps for square-zero tensor boundaries

Source: Stacks Project, Tags 09MS, 08KS, and 01XC.
(blueprint: lem-sc-square-zero-ideal-tensor-unit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] RingedSpace.moduleCohomology
noncomputable section

/-- The adjunction comparison with Mathlib pullback. Source: Stacks Tag 0096.
(blueprint: lem-sc-square-zero-ideal-tensor-unit). -/
def boundaryPullbackComparison {X Z : Scheme.{u}} (j : Z ⟶ X) :
    tensorPullback j ≅ pullback j :=
  (Classical.choose (exists_tensorPullbackAdjunction j)).leftAdjointUniq
    (pullbackPushforwardAdjunction j)

/-- The tensor comparison induced by the monoidal Mathlib pullback.
Source: Stacks Tag 01CD. (blueprint: lem-sc-square-zero-ideal-tensor-unit). -/
def boundaryPullbackTensorIso {X Z : Scheme.{u}} (j : Z ⟶ X) (A B : X.Modules) :
    (tensorPullback j).obj (A ⊗ B) ≅
      (tensorPullback j).obj A ⊗ (tensorPullback j).obj B :=
  (boundaryPullbackComparison j).app (A ⊗ B) ≪≫
    (Functor.Monoidal.μIso (pullback j) A B).symm ≪≫
    (((boundaryPullbackComparison j).app A).symm ⊗ᵢ
      ((boundaryPullbackComparison j).app B).symm)

/-- Tensor powers of an isomorphism, including exponent zero.
Source: Stacks Tag 01CD. (blueprint: lem-sc-square-zero-ideal-tensor-unit). -/
def boundaryTensorPowIso {Z : Scheme.{u}} {A B : Z.Modules} (t : A ≅ B) :
    ∀ d : ℕ, A.tensorPow d ≅ B.tensorPow d
  | 0 => Iso.refl _
  | d + 1 => t ⊗ᵢ boundaryTensorPowIso t d

/-- The degreewise pullback comparison, with the canonical unit comparison in degree zero.
Source: Stacks Tag 01CD. (blueprint: lem-sc-square-zero-ideal-tensor-unit). -/
def boundaryPullbackPowIso {X Z : Scheme.{u}} (j : Z ⟶ X) (L : X.Modules) :
    ∀ d : ℕ, (tensorPullback j).obj (L.tensorPow d) ≅
      ((tensorPullback j).obj L).tensorPow d
  | 0 => (boundaryPullbackComparison j).app _ ≪≫ pullbackObjUnitIso j
  | d + 1 => boundaryPullbackTensorIso j L (L.tensorPow d) ≪≫
      (Iso.refl _ ⊗ᵢ boundaryPullbackPowIso j L d)

/-- The section-degree comparison. Source: Stacks Tag 09MS, graded ideal sequences.
(blueprint: lem-sc-square-zero-ideal-tensor-unit). -/
def boundarySectionDegreeIso {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) (n e : ℕ) :
    (tensorPullback j).obj (L.tensorPow (n * (e + 1))) ≅
      (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1) :=
  boundaryPullbackPowIso j L (n * (e + 1)) ≪≫
    ((tensorPullback j).obj L).tensorPowMulIso n (e + 1)

/-- The coefficient-degree comparison uses the generic tensor comparison, since the ideal
need not be invertible. Source: Stacks Tags 01CD and 09MS.
(blueprint: lem-sc-square-zero-ideal-tensor-unit). -/
def boundaryCoefficientDegreeIso {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) (n e : ℕ) :
    (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow (n * (e + 1))) ≅
      (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
        (((tensorPullback j).obj L).tensorPow n).tensorPow e :=
  (tensorPullback j).mapIso
      ((Iso.refl _ ⊗ᵢ L.tensorPowMulIso n (e + 1)) ≪≫ (α_ _ _ _).symm) ≪≫
    boundaryPullbackTensorIso j (j.ker.toModules ⊗ L.tensorPow n)
      ((L.tensorPow n).tensorPow e) ≪≫
    (Iso.refl _ ⊗ᵢ (boundaryPullbackPowIso j (L.tensorPow n) e ≪≫
      boundaryTensorPowIso (boundaryPullbackPowIso j L n) e))

/-- The multiplication inclusion is the kernel, with its canonical inclusion equation.
Source: Stacks Tags 08KS and 09MS. (blueprint: lem-sc-square-zero-ideal-tensor-unit).
Proof: the unit quotient theorem identifies its kernel with the image of multiplication.
Twisting the ideal inclusion by an invertible module is mono, so multiplication equals
its image up to the unique image isomorphism. Transport the limiting kernel fork along
that isomorphism, and compare adjunction units by uniqueness of left adjoints. -/
theorem boundaryIdealKernelIso_exists {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (M : X.Modules) [M.IsInvertible] :
    ∃ t : j.ker.toModules ⊗ M ≅
        kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app M),
      t.hom ≫ kernel.ι _ = j.ker.toModulesι ▷ M ≫ (λ_ M).hom := by
  let μ : j.ker.toModules ⊗ M ⟶ M := j.ker.toModulesι ▷ M ≫ (λ_ M).hom
  have : Mono μ := inferInstance
  obtain ⟨_, h, _⟩ := closedImmersion_unit_quotient j
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction j)
  obtain ⟨w, ⟨hk⟩⟩ := (h M).2.1
  have : Mono (factorThruImage μ) := mono_of_mono_fac (image.fac μ)
  have : IsIso (factorThruImage μ) := isIso_of_mono_of_epi _
  let hμ := IsKernel.isoKernel (adj.unit.app M) μ hk
    (asIso (factorThruImage μ)) (image.fac μ)
  let adj' := Classical.choose (exists_tensorPullbackAdjunction j)
  let t := (pushforward j).mapIso ((adj.leftAdjointUniq adj').app M)
  have hη : adj.unit.app M ≫ t.hom = adj'.unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app adj adj' M
  let hμ' := IsKernel.ofCompIso (adj.unit.app M) (adj'.unit.app M) t.symm
    (by rw [← hη]; simp) hμ
  let k := hμ'.conePointUniqueUpToIso (kernelIsKernel (adj'.unit.app M))
  refine ⟨k, ?_⟩
  exact IsLimit.conePointUniqueUpToIso_hom_comp hμ'
    (kernelIsKernel (adj'.unit.app M)) WalkingParallelPair.zero

/-- The kernel comparison is determined by its inclusion equation; no unspecified object
is selected. Source: Stacks Tag 09MS. (blueprint: lem-sc-square-zero-ideal-tensor-unit). -/
def boundaryIdealKernelIso {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (M : X.Modules) [M.IsInvertible] :
    j.ker.toModules ⊗ M ≅
      kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app M) :=
  Classical.choose (boundaryIdealKernelIso_exists j M)

/-- Square-zero annihilation makes the adjunction unit on every ideal tensor power invertible.
This statement concerns modules only, with no cohomology, section, or derivation assertion.

Source: Stacks Project, Tags 09MS and 08KS.
(blueprint: lem-sc-square-zero-ideal-tensor-unit).
Proof: on an affine open where L is free of rank one, identify I tensor L^d with I.
Multiplication by I is then zero because I squared is zero. This local calculation glues,
so I annihilates I tensor L^d on every open. The ideal is quasi-coherent, and twisting
by an invertible module preserves quasi-coherence. Apply the annihilated-module unit
isomorphism for the closed immersion. Degree zero is the right unitor case. -/
theorem square_zero_ideal_tensor_unit_isIso {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (d : ℕ) :
    IsIso ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
      (j.ker.toModules ⊗ L.tensorPow d)) := by
  have := SheafOfModules.isQuasicoherent_unit (R := j.ker.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((SheafOfModules.pushforward j.ker.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit j.ker.subscheme.ringCatSheaf)) :=
    isQuasicoherent_pushforward_of_isClosedImmersion j.ker.subschemeι _
  have : j.ker.toModules.IsQuasicoherent :=
    isQuasicoherent_kernel j.ker.toPushforwardSubscheme
  let M := L.tensorPow d
  let T := j.ker.toModules ⊗ M
  have : T.IsQuasicoherent := isQuasicoherent_tensorObj _ _
  let μ : T ⟶ M := j.ker.toModulesι ▷ M ≫ (λ_ M).hom
  have : Mono μ := inferInstance
  have haff (U : X.affineOpens) (a : Γ(X, U.1)) (ha : a ∈ j.ker.ideal U)
      (t : Γ(T, U.1)) : a • t = 0 := by
    have ht : μ.app U.1 t ∈ j.ker.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
      have hr := ((ideal_times_quasiCoherent_affine_sections j.ker M).2.2.2.1 U).1
      apply hr.subset
      refine ⟨(factorThruImage μ).app U.1 t, ?_⟩
      exact congrArg (fun k : T ⟶ M ↦ k.app U.1 t) (image.fac μ)
    have hz := Submodule.smul_mem_smul ha ht
    have hsq : j.ker.ideal U * j.ker.ideal U = ⊥ := by
      have h := congrArg (fun J : X.IdealSheafData ↦ J.ideal U) hI
      simpa only [IdealSheafData.ideal_pow, Pi.pow_apply, IdealSheafData.ideal_bot,
        Pi.bot_apply, pow_two, IdealSheafData.ideal_mul, Pi.mul_apply] using h
    rw [← Submodule.mul_smul, hsq, Submodule.bot_smul,
      Submodule.mem_bot] at hz
    have hinj := (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U.1)).map μ)).mp
      (inferInstance : Mono
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U.1)).map μ))
    apply hinj
    change μ.app U.1 (a • t) = μ.app U.1 0
    rw [Hom.app_smul, map_zero]
    exact hz
  apply ((closedImmersion_pushforward_annihilated j).2 T ?_).2.1
  intro V a ha t
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨T.presheaf, T.isSheaf⟩
    (fun i : {U : X.affineOpens // U.1 ≤ V} ↦ i.1.1) V
    (fun i ↦ homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩
  · intro i
    rw [map_zero]
    change T.val.map (homOfLE i.2).op (a • t) = 0
    rw [PresheafOfModules.map_smul]
    apply haff i.1
    obtain ⟨b, hb⟩ := (j.ker.range_toModulesι_app_eq_idealOfOpens V).superset ha
    rw [← hb]
    change (𝟙_ X.Modules).presheaf.map (homOfLE i.2).op
      (j.ker.toModulesι.app V b) ∈ j.ker.ideal i.1
    have hm := (j.ker.range_toModulesι_app i.1).subset
      ⟨j.ker.toModules.presheaf.map (homOfLE i.2).op b, rfl⟩
    have hn := Hom.app_presheaf_map j.ker.toModulesι (homOfLE i.2) b
    exact hn ▸ hm

/-- The cohomology comparison is constructed from the coefficient isomorphism, the inverse
closed-immersion edge, the inverse annihilated-module unit, and the kernel inclusion.
Source: Stacks Tags 09MS and 01XC. (blueprint: lem-sc-square-zero-ideal-tensor-unit). -/
def boundaryCoefficientCohomologyIso {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n e : ℕ) :
    AddCommGrpCat.of ((RingedSpace.moduleCohomology Z.toRingedSpace 1).obj
        (show Z.Modules from (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
          (((tensorPullback j).obj L).tensorPow n).tensorPow e)) ≅
      AddCommGrpCat.of ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        (kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
          (L.tensorPow (n * (e + 1)))))) := by
  let T := j.ker.toModules ⊗ L.tensorPow (n * (e + 1))
  have := SheafOfModules.isQuasicoherent_unit (R := j.ker.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((SheafOfModules.pushforward j.ker.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit j.ker.subscheme.ringCatSheaf)) :=
    isQuasicoherent_pushforward_of_isClosedImmersion j.ker.subschemeι _
  have : j.ker.toModules.IsQuasicoherent :=
    isQuasicoherent_kernel j.ker.toPushforwardSubscheme
  have : T.IsQuasicoherent := isQuasicoherent_tensorObj _ _
  have : ((tensorPullback j).obj T).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      ((boundaryPullbackComparison j).app T).symm
      (inferInstance : ((pullback j).obj T).IsQuasicoherent)
  have := square_zero_ideal_tensor_unit_isIso j L hI (n * (e + 1))
  have := ((affine_morphism_cohomology_edge j ((tensorPullback j).obj T)).2 1).1
  let HZ := RingedSpace.moduleCohomology Z.toRingedSpace 1 ⋙
    forget₂ _ AddCommGrpCat.{u}
  let HX := RingedSpace.moduleCohomology X.toRingedSpace 1 ⋙
    forget₂ _ AddCommGrpCat.{u}
  let k :=
    (HZ.mapIso (boundaryCoefficientDegreeIso j L n e).symm ≪≫
      (asIso (moduleCohomologyEdgeMap j ((tensorPullback j).obj T) 1)).symm ≪≫
      HX.mapIso (asIso
        ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app T)).symm ≪≫
      HX.mapIso (boundaryIdealKernelIso j (L.tensorPow (n * (e + 1)))))
  exact k

/-- A package of the section and coefficient comparison maps, including degree zero.
Source: Stacks Tag 09MS. (blueprint: lem-sc-square-zero-ideal-tensor-unit). -/
structure TensorBoundaryComparisonData {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) (n : ℕ) where
  a : ∀ e : ℕ, (tensorPullback j).obj (L.tensorPow (n * (e + 1))) ≅
    (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1)
  k : ∀ e : ℕ,
    AddCommGrpCat.of ((RingedSpace.moduleCohomology Z.toRingedSpace 1).obj
      (show Z.Modules from (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
        (((tensorPullback j).obj L).tensorPow n).tensorPow e)) ≅
    AddCommGrpCat.of ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
      (kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (L.tensorPow (n * (e + 1))))))

/-- The package is built from the explicit comparison constructions.
Source: Stacks Tag 09MS. (blueprint: lem-sc-square-zero-ideal-tensor-unit). -/
def canonicalTensorBoundaryComparisons {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) : TensorBoundaryComparisonData j L n where
  a := boundarySectionDegreeIso j L n
  k := boundaryCoefficientCohomologyIso j L hI n

end
end AlgebraicGeometry.Scheme.Modules
