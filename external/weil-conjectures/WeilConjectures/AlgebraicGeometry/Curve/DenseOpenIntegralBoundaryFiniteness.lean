/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology


public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Curve.DenseIrreducibleOpens
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalSectionsStalks
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomologyExtension
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-! # Finite cohomology of the dense-open boundary

Source: Stacks Project, Tags 0GJA and 095L.
(blueprint: lem-pbc-h2-dense-open-integral-boundary-finiteness). -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve

/-- Lift a geometric point into its constructible stratum and use the finite set stalk
there. Forgetting abelian groups and inverse image both commute with geometric stalks.
Source: Stacks Project, Tags 03RW and 03Q1. -/
private theorem finite_constructible_stalk {X : Scheme.{u}}
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj A))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Finite (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj A) := by
  classical
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  obtain ⟨S, hS⟩ := hA
  have hx : s (IsLocalRing.closedPoint Ω) ∈ ⋃ j, S.stratum j := by
    rw [S.iUnion_stratum_eq_univ]; trivial
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  have : LocallySmall.{u} (S.domain j).Etale := locallySmall_self _
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  rw [← S.range_immersion j] at hj
  obtain ⟨t, ht⟩ := Scheme.exists_comp_eq_of_mem_range (S.immersion j) s
    (by simpa using hj)
  have hfin : Finite (((Scheme.pointSmallEtale t).sheafFiber).obj
      ((Scheme.etaleSetPullback (S.immersion j)).obj
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj A))) :=
    (hS j).finite_sheafFiber Ω t
  let ea := (etaleInverseImageAlgebraicStructures (S.domain j) X (S.immersion j)).2.choose
  let e₁ := (Scheme.pointSmallEtale t).sheafFiber.mapIso (ea.app A)
  let e₂ := ((Scheme.pointSmallEtale t).sheafFiberCompIso
    (forget AddCommGrpCat.{u + 1})).app
      ((Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion j)).obj A)
  let e₃ := (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
    (S.immersion j) t).app A
  have hfin' : Finite (((Scheme.pointSmallEtale t).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion j)).obj A)) :=
    @Finite.of_equiv _ _ hfin ((e₁.symm ≪≫ e₂).toEquiv)
  have hfin'' : Finite (((Scheme.pointSmallEtale (t ≫ S.immersion j)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj A) :=
    @Finite.of_equiv _ _ hfin' e₃.addCommGroupIsoToAddEquiv.toEquiv
  rwa [ht] at hfin''

/-- The closed-boundary term of a constructible torsion sheaf on a curve has finite
cohomology in every degree.
Source: Stacks Project, Tag 0GJA, proof, and Tag 095L.
(blueprint: lem-pbc-h2-dense-open-integral-boundary-finiteness).

Proof: Density excludes every generic point from the closed complement Z. Since the
curve is Noetherian of dimension at most one, the reduced scheme underlying Z is a
finite disjoint union of closed points. Their residue fields are k, since k is
algebraically closed and the curve is of finite type. Nilpotent thickening does not
change the small etale topos. Finite direct image along Z -> X is exact; the Leray
comparison identifies the cohomology of Q = i_*i^*F with the cohomology of i^*F on Z.
The small etale topos of Spec k is the topos of sets, so its global sections functor
is exact. Hence positive cohomology is zero. H^0(Q) is the product of the finitely
many geometric stalks of F on Z. The coefficient encoding has the same underlying
abelian stalks as P.F, and constructibility as a set sheaf makes these finite.
Consequently H^0(Q) is finite, and the zero groups in positive degrees are finite.
When Z is empty, its direct image is zero and the same conclusion holds. -/
theorem dense_open_integral_boundary_finiteness {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let Q := (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      U.closedComplement).obj
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.closedComplement).obj F)
    ∀ q : ℕ, Finite (Sheaf.H
      ((sheafCompose P.C.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj Q) q) := by
  classical
  dsimp only
  have : IsCurve P.toSpec := P.isCurve
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
  let T := sheafCompose P.C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let eF : T.obj F ≅ P.F :=
    { hom := ⟨Functor.whiskerLeft P.F.obj
        (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.counitIso.hom⟩
      inv := ⟨Functor.whiskerLeft P.F.obj
        (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.counitIso.inv⟩
      hom_inv_id := by ext V; simp; rfl
      inv_hom_id := by ext V; simp }
  let Z := (Scheme.IdealSheafData.vanishingIdeal
    ⟨(U : Set P.C)ᶜ, U.isOpen.isClosed_compl⟩).subscheme
  let i : Z ⟶ P.C := U.closedComplement
  have hdim : topologicalKrullDim Z ≤ 0 := by
    obtain ⟨n, V, hVU, _, _, _, hVdim, _⟩ := exists_dense_irreducible_opens P.toSpec U hU
    let b : Z → ↥(⋃ a, (V a : Set P.C))ᶜ := fun z ↦ ⟨i.base z, by
      have hz : i.base z ∈ (U : Set P.C)ᶜ := U.range_closedComplement ▸ ⟨z, rfl⟩
      intro hv
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hv
      exact hz (hVU a ha)⟩
    have hb : Topology.IsInducing b :=
      (Topology.IsInducing.of_comp_iff Topology.IsInducing.subtypeVal).mp
        i.isClosedEmbedding.isInducing
    exact hb.topologicalKrullDim_le.trans hVdim
  let B := (sheafCompose Z.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
      ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) i).obj F)
  obtain ⟨eB⟩ := Etale.pullback_forget_modules_iso (ULift.{u + 1} ℤ) i F
  let eA : B ≅ (Etale.upperStar AddCommGrpCat.{u + 1} i).obj P.F :=
    eB ≪≫ (Etale.upperStar AddCommGrpCat.{u + 1} i).mapIso eF
  intro q
  change Finite (Sheaf.H ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj B) q)
  have hB : Finite (Sheaf.H B q) := by
    cases q with
    | zero =>
      let : Z.Over (Spec (.of k)) := ⟨i ≫ P.toSpec⟩
      have : IsSeparated (Z ↘ Spec (.of k)) := by
        change IsSeparated (i ≫ P.toSpec)
        infer_instance
      have : LocallyOfFiniteType (Z ↘ Spec (.of k)) := by
        change LocallyOfFiniteType (i ≫ P.toSpec)
        infer_instance
      have : QuasiCompact (Z ↘ Spec (.of k)) := by
        change QuasiCompact (i ≫ P.toSpec)
        infer_instance
      obtain ⟨hZ, hΓ, _⟩ := Scheme.zeroDimensional_sections_stalks k Z hdim
        (fun z ↦ AlgebraicClosure (Z.residueField z)) Z.algClosurePoint
        (fun z ↦ Z.algClosurePoint_base z default)
      have : Finite Z := hZ
      let M : Z → AddCommGrpCat.{u + 1} := fun z ↦
        (Scheme.pointSmallEtale (Z.algClosurePoint z)).sheafFiber.obj B
      have hM (z : Z) : Finite (M z) := by
        let e₁ := (Scheme.pointSmallEtale (Z.algClosurePoint z)).sheafFiber.mapIso eA
        let e₂ := (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
          i (Z.algClosurePoint z)).app P.F
        have h := finite_constructible_stalk P.F hP _ (Z.algClosurePoint z ≫ i)
        exact @Finite.of_equiv _ _ h
          ((e₁ ≪≫ e₂).addCommGroupIsoToAddEquiv.toEquiv.symm)
      let (z : Z) : Finite (M z) := hM z
      have : Finite (↑(∏ᶜ M)) :=
        Finite.of_injective (fun (x : ↑(∏ᶜ M)) (z : Discrete Z) ↦ Limits.Pi.π M z.as x)
          (Limits.Concrete.to_product_injective_of_isLimit
          (Discrete.functor M) (Limits.productIsProduct M))
      let γ : B.obj.obj (Opposite.op (Scheme.Etale.mk (𝟙 Z))) ⟶ ∏ᶜ M :=
        Limits.Pi.lift (fun z : Z ↦
          (Scheme.pointSmallEtale (Z.algClosurePoint z)).toPresheafFiber
            (Scheme.Etale.mk (𝟙 Z))
            (Over.homMk (Z.algClosurePoint z) (Category.comp_id _)) B.obj)
      have : IsIso γ := hΓ B
      have hsections : Finite (B.obj.obj (Opposite.op (Scheme.Etale.mk (𝟙 Z)))) :=
        Finite.of_injective γ ((AddCommGrpCat.mono_iff_injective γ).mp inferInstance)
      exact @Finite.of_equiv _ _ hsections
        (Sheaf.H.equiv₀ B (MorphismProperty.Over.mkIdTerminal _ _)).toEquiv.symm
    | succ n =>
      have h := (zero_dimensional_etale_cohomology k Z (i ≫ P.toSpec) hdim B
        (fun z ↦ AlgebraicClosure (Z.residueField z)) Z.algClosurePoint
        (fun z ↦ Z.algClosurePoint_base z default)).2.1 (n + 1) (Nat.zero_lt_succ n)
      let e := (Scheme.nonempty_sheafH_extDerivedIso Z (n + 1)).some.app B
      have : Subsingleton (Sheaf.H B (n + 1)) := by
        constructor
        intro x y
        exact e.addCommGroupIsoToAddEquiv.injective (h.elim _ _)
      infer_instance
  have : Finite (Sheaf.H ((𝟭 _).obj B) q) := hB
  exact Finite.of_injective _ (Etale.bijective_edgeMap_of_isFinite i B q).injective

end AlgebraicGeometry.IsCurve
