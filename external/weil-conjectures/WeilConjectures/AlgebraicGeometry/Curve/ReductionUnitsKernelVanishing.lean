/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsFiltration
import WeilConjectures.AlgebraicGeometry.EtaleQcoherentCohomologyULift
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianZariskiCohomology
import WeilConjectures.AlgebraicGeometry.ZariskiDimensionBound
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-! # Degree-two vanishing for the infinitesimal units kernel on a curve

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-kernel-h2)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

/-- The kernel of the units comparison on the reduction of a curve has zero H^2.
Source: literature/blueprint/master/blueprint/sec-curve-estimates/lem-sc-second-kummer-divisors/
lem-sc-brauer-zero-all-curves.md, Proof, Step 1 and the following Claim.
(blueprint: lem-sc-reduction-units-kernel-h2)

Proof: Finite type over a field makes C Noetherian. The coherent nilradical N is
nilpotent, with N^m = 0 for a uniform m found on a finite affine cover. On an affine
etale V over C, flatness identifies the pulled-back N with the reduction ideal.
Consequently the kernel of G_m,C -> i_*G_m,C_red is 1 + N_et. Filter it by 1 + N^j
for j >= 1. The successive quotients are the additive quasi-coherent sheaves
(N^j/N^(j+1))_et: multiplication becomes addition because ab belongs to N^(j+1).
Their H^q vanishes for q >= 2. Indeed, a finite affine cover has affine intersections
by separatedness; affine etale acyclicity and the Cech spectral sequence compare
etale cohomology with Zariski cohomology. Grothendieck vanishing gives zero in degrees
above dim C <= 1. The long exact sequences of the filtration, descending from
1 + N^m = 0, now give H^2(C,1 + N_et) = 0. Reduction induces an exact equivalence
of etale topoi. Applying i^* identifies the above kernel with the kernel of
upperStarGmSheafToGmSheaf i, since its counit on G_m,C_red is an isomorphism.
Topological invariance of cohomology transports the vanishing to C_red. Empty,
zero-dimensional, disconnected and reduced curves are covered by the same argument. -/
theorem subsingleton_H_two_reduction_units_kernel {k : Type u} [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] :
    Subsingleton (Sheaf.H
      (kernel (Scheme.upperStarGmSheafToGmSheaf C.nilradical.subschemeι)) 2) := by
  classical
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian C := ⟨⟩
  have : C.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from f]
    infer_instance
  have hqc (F : C.Modules) [F.IsQuasicoherent] :
      Subsingleton (Sheaf.H
        ((sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Scheme.Modules.etaleTensorSectionsSheaf F)) 2) := by
    obtain ⟨e⟩ := module_cohomology_iso_underlying_abelian C F 2
    have hz := isZero_zariskiCohomology_of_dimension_bound C 1
      (IsCurve.krullDim_le_one (f := f))
      ((SheafOfModules.toSheaf (moduleRings C.toRingedSpace)).obj F) 2 (by decide)
    have : Subsingleton (Sheaf.H'
        ((SheafOfModules.toSheaf (moduleRings C.toRingedSpace)).obj F) 2 ⊤) :=
      AddCommGrpCat.subsingleton_of_isZero hz
    have : Subsingleton ((RingedSpace.moduleCohomology C.toRingedSpace 2).obj F) :=
      e.addCommGroupIsoToAddEquiv.injective.subsingleton
    obtain ⟨_, _, c, _, _⟩ := Scheme.Modules.etale_zariski_qcoh_comparison C
    let : HasExt.{u} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u}) := inferInstance
    let : HasExt.{u + 1} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u}) :=
      HasExt.standard _
    let : HasDerivedCategory (Sheaf C.smallEtaleTopology AddCommGrpCat.{u}) :=
      HasDerivedCategory.standard _
    let a : Sheaf.H.{u} (Scheme.Modules.etaleTensorSectionsSheaf F) 2 ≃+
        ((RingedSpace.moduleCohomology C.toRingedSpace 2).obj F) :=
      (Abelian.Ext.homAddEquiv.{u + 1, u}.trans
        Abelian.Ext.homAddEquiv.{u + 1, u + 1}.symm).trans (c F 2).symm
    have hsmall : Subsingleton (Sheaf.H.{u}
        (Scheme.Modules.etaleTensorSectionsSheaf F) 2) :=
      a.injective.subsingleton
    obtain ⟨b⟩ := Scheme.Modules.nonempty_etaleTensorSectionsSheaf_cohomology_ulift C F 2
    refine ⟨fun x y ↦ b.injective ?_⟩
    exact @Subsingleton.elim _ hsmall (b x) (b y)
  have : Surjective C.nilradical.subschemeι :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism C).2.2.1
  have : IsUniversalHomeomorphism C.nilradical.subschemeι := {}
  obtain ⟨n, E, ⟨e⟩, hn, hstep⟩ := Scheme.exists_reduction_units_finite_filtration C
  have hE : ∀ j, j ≤ n → Subsingleton (Sheaf.H (E j) 2) := by
    intro j hj
    induction hj using Nat.decreasingInduction with
    | self => exact Sheaf.subsingleton_H_of_isZero hn 2
    | of_succ j hj ih =>
      obtain ⟨F, hF, S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := hstep j hj
      have := hF
      have : Subsingleton (Sheaf.H (E (j + 1)) 2) := ih
      let a₁ : Sheaf.H S.X₁ 2 ≃+ Sheaf.H (E (j + 1)) 2 :=
        ((Sheaf.functorH _ 2).mapIso e₁).addCommGroupIsoToAddEquiv
      have : Subsingleton (Sheaf.H S.X₁ 2) := a₁.injective.subsingleton
      have := hqc F
      let b := Etale.cohomologyEquiv C.nilradical.subschemeι
        ((sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Scheme.Modules.etaleTensorSectionsSheaf F)) 2
      let a₃ := ((Sheaf.functorH _ 2).mapIso e₃).addCommGroupIsoToAddEquiv.trans b.symm
      have : Subsingleton (Sheaf.H S.X₃ 2) := a₃.injective.subsingleton
      have : Subsingleton (Sheaf.H S.X₂ 2) := by
        refine ⟨fun x y ↦ ?_⟩
        have hzero (z : Sheaf.H S.X₂ 2) : z = 0 := by
          obtain ⟨w, hw⟩ := (Sheaf.H.exact_map_map hS 2 z).mp (Subsingleton.elim _ _)
          simpa only [Subsingleton.elim w 0, map_zero] using hw.symm
        rw [hzero x, hzero y]
      let a₂ : Sheaf.H (E j) 2 ≃+ Sheaf.H S.X₂ 2 :=
        ((Sheaf.functorH _ 2).mapIso e₂.symm).addCommGroupIsoToAddEquiv
      exact a₂.injective.subsingleton
  have := hE 0 (Nat.zero_le n)
  let a : Sheaf.H
      (kernel (Scheme.upperStarGmSheafToGmSheaf C.nilradical.subschemeι)) 2 ≃+
      Sheaf.H (E 0) 2 :=
    ((Sheaf.functorH _ 2).mapIso e.symm).addCommGroupIsoToAddEquiv
  exact a.injective.subsingleton

end AlgebraicGeometry.IsCurve
