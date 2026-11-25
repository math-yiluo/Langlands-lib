/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
import WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # The unit-compatible Cech--Koszul comparison on one ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 0A0A and 0941.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
private def koszulTensorTowerEvaluationIso
    (N : ringedSiteComplex O) (m : ℕᵒᵖ) :
    (((evaluation ℕᵒᵖ (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).obj m).mapHomologicalComplex
        (.up ℤ)).obj ((ringedKoszulTensorTowerFunctor O r b).obj N) ≅
      ((ringedKoszulTensor O).obj N).obj ((ringedKoszulDualTower O r b).obj m) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro n k h
    have hk : n + 1 = k := h
    subst k
    simp [ringedKoszulTensorTowerFunctor, ringedKoszulTensorTowerComplex,
      ringedKoszulTensorTower, CochainComplex.of_d])

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem koszulTensorTower_map_quasiIso
    (hk : ∀ m : ℕ, CochainComplex.IsKFlatTensor
      ((ringedKoszulDualTower O r b).obj (op m)))
    {N M : ringedSiteComplex O} (f : N ⟶ M) [QuasiIso f] :
    QuasiIso ((ringedKoszulTensorTowerFunctor O r b).map f) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let := SheafOfModules.monoidalCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
  intro m
  let t := HomologicalComplex.mapBifunctorMap f
    (𝟙 ((ringedKoszulDualTower O r b).obj m))
    (MonoidalCategory.curriedTensor A) (.up ℤ)
  have hcomm : ((((evaluation ℕᵒᵖ A).obj m).mapHomologicalComplex (.up ℤ)).map
      ((ringedKoszulTensorTowerFunctor O r b).map f)) ≫
        (koszulTensorTowerEvaluationIso O r b M m).hom =
      (koszulTensorTowerEvaluationIso O r b N m).hom ≫ t := by
    apply HomologicalComplex.hom_ext
    intro n
    change t.f n ≫ 𝟙 _ = 𝟙 _ ≫ t.f n
    simp only [Category.comp_id, Category.id_comp]
  apply (quasiIso_iff_of_arrow_mk_iso _ t
    (Arrow.isoMk (koszulTensorTowerEvaluationIso O r b N m)
      (koszulTensorTowerEvaluationIso O r b M m) hcomm.symm)).mpr
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic f).mp inferInstance
  have ht := hk m.unop
    (CochainComplex.mappingCone f) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).mpr
  intro i
  exact (ht i).of_iso
    (CochainComplex.mapBifunctorMappingCone₁Iso f
      ((ringedKoszulDualTower O r b).obj m) (MonoidalCategory.curriedTensor A))

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

/-- A single-site comparison of the actual Cech internal Hom and the actual strict
Koszul tensor tower, including the degree-zero unit. No restriction or uniqueness
assertion is part of this calculation.

Source: Stacks Project, sites-cohomology.tex, Tags 0A0A and 0941;
more-algebra.tex, Tag 0913; derived.tex, Tag 0949.
(auxiliary; not a blueprint node).

Proof: evaluate the transposed strict tensor tower at each index to identify its
map with tensor by the finite dual Koszul complex. K-flatness of those finite duals,
and the tensor mapping-cone isomorphism, show that the tower functor sends every
quasi-isomorphism to a quasi-isomorphism. Descend that actual functor by the
localization lifting universal property; its factorization is tensorFactors. Obtain
total right derived inverse limit, its comparison, and its computation on K-injective
towers from the strict-tower theorem. These fields explicitly construct D. Apply
the prescribed-presentation telescope/Hom comparison to D; its natural isomorphism
and unit equation give the result. No slice comparison or normalization uniqueness
is used. -/
theorem exists_ringed_cech_koszul_comparison_on_site :
    ∃ (D : RingedKoszulLimitPresentation O r b)
      (theta : ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ≅ D.completion),
      ∀ E, ringedCechCompletionUnit O (ringedExtendedCech O r b).1
        (ringedExtendedCech O r b).2 E ≫ theta.hom.app E = D.unit E := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let F := ringedKoszulTensorTowerFunctor O r b ⋙ DerivedCategory.Q.{w}
  have hF : W.IsInvertedBy F := by
    intro N M f hf
    have : QuasiIso f := hf
    have := koszulTensorTower_map_quasiIso O r b
      (ringed_cech_koszul_dual_tower_isKFlat O r b) f
    exact DerivedCategory.isIso_Q_map_iff_quasiIso _ _ |>.mpr this
  let T := Localization.lift F hF DerivedCategory.Q.{w}
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  obtain ⟨RF, c, hc, hI, _⟩ := ringedStrictTowerHomotopyLimit J R
    (by
      intro U a b
      exact @mul_comm (O.obj.obj U) inferInstance a b)
  let D : RingedKoszulLimitPresentation O r b :=
    { tensorTower := T
      tensorFactors := Localization.fac F hF DerivedCategory.Q.{w}
      inverseLimit := RF
      comparison := c
      isRightDerived := hc
      comparison_isIso := hI }
  obtain ⟨theta, htheta⟩ := exists_ringed_cech_koszul_hom_limit_comparison O r b D
  exact ⟨D, theta, htheta⟩

end CategoryTheory
