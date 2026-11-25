/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Line.LineQuotientHomogeneousFractionMap
import all WeilConjectures.AlgebraicGeometry.Graded.GradedImmersionAmpleCriterion
import all WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
import WeilConjectures.AlgebraicGeometry.PullbackMonoidalUnitComparison
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import all WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackQuasiCoherent

/-!
# Trivialized coefficients of a symmetric graded line map

## References

* Stacks Project, Constructions, Tags 01OA and 01O9
* Stacks Project, Constructions, Tags 01OA and 01O9 (the induced graded algebra map into tensor
  powers of an invertible sheaf, and its generation locus)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped AlgebraicGeometry TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] tensorPullbackSection

private noncomputable def powerCoefficient {X : Scheme.{u}} {M : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) (n : ℕ) :
    Γ(M.tensorPow n, ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  (unitSectionsEquiv ⊤).symm.toLinearMap.comp
    ((AlgebraicSpace.trivializedPower e n).hom.val.app (op ⊤)).hom

private theorem powerCoefficient_frame {X : Scheme.{u}} {M : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) (n : ℕ) :
    powerCoefficient e n
      (tensorPowLocalSection (e.inv.app ⊤ (unitSectionsEquiv ⊤ 1)) n) = 1 := by
  induction n with
  | zero => exact (unitSectionsEquiv ⊤).symm_apply_apply 1
  | succ n ih =>
    change (unitSectionsEquiv ⊤).symm
      ((λ_ (𝟙_ X.Modules)).hom.app ⊤
        ((e.hom ⊗ₘ (AlgebraicSpace.trivializedPower e n).hom).app ⊤
          (tmulSection (e.inv.app ⊤ (unitSectionsEquiv ⊤ 1))
            (tensorPowLocalSection (e.inv.app ⊤ (unitSectionsEquiv ⊤ 1)) n)))) = 1
    rw [tensorHom_app_tmulSection]
    have he : e.hom.app ⊤ (e.inv.app ⊤ (unitSectionsEquiv ⊤ 1)) =
        unitSectionsEquiv ⊤ 1 := inv_app_hom_app_apply_of_iso e.symm _
    rw [he, leftUnitor_hom_app_tmulSection, one_smul]
    exact ih

private theorem powerCoefficient_mul {X : Scheme.{u}} {M : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) (m n : ℕ)
    (a : Γ(M.tensorPow m, ⊤)) (b : Γ(M.tensorPow n, ⊤)) :
    powerCoefficient e (m + n)
      ((M.tensorPowAddIso m n).inv.app ⊤ (tmulSection a b)) =
      powerCoefficient e m a * powerCoefficient e n b := by
  let l := e.inv.app ⊤ (unitSectionsEquiv ⊤ 1)
  have hl : IsFreeGenerator l := (isFreeGenerator_one ⊤).app_hom e.symm
  obtain ⟨r, rfl⟩ := (tensorPowLocalSection_generator hl m).exists_smul_eq a
  obtain ⟨s, rfl⟩ := (tensorPowLocalSection_generator hl n).exists_smul_eq b
  rw [smul_tmulSection, tmulSection_smul, smul_smul, Hom.app_smul,
    tensorPowLocalSection_mul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul]
  simp only [l, powerCoefficient_frame, smul_eq_mul, mul_one]

private noncomputable def chartCoefficient {Z S : Scheme.{u}} {h : Z ⟶ S}
    {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) {X : Scheme.{u}} (j : X ⟶ Z)
    (V : S.affineOpens) (hj : (⊤ : X.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit X.ringCatSheaf) (n : ℕ) :
    A.grading V n →+ Γ(X, ⊤) where
  toFun a := powerCoefficient e n (ψ.evaluate j V hj n a)
  map_zero' := by simp only [RelativeGradedLineMap.evaluate, map_zero]
  map_add' a b := by simp only [RelativeGradedLineMap.evaluate, map_add]

private theorem chartCoefficient_one {Z S : Scheme.{u}} {h : Z ⟶ S}
    {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) {X : Scheme.{u}} (j : X ⟶ Z)
    (V : S.affineOpens) (hj : (⊤ : X.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit X.ringCatSheaf) :
    chartCoefficient ψ j V hj e 0 ⟨1, SetLike.one_mem_graded (A.grading V)⟩ = 1 := by
  change powerCoefficient e 0 (ψ.evaluate j V hj 0 _) = 1
  rw [evaluate_one]
  exact (unitSectionsEquiv ⊤).symm_apply_apply 1

private theorem chartCoefficient_mul {Z S : Scheme.{u}} {h : Z ⟶ S}
    {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) {X : Scheme.{u}} (j : X ⟶ Z)
    (V : S.affineOpens) (hj : (⊤ : X.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit X.ringCatSheaf)
    (m n : ℕ) (a : A.grading V m) (b : A.grading V n) :
    chartCoefficient ψ j V hj e (m + n)
      ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
      chartCoefficient ψ j V hj e m a * chartCoefficient ψ j V hj e n b := by
  change powerCoefficient e (m + n) (ψ.evaluate j V hj (m + n) _) = _
  rw [evaluate_mul, powerCoefficient_mul]
  rfl

private noncomputable def chartCoefficientRingHom {Z S : Scheme.{u}} {h : Z ⟶ S}
    {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) {X : Scheme.{u}} (j : X ⟶ Z)
    (V : S.affineOpens) (hj : (⊤ : X.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit X.ringCatSheaf) :
    A.obj V →+* Γ(X, ⊤) := by
  letI := A.gradedAlgebra V
  exact (DirectSum.toSemiring (chartCoefficient ψ j V hj e)
    (chartCoefficient_one ψ j V hj e)
    (fun {m n} a b ↦ chartCoefficient_mul ψ j V hj e m n a b)).comp
      (DirectSum.decomposeRingEquiv (A.grading V)).toRingHom

private theorem chartCoefficientRingHom_apply {Z S : Scheme.{u}} {h : Z ⟶ S}
    {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) {X : Scheme.{u}} (j : X ⟶ Z)
    (V : S.affineOpens) (hj : (⊤ : X.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit X.ringCatSheaf)
    (n : ℕ) (a : A.grading V n) :
    chartCoefficientRingHom ψ j V hj e a.val =
      powerCoefficient e n (ψ.evaluate j V hj n a) := by
  let := A.gradedAlgebra V
  unfold chartCoefficientRingHom
  change DirectSum.toSemiring (chartCoefficient ψ j V hj e)
    (chartCoefficient_one ψ j V hj e)
    (fun {m n} a b ↦ chartCoefficient_mul ψ j V hj e m n a b)
      (DirectSum.decompose (A.grading V) a.val) = _
  rw [DirectSum.decompose_coe, DirectSum.toSemiring_of]
  rfl

private theorem normalized_section {X Y : Scheme.{u}} (j : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    ((tensorPullbackSectionAdjunction j).unit.app M).app U s =
      tensorPullbackSection j M U s :=
  (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction j)).1 M U s

private theorem chartCoefficient_smul {Z S : Scheme.{u}} {h : Z ⟶ S}
    {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) {X : Scheme.{u}} (j : X ⟶ Z)
    (V : S.affineOpens) (hj : (⊤ : X.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit X.ringCatSheaf)
    (n : ℕ) (r : Γ(S, V.1)) (a : A.grading V n) :
    chartCoefficient ψ j V hj e n (r • a) =
      j.appLE (h ⁻¹ᵁ V.1) ⊤ hj (h.app V.1 r) * chartCoefficient ψ j V hj e n a := by
  change powerCoefficient e n (ψ.evaluate j V hj n (r • a)) = _
  unfold RelativeGradedLineMap.evaluate
  rw [ψ.smul, Hom.app_smul]
  change powerCoefficient e n
    ((boundaryPullbackPowIso j L n).hom.app ⊤
      (((tensorPullback j).obj (L.tensorPow n)).presheaf.map (homOfLE hj).op
        (j.app (h ⁻¹ᵁ V.1) (h.app V.1 r) • _))) = _
  erw [map_smul]
  rw [Hom.app_smul, LinearMap.map_smul]
  rfl

private theorem chartCoefficientRingHom_scalar {Z S : Scheme.{u}} {h : Z ⟶ S}
    {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) {X : Scheme.{u}} (j : X ⟶ Z)
    (V : S.affineOpens) (hj : (⊤ : X.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit X.ringCatSheaf)
    (r : Γ(S, V.1)) :
    chartCoefficientRingHom ψ j V hj e (algebraMap Γ(S, V.1) (A.obj V) r) =
      j.appLE (h ⁻¹ᵁ V.1) ⊤ hj (h.app V.1 r) := by
  let a : A.grading V 0 := ⟨1, SetLike.one_mem_graded (A.grading V)⟩
  have ha : algebraMap Γ(S, V.1) (A.obj V) r = ((r • a : A.grading V 0) : A.obj V) := by
    change algebraMap Γ(S, V.1) (A.obj V) r = r • (1 : A.obj V)
    rw [Algebra.smul_def, mul_one]
  rw [ha, chartCoefficientRingHom_apply]
  change chartCoefficient ψ j V hj e 0 (r • a) = _
  rw [chartCoefficient_smul, chartCoefficient_one, mul_one]

private theorem powerCoefficient_one {X : Scheme.{u}} {M : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) (s : Γ(M.tensorPow 1, ⊤)) :
    powerCoefficient e 1 s =
      (unitSectionsEquiv ⊤).symm (e.hom.app ⊤ ((ρ_ M).hom.app ⊤ s)) := by
  have he : (AlgebraicSpace.trivializedPower e 1).hom = (ρ_ M).hom ≫ e.hom := by
    change (e.hom ⊗ₘ 𝟙 _) ≫ (λ_ (𝟙_ X.Modules)).hom = _
    rw [unitors_equal, tensorHom_def, whiskerLeft_id, Category.comp_id]
    exact rightUnitor_naturality e.hom
  change (unitSectionsEquiv ⊤).symm
    ((AlgebraicSpace.trivializedPower e 1).hom.app ⊤ s) = _
  rw [he, Hom.comp_app, ConcreteCategory.comp_apply]
  rfl

private theorem boundary_power_one {X Y : Scheme.{u}} (j : X ⟶ Y) (L : Y.Modules) :
    (boundaryPullbackPowIso j L 1).hom ≫ (ρ_ ((tensorPullback j).obj L)).hom =
      (tensorPullback j).map (ρ_ L).hom := by
  let : (tensorPullback j).Monoidal :=
    Functor.Monoidal.transport (boundaryPullbackComparison j).symm
  have hη : (boundaryPullbackPowIso j L 0).hom =
      Functor.OplaxMonoidal.η (tensorPullback j) := by
    change (boundaryPullbackComparison j).hom.app _ ≫ (pullbackObjUnitIso j).hom =
      (boundaryPullbackComparison j).hom.app _ ≫ Functor.OplaxMonoidal.η (pullback j)
    rw [pullback_monoidal_unit_comparison]
    rfl
  have hδ : (boundaryPullbackTensorIso j L (𝟙_ Y.Modules)).hom =
      Functor.OplaxMonoidal.δ (tensorPullback j) L (𝟙_ Y.Modules) := by
    apply (cancel_epi (boundaryPullbackTensorIso j L (𝟙_ Y.Modules)).inv).mp
    rw [Iso.inv_hom_id]
    exact (Functor.Monoidal.μ_δ (tensorPullback j) L (𝟙_ Y.Modules)).symm
  change (boundaryPullbackTensorIso j L (𝟙_ Y.Modules)).hom ≫
    (𝟙 _ ⊗ₘ (boundaryPullbackPowIso j L 0).hom) ≫
      (ρ_ ((tensorPullback j).obj L)).hom = _
  rw [hη, hδ, id_tensorHom]
  exact Functor.OplaxMonoidal.right_unitality_hom (tensorPullback j) L

private theorem chartCoefficientRingHom_generator {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    {X : Scheme.{u}} (j : X ⟶ T) (V : S.affineOpens)
    (hj : (⊤ : X.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit X.ringCatSheaf)
    (m : Γ(E, V.1)) :
    chartCoefficientRingHom ψ j V hj e (SymmetricAlgebra.ι Γ(S, V.1) Γ(E, V.1) m) =
      (unitSectionsEquiv ⊤).symm (e.hom.app ⊤
        (((tensorPullback j).obj L).presheaf.map (homOfLE hj).op
          (tensorPullbackSection j L (h ⁻¹ᵁ V.1)
            (q.app (h ⁻¹ᵁ V.1) (tensorPullbackSection h E V.1 m))))) := by
  rw [show SymmetricAlgebra.ι Γ(S, V.1) Γ(E, V.1) m =
    (quotientSymmetricGenerator E V m).val from rfl,
    chartCoefficientRingHom_apply, powerCoefficient_one]
  unfold RelativeGradedLineMap.evaluate
  apply congrArg (fun s : Γ((tensorPullback j).obj L, ⊤) ↦
    (unitSectionsEquiv ⊤).symm (e.hom.app ⊤ s))
  erw [← ConcreteCategory.comp_apply, ← Hom.comp_app, boundary_power_one,
    Hom.app_presheaf_map]
  have hn := congrArg (fun f ↦ f.app (h ⁻¹ᵁ V.1)
    (ψ.component V 1 (quotientSymmetricGenerator E V m)))
    ((tensorPullbackSectionAdjunction j).unit_naturality (ρ_ L).hom)
  change ((tensorPullback j).map (ρ_ L).hom).app (j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
      (((tensorPullbackSectionAdjunction j).unit.app (L.tensorPow 1)).app
        (h ⁻¹ᵁ V.1) (ψ.component V 1 (quotientSymmetricGenerator E V m))) =
    ((tensorPullbackSectionAdjunction j).unit.app L).app (h ⁻¹ᵁ V.1)
      ((ρ_ L).hom.app (h ⁻¹ᵁ V.1) (ψ.component V 1 (quotientSymmetricGenerator E V m))) at hn
  apply congrArg (fun s : Γ((tensorPullback j).obj L, j ⁻¹ᵁ (h ⁻¹ᵁ V.1)) ↦
    ((tensorPullback j).obj L).presheaf.map (homOfLE hj).op s)
  exact hn.trans ((congrArg
    (fun s : Γ(L, h ⁻¹ᵁ V.1) ↦
      ((tensorPullbackSectionAdjunction j).unit.app L).app (h ⁻¹ᵁ V.1) s)
    (hψ V m)).trans (normalized_section j L (h ⁻¹ᵁ V.1) _))

private noncomputable def openSectionCoefficient {T : Scheme.{u}} (L : T.Modules)
    (W : T.Opens)
    (e : (tensorPullback W.ι).obj L ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    Γ(L, W) →+ Γ(W.toScheme, ⊤) where
  toFun s := (unitSectionsEquiv ⊤).symm (e.hom.app ⊤
    (((tensorPullback W.ι).obj L).presheaf.map
      (homOfLE (show (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W by simp)).op
      (tensorPullbackSection W.ι L W s)))
  map_zero' := by simp only [← normalized_section, map_zero]
  map_add' a b := by simp only [← normalized_section, map_add]

private theorem openSectionCoefficient_smul {T : Scheme.{u}} (L : T.Modules)
    (W : T.Opens)
    (e : (tensorPullback W.ι).obj L ≅ SheafOfModules.unit W.toScheme.ringCatSheaf)
    (r : Γ(T, W)) (s : Γ(L, W)) :
    openSectionCoefficient L W e (r • s) =
      W.ι.appLE W ⊤ (by simp) r * openSectionCoefficient L W e s := by
  change (unitSectionsEquiv ⊤).symm (e.hom.app ⊤
    (((tensorPullback W.ι).obj L).presheaf.map _
      (tensorPullbackSection W.ι L W (r • s)))) = _
  rw [← normalized_section, Hom.app_smul]
  change (unitSectionsEquiv ⊤).symm (e.hom.app ⊤
    (((tensorPullback W.ι).obj L).presheaf.map _
      (W.ι.app W r • _))) = _
  erw [map_smul]
  rw [Hom.app_smul, LinearEquiv.map_smul, normalized_section]
  rfl

private theorem openSectionCoefficient_restrict {T : Scheme.{u}} (L : T.Modules)
    (W U : T.Opens) (hWU : W ≤ U)
    (e : (tensorPullback W.ι).obj L ≅ SheafOfModules.unit W.toScheme.ringCatSheaf)
    (s : Γ(L, U)) :
    openSectionCoefficient L W e (L.presheaf.map (homOfLE hWU).op s) =
      (unitSectionsEquiv ⊤).symm (e.hom.app ⊤
        (((tensorPullback W.ι).obj L).presheaf.map
          (homOfLE (show (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ U from
            by simpa only [W.ι_preimage_self] using W.ι.preimage_mono hWU)).op
          (tensorPullbackSection W.ι L U s))) := by
  change (unitSectionsEquiv ⊤).symm (e.hom.app ⊤
    (((tensorPullback W.ι).obj L).presheaf.map _
      (tensorPullbackSection W.ι L W (L.presheaf.map (homOfLE hWU).op s)))) = _
  have hu := Hom.app_presheaf_map ((tensorPullbackSectionAdjunction W.ι).unit.app L)
    (homOfLE hWU) s
  rw [normalized_section, normalized_section] at hu
  erw [hu, presheaf_map_map_apply]
  rfl

private theorem openSectionCoefficient_surjective {T : Scheme.{u}} (L : T.Modules)
    (W : T.Opens)
    (e : (tensorPullback W.ι).obj L ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    Function.Surjective (openSectionCoefficient L W e) := by
  have hc := bijective_app_of_iso ((boundaryPullbackComparison W.ι).app L) (W.ι ⁻¹ᵁ W)
  have hh : Function.Bijective (fun s : Γ(L, W) ↦
      ((boundaryPullbackComparison W.ι).app L).hom.app (W.ι ⁻¹ᵁ W)
        (((tensorPullbackSectionAdjunction W.ι).unit.app L).app W s)) := by
    have he : (fun s : Γ(L, W) ↦
        ((boundaryPullbackComparison W.ι).app L).hom.app (W.ι ⁻¹ᵁ W)
          (((tensorPullbackSectionAdjunction W.ι).unit.app L).app W s)) =
        (pullbackUnit W.ι L).app W := funext (boundary_unit_transport W.ι L W)
    rw [he]
    exact bijective_pullbackUnit_app_of_isOpenImmersion W.ι L W.opensRange_ι.ge
  have hη := (Function.Bijective.of_comp_iff' hc _).mp hh
  have hi : IsIso (homOfLE
      (show (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W by simp)) :=
    homOfLE_isIso_of_eq _ W.ι_preimage_self.symm
  have hr := ConcreteCategory.bijective_of_isIso
    (((tensorPullback W.ι).obj L).presheaf.map
      (homOfLE (show (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W by simp)).op)
  intro r
  obtain ⟨u, hu⟩ := (bijective_app_of_iso e ⊤).surjective (unitSectionsEquiv ⊤ r)
  obtain ⟨t, ht⟩ := hr.surjective u
  obtain ⟨s, hs⟩ := hη.surjective t
  refine ⟨s, ?_⟩
  change (unitSectionsEquiv ⊤).symm (e.hom.app ⊤
    (((tensorPullback W.ι).obj L).presheaf.map _ (tensorPullbackSection W.ι L W s))) = r
  rw [← normalized_section, hs, ht, hu]
  exact (unitSectionsEquiv ⊤).symm_apply_apply r

private theorem coefficient_irrelevant_top {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (V : S.affineOpens) (W : T.affineOpens) (hWV : W.1 ≤ h ⁻¹ᵁ V.1)
    (e : (tensorPullback W.1.ι).obj L ≅ SheafOfModules.unit W.1.toScheme.ringCatSheaf)
    (α : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V →+* Γ(W.1.toScheme, ⊤))
    (hα : ∀ m : Γ(E, V.1),
      α (SymmetricAlgebra.ι Γ(S, V.1) Γ(E, V.1) m) =
        openSectionCoefficient L W.1 e
          (q.app W.1 (((tensorPullback h).obj E).presheaf.map (homOfLE hWV).op
            (tensorPullbackSection h E V.1 m)))) :
    Ideal.map α (HomogeneousIdeal.irrelevant
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)).toIdeal = ⊤ := by
  classical
  let I := Ideal.map α (HomogeneousIdeal.irrelevant
    ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)).toIdeal
  let : Algebra Γ(S, V.1) Γ(T, W.1) := (h.appLE V.1 W.1 hWV).hom.toAlgebra
  let : ∀ G : S.Modules, Module Γ(S, V.1) Γ((tensorPullback h).obj G, W.1) :=
    fun G ↦ Module.compHom _ (h.appLE V.1 W.1 hWV).hom
  obtain ⟨c, hc, _, hp, _⟩ := exists_tensorPullback_affine_sections h V W hWV
  have ht (t : Γ(E, V.1) ⊗[Γ(S, V.1)] Γ(T, W.1)) :
      openSectionCoefficient L W.1 e (q.app W.1 (c E inferInstance t)) ∈ I := by
    induction t using TensorProduct.inductionOn with
    | tmul m r =>
      rw [hp, Hom.app_smul, openSectionCoefficient_smul]
      apply I.mul_mem_left
      have hu : (((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app E).app
          V.1 m) = tensorPullbackSection h E V.1 m := by
        unfold tensorPullbackSection
        exact Classical.choose_spec (exists_tensorPullbackAdjunction h) E (op V.1) m
      have he := congrArg (fun z : Γ((tensorPullback h).obj E, h ⁻¹ᵁ V.1) ↦
        openSectionCoefficient L W.1 e
          (q.app W.1 (((tensorPullback h).obj E).presheaf.map (homOfLE hWV).op z))) hu
      have hm : α (SymmetricAlgebra.ι Γ(S, V.1) Γ(E, V.1) m) ∈ I :=
        Ideal.mem_map_of_mem α (HomogeneousIdeal.mem_irrelevant_of_mem _
          (by decide : 0 < (1 : ℕ)) (quotientSymmetricGenerator E V m).property)
      exact he.symm ▸ ((hα m) ▸ hm)
    | add t t' ht ht' =>
      rw [map_add, map_add, map_add]
      exact I.add_mem ht ht'
  obtain ⟨l, hl⟩ := openSectionCoefficient_surjective L W.1 e 1
  obtain ⟨s, hs⟩ := surjective_affine_of_epi q W.2 l
  obtain ⟨t, ht'⟩ := (hc E inferInstance).surjective s
  apply I.eq_top_of_isUnit_mem (ht t)
  rw [ht', hs, hl]
  exact isUnit_one

/-- Trivializing a line quotient turns its graded extension into an ordinary ring map.
This is an algebra statement about its coefficients and does not construct a Proj map. -/
theorem line_quotient_trivialized_coefficients {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (V : S.affineOpens) (W : T.affineOpens) (hWV : W.1 ≤ h ⁻¹ᵁ V.1)
    (e : (tensorPullback W.1.ι).obj L ≅ SheafOfModules.unit W.1.toScheme.ringCatSheaf) :
    ∃ α : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V →+*
        Γ(W.1.toScheme, ⊤),
      (∀ r : Γ(S, V.1), α (algebraMap Γ(S, V.1)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).obj V) r) =
          W.1.ι.appLE W.1 ⊤ (by simp) (h.appLE V.1 W.1 hWV r)) ∧
      (∀ m : E.val.obj (op V.1),
        α (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1)) m) =
          (Scheme.Modules.unitSectionsEquiv ⊤).symm
            (e.hom.app ⊤
              (((Scheme.Modules.tensorPullback W.1.ι).obj L).presheaf.map
                (homOfLE (show (⊤ : W.1.toScheme.Opens) ≤ W.1.ι ⁻¹ᵁ W.1 by simp)).op
                (Scheme.Modules.tensorPullbackSection W.1.ι L W.1
                  (L.presheaf.map (homOfLE hWV).op
                    (q.app (h ⁻¹ᵁ V.1)
                      (Scheme.Modules.tensorPullbackSection h E V.1 m))))))) ∧
      (∀ (n : ℕ) (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V n),
        α a = (Scheme.Modules.unitSectionsEquiv ⊤).symm
          ((AlgebraicSpace.trivializedPower e n).hom.app ⊤
            (ψ.evaluate W.1.ι V
              (by simpa only [W.1.ι_preimage_self] using W.1.ι.preimage_mono hWV) n a))) ∧
      Ideal.map α (HomogeneousIdeal.irrelevant
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)).toIdeal = ⊤  := by
  classical
  let hj : (⊤ : W.1.toScheme.Opens) ≤ W.1.ι ⁻¹ᵁ (h ⁻¹ᵁ V.1) :=
    by simpa only [W.1.ι_preimage_self] using W.1.ι.preimage_mono hWV
  let α := chartCoefficientRingHom ψ W.1.ι V hj e
  have hgen (m : Γ(E, V.1)) :
      α (SymmetricAlgebra.ι Γ(S, V.1) Γ(E, V.1) m) =
        openSectionCoefficient L W.1 e
          (q.app W.1 (((tensorPullback h).obj E).presheaf.map (homOfLE hWV).op
            (tensorPullbackSection h E V.1 m))) := by
    rw [Hom.app_presheaf_map, openSectionCoefficient_restrict]
    exact chartCoefficientRingHom_generator h E L q ψ hψ W.1.ι V hj e m
  refine ⟨α, ?_, ?_, ?_, coefficient_irrelevant_top h E L q V W hWV e α hgen⟩
  · intro r
    rw [chartCoefficientRingHom_scalar]
    have hn := ConcreteCategory.congr_hom
      (W.1.ι.naturality (homOfLE hWV).op) (h.app V.1 r)
    change W.1.toScheme.presheaf.map (homOfLE hj).op
      (W.1.ι.app (h ⁻¹ᵁ V.1) (h.app V.1 r)) =
      W.1.toScheme.presheaf.map
        (homOfLE (show (⊤ : W.1.toScheme.Opens) ≤ W.1.ι ⁻¹ᵁ W.1 by simp)).op
        (W.1.ι.app W.1 (T.presheaf.map (homOfLE hWV).op (h.app V.1 r)))
    change W.1.ι.app W.1 (T.presheaf.map (homOfLE hWV).op (h.app V.1 r)) =
      W.1.toScheme.presheaf.map (homOfLE (W.1.ι.preimage_mono hWV)).op
        (W.1.ι.app (h ⁻¹ᵁ V.1) (h.app V.1 r)) at hn
    rw [hn, Scheme.presheaf_map_map_apply]
    rfl
  · intro m
    change α (SymmetricAlgebra.ι Γ(S, V.1) Γ(E, V.1) m) = _
    erw [hgen m, Hom.app_presheaf_map q (homOfLE hWV)]
    rfl
  · intro n a
    exact chartCoefficientRingHom_apply ψ W.1.ι V hj e n a

end AlgebraicGeometry.Scheme.Modules
