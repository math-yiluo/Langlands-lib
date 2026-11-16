import Langlands.AlgebraicGeometry.Modules.SupportedSectionCoefficients
import Mathlib.RingTheory.RingHom.Flat

/-! # Support-preserving coefficients under flat scalar extension -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules.FlatBaseChange

variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
  {V W : ModuleCat.{u} R}

/-- The scalar extension of the kernel inside the extended source. -/
def scalarKernelImage (r : V ⟶ W) :
    Submodule A ((ModuleCat.extendScalars φ).obj V) :=
  LinearMap.range ((ModuleCat.extendScalars φ).map
    (ModuleCat.ofHom (LinearMap.ker r.hom).subtype)).hom

/-- Tensoring with a flat algebra preserves the kernel of a linear map. -/
lemma mem_scalarKernelImage_iff (hφ : φ.Flat) (r : V ⟶ W)
    (a : (ModuleCat.extendScalars φ).obj V) :
    a ∈ scalarKernelImage φ r ↔ (ModuleCat.extendScalars φ).map r a = 0 := by
  let : Module R A := Module.compHom A φ
  let : Module.Flat R A := hφ
  have hex := Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map r.hom)
  exact (hex a).symm

/-- A nonzero linear observation on a scalar-extended kernel detects a nonzero
observation on the pullback of one actual kernel vector. -/
lemma exists_kernel_coefficient_of_ne_zero (hφ : φ.Flat) (r : V ⟶ W)
    {V' T : ModuleCat.{u} A}
    (c : (ModuleCat.extendScalars φ).obj V ⟶ V') (q : V' ⟶ T)
    (a : (ModuleCat.extendScalars φ).obj V)
    (ha : (ModuleCat.extendScalars φ).map r a = 0) (hne : q (c a) ≠ 0) :
    ∃ s : V, r s = 0 ∧ q (c ((1 : A) ⊗ₜ[R,φ] s)) ≠ 0 := by
  classical
  let : Module R A := Module.compHom A φ
  let : Module.Flat R A := hφ
  obtain ⟨b, hb⟩ := (mem_scalarKernelImage_iff φ hφ r a).mpr ha
  by_contra h
  have hz : ∀ s : LinearMap.ker r.hom,
      q (c ((1 : A) ⊗ₜ[R,φ] (s : V))) = 0 := by
    intro s
    by_contra hs
    exact h ⟨s, s.property, hs⟩
  have hall : ∀ b : A ⊗[R] LinearMap.ker r.hom,
      q (c ((LinearMap.ker r.hom).subtype.lTensor A b)) = 0 := by
    intro b
    induction b using TensorProduct.inductionOn with
    | tmul z s =>
        change q.hom (c.hom (z ⊗ₜ[R,φ] (s : V))) = 0
        have ht : (z ⊗ₜ[R,φ] (s : V) : (ModuleCat.extendScalars φ).obj V) =
            z • ((1 : A) ⊗ₜ[R,φ] (s : V)) := by
          rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
        rw [ht, map_smul, map_smul, hz s, smul_zero]
    | add b₁ b₂ h₁ h₂ =>
        change q.hom (c.hom ((LinearMap.ker r.hom).subtype.lTensor A (b₁ + b₂))) = 0
        rw [map_add, map_add, map_add, h₁, h₂, add_zero]
  apply hne
  rw [← hb]
  exact hall b

end Langlands.AlgebraicGeometry.Modules.FlatBaseChange

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections.FlatBaseChange

variable {R R' : CommRingCat.{u}}
  {X X' Z Z' : Scheme.{u}}
  (φ : R ⟶ R') (hφ : φ.hom.Flat)
  (f : X ⟶ Spec R) (f' : X' ⟶ Spec R')
  (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  (i : Z ⟶ X) (i' : Z' ⟶ X') (gZ : Z' ⟶ Z) (sq : gZ ≫ i = i' ≫ g)

include hφ

set_option maxHeartbeats 800000 in
/-- A section in the upstairs restriction kernel which generates at a point
detects a downstairs kernel section generating at its image. The two comparison
hypotheses concern the canonical scalar base-change maps themselves. -/
lemma exists_vanishing_coefficient_generating
    (M : Langlands.AlgebraicGeometry.Picard.LineBundle X)
    [IsIso (scalarSectionsBaseChangeMap φ f f' g w M.obj)]
    [IsIso (scalarSectionsBaseChangeMap φ (i ≫ f) (i' ≫ f') gZ
      (square_restrict_comm φ f f' g w i i' gZ sq)
      ((Scheme.Modules.pullback i).obj M.obj))]
    (t : GlobalSections ((Scheme.Modules.pullback g).obj M.obj))
    (ht : pullbackSection i' ((Scheme.Modules.pullback g).obj M.obj) t = 0)
    (y : X')
    (hy : y ∈ trivializationOpen ((Scheme.Modules.pullback g).obj M.obj) t) :
    ∃ s : GlobalSections M.obj, pullbackSection i M.obj s = 0 ∧
      g y ∈ trivializationOpen M.obj s := by
  let r : (relativeGlobalSections f).obj M.obj ⟶
      (relativeGlobalSections (i ≫ f)).obj ((Scheme.Modules.pullback i).obj M.obj) :=
    relativeGlobalSectionsPullback
      (Over.homMk i : Over.mk (i ≫ f) ⟶ Over.mk f) M.obj
  let r' : (relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M.obj) ⟶
      (relativeGlobalSections (i' ≫ f')).obj
        ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M.obj)) :=
    relativeGlobalSectionsPullback
      (Over.homMk i' : Over.mk (i' ≫ f') ⟶ Over.mk f')
      ((Scheme.Modules.pullback g).obj M.obj)
  let c := scalarSectionsBaseChangeMap φ f f' g w M.obj
  let cZ := restrictionScalarSectionsBaseChangeMap φ f f' g w i i' gZ sq M.obj
  let a := (asIso c).inv t
  have hca : c a = t :=
    ConcreteCategory.congr_hom (asIso c).inv_hom_id t
  have hcZ : IsIso cZ := by
    dsimp [cZ, restrictionScalarSectionsBaseChangeMap]
    infer_instance
  have ha : (ModuleCat.extendScalars φ.hom).map r a = 0 := by
    apply (ModuleCat.mono_iff_injective cZ).mp inferInstance
    have hcomm : (ModuleCat.extendScalars φ.hom).map r ≫ cZ = c ≫ r' :=
      scalarSectionsBaseChangeMap_comp_restriction φ f f' g w i i' gZ sq M.obj
    have heq := ConcreteCategory.congr_hom hcomm a
    simp only [ConcreteCategory.comp_apply] at heq
    have hrt : r' t = 0 :=
      (relativeGlobalSectionsPullback_apply
        (Over.homMk i' : Over.mk (i' ≫ f') ⟶ Over.mk f')
        ((Scheme.Modules.pullback g).obj M.obj) t).trans ht
    exact heq.trans ((congrArg (fun z => r' z) hca).trans hrt) |>.trans (map_zero cZ.hom).symm
  let res := X'.fromSpecResidueField y
  let q : (relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M.obj) ⟶
      (relativeGlobalSections (res ≫ f')).obj
        ((Scheme.Modules.pullback res).obj ((Scheme.Modules.pullback g).obj M.obj)) :=
    relativeGlobalSectionsPullback
      (Over.homMk res : Over.mk (res ≫ f') ⟶ Over.mk f')
      ((Scheme.Modules.pullback g).obj M.obj)
  have hqt : q t ≠ 0 := by
    change relativeGlobalSectionsPullback
      (Over.homMk res : Over.mk (res ≫ f') ⟶ Over.mk f')
      ((Scheme.Modules.pullback g).obj M.obj) t ≠ 0
    rw [relativeGlobalSectionsPullback_apply]
    have h := (lineBundleResidueOpenComparison X'
      ((Langlands.AlgebraicGeometry.Picard.LineBundle.pullback g).obj M) t)
    exact (Set.ext_iff.mp h y).mpr hy
  obtain ⟨s, hrs, hqs⟩ := Modules.FlatBaseChange.exists_kernel_coefficient_of_ne_zero φ.hom hφ r c q a ha
    (fun hz => hqt ((congrArg (fun z => q z) hca).symm.trans hz))
  change GlobalSections M.obj at s
  have hcs : c ((1 : R') ⊗ₜ[R,φ.hom] s) = pullbackSection g M.obj s := by
    rw [pullbackSection_eq_sectionPullback]
    exact scalarSectionsBaseChangeMap_one_tmul φ f f' g w M.obj s
  erw [hcs] at hqs
  have hy' : y ∈ trivializationOpen ((Scheme.Modules.pullback g).obj M.obj)
      (pullbackSection g M.obj s) := by
    apply (Set.ext_iff.mp (lineBundleResidueOpenComparison X'
      ((Langlands.AlgebraicGeometry.Picard.LineBundle.pullback g).obj M)
      (pullbackSection g M.obj s)) y).mp
    change pullbackSection res ((Scheme.Modules.pullback g).obj M.obj)
      (pullbackSection g M.obj s) ≠ 0
    intro hz
    exact hqs ((relativeGlobalSectionsPullback_apply
      (Over.homMk res : Over.mk (res ≫ f') ⟶ Over.mk f')
      ((Scheme.Modules.pullback g).obj M.obj) (pullbackSection g M.obj s)).trans hz)
  refine ⟨s, ?_, ?_⟩
  · exact (relativeGlobalSectionsPullback_apply
      (Over.homMk i : Over.mk (i ≫ f) ⟶ Over.mk f) M.obj s).symm.trans hrs
  · rw [lineBundlePullbackSectionOpen X X' g M s] at hy'
    exact hy'


end Langlands.AlgebraicGeometry.Modules.DerivedSections.FlatBaseChange
