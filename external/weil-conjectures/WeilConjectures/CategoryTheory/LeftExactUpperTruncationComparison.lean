/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Left exact upper truncation comparisons

Source: Stacks Project, Tag 05TC (2), and the canonical cycle calculation of Tag 0AVW.
(blueprint: lem-sc-left-exact-upper-truncation-comparison).
-/

@[expose] public section
set_option autoImplicit false

universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def cyclesComparison (S : ShortComplex C) :
    F.obj S.cycles ≅ (S.map F).cycles :=
  (S.map F).isoCyclesOfIsLimit (KernelFork.mapIsLimit _ S.cyclesIsKernel F)
set_option backward.isDefEq.respectTransparency false in
private theorem cyclesComparison_i (S : ShortComplex C) :
    (cyclesComparison F S).hom ≫ (S.map F).iCycles = F.map S.iCycles := by
  exact (S.map F).isoCyclesOfIsLimit_hom_iCycles _
set_option backward.isDefEq.respectTransparency false in
private theorem map_cycles_isIso {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    [IsIso (ShortComplex.cyclesMap φ)] :
    IsIso (ShortComplex.cyclesMap (F.mapShortComplex.map φ)) := by
  have h : ShortComplex.cyclesMap (F.mapShortComplex.map φ) =
      (cyclesComparison F S₁).inv ≫ F.map (ShortComplex.cyclesMap φ) ≫
        (cyclesComparison F S₂).hom := by
    apply (cancel_mono (S₂.map F).iCycles).mp
    dsimp only [Functor.mapShortComplex] at *
    rw [ShortComplex.cyclesMap_i, Category.assoc, Category.assoc,
      cyclesComparison_i, ← F.map_comp, ShortComplex.cyclesMap_i, F.map_comp]
    rw [← cancel_epi (cyclesComparison F S₁).hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, cyclesComparison_i]
  rw [h]
  infer_instance
set_option backward.isDefEq.respectTransparency false in
private theorem cycles_iso {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    [Epi φ.τ₁] [Mono φ.τ₂] [IsIso (ShortComplex.homologyMap φ)] :
    IsIso (ShortComplex.cyclesMap φ) := by
  let B₁ := ShortComplex.mk S₁.toCycles S₁.homologyπ S₁.toCycles_comp_homologyπ
  let B₂ := ShortComplex.mk S₂.toCycles S₂.homologyπ S₂.toCycles_comp_homologyπ
  let ψ : B₁ ⟶ B₂ :=
    { τ₁ := φ.τ₁
      τ₂ := ShortComplex.cyclesMap φ
      τ₃ := ShortComplex.homologyMap φ
      comm₁₂ := (ShortComplex.toCycles_naturality φ).symm
      comm₂₃ := (ShortComplex.homologyπ_naturality φ).symm }
  have : Epi ψ.τ₁ := inferInstanceAs (Epi φ.τ₁)
  have : Epi ψ.τ₃ := inferInstanceAs (Epi (ShortComplex.homologyMap φ))
  have : Epi B₁.g := inferInstanceAs (Epi S₁.homologyπ)
  have : Epi B₂.g := inferInstanceAs (Epi S₂.homologyπ)
  have : Epi (ShortComplex.cyclesMap φ) :=
    ShortComplex.epi_τ₂_of_exact_of_epi ψ
      (B₂.exact_of_g_is_cokernel S₂.homologyIsCokernel)
  have : Mono (ShortComplex.cyclesMap φ) :=
    mono_of_mono_fac (ShortComplex.cyclesMap_i φ)
  exact isIso_of_mono_of_epi _
set_option backward.isDefEq.respectTransparency false in
private theorem truncation_prev_iso (I : CochainComplex C ℤ) (n : ℤ) :
    IsIso ((I.ιTruncLE n).f (n - 1)) := by
  change IsIso (((I.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f (n - 1)).unop)
  have h : IsIso ((I.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f (n - 1)) := by
    dsimp only [HomologicalComplex.πTruncGE]
    apply ((ComplexShape.embeddingUpIntLE n).op.isIso_liftExtend_f_iff _ _
      (i := 1) (by simp)).mpr
    apply I.op.isIso_restrictionToTruncGE'
    simp [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
  infer_instance

variable [Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

omit [Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
  [HasDerivedCategory C] [HasDerivedCategory D] in
set_option backward.isDefEq.respectTransparency false in
/-- A left exact functor commutes with cohomology in the top degree of upper truncation.
Source: Stacks Project, Tag 0AVW, canonical cycle calculation.
(blueprint: lem-sc-left-exact-upper-truncation-comparison).

Proof: In degrees n-1 and n the upper smart truncation has respectively I^(n - 1)
and ker(d^n), and its differential is the differential into that kernel. A left exact
functor preserves this kernel. Thus applying F to the truncation inclusion identifies
the two cycle objects and the two boundary maps (using the isomorphism in degree n-1).
Their cokernels are canonically isomorphic, and the induced map is precisely degree-n
homology of the mapped truncation inclusion. No boundedness, geometric hypothesis,
or K-injectivity of I is needed. Zero complexes and all integer degrees are included. -/
theorem upperTruncation_raw_comparison (I : CochainComplex C ℤ) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map (I.ιTruncLE n)) n) := by
  let φ := (HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map (I.ιTruncLE n)
  have : IsIso φ.τ₁ := by
    change IsIso ((I.ιTruncLE n).f ((ComplexShape.up ℤ).prev n))
    rw [CochainComplex.prev]
    exact truncation_prev_iso I n
  have : Mono φ.τ₂ := by
    change Mono ((I.ιTruncLE n).f n)
    dsimp [CochainComplex.ιTruncLE]
    infer_instance
  have : IsIso (ShortComplex.homologyMap φ) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap (I.ιTruncLE n) n))
  have : IsIso (ShortComplex.cyclesMap φ) := cycles_iso φ
  have hc := map_cycles_isIso F φ
  have hprev : Epi (F.map φ.τ₁) := inferInstance
  have hmap := ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi hc hprev
  exact hmap

omit [PreservesFiniteLimits F] in
/-- The derived functor does not change top-degree cohomology under upper truncation.
Source: Stacks Project, Tag 05TC (2).
(blueprint: lem-sc-left-exact-upper-truncation-comparison).
Proof: The quotient of the upper truncation inclusion is quasi-isomorphic to the lower
truncation in degree n+1. Negative vanishing for its bounded-below derived image and the
homology sequence of the truncation triangle give invertibility in degree n. -/
theorem upperTruncation_derived_comparison (I : CochainComplex C ℤ) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor D n).map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map (I.ιTruncLE n)))) := by
  let hS := I.shortComplexTruncLE_shortExact n
  let T := F.rightDerivedFunctor.mapTriangle.obj (DerivedCategory.triangleOfSES hS)
  have hT : T ∈ distTriang _ := F.rightDerivedFunctor.map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hS)
  let J := I.truncGE (n + 1)
  let E : DerivedCategory.Plus C :=
    ⟨DerivedCategory.Q.obj J, ⟨n + 1, inferInstance⟩⟩
  have : E.IsGE (n + 1) := by
    apply (DerivedCategory.Plus.isGE_ι_obj_iff E (n + 1)).mp
    change (DerivedCategory.Q.obj J).IsGE (n + 1)
    infer_instance
  let e := asIso (DerivedCategory.Q.map (I.shortComplexTruncLEX₃ToTruncGE n (n + 1)))
  have hz (q : ℤ) (hq : q < n + 1) :
      IsZero ((DerivedCategory.homologyFunctor D q).obj T.obj₃) := by
    have h := F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE E (n + 1) hq
    exact h.of_iso
      ((DerivedCategory.homologyFunctor D q).mapIso
        (F.rightDerivedFunctor.mapIso e) ≪≫
       (DerivedCategory.homologyFunctor D q).mapIso
         (F.rightDerivedFunctorPlusCompatibility.app E).symm)
  exact DerivedCategory.isIso_homologyMap_mor₁ T hT (n - 1) n (by omega)
    (hz (n - 1) (by omega)) (hz n (by omega))

/-- Raw and derived upper-truncation comparisons, packaged for the naturality square.
Source: Stacks Project, Tags 05TC (2) and 0AVW.
(blueprint: lem-sc-left-exact-upper-truncation-comparison). -/
theorem upperTruncation_comparisons (I : CochainComplex C ℤ) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map (I.ιTruncLE n)) n) ∧
    IsIso ((DerivedCategory.homologyFunctor D n).map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map (I.ιTruncLE n)))) :=
  ⟨F.upperTruncation_raw_comparison I n, F.upperTruncation_derived_comparison I n⟩

set_option backward.isDefEq.respectTransparency false in
/-- Left homology data after preserving cycles, with an actual cokernel of the mapped
boundary. Source: Stacks Project, Tag 0AVW, canonical cycle calculation.
(blueprint: lem-sc-left-exact-upper-truncation-comparison). -/
noncomputable def mappedCyclesHomologyData (I : CochainComplex C ℤ) (n : ℤ) :
    ((I.sc n).map F).LeftHomologyData := by
  let h := (I.sc n).homologyData.left
  have wi : F.map h.i ≫ F.map (I.sc n).g = 0 := by
    rw [← F.map_comp, h.wi, F.map_zero]
  let hi := KernelFork.mapIsLimit _ h.hi F
  have hf : hi.lift (KernelFork.ofι ((I.sc n).map F).f ((I.sc n).map F).zero) =
      F.map h.f' := by
    apply Fork.IsLimit.hom_ext hi
    rw [Fork.IsLimit.lift_ι hi]
    simp only [KernelFork.map_ι, Fork.ι_ofι, ← F.map_comp, h.f'_i]
    rfl
  exact
    { K := F.obj h.K
      H := cokernel (F.map h.f')
      i := F.map h.i
      π := cokernel.π (F.map h.f')
      wi := wi
      hi := hi
      wπ := by rw [hf]; exact cokernel.condition _
      hπ := by
        let e : parallelPair (hi.lift
            (KernelFork.ofι ((I.sc n).map F).f ((I.sc n).map F).zero)) 0 ≅
            parallelPair (F.map h.f') 0 :=
          parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hf) (by simp)
        refine IsColimit.precomposeInvEquiv e _
          (IsColimit.ofIsoColimit (cokernelIsCokernel (F.map h.f')) ?_)
        exact Cofork.ext (Iso.refl _) (by
          simp only [Fork.ofι_pt, Cocone.precompose_obj_pt, Cofork.ofπ_pt,
            Cofork.π_ofπ, Iso.refl_hom, Category.comp_id, Cofork.π_precompose,
            parallelPair_obj_one]
          change cokernel.π (F.map h.f') = 𝟙 (F.obj h.K) ≫ cokernel.π (F.map h.f')
          rw [Category.id_comp]) }

/-- The comparison from termwise application to derived application, transported to
complexes. Source: Stacks Project, Tag 079V, definition of right derived functor.
(blueprint: lem-sc-left-exact-upper-truncation-comparison). -/
noncomputable def complexDerivedUnit :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
    (DerivedCategory.quotientCompQhIso D)).inv ≫
  whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) F.rightDerivedFunctorUnit ≫
  (isoWhiskerRight (DerivedCategory.quotientCompQhIso C) F.rightDerivedFunctor).hom

/-- The actual map from the cokernel of mapped boundaries to derived cohomology of
upper truncation. All inverses are inverses of specified isomorphisms.
Source: Stacks Project, Tag 0AVW, canonical cycle calculation.
(blueprint: lem-sc-left-exact-upper-truncation-comparison). -/
noncomputable def upperTruncationBoundaryComparison (I : CochainComplex C ℤ) (n : ℤ) :
    cokernel (F.map (I.sc n).homologyData.left.f') ⟶
      (DerivedCategory.homologyFunctor D n).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj (I.truncLE n))) :=
  have : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map (I.ιTruncLE n)) n) :=
    (F.upperTruncation_comparisons I n).1
  (F.mappedCyclesHomologyData I n).homologyIso.inv ≫
    CategoryTheory.inv (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map (I.ιTruncLE n)) n) ≫
    ((DerivedCategory.homologyFunctorFactors D n).app
      ((F.mapHomologicalComplex (.up ℤ)).obj (I.truncLE n))).inv ≫
    (DerivedCategory.homologyFunctor D n).map
      (F.complexDerivedUnit.app (I.truncLE n))

/-- The upper-truncation unit is invertible in the top degree of a K-injective complex.
Source: Stacks Project, Tag 05TC (2), and Tag 079V, derived comparison naturality.
(blueprint: lem-sc-left-exact-upper-truncation-comparison).
Proof: Apply degree-n homology to the naturality square for the truncation inclusion.
Its two vertical arrows are invertible by upperTruncation_comparisons. The bottom
unit is invertible because I is K-injective. Cancel the right vertical arrow. -/
theorem isIso_complexDerivedUnit_upperTruncation
    (I : CochainComplex C ℤ) [I.IsKInjective] (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor D n).map
      (F.complexDerivedUnit.app (I.truncLE n))) := by
  let H := DerivedCategory.homologyFunctor D n
  let i := I.ιTruncLE n
  obtain ⟨hraw, hderived⟩ := F.upperTruncation_comparisons I n
  have : IsIso (H.map (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map i))) :=
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors D n)
      ((F.mapHomologicalComplex (.up ℤ)).map i)).2 hraw
  have : IsIso (F.complexDerivedUnit.app I) := by
    dsimp [complexDerivedUnit]
    infer_instance
  have hnat := congrArg H.map (F.complexDerivedUnit.naturality i)
  simp only [Functor.comp_map, Functor.map_comp] at hnat
  have : IsIso (H.map (F.complexDerivedUnit.app (I.truncLE n)) ≫
      H.map (F.rightDerivedFunctor.map (DerivedCategory.Q.map i))) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (H.map (F.rightDerivedFunctor.map (DerivedCategory.Q.map i)))

end CategoryTheory.Functor
