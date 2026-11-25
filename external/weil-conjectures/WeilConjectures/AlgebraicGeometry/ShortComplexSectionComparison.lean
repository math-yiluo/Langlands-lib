/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # The section comparison for a short complex

Source: Stacks Project, Tags 015B and 01E4.
(blueprint: lem-pc-short-complex-section-comparison)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section

/-- Left exactness and preservation of the two quotient epimorphisms preserve left homology. -/
private theorem preservesLeftHomologyOf_of_section_epis
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] (S : ShortComplex C)
    [Epi (F.map (factorThruImage S.toCycles))] [Epi (F.map S.homologyπ)] :
    F.PreservesLeftHomologyOf S := by
  let T := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
  have hT : T.Exact := T.exact_of_g_is_cokernel S.homologyIsCokernel
  let B := ShortComplex.mk (image.ι S.toCycles) S.homologyπ
    (image_ι_comp_eq_zero S.toCycles_comp_homologyπ)
  have hB : B.Exact := B.exact_of_f_is_kernel hT.isLimitImage'
  have hBF : (B.map F).Exact :=
    hB.map_of_mono_of_preservesKernel F inferInstance inferInstance
  let φ : T.map F ⟶ B.map F :=
    { τ₁ := F.map (factorThruImage S.toCycles)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, B, ← F.map_comp] }
  have hTF : (T.map F).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hBF
  have : Epi (T.map F).g := inferInstanceAs (Epi (F.map S.homologyπ))
  have hp : IsColimit (F.mapCocone
      (CokernelCofork.ofπ S.homologyπ S.toCycles_comp_homologyπ)) := by
    exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm hTF.gIsCokernel
  have : PreservesColimit (parallelPair S.toCycles 0) F :=
    preservesColimit_of_preserves_colimit_cocone S.homologyIsCokernel hp
  have : (ShortComplex.LeftHomologyData.canonical S).IsPreservedBy F :=
    ⟨inferInstance, by simpa only [ShortComplex.LeftHomologyData.canonical_f'] using
      (inferInstance : PreservesColimit (parallelPair S.toCycles 0) F)⟩
  exact Functor.PreservesLeftHomologyOf.mk' F
    (ShortComplex.LeftHomologyData.canonical S)

private theorem homologyπ_mapHomologyIso_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C) [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := ShortComplex.LeftHomologyData.canonical S
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% (h.map F).homologyπ_comp_homologyIso_hom]
  simp only [ShortComplex.LeftHomologyData.map_π]
  rw [← F.map_comp, h.π_comp_homologyIso_inv, F.map_comp]

private theorem mapHomologyIso_inv_homologyπ
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C) [F.PreservesLeftHomologyOf S] :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  rw [← cancel_epi (S.mapCyclesIso F).hom, ← reassoc_of% (homologyπ_mapHomologyIso_hom F S),
    Iso.hom_inv_id_assoc]
  simp

private theorem adjoint_homology_comparison_cycles
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) (U : D ⥤ C) [L.PreservesZeroMorphisms] [U.PreservesZeroMorphisms]
    [L.PreservesHomology] [PreservesFiniteLimits U] (adj : L ⊣ U)
    (S : ShortComplex D) :
    let P := S.map U
    let k := (P.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ S.cyclesIsKernel U)).inv
    P.homologyπ ≫ adj.homEquiv P.homology S.homology
        ((P.mapHomologyIso L).inv ≫ ShortComplex.homologyMap
          (S.mapNatTrans adj.counit)) = k ≫ U.map S.homologyπ := by
  dsimp only
  let P := S.map U
  let k := (P.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ S.cyclesIsKernel U)).inv
  have hk : k ≫ U.map S.iCycles = P.iCycles := by
    exact P.isoCyclesOfIsLimit_inv_ι _
  let φ : P.map L ⟶ S := S.mapNatTrans adj.counit
  have hc : (P.mapCyclesIso L).inv ≫ ShortComplex.cyclesMap φ =
      L.map k ≫ adj.counit.app S.cycles := by
    apply (cancel_mono S.iCycles).1
    rw [Category.assoc, ShortComplex.cyclesMap_i]
    change (P.mapCyclesIso L).inv ≫ (P.map L).iCycles ≫
      adj.counit.app S.X₂ = (L.map k ≫ adj.counit.app S.cycles) ≫ S.iCycles
    have hi : (P.mapCyclesIso L).inv ≫ (P.map L).iCycles = L.map P.iCycles := by
      rw [← ShortComplex.mapCyclesIso_hom_iCycles P L,
        Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hi]
    have hn := adj.counit.naturality S.iCycles
    change L.map (U.map S.iCycles) ≫ adj.counit.app S.X₂ =
      adj.counit.app S.cycles ≫ S.iCycles at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← L.map_comp, hk]
  apply (adj.homEquiv _ _).symm.injective
  rw [← adj.homEquiv_naturality_left, Equiv.symm_apply_apply,
    adj.homEquiv_counit, L.map_comp, Category.assoc]
  change L.map P.homologyπ ≫ ((P.mapHomologyIso L).inv ≫
    ShortComplex.homologyMap φ) = L.map k ≫ L.map (U.map S.homologyπ) ≫
    adj.counit.app S.homology
  rw [← Category.assoc, mapHomologyIso_inv_homologyπ,
    Category.assoc, ShortComplex.homologyπ_naturality, ← Category.assoc, hc]
  have hn := adj.counit.naturality S.homologyπ
  change L.map (U.map S.homologyπ) ≫ adj.counit.app S.homology =
    adj.counit.app S.cycles ≫ S.homologyπ at hn
  simp only [hn, Category.assoc]

private theorem evaluated_adjoint_homology_comparison_isIso
    {C D A : Type*} [Category C] [Category D] [Category A]
    [Abelian C] [Abelian D] [Abelian A]
    (L : C ⥤ D) (U : D ⥤ C) (E : C ⥤ A)
    [L.PreservesZeroMorphisms] [U.PreservesZeroMorphisms] [E.PreservesZeroMorphisms]
    [L.PreservesHomology] [E.PreservesHomology] [PreservesFiniteLimits U]
    (adj : L ⊣ U) (S : ShortComplex D) [(U ⋙ E).PreservesLeftHomologyOf S] :
    IsIso (E.map (adj.homEquiv (S.map U).homology S.homology
      (((S.map U).mapHomologyIso L).inv ≫
        ShortComplex.homologyMap (S.mapNatTrans adj.counit)))) := by
  let P := S.map U
  let k := (P.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ S.cyclesIsKernel U)).inv
  let t := adj.homEquiv P.homology S.homology
    ((P.mapHomologyIso L).inv ≫ ShortComplex.homologyMap (S.mapNatTrans adj.counit))
  have ht : P.homologyπ ≫ t = k ≫ U.map S.homologyπ :=
    adjoint_homology_comparison_cycles L U adj S
  have hk : k ≫ U.map S.iCycles = P.iCycles := P.isoCyclesOfIsLimit_inv_ι _
  have hc : (P.mapCyclesIso E).hom ≫ E.map k = (S.mapCyclesIso (U ⋙ E)).hom := by
    apply (cancel_mono ((U ⋙ E).map S.iCycles)).1
    change ((P.mapCyclesIso E).hom ≫ E.map k) ≫ E.map (U.map S.iCycles) = _
    rw [Category.assoc, ← E.map_comp, hk]
    exact P.mapCyclesIso_hom_iCycles E |>.trans
      (S.mapCyclesIso_hom_iCycles (U ⋙ E)).symm
  have he : (P.mapHomologyIso E).hom ≫ E.map t = (S.mapHomologyIso (U ⋙ E)).hom := by
    apply (cancel_epi (P.map E).homologyπ).1
    rw [← Category.assoc, homologyπ_mapHomologyIso_hom, Category.assoc,
      ← E.map_comp, ht, E.map_comp, ← Category.assoc, hc]
    exact (homologyπ_mapHomologyIso_hom (U ⋙ E) S).symm
  have : E.map t = (P.mapHomologyIso E).inv ≫ (S.mapHomologyIso (U ⋙ E)).hom := by
    rw [← he, Iso.inv_hom_id_assoc]
  change IsIso (E.map t)
  rw [this]
  infer_instance

namespace AlgebraicGeometry.Scheme.Modules

private theorem epi_sections_of_h1_kernel_zero
    {Y : Scheme.{u}} {M N : Y.Modules} (f : M ⟶ N) [Epi f] (V : Y.Opens)
    (h : IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).obj
      ((restrictFunctor V.ι).obj (kernel f)))) :
    Epi ((SheafOfModules.evaluation Y.ringCatSheaf (op V)).map f) := by
  let R := restrictFunctor V.ι
  let : R.Additive := ⟨by intros; rfl⟩
  let F := RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace
  let : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.evaluation V.toScheme.ringCatSheaf (op ⊤)))
  let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hT : T.ShortExact := { exact := ShortComplex.exact_kernel f }
  have hTR : (T.map R).ShortExact := hT.map_of_exact R
  let : EnoughInjectives
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives V.toScheme.toRingedSpace).2
  obtain ⟨δ, _, hall⟩ := hTR.exists_rightDerived_full_long_exact F
  obtain ⟨_, _, _, hex, _⟩ := hall 0
  have hd : δ 0 = 0 := h.eq_of_tgt _ _
  have : Epi ((F.rightDerived 0).map (R.map f)) := hex.epi_f hd
  have : Epi (F.map (R.map f)) := by
    have hn := F.rightDerivedZeroIsoSelf.hom.naturality (R.map f)
    have hc : Epi ((F.rightDerived 0).map (R.map f) ≫
      F.rightDerivedZeroIsoSelf.hom.app (R.obj N)) := inferInstance
    rw [hn] at hc
    exact epi_of_epi (F.rightDerivedZeroIsoSelf.hom.app (R.obj M)) (F.map (R.map f))
  apply (ModuleCat.epi_iff_surjective _).mpr
  have hs := (ModuleCat.epi_iff_surjective (F.map (R.map f))).mp inferInstance
  change Function.Surjective (f.val.app (op (V.ι ''ᵁ ⊤))) at hs
  have htop : V.ι ''ᵁ ⊤ = V := by simp
  rw [htop] at hs
  exact hs

private noncomputable def kernel_homologyπ_iso_image
    {C : Type*} [Category C] [Abelian C] (S : ShortComplex C) :
    kernel S.homologyπ ≅ image S.f := by
  let T := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
  have hT : T.Exact := T.exact_of_g_is_cokernel S.homologyIsCokernel
  let e := IsLimit.conePointUniqueUpToIso (kernelIsKernel S.homologyπ) hT.isLimitImage'
  let e' : image S.toCycles ≅ image S.f :=
    image.isoStrongEpiMono (factorThruImage S.toCycles)
      (image.ι S.toCycles ≫ S.iCycles) (by rw [← Category.assoc, image.fac, S.toCycles_i])
  exact e ≪≫ e'

/-- First-cohomology vanishing of the incoming kernel and image suffices for the
canonical sheafification comparison of a short complex to be invertible on sections.
Source: Stacks Project, Tag 015B (degree-zero and degree-one exact sequence),
and Tag 01E4 (the canonical cocycle-to-sheaf-class comparison).
(blueprint: lem-pc-short-complex-section-comparison)

Proof: Put Z = ker(S.g), B = im(S.f), and L = ker(S.f). Restrict to V, which
preserves kernels, images and homology because open restriction is exact. In
0 -> L -> S.X1 -> B -> 0 the first-cohomology vanishing of L makes
Gamma(S.X1) -> Gamma(B) surjective. In 0 -> B -> Z -> S.homology -> 0 the
first-cohomology vanishing of B makes Gamma(Z) -> Gamma(S.homology) surjective
with kernel Gamma(B). Left exactness identifies Gamma(Z) with the kernel of
Gamma(S.g). Consequently Gamma(S.homology) is the cokernel of the incoming
map to that kernel, and the canonical homology comparison is an isomorphism.
Evaluation of a presheaf of modules followed by forgetting scalars is exact,
so its homology is precisely homology of the section short complex.
To identify the displayed arrow, commute exact sheafification with homology
using mapHomologyIso and apply the homology map of its counit at S. Under
the sheafification adjunction this sends a presheaf cycle class to the class
of the same cycle in S.homology: the unit sends the cycle to its sheafification,
and the counit returns it to S. This is also the map characterized by the
cokernel universal property above. Equality follows after precomposition with
the epimorphic homology projection from the cycles. Thus the displayed arrow,
including its specified adjunction normalization, is invertible. If S.f = 0,
its image is zero and the same proof applies; if V is empty all section groups
are zero. No boundedness or acyclicity of S.X2 or S.homology is required. -/
theorem shortComplex_sectionComparison_isIso
    {Y : Scheme.{u}} (S : ShortComplex (SheafOfModules.{u} Y.ringCatSheaf))
    (V : Y.Opens)
    (hkernel : IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).obj
      ((restrictFunctor V.ι).obj (kernel S.f))))
    (himage : IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).obj
      ((restrictFunctor V.ι).obj (image S.f)))) :
    IsIso (((PresheafOfModules.toPresheaf.{u} Y.ringCatSheaf.obj).map
      ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 Y.ringCatSheaf.obj)).homEquiv
        (S.map (SheafOfModules.forget.{u} Y.ringCatSheaf)).homology S.homology
        (((S.map (SheafOfModules.forget.{u} Y.ringCatSheaf)).mapHomologyIso
          (PresheafOfModules.sheafification.{u} (𝟙 Y.ringCatSheaf.obj))).inv ≫
          ShortComplex.homologyMap (S.mapNatTrans
            (PresheafOfModules.sheafificationAdjunction.{u}
              (𝟙 Y.ringCatSheaf.obj)).counit)))).app (op V)) := by
  let F := SheafOfModules.evaluation Y.ringCatSheaf (op V)
  let R := restrictFunctor V.ι
  have hk : IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).obj
      (R.obj (kernel (factorThruImage S.toCycles)))) := by
    let e := kernelFactorThruImage S.toCycles ≪≫
      (kernelCompMono S.toCycles S.iCycles).symm ≪≫ kernelIsoOfEq S.toCycles_i
    exact hkernel.of_iso
      ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).mapIso (R.mapIso e))
  have hb : IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).obj
      (R.obj (kernel S.homologyπ))) := by
    exact himage.of_iso
      ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).mapIso
        (R.mapIso (kernel_homologyπ_iso_image S)))
  have : Epi (F.map (factorThruImage S.toCycles)) :=
    epi_sections_of_h1_kernel_zero _ V hk
  have : Epi (F.map S.homologyπ) := epi_sections_of_h1_kernel_zero _ V hb
  let E := PresheafOfModules.toPresheaf.{u} Y.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat).obj (op V)
  let G := forget₂ (ModuleCat.{u} (Y.ringCatSheaf.obj.obj (op V))) AddCommGrpCat.{u}
  have : (F ⋙ G).PreservesLeftHomologyOf S := by
    have : Epi ((F ⋙ G).map (factorThruImage S.toCycles)) := by
      change Epi (G.map (F.map (factorThruImage S.toCycles)))
      infer_instance
    have : Epi ((F ⋙ G).map S.homologyπ) := by
      change Epi (G.map (F.map S.homologyπ))
      infer_instance
    exact preservesLeftHomologyOf_of_section_epis (F ⋙ G) S
  have : (SheafOfModules.forget.{u} Y.ringCatSheaf ⋙ E).PreservesLeftHomologyOf S :=
    inferInstanceAs ((F ⋙ G).PreservesLeftHomologyOf S)
  exact evaluated_adjoint_homology_comparison_isIso
    (PresheafOfModules.sheafification.{u} (𝟙 Y.ringCatSheaf.obj))
    (SheafOfModules.forget.{u} Y.ringCatSheaf) E
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 Y.ringCatSheaf.obj)) S

end AlgebraicGeometry.Scheme.Modules
