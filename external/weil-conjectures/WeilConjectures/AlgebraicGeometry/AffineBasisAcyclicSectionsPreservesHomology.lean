/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Finite section homology from cokernel and homology acyclicity

Source: Stacks Project, Tags 015B and 08C2.
(blueprint: lem-sc-affine-basis-acyclic-sections-preserves-homology).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

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

private def boundaryInclusion {C : Type v} [Category.{w} C] [Abelian C]
    (S : ShortComplex C) : image S.f ⟶ S.cycles :=
  S.liftCycles (image.ι S.f) (by
    apply (cancel_epi (factorThruImage S.f)).1
    simp)

private theorem boundaryInclusion_fac {C : Type v} [Category.{w} C] [Abelian C]
    (S : ShortComplex C) : boundaryInclusion S ≫ S.iCycles = image.ι S.f := by
  simp [boundaryInclusion]

private theorem boundary_shortExact {C : Type v} [Category.{w} C] [Abelian C]
    (S : ShortComplex C) :
    ∃ hb : boundaryInclusion S ≫ S.homologyπ = 0,
      (ShortComplex.mk (boundaryInclusion S) S.homologyπ hb).ShortExact := by
  have hf : factorThruImage S.f ≫ boundaryInclusion S = S.toCycles := by
    apply (cancel_mono S.iCycles).1
    simp [boundaryInclusion_fac]
  have hb : boundaryInclusion S ≫ S.homologyπ = 0 := by
    apply (cancel_epi (factorThruImage S.f)).1
    rw [← Category.assoc, hf, S.toCycles_comp_homologyπ, comp_zero]
  let T := ShortComplex.mk (boundaryInclusion S) S.homologyπ hb
  let φ : ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ ⟶ T :=
    { τ₁ := factorThruImage S.f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simpa [T] using hf
      comm₂₃ := by simp [T] }
  have hmono : Mono (boundaryInclusion S) := mono_of_mono_fac (boundaryInclusion_fac S)
  refine ⟨hb, ?_⟩
  exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
                    (ShortComplex.exact_of_g_is_cokernel _ S.homologyIsCokernel)
          mono_f := hmono
          epi_g := inferInstance }

private theorem cohomology_middle_acyclic {Y : Scheme.{u}} (V : Y.Opens)
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    (hleft : ∀ r : ℕ, 0 < r →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj S.X₁)))
    (hright : ∀ r : ℕ, 0 < r →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj S.X₃))) (r : ℕ) (hr : 0 < r) :
    IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
      ((restrictFunctor V.ι).obj S.X₂)) := by
  let : EnoughInjectives (SheafOfModules.{u} V.toScheme.ringCatSheaf) :=
    RingedSpace.moduleSheaves_abelian_enoughInjectives V.toScheme.toRingedSpace |>.2
  let F := RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace
  have : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (SheafOfModules.forget.{u} V.toScheme.ringCatSheaf ⋙
      PresheafOfModules.evaluation.{u} V.toScheme.ringCatSheaf.obj (op ⊤))
    infer_instance
  obtain ⟨δ, _, he⟩ := (hS.map_of_exact (restrictFunctor V.ι)).exists_rightDerived_full_long_exact F
  exact (he r).1.isZero_of_both_isZero (hleft r hr) (hright r hr)

private theorem cohomology_right_acyclic {Y : Scheme.{u}} (V : Y.Opens)
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    (hleft : ∀ r : ℕ, 0 < r →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj S.X₁)))
    (hmiddle : ∀ r : ℕ, 0 < r →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj S.X₂))) (r : ℕ) (hr : 0 < r) :
    IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
      ((restrictFunctor V.ι).obj S.X₃)) := by
  let : EnoughInjectives (SheafOfModules.{u} V.toScheme.ringCatSheaf) :=
    RingedSpace.moduleSheaves_abelian_enoughInjectives V.toScheme.toRingedSpace |>.2
  let F := RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace
  have : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (SheafOfModules.forget.{u} V.toScheme.ringCatSheaf ⋙
      PresheafOfModules.evaluation.{u} V.toScheme.ringCatSheaf.obj (op ⊤))
    infer_instance
  obtain ⟨δ, _, he⟩ := (hS.map_of_exact (restrictFunctor V.ι)).exists_rightDerived_full_long_exact F
  rcases (he r).2 with ⟨w₁, w₂, hex, _⟩
  exact hex.isZero_of_both_isZero (hmiddle r hr) (hleft (r + 1) (by omega))

private theorem quotient_boundary_shortExact
    {C : Type*} [Category C] [Abelian C] (S : ShortComplex C) :
    ∃ hw : S.homologyι ≫ factorThruImage S.fromOpcycles = 0,
      (ShortComplex.mk S.homologyι (factorThruImage S.fromOpcycles) hw).ShortExact := by
  have hw : S.homologyι ≫ factorThruImage S.fromOpcycles = 0 := by
    apply (cancel_mono (image.ι S.fromOpcycles)).mp
    simp
  let T := ShortComplex.mk S.homologyι (factorThruImage S.fromOpcycles) hw
  let φ : T ⟶ ShortComplex.mk S.homologyι S.fromOpcycles
      S.homologyι_comp_fromOpcycles :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := image.ι S.fromOpcycles
      comm₁₂ := by simp [T]
      comm₂₃ := by simp [T] }
  refine ⟨hw, ?_⟩
  exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
            (ShortComplex.exact_of_f_is_kernel _ S.homologyIsKernel)
          mono_f := inferInstance
          epi_g := inferInstance }

private noncomputable def outgoing_image_iso
    {C : Type*} [Category C] [Abelian C] (S : ShortComplex C) :
    image S.g ≅ image S.fromOpcycles := by
  let : StrongEpi (S.pOpcycles ≫ factorThruImage S.fromOpcycles) := strongEpi_of_epi _
  exact (image.isoStrongEpiMono (f := S.g)
    (S.pOpcycles ≫ factorThruImage S.fromOpcycles)
    (image.ι S.fromOpcycles) (by simp)).symm



/-- Acyclic differential cokernels and homology sheaves make sections preserve
left homology of the original complex. No term acyclicity or boundedness is needed.
Source: Stacks Project, Tags 015B and 08C2, finite cycle and boundary sequences.
(blueprint: lem-sc-affine-basis-acyclic-sections-preserves-homology).

Proof: Let C^r=coker(d^(r-1)) and B^(r+1)=im(d^r). The short exact sequence
0 → H^r(F) → C^r → B^(r+1) → 0 and the two acyclicity hypotheses imply
H^q(V,B^(r+1))=0 for q>0 by the long exact sequence. The image of the
induced differential out of C^r is canonically the image of d^r, because
F^r → C^r is epi. The sequence 0 → B^r → Z^r → H^r(F) → 0 then makes
Z^r acyclic. In particular both the incoming kernel Z^(n-1) and the incoming
image B^n have vanishing H^1 on V. The module-to-abelian cohomology comparison
translates these vanishings to right-derived module sections. For an epi with
H^1-acyclic kernel the initial long exact sequence makes its section map epi.
Apply this to the incoming map onto boundaries and the cycle-class quotient.
Left exactness identifies section cycles and section boundaries; exactness and
the latter epi make sections of H^n(F) the cokernel of the section differential
into cycles. Thus sections preserve the canonical left homology data.
Restriction is exact and all comparison isomorphisms preserve the actual maps.
This works for every integer degree, empty V and zero complexes. Only W=V is
needed, so the basis hypotheses here are stronger than the finite argument uses. -/
theorem affineBasisAcyclicSections_preservesLeftHomology
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    (F : CochainComplex X.Modules ℤ)
    (hcokernels : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((cokernel (F.d (n - 1) n)).restrict W.ι).H (q + 1)))
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1))) (n : ℤ) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    S.PreservesLeftHomologyOf (F.sc n) := by
  dsimp
  let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
  let : S.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
  let R := Scheme.Modules.restrictFunctor V.ι
  let A (M : X.Modules) : Prop := ∀ q : ℕ, 0 < q →
    IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace q).obj (R.obj M))
  have convertH (M : X.Modules) (h : ∀ q : ℕ, Subsingleton ((M.restrict V.ι).H (q + 1))) :
      A M := by
    intro q hq
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    let := h r
    obtain ⟨e, _⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison V.toScheme (r + 1)
    have : Subsingleton ((RingedSpace.moduleCohomology
        V.toScheme.toRingedSpace (r + 1)).obj (R.obj M)) :=
      (e (R.obj M)).injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have hh (r : ℤ) : A (F.homology r) :=
    convertH _ (hhomology V hV le_rfl r)
  have hop (r : ℤ) : A (F.opcycles r) := by
    have hc : A (cokernel (F.d (r - 1) r)) :=
      convertH _ (hcokernels V hV le_rfl r)
    have e : F.opcycles r ≅ cokernel (F.d (r - 1) r) :=
      (F.sc r).opcyclesIsoCokernel ≪≫ eqToIso
        (congrArg (fun a : ℤ ↦ cokernel (F.d a r)) (CochainComplex.prev ℤ r))
    intro q hq
    exact (hc q hq).of_iso
      ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace q).mapIso (R.mapIso e))
  have hbout (r : ℤ) : A (image (F.sc r).g) := by
    obtain ⟨hw, hT⟩ := quotient_boundary_shortExact (F.sc r)
    have hb : A (image (F.sc r).fromOpcycles) := by
      intro q hq
      exact cohomology_right_acyclic V
        (ShortComplex.mk (F.sc r).homologyι (factorThruImage (F.sc r).fromOpcycles) hw)
        hT (hh r) (hop r) q hq
    intro q hq
    exact (hb q hq).of_iso
      ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace q).mapIso
        (R.mapIso (outgoing_image_iso (F.sc r))))
  have hbin (r : ℤ) : A (image (F.sc r).f) := by
    have e : image (F.sc r).f ≅ image (F.sc (r - 1)).g := by
      have he : (ComplexShape.up ℤ).next (r - 1) = r := by
        rw [CochainComplex.next]
        omega
      exact eqToIso
        (congrArg (fun a : ℤ ↦ image (F.d a r)) (CochainComplex.prev ℤ r)) ≪≫
        (eqToIso (congrArg (fun a : ℤ ↦ image (F.d (r - 1) a)) he)).symm
    intro q hq
    exact (hbout (r - 1) q hq).of_iso
      ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace q).mapIso (R.mapIso e))
  have hz (r : ℤ) : A (F.cycles r) := by
    obtain ⟨hw, hT⟩ := boundary_shortExact (F.sc r)
    intro q hq
    exact cohomology_middle_acyclic V
      (ShortComplex.mk (boundaryInclusion (F.sc r)) (F.sc r).homologyπ hw)
      hT (hbin r) (hh r) q hq
  have hk : A (kernel (F.sc n).f) := by
    have e : kernel (F.sc n).f ≅ F.cycles (n - 1) := by
      have he : (ComplexShape.up ℤ).next (n - 1) = n := by
        rw [CochainComplex.next]
        omega
      exact eqToIso
        (congrArg (fun a : ℤ ↦ kernel (F.d a n)) (CochainComplex.prev ℤ n)) ≪≫
        (eqToIso (congrArg (fun a : ℤ ↦ kernel (F.d (n - 1) a)) he)).symm ≪≫
        (F.sc (n - 1)).cyclesIsoKernel.symm
    intro q hq
    exact (hz (n - 1) q hq).of_iso
      ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace q).mapIso (R.mapIso e))
  have hk' : IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).obj
      (R.obj (kernel (factorThruImage (F.sc n).toCycles)))) := by
    let e := kernelFactorThruImage (F.sc n).toCycles ≪≫
      (kernelCompMono (F.sc n).toCycles (F.sc n).iCycles).symm ≪≫
      kernelIsoOfEq (F.sc n).toCycles_i
    exact (hk 1 (by decide)).of_iso
      ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).mapIso (R.mapIso e))
  have hb' : IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).obj
      (R.obj (kernel (F.sc n).homologyπ))) := by
    exact (hbin n 1 (by decide)).of_iso
      ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).mapIso
        (R.mapIso (kernel_homologyπ_iso_image (F.sc n))))
  have : Epi (S.map (factorThruImage (F.sc n).toCycles)) :=
    epi_sections_of_h1_kernel_zero _ V hk'
  have : Epi (S.map (F.sc n).homologyπ) := epi_sections_of_h1_kernel_zero _ V hb'
  exact preservesLeftHomologyOf_of_section_epis S (F.sc n)


end AlgebraicGeometry
