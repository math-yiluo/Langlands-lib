/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Incoming kernel and image acyclicity for integer complexes

Source: Stacks Project, Tags 015B and 08C2, conditions (3)(b) and (3)(c).
(blueprint: lem-sc-integer-section-acyclic-incoming-kernel-image).
-/

@[expose] public section

universe u v w
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

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

private theorem opcycles_shortExact {C : Type*} [Category C] [Abelian C]
    (S : ShortComplex C) :
    ∃ hw : S.homologyι ≫ factorThruImage S.fromOpcycles = 0,
      (ShortComplex.mk S.homologyι (factorThruImage S.fromOpcycles) hw).ShortExact := by
  have hw : S.homologyι ≫ factorThruImage S.fromOpcycles = 0 := by
    apply (cancel_mono (image.ι S.fromOpcycles)).1
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
  exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
                    (ShortComplex.exact_of_f_is_kernel _ S.homologyIsKernel)
          mono_f := inferInstance
          epi_g := inferInstance }

private def imageFromOpcyclesIso {C : Type*} [Category C] [Abelian C]
    (S : ShortComplex C) : image S.fromOpcycles ≅ image S.g := by
  have : StrongEpi (S.pOpcycles ≫ factorThruImage S.fromOpcycles) :=
    strongEpi_of_epi _
  exact image.isoStrongEpiMono (S.pOpcycles ≫ factorThruImage S.fromOpcycles)
    (image.ι S.fromOpcycles) (by simp)

private theorem cohomology_isZero_of_H {Y : Scheme.{u}} (M : Y.Modules) (q : ℕ)
    (h : Subsingleton (M.H q)) :
    IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace q).obj M) := by
  obtain ⟨e, _⟩ := exists_moduleCohomology_source_comparison Y q
  exact ModuleCat.isZero_iff_subsingleton.mpr ((e M).injective.subsingleton)

/-- The incoming kernel and image have vanishing first module cohomology if the
positive ordinary cohomology of differential cokernels and homology sheaves vanishes.
Source: Stacks Project, Tag 015B, applied to the cycle and opcycle sequences;
Tag 08C2, hypotheses (3)(b) and (3)(c).
(blueprint: lem-sc-integer-section-acyclic-incoming-kernel-image).

Proof: Write Q^j = coker(d^(j-1)), B^j = im(d^(j-1)), Z^j = ker(d^j).
The sequence 0 -> H^j(F) -> Q^j -> B^(j+1) -> 0 gives H^1(B^(j+1)) = 0,
because H^1(Q^j) and H^2(H^j(F)) vanish. Next,
0 -> B^j -> Z^j -> H^j(F) -> 0 gives H^1(Z^j) = 0 from the vanishing
of H^1(B^j) and H^1(H^j(F)). Open restriction preserves these short exact
sequences. The natural module/ordinary cohomology comparison converts the
hypotheses into zero objects in module right-derived sections. For the incoming
map in degree p, its kernel is Z^(p-1) and its image is B^p. Both identifications
come from the universal properties of kernels and images. This argument uses
only two adjacent degrees, so no boundedness or limiting argument is needed.
Zero complexes and empty opens satisfy the same sequences and identifications. -/
theorem integer_section_acyclic_incoming_kernel_image
    {Y : Scheme.{u}} (F : CochainComplex Y.Modules ℤ) (V : Y.Opens)
    (hcokernels : ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((cokernel (F.d (n - 1) n)).restrict V.ι).H (q + 1)))
    (hhomology : ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict V.ι).H (q + 1))) (p : ℤ) :
    IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).obj
      ((restrictFunctor V.ι).obj (kernel (F.sc p).f))) ∧
    IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).obj
      ((restrictFunctor V.ι).obj (image (F.sc p).f))) := by
  let A (M : Y.Modules) : Prop := ∀ r : ℕ, 0 < r →
    IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
      ((restrictFunctor V.ι).obj M))
  have hH (n : ℤ) : A (F.homology n) := by
    intro r hr
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    exact cohomology_isZero_of_H _ _ (hhomology n q)
  have hQ (n : ℤ) : A ((F.sc n).opcycles) := by
    intro r hr
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    have h := cohomology_isZero_of_H _ _ (hcokernels n q)
    let e : (F.sc n).opcycles ≅ cokernel (F.d (n - 1) n) :=
      (F.sc n).opcyclesIsoCokernel ≪≫
        eqToIso (congrArg (fun j : ℤ ↦ cokernel (F.d j n)) (CochainComplex.prev ℤ n))
    exact h.of_iso ((restrictFunctor V.ι ⋙
      RingedSpace.moduleCohomology V.toScheme.toRingedSpace (q + 1)).mapIso e)
  have hB (n : ℤ) : A (image (F.sc n).g) := by
    obtain ⟨hw, hT⟩ := opcycles_shortExact (F.sc n)
    intro r hr
    have h := cohomology_right_acyclic V
      (ShortComplex.mk (F.sc n).homologyι
        (factorThruImage (F.sc n).fromOpcycles) hw) hT (hH n) (hQ n) r hr
    exact h.of_iso ((restrictFunctor V.ι ⋙
      RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).mapIso
        (imageFromOpcyclesIso (F.sc n)).symm)
  have hBi (n : ℤ) : A (image (F.sc n).f) := by
    intro r hr
    let e : image (F.sc n).f ≅ image (F.sc (n - 1)).g :=
      eqToIso (by
        change image (F.d ((ComplexShape.up ℤ).prev n) n) =
          image (F.d (n - 1) ((ComplexShape.up ℤ).next (n - 1)))
        rw [CochainComplex.prev ℤ n, CochainComplex.next ℤ (n - 1), sub_add_cancel])
    exact (hB (n - 1) r hr).of_iso ((restrictFunctor V.ι ⋙
      RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).mapIso e)
  have hZ (n : ℤ) : A (F.cycles n) := by
    obtain ⟨hw, hT⟩ := boundary_shortExact (F.sc n)
    intro r hr
    exact cohomology_middle_acyclic V
      (ShortComplex.mk (boundaryInclusion (F.sc n)) (F.sc n).homologyπ hw)
      hT (hBi n) (hH n) r hr
  let e : kernel (F.sc p).f ≅ F.cycles (p - 1) :=
    eqToIso (by
      change kernel (F.d ((ComplexShape.up ℤ).prev p) p) =
        kernel (F.d (p - 1) ((ComplexShape.up ℤ).next (p - 1)))
      rw [CochainComplex.prev ℤ p, CochainComplex.next ℤ (p - 1), sub_add_cancel]) ≪≫
      (F.sc (p - 1)).cyclesIsoKernel.symm
  exact ⟨(hZ (p - 1) 1 (by decide)).of_iso ((restrictFunctor V.ι ⋙
    RingedSpace.moduleCohomology V.toScheme.toRingedSpace 1).mapIso e),
      hBi p 1 (by decide)⟩

end AlgebraicGeometry.Scheme.Modules
