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

/-! # Dimension shifting for the incoming differentials

Source: Stacks Project, Tags 015B and 015J.
(blueprint: lem-pc-section-acyclic-incoming-kernel-image)
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

private theorem outgoing_shortExact {C : Type v} [Category.{w} C] [Abelian C]
    (K : CochainComplex C ℕ) (n : ℕ) :
    ∃ hw : K.iCycles n ≫ factorThruImage (K.d n (n + 1)) = 0,
      (ShortComplex.mk (K.iCycles n) (factorThruImage (K.d n (n + 1))) hw).ShortExact := by
  have hw : K.iCycles n ≫ factorThruImage (K.d n (n + 1)) = 0 := by
    apply (cancel_mono (image.ι (K.d n (n + 1)))).1
    simp
  let T := ShortComplex.mk (K.iCycles n) (factorThruImage (K.d n (n + 1))) hw
  let φ : T ⟶ ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d n (n + 1)) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := image.ι (K.d n (n + 1))
      comm₁₂ := by simp [T]
      comm₂₃ := by simp [T] }
  refine ⟨hw, ?_⟩
  exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
                    (ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel n (n + 1) (by simp)))
          mono_f := inferInstance
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

/-- The kernels and images of incoming differentials of a nonnegative complex
are section-acyclic if its terms and homology are section-acyclic.
Source: Stacks Project, Tag 015B (long exact sequence), applied to the cycle and
boundary sequences in the proof of Tag 015J.
(blueprint: lem-pc-section-acyclic-incoming-kernel-image)

Proof: Write B^0 = 0, Z^n = ker(d^n), and B^(n+1) = im(d^n). Restriction to V
is exact and hence preserves these objects and the homology objects. Induct on n.
The sequence 0 -> B^n -> Z^n -> H^n(K) -> 0 shows that Z^n is acyclic once
B^n is acyclic: in each positive degree the cohomology of Z^n lies between the
zero cohomology of the two outer terms. The sequence
0 -> Z^n -> K^n -> B^(n+1) -> 0 then shows that B^(n+1) is acyclic: for r > 0,
H^r(B^(n+1)) lies between H^r(K^n) and H^(r+1)(Z^n), both zero.
The long exact sequences are for module right-derived global sections on V.
This proves the simultaneous induction from B^0 = 0. For p > 0 the incoming
kernel is Z^(p-1), and its image is B^p. For p = 0 Mathlib's incoming map is
K.d 0 0 = 0 (since the predecessor of zero is zero); its kernel is K^0,
acyclic by the term hypothesis, and its image is zero. Transport all assertions
through these kernel and image isomorphisms. The argument includes the zero
complex and the empty open, since zero objects have zero derived cohomology. -/
theorem section_acyclic_incoming_kernel_image
    {Y : Scheme.{u}} (K : CochainComplex Y.Modules ℕ) (V : Y.Opens)
    (hterms : ∀ (n r : ℕ), 0 < r →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj (K.X n))))
    (hhomology : ∀ (n r : ℕ), 0 < r →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj (K.homology n)))) :
    ∀ (p r : ℕ), 0 < r →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj (kernel (K.sc p).f))) ∧
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj (image (K.sc p).f))) := by
  let A (M : Y.Modules) : Prop := ∀ r : ℕ, 0 < r →
    IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
      ((restrictFunctor V.ι).obj M))
  have hzero : (K.sc 0).f = 0 := by
    change K.d ((ComplexShape.up ℕ).prev 0) 0 = 0
    simp
  have hbzero : IsZero (image (K.sc 0).f) := by
    rw [IsZero.iff_id_eq_zero]
    apply (cancel_epi (factorThruImage (K.sc 0).f)).1
    apply (cancel_mono (image.ι (K.sc 0).f)).1
    simp
  have habzero : A (image (K.sc 0).f) := by
    intro r _
    have : (RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).Additive := by
      dsimp [RingedSpace.moduleCohomology]
      infer_instance
    exact (RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).map_isZero
      ((restrictFunctor V.ι).map_isZero hbzero)
  have hc (n : ℕ) : A (K.cycles n) ∧ A (image (K.d n (n + 1))) := by
    induction n with
    | zero =>
      obtain ⟨hb, hB⟩ := boundary_shortExact (K.sc 0)
      have hz : A (K.cycles 0) := by
        intro r hr
        exact cohomology_middle_acyclic (Y := Y) V
          (ShortComplex.mk (boundaryInclusion (K.sc 0)) (K.sc 0).homologyπ hb)
          hB habzero (hhomology 0) r hr
      obtain ⟨hw, hT⟩ := outgoing_shortExact K 0
      refine ⟨hz, ?_⟩
      intro r hr
      exact cohomology_right_acyclic (Y := Y) V
        (ShortComplex.mk (K.iCycles 0) (factorThruImage (K.d 0 (0 + 1))) hw)
        hT hz (hterms 0) r hr
    | succ n ih =>
      have hb : A (image (K.sc (n + 1)).f) := by
        intro r hr
        let e : image (K.sc (n + 1)).f ≅ image (K.d n (n + 1)) :=
          eqToIso (congrArg (fun j : ℕ ↦ image (K.d j (n + 1)))
            (CochainComplex.prev_nat_succ n))
        exact IsZero.of_iso (ih.2 r hr)
          ((restrictFunctor V.ι ⋙ RingedSpace.moduleCohomology
            V.toScheme.toRingedSpace r).mapIso e)
      obtain ⟨hw, hB⟩ := boundary_shortExact (K.sc (n + 1))
      have hz : A (K.cycles (n + 1)) := by
        intro r hr
        exact cohomology_middle_acyclic (Y := Y) V
          (ShortComplex.mk (boundaryInclusion (K.sc (n + 1))) (K.sc (n + 1)).homologyπ hw)
          hB hb (hhomology (n + 1)) r hr
      obtain ⟨hw, hT⟩ := outgoing_shortExact K (n + 1)
      refine ⟨hz, ?_⟩
      intro r hr
      exact cohomology_right_acyclic (Y := Y) V
        (ShortComplex.mk (K.iCycles (n + 1)) (factorThruImage (K.d (n + 1) (n + 1 + 1))) hw)
        hT hz (hterms (n + 1)) r hr
  intro p r hr
  cases p with
  | zero =>
    refine ⟨?_, habzero r hr⟩
    have he : kernel (K.sc 0).f ≅ K.X 0 := by
      change kernel (K.d ((ComplexShape.up ℕ).prev 0) 0) ≅ K.X 0
      rw [CochainComplex.prev_nat_zero, show K.d 0 0 = 0 by simp]
      exact kernelZeroIsoSource
    exact IsZero.of_iso (hterms 0 r hr)
      ((restrictFunctor V.ι ⋙ RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).mapIso he)
  | succ n =>
    have he : K.cycles n ≅ kernel (K.sc (n + 1)).f := by
      let e₁ : kernel (K.sc n).g ≅ kernel (K.d n (n + 1)) :=
        eqToIso (congrArg (fun j : ℕ ↦ kernel (K.d n j)) (CochainComplex.next ℕ n))
      let e₂ : kernel (K.sc (n + 1)).f ≅ kernel (K.d n (n + 1)) :=
        eqToIso (congrArg (fun j : ℕ ↦ kernel (K.d j (n + 1)))
          (CochainComplex.prev_nat_succ n))
      exact (K.sc n).cyclesIsoKernel ≪≫ e₁ ≪≫ e₂.symm
    refine ⟨?_, ?_⟩
    · exact IsZero.of_iso ((hc n).1 r hr)
        ((restrictFunctor V.ι ⋙ RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).mapIso
          he.symm)
    · let e : image (K.sc (n + 1)).f ≅ image (K.d n (n + 1)) :=
        eqToIso (congrArg (fun j : ℕ ↦ image (K.d j (n + 1)))
          (CochainComplex.prev_nat_succ n))
      exact IsZero.of_iso ((hc n).2 r hr)
        ((restrictFunctor V.ι ⋙ RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).mapIso e)

end AlgebraicGeometry.Scheme.Modules
