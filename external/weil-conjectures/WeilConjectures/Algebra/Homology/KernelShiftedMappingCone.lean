/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The kernel of a degreewise epimorphism and its shifted mapping cone

Source: Stacks Project, Derived Categories, Tags 070M and 014Q; the chain-level
comparison implicit in the proof of Tag 070M
(blueprint: lem-weil-degreewise-epi-kernel-cocone-qis).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

private lemma prev_rel (p : ℤ) : (ComplexShape.up ℤ).Rel (p + (-1)) p := by
  change p + (-1) + 1 = p
  omega

private lemma next_rel (p : ℤ) : (ComplexShape.up ℤ).Rel p (p + 1) := rfl

private noncomputable def comparison
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) :
    kernel f ⟶ (mappingCone f)⟦(-1 : ℤ)⟧ where
  f p := (kernel.ι f).f p ≫
    homotopyCofiber.inlX f p (p + (-1)) (prev_rel p)
  comm' p q hpq := by
    obtain rfl : q = p + 1 := by simpa using hpq.symm
    rw [shiftFunctor_obj_d', Category.assoc]
    change (kernel.ι f).f p ≫ homotopyCofiber.inlX f p (p + (-1)) _ ≫
      ((-1 : ℤ).negOnePow • (mappingCone f).d (p + (-1)) (p + 1 + (-1))) =
      (kernel f).d p (p + 1) ≫ (kernel.ι f).f (p + 1) ≫
        homotopyCofiber.inlX f (p + 1) (p + 1 + (-1)) (prev_rel (p + 1))
    dsimp only [mappingCone, homotopyCofiber_d]
    simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
      Preadditive.comp_neg]
    have h : -( (kernel.ι f).f p ≫ homotopyCofiber.inlX f p (p + (-1))
        (prev_rel p) ≫ homotopyCofiber.d f (p + (-1)) p) =
        (kernel f).d p (p + 1) ≫ (kernel.ι f).f (p + 1) ≫
          homotopyCofiber.inlX f (p + 1) p (next_rel p) := by
      rw [homotopyCofiber.inlX_d f (p + (-1)) p (p + 1) (prev_rel p) (next_rel p)]
      simp only [Preadditive.comp_add, Preadditive.comp_neg]
      have hz : (kernel.ι f).f p ≫ f.f p = 0 := by
        simpa only [comp_f, zero_f] using congrArg (fun g ↦ g.f p) (kernel.condition f)
      simp only [reassoc_of% hz, zero_comp, add_zero, neg_neg]
      rw [reassoc_of% ((kernel.ι f).comm p (p + 1))]
    convert h using 1
    · simp only [show p + 1 + (-1) = p by omega, homotopyCofiber_X]
    · congr! 10 <;> omega
    · congr! 10 <;> omega

private lemma comparison_projections
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (p r : ℤ) (hr : r = p + (-1)) :
    (comparison f).f p ≫
        ((mappingCone f).shiftFunctorObjXIso (-1) p r hr).hom ≫
          homotopyCofiber.sndX f r = 0 ∧
    (comparison f).f p ≫
        ((mappingCone f).shiftFunctorObjXIso (-1) p r hr).hom ≫
          homotopyCofiber.fstX f r p (by change r + 1 = p; omega) =
            (kernel.ι f).f p := by
  subst r
  dsimp only [comparison, shiftFunctorObjXIso]
  simp

private noncomputable def quotientMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) :
    (mappingCone f)⟦(-1 : ℤ)⟧ ⟶ (mappingCone (𝟙 Q))⟦(-1 : ℤ)⟧ :=
  (mappingCone.map f (𝟙 Q) f (𝟙 Q) rfl)⟦(-1 : ℤ)⟧'

private lemma inl_quotientMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (p : ℤ) :
    homotopyCofiber.inlX f p (p + (-1)) (prev_rel p) ≫ (quotientMap f).f p =
      f.f p ≫ homotopyCofiber.inlX (𝟙 Q) p (p + (-1)) (prev_rel p) := by
  change (mappingCone.inl f).v p (p + (-1)) rfl ≫
    (mappingCone.map f (𝟙 Q) f (𝟙 Q) rfl).f (p + (-1)) = _
  simpa only [mappingCone.inl, HomComplex.Cochain.mk_v] using (by simp [mappingCone.map] :
    (mappingCone.inl f).v p (p + (-1)) rfl ≫
      (mappingCone.map f (𝟙 Q) f (𝟙 Q) rfl).f (p + (-1)) =
        f.f p ≫ (mappingCone.inl (𝟙 Q)).v p (p + (-1)) rfl)

private lemma inr_quotientMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (p : ℤ) :
    homotopyCofiber.inrX f (p + (-1)) ≫ (quotientMap f).f p =
      homotopyCofiber.inrX (𝟙 Q) (p + (-1)) := by
  change (mappingCone.inr f).f (p + (-1)) ≫
    (mappingCone.map f (𝟙 Q) f (𝟙 Q) rfl).f (p + (-1)) = _
  simpa only [mappingCone.inr, homotopyCofiber.inr_f] using (by simp [mappingCone.map] :
    (mappingCone.inr f).f (p + (-1)) ≫
      (mappingCone.map f (𝟙 Q) f (𝟙 Q) rfl).f (p + (-1)) =
        (mappingCone.inr (𝟙 Q)).f (p + (-1)))

private lemma quotientMap_fst
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (p : ℤ) :
    (quotientMap f).f p ≫
      homotopyCofiber.fstX (𝟙 Q) (p + (-1)) p (prev_rel p) =
        homotopyCofiber.fstX f (p + (-1)) p (prev_rel p) ≫ f.f p := by
  apply homotopyCofiber.ext_from_X f p (p + (-1)) (prev_rel p)
  · rw [← Category.assoc, inl_quotientMap, Category.assoc]
    simp
  · rw [← Category.assoc, inr_quotientMap]
    simp

private lemma quotientMap_snd
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (p : ℤ) :
    (quotientMap f).f p ≫ homotopyCofiber.sndX (𝟙 Q) (p + (-1)) =
      homotopyCofiber.sndX f (p + (-1)) := by
  apply homotopyCofiber.ext_from_X f p (p + (-1)) (prev_rel p)
  · rw [← Category.assoc, inl_quotientMap, Category.assoc]
    simp
  · rw [← Category.assoc, inr_quotientMap]
    simp

private lemma comparison_quotientMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) :
    comparison f ≫ quotientMap f = 0 := by
  ext p
  dsimp only [comp_f, comparison, zero_f]
  rw [Category.assoc, inl_quotientMap, ← Category.assoc]
  have hz : (kernel.ι f).f p ≫ f.f p = 0 := by
    simpa only [comp_f, zero_f] using congrArg (fun g ↦ g.f p) (kernel.condition f)
  rw [hz, zero_comp]

private lemma quotientMap_epi
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (hf : ∀ p : ℤ, Epi (f.f p)) (p : ℤ) :
    Epi ((quotientMap f).f p) := by
  have := hf p
  constructor
  intro Z a b hab
  apply homotopyCofiber.ext_from_X (𝟙 Q) p (p + (-1)) (prev_rel p)
  · apply (cancel_epi (f.f p)).1
    have h := congrArg
      (fun t ↦ homotopyCofiber.inlX f p (p + (-1)) (prev_rel p) ≫ t) hab
    rw [← Category.assoc, ← Category.assoc, inl_quotientMap] at h
    simpa only [Category.assoc] using h
  · simpa only [← Category.assoc, inr_quotientMap] using
      congrArg (fun t ↦ homotopyCofiber.inrX f (p + (-1)) ≫ t) hab

private lemma comparison_mono
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (p : ℤ) :
    Mono ((comparison f).f p) := by
  have h : (comparison f).f p ≫
      homotopyCofiber.fstX f (p + (-1)) p (prev_rel p) = (kernel.ι f).f p := by
    dsimp only [comparison]
    simp
  exact mono_of_mono_fac h

private noncomputable def comparisonSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (comparison f) (quotientMap f) (comparison_quotientMap f)

private lemma comparisonSequence_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (hf : ∀ p : ℤ, Epi (f.f p)) :
    (comparisonSequence f).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro p
  dsimp only [comparisonSequence, ShortComplex.map, eval_map]
  refine { exact := ?_, mono_f := comparison_mono f p, epi_g := quotientMap_epi f hf p }
  apply ShortComplex.exact_of_f_is_kernel
  have : Mono ((comparison f).f p) := comparison_mono f p
  apply KernelFork.IsLimit.ofι'
  intro A k hk
  have hk' : k ≫ (quotientMap f).f p = 0 := hk
  have hfst : (k ≫ homotopyCofiber.fstX f (p + (-1)) p (prev_rel p)) ≫
      f.f p = 0 := by
    rw [Category.assoc, ← quotientMap_fst, ← Category.assoc, hk', zero_comp]
  have hsnd : k ≫ homotopyCofiber.sndX f (p + (-1)) = 0 := by
    rw [← quotientMap_snd, ← Category.assoc, hk', zero_comp]
  let hkf := KernelFork.mapIsLimit _ (kernelIsKernel f) (eval C (ComplexShape.up ℤ) p)
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hkf
    (k ≫ homotopyCofiber.fstX f (p + (-1)) p (prev_rel p)) hfst
  refine ⟨l, ?_⟩
  change l ≫ (comparison f).f p = k
  apply homotopyCofiber.ext_to_X f (p + (-1)) p (prev_rel p)
  · dsimp only [comparison]
    simpa using hl
  · dsimp only [comparison]
    simpa using hsnd.symm

private lemma identityCone_homology_isZero
    {C : Type u} [Category.{v} C] [Abelian C] (Q : CochainComplex C ℤ) (n : ℤ) :
    IsZero (((mappingCone (𝟙 Q))⟦(-1 : ℤ)⟧).homology n) := by
  have h := ((mappingCone.homotopyToZeroOfId Q).shift (-1)).homologyMap_eq n
  rw [IsZero.iff_id_eq_zero]
  simpa using h

private lemma comparison_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (hf : ∀ p : ℤ, Epi (f.f p)) :
    QuasiIso (comparison f) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have hS := comparisonSequence_shortExact f hf
    have hm := (hS.homology_exact₁ (n - 1) n (by change n - 1 + 1 = n; omega)).mono_g
      ((identityCone_homology_isZero Q (n - 1)).eq_of_src _ _)
    have he := (hS.homology_exact₂ n).epi_f
      ((identityCone_homology_isZero Q n).eq_of_tgt _ _)
    change Mono (homologyMap (comparison f) n) at hm
    change Epi (homologyMap (comparison f) n) at he
    exact isIso_of_mono_of_epi _

/-- Source: Stacks Project, Derived Categories, Tags 070M and 014Q
(blueprint: lem-weil-degreewise-epi-kernel-cocone-qis).
The termwise kernel of a degreewise epimorphism maps quasi-isomorphically to the cone
shifted by `-1`. Mathlib orders the cone summands as `P^(r+1) ⊞ Q^r`, so the two
projection identities below specify the map written `(0, ι)` with the source's ordering.

Proof: (1) The kernel inclusion commutes with differentials, since `f` does. The cone
and shift differentials then show that `(0, ι)` is a chain map, using `ι ≫ f = 0`
[def-sp-abelian, def-weil-abstract-derived-category].
(2) Map the shifted cone to the shifted cone of `𝟙 Q` by `(y, x) ↦ (y, f x)`.
Degreewise this is the direct sum of the identity of `Q^(p-1)` and the kernel exact
sequence of `f^p`, giving a short exact sequence with kernel the displayed comparison.
The shifted identity cone is contractible by `h(y, q) = (0, -y)`, hence has zero
cohomology [def-sp-abelian, def-weil-abstract-derived-category].
(3) The short exact sequence gives a distinguished triangle
[lem-weil-pbc-complex-ses-triangle]. Compare it to the identity triangle on the kernel
[def-weil-triangulated-category]; the first and third components are isomorphisms, so
[lem-sf-triangle-morphism-iso] makes the localized comparison an isomorphism.
Cohomology factors through the localization [def-weil-abstract-derived-category], so
the comparison is a quasi-isomorphism and identifies these objects in the derived category. -/
theorem exists_kernel_to_shifted_mappingCone_of_degreewise_epi
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (hf : ∀ p : ℤ, Epi (f.f p)) :
    ∃ κ : kernel f ⟶ (mappingCone f)⟦(-1 : ℤ)⟧,
      (∀ p : ℤ,
        κ.f p ≫ ((mappingCone f).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
          homotopyCofiber.sndX f (p - 1) = 0 ∧
        κ.f p ≫ ((mappingCone f).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
          homotopyCofiber.fstX f (p - 1) p (by change p - 1 + 1 = p; omega) =
            (kernel.ι f).f p) ∧
      QuasiIso κ ∧
      Nonempty ((DerivedCategory.Q.obj (kernel f)) ≅
        DerivedCategory.Q.obj ((mappingCone f)⟦(-1 : ℤ)⟧)) := by
  have := comparison_quasiIso f hf
  refine ⟨comparison f, ?_, inferInstance, ?_⟩
  · intro p
    exact comparison_projections f p (p - 1) (by omega)
  · have := (DerivedCategory.isIso_Q_map_iff_quasiIso C (comparison f)).mpr inferInstance
    exact ⟨asIso (DerivedCategory.Q.map (comparison f))⟩

end CochainComplex
