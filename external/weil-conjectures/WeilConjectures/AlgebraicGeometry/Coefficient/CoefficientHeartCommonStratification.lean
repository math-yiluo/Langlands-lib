/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseRestriction
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement

/-!
# Common stratifications and restriction of coefficient modules

Source: Weil blueprint, sec-six-functors-basics/sk-lem-coefficient-heart/
sk-lem-coefficient-heart-common-stratification.md, clauses (1)--(3)
(blueprint: lemma-constructible-sheaves).

Refinement means containment of stratum images, with their given scheme structures.
No factorization through a stratum is inferred from containment of images.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private noncomputable def coefficientPullbackForgetIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.upperStar Λ f ⋙ Mod.forget (condensedRingObj Λ X) ≅
      Mod.forget (condensedRingObj Λ Y) ⋙ upperStar Ab.{u + 1} f :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)))
    (Mod.forget (condensedRingObj Λ X))

private lemma coefficientSheafZero
    {X : Scheme.{u}} [IsNoetherian X] (R : X.FiniteLocallyClosedStratification)
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (hF : ∀ a : Fin R.n, IsZero ((upperStar Ab.{u + 1} (R.immersion a)).obj F)) :
    IsZero F := by
  let S := Scheme.Stratification.ofNoetherianSpace R.n R.stratum
    R.isLocallyClosed_stratum R.iUnion_stratum_eq_univ R.pairwise_disjoint_stratum
    R.domain R.immersion R.isImmersion R.range_immersion
  apply Scheme.proEtale_isZero_of_stratum_cover.{u, u} X S
    (fun a ↦ .singleton (𝟙 (R.domain a)) (CategoryTheory.Precoverage.mem_coverings_of_isIso _)) F
  intro a j
  change IsZero ((Scheme.proEtaleSheafInverseImage (𝟙 (R.domain a) ≫ R.immersion a)
    Ab.{u + 1}).obj F)
  rw [Category.id_comp]
  exact hF a

private lemma coefficientModuleZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} [IsNoetherian X]
    (R : X.FiniteLocallyClosedStratification)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ a : Fin R.n, IsZero ((CondensedRing.upperStar Λ (R.immersion a)).obj M)) :
    IsZero M := by
  have h : IsZero ((Mod.forget (condensedRingObj Λ X)).obj M) := by
    apply coefficientSheafZero R
    intro a
    exact ((Mod.forget _).map_isZero (hM a)).of_iso
      ((coefficientPullbackForgetIso Λ (R.immersion a)).app M).symm
  rw [IsZero.iff_id_eq_zero]
  apply (Mod.forget (condensedRingObj Λ X)).map_injective
  simpa only [Functor.map_id, Functor.map_zero] using h.eq_of_src
    ((Mod.forget (condensedRingObj Λ X)).map (𝟙 M)) 0

private lemma coefficientMapZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} [IsNoetherian X]
    (R : X.FiniteLocallyClosedStratification)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : M ⟶ N)
    (hf : ∀ a : Fin R.n, (CondensedRing.upperStar Λ (R.immersion a)).map f = 0) :
    f = 0 := by
  have hz : IsZero (Abelian.image f) := by
    apply coefficientModuleZero Λ R
    intro a
    let F := CondensedRing.upperStar Λ (R.immersion a)
    have hz' : IsZero (Abelian.image (F.map f)) := by
      rw [hf a]
      exact isZero_kernel_of_mono _
    exact hz'.of_iso (Abelian.PreservesImage.iso F f)
  rw [← Abelian.image.fac f]
  exact (by rw [hz.eq_of_tgt (Abelian.factorThruImage f) 0, zero_comp])

private lemma coefficientMonoEpi
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} [IsNoetherian X]
    (R : X.FiniteLocallyClosedStratification)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : M ⟶ N) :
    (Mono f ↔ ∀ a : Fin R.n, Mono ((CondensedRing.upperStar Λ (R.immersion a)).map f)) ∧
    (Epi f ↔ ∀ a : Fin R.n, Epi ((CondensedRing.upperStar Λ (R.immersion a)).map f)) := by
  constructor
  · constructor
    · intro h a
      exact inferInstance
    · intro h
      apply Preadditive.mono_of_cancel_zero
      intro P g hg
      apply coefficientMapZero Λ R
      intro a
      have := h a
      apply zero_of_comp_mono ((CondensedRing.upperStar Λ (R.immersion a)).map f)
      rw [← Functor.map_comp, hg, Functor.map_zero]
  · constructor
    · intro h a
      exact inferInstance
    · intro h
      apply Preadditive.epi_of_cancel_zero
      intro P g hg
      apply coefficientMapZero Λ R
      intro a
      have := h a
      apply zero_of_epi_comp ((CondensedRing.upperStar Λ (R.immersion a)).map f)
      rw [← Functor.map_comp, hg, Functor.map_zero]

private lemma coefficientCompZero
    {C : Type*} [Category C] [Abelian C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    (h : imageSubobject f = kernelSubobject g) : f ≫ g = 0 := by
  have hh : (kernelSubobject g).Factors f := by
    rw [← h]
    simpa only [Category.id_comp] using imageSubobject_factors_comp_self f (𝟙 _)
  exact (kernelSubobject_factors_iff g f).mp hh

private lemma coefficientExactDetection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} [IsNoetherian X]
    (R : X.FiniteLocallyClosedStratification)
    {A B C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : A ⟶ B) (g : B ⟶ C) :
    imageSubobject f = kernelSubobject g ↔
      ∀ a : Fin R.n,
        imageSubobject ((CondensedRing.upperStar Λ (R.immersion a)).map f) =
          kernelSubobject ((CondensedRing.upperStar Λ (R.immersion a)).map g) := by
  constructor
  · intro h a
    let S := ShortComplex.mk f g (coefficientCompZero f g h)
    exact (S.map (CondensedRing.upperStar Λ (R.immersion a))).exact_iff_image_eq_kernel.mp
      (((S.exact_iff_image_eq_kernel).mpr h).map _)
  · intro h
    have w : f ≫ g = 0 := by
      apply coefficientMapZero Λ R
      intro a
      rw [Functor.map_comp]
      exact coefficientCompZero _ _ (h a)
    let S := ShortComplex.mk f g w
    apply S.exact_iff_image_eq_kernel.mp
    rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
    apply coefficientMapZero Λ R
    intro a
    let F := CondensedRing.upperStar Λ (R.immersion a)
    have he : (S.map F).Exact := (S.map F).exact_iff_image_eq_kernel.mpr (h a)
    rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at he
    obtain ⟨k, hk⟩ := kernel.lift' (F.map g) (F.map (kernel.ι g))
      (by rw [← F.map_comp, kernel.condition, Functor.map_zero])
    obtain ⟨l, hl⟩ := cokernel.desc' (F.map f) (F.map (cokernel.π f))
      (by rw [← F.map_comp, cokernel.condition, Functor.map_zero])
    change kernel.ι (F.map g) ≫ cokernel.π (F.map f) = 0 at he
    rw [F.map_comp, ← hl, ← hk, Category.assoc, reassoc_of% he, zero_comp, comp_zero]

/-- Exactness, monomorphisms and epimorphisms of coefficient modules are detected on every
finite locally closed stratification. Source: blueprint det-lem-coefficient-heart-common-
stratification, step (7). It uses exact inverse image for cartesian coefficients and the
finite-stratum zero-detection theorem on underlying abelian sheaves.
(blueprint: new-det-lem-coefficient-heart-common-stratification-exactness).

Proof: convert the finite locally closed stratification into a constructible scheme
stratification, and use identity covers in the existing Noetherian stratum-detection
theorem. The forgetful functor is faithful, so vanishing of underlying sheaves detects
vanishing of coefficient modules. Exact pullback preserves the image of a morphism;
therefore a morphism with zero restrictions has zero image and is zero. Cancellation
against these morphisms detects monomorphisms and epimorphisms. For arbitrary arrows
f and g, local exactness first forces f followed by g to vanish. Exactness is then
equivalent to the vanishing of the map from the kernel of g to the cokernel of f.
After restriction this map factors through the corresponding local kernel-to-cokernel
map, which vanishes. The established detection of zero morphisms finishes the proof.
-/
theorem coefficientHeart_commonStratification_exactness
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] (X : Scheme.{u}) [IsNoetherian X] :
  ∀ R : X.FiniteLocallyClosedStratification,
    (∀ a : Fin R.n,
      PreservesFiniteLimits (CondensedRing.upperStar (coefficientHeartRingObj Λ) (R.immersion a)) ∧
      PreservesFiniteColimits (CondensedRing.upperStar (coefficientHeartRingObj Λ) (R.immersion a))
        ∧
      Nonempty (CondensedRing.upperStar (coefficientHeartRingObj Λ) (R.immersion a) ⋙
          Mod.forget (condensedRingObj (coefficientHeartRingObj Λ) (R.domain a)) ≅
        Mod.forget (condensedRingObj (coefficientHeartRingObj Λ) X) ⋙ upperStar Ab.{u + 1}
          (R.immersion a))) ∧
    (∀ (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj
      (coefficientHeartRingObj Λ) X))
      (f : A ⟶ B),
      (Mono f ↔ ∀ a : Fin R.n, Mono ((CondensedRing.upperStar (coefficientHeartRingObj Λ)
        (R.immersion a)).map f)) ∧
      (Epi f ↔ ∀ a : Fin R.n, Epi ((CondensedRing.upperStar (coefficientHeartRingObj Λ) (R.immersion
        a)).map f))) ∧
    ∀ (A B C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj
      (coefficientHeartRingObj Λ) X))
      (f : A ⟶ B) (g : B ⟶ C),
      imageSubobject f = kernelSubobject g ↔
        ∀ a : Fin R.n,
          imageSubobject ((CondensedRing.upperStar (coefficientHeartRingObj Λ) (R.immersion a)).map
            f) =
            kernelSubobject ((CondensedRing.upperStar (coefficientHeartRingObj Λ) (R.immersion
              a)).map g) := by
  intro R
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact ⟨inferInstance, inferInstance,
      ⟨coefficientPullbackForgetIso (coefficientHeartRingObj Λ) (R.immersion a)⟩⟩
  · intro A B f
    exact coefficientMonoEpi (coefficientHeartRingObj Λ) R f
  · intro A B C f g
    exact coefficientExactDetection (coefficientHeartRingObj Λ) R f g

/-- Common refinement, lisse restriction, and detection of exactness on strata.
Source: blueprint sk-lem-coefficient-heart-common-stratification (1)--(3)
(blueprint: lemma-constructible-sheaves).

Proof: assemble the three independently proved clauses.
1. Intersect the finite input partitions and apply Noetherian induction on closed
subsets. Choose an irreducible nonempty relative open contained in one covering part,
then recursively stratify its proper closed complement. Closed tails give open prefixes.
Realize the pieces as vanishing-ideal subschemes in their open coborders. Their immersions
identify the domains with irreducible, hence connected, subsets.
2. Pull back finite-free covers to preserve lisse modules. Finite constant models give
local finite presentations. Transfer these presentations to a refined stratum through
the existing immersion-range theorem, retaining the given scheme structures. The
finite-subfield and algebraic-closure local-triviality lemmas give lisse restrictions.
3. Exact coefficient pullback has the underlying abelian-sheaf inverse image. Finite
stratum detection and faithful forgetfulness detect zero modules and zero morphisms.
Cancellation detects monomorphisms and epimorphisms. The kernel-to-cokernel criterion,
together with zero-morphism detection, detects exactness of arbitrary pairs. -/
theorem coefficientHeart_commonStratification (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] (X : Scheme.{u}) [IsNoetherian X]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ) :
    CoefficientHeartStratificationAssertions (coefficientHeartRingObj Λ) X := by
  refine ⟨coefficientHeart_commonStratification_refinement Λ X,
    coefficientHeart_commonStratification_lisse ℓ Λ X hΛ,
    coefficientHeart_commonStratification_exactness Λ X⟩

end AlgebraicGeometry.ProEtale
