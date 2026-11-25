/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicConstructibleFiniteReductions
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientScalarEquivalence
import WeilConjectures.AlgebraicGeometry.NilpotentReductionLissity
import all WeilConjectures.AlgebraicGeometry.NilpotentReductionStep
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Lissity reflected by a nilpotent surjection of constant coefficients

Source: Stacks Project, Cohomology on Sites, Tag 094I.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

universe w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion
namespace SheafOfModules

private theorem extensionModelIso {D : Type w} [SmallCategory D]
    (T : GrothendieckTopology D) {B R : Type w} [CommRing B] [CommRing R]
    (f : B →+* R) (K : ConstantCompletion.D (constant T B)) :
    letI := HasDerivedCategory.standard (Mod (constant T B))
    letI := HasDerivedCategory.standard (Mod (constant T R))
    Nonempty ((constantCoefficientScalarExtension T f).obj K ≅
      (AlgebraicGeometry.Scheme.adicFiniteExtension T f).obj K) := by
  let := HasDerivedCategory.standard (Mod (constant T B))
  let := HasDerivedCategory.standard (Mod (constant T R))
  let φ := AlgebraicGeometry.Scheme.adicFiniteConstantMap f T
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (DerivedCategory.Q.objPreimage K)
  have : QuasiIso s := hs
  let eP : (Q (constant T B)).obj P ≅ K :=
    asIso ((Q (constant T B)).map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨E, ho, hm, hadd, ⟨e⟩⟩ := reduction_model T f P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hP)
  have hE : E = change φ := CategoryTheory.Functor.ext ho (fun _ _ g ↦ hm g)
  subst E
  have : IsIso ((extendComparison φ).app P) := (derivedExtension φ).computation P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hP)
  exact ⟨(constantCoefficientScalarExtension T f).mapIso eP.symm ≪≫ e.symm ≪≫
    (asIso ((extendComparison φ).app P)).symm ≪≫ (extend φ).mapIso eP⟩

private theorem lisse_iso {D : Type w} [SmallCategory D]
    (T : GrothendieckTopology D) (B : Type w) [CommRing B]
    {F G : Mod (constant T B)} (e : F ≅ G)
    (h : IsLocallyConstantFiniteTypeModules T B G) :
    IsLocallyConstantFiniteTypeModules T B F := by
  intro V
  obtain ⟨S, hS, hm⟩ := h V
  refine ⟨S, hS, ?_⟩
  intro U f hf
  obtain ⟨M, hM, ⟨i⟩⟩ := hm U f hf
  exact ⟨M, hM, ⟨(overFunctor _ U).mapIso e ≪≫ i⟩⟩

/-- A nilpotent surjection of constant coefficient rings reflects lissity of a bounded-above
complex. Source: Stacks Project, Cohomology on Sites, Tag 094I.
(auxiliary; not a blueprint node).

Proof: factor f through B/ker(f) and the canonical quotient isomorphism to R. Both
presentations of derived scalar extension are computed by the same K-flat model.
Scalar associativity and the quotient isomorphism transport the hypothesis to reduction
modulo ker(f). Apply nilpotent-reduction lissity, using the nilpotence exponent of the
kernel. The construction works for the zero ring and for the empty site. -/
theorem lisse_of_nilpotent_coefficient_surjection
    {D : Type w} [SmallCategory D] [HasPullbacks D] (T : GrothendieckTopology D)
    {B R : Type w} [CommRing B] [CommRing R] [IsNoetherianRing B]
    (f : B →+* R) (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (K : ConstantCompletion.D (constant T B))
    (hbounded : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero ((coefficientModelCohomology _ q).obj K))
    (hmod : ∀ q : ℤ, IsLocallyConstantFiniteTypeModules T R
      ((coefficientModelCohomology _ q).obj
        ((AlgebraicGeometry.Scheme.adicFiniteExtension T f).obj K))) :
    ∀ q : ℤ, IsLocallyConstantFiniteTypeModules T B
      ((coefficientModelCohomology _ q).obj K) := by
  let := HasDerivedCategory.standard (Mod (constant T B))
  let := HasDerivedCategory.standard (Mod (constant T R))
  let I := RingHom.ker f
  let := HasDerivedCategory.standard (Mod (constant T (B ⧸ I)))
  let q := Ideal.Quotient.mk I
  let e := f.quotientKerEquivOfSurjective hf
  have he : f = e.toRingHom.comp q := by
    ext x
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk hf x).symm
  let L := (AlgebraicGeometry.Scheme.adicFiniteExtension T q).obj K
  obtain ⟨iL⟩ := extensionModelIso T e.toRingHom L
  let ic := (AlgebraicGeometry.Scheme.adicFiniteExtensionComp T q e.toRingHom f he).app K
  have hL (j : ℤ) : IsLocallyConstantFiniteTypeModules T (B ⧸ I)
      ((coefficientModelCohomology _ j).obj L) := by
    apply locallyConstantFiniteTypeModules_of_scalarExtension_bijective
      T e.toRingHom e.bijective L j
    exact lisse_iso T R ((coefficientModelCohomology _ j).mapIso (iL ≪≫ ic)) (hmod j)
  obtain ⟨iq⟩ := extensionModelIso T q K
  have hq (j : ℤ) : IsLocallyConstantFiniteTypeModules T (B ⧸ I)
      ((coefficientModelCohomology _ j).obj
        ((constantCoefficientScalarExtension T q).obj K)) :=
    lisse_iso T (B ⧸ I) ((coefficientModelCohomology _ j).mapIso iq) (hL j)
  have hT : T.toPrecoverage.toGrothendieck = T := by
    apply le_antisymm T.toGrothendieck_toPrecoverage_le
    intro V S hS
    simpa only [Sieve.generate_sieve] using
      Precoverage.generate_mem_toGrothendieck ((T.arrows_mem_toPrecoverage_iff S).mpr hS)
  have hn := locallyConstantFiniteTypeModules_reduction_pow.{w, w + 1} T.toPrecoverage
  rw [hT] at hn
  let (I' : Ideal B) := HasDerivedCategory.standard (Mod (constant T (B ⧸ I')))
  have h := (hn B I K hbounded hq).2
  obtain ⟨m, hm⟩ := hnil
  have hm' : I ^ (m + 1) = ⊥ := by
    rw [pow_succ, hm, zero_mul]
    rfl
  exact h (m + 1) (Nat.succ_pos m) hm'

end SheafOfModules
