/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomContinuity
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import all WeilConjectures.CategoryTheory.HomColimitExtension

/-! # Hom continuity for locally finitely presented integral coefficients -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

noncomputable local instance hasZeroMorphisms_condensedRingObj_integralLfpHom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

set_option backward.isDefEq.respectTransparency true in
-- Exact single-sheaf triangles carry the integral coefficient instance.
/-- Hom continuity for a locally finitely presented integral module on the scheme itself.
Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3) and Lemma 6.8.12.
(auxiliary; not a blueprint node)

Proof. Resolve P by the two locally finite free modules F₁ and F₀ in the integral
resolution theorem. For the fixed diagram N and its canonical colimit cocone, the
finite free continuity theorem gives the Hom-colimit property of F₁[0] and F₀[0]
in every integer shift. The short exact sequence F₁ → F₀ → P gives a distinguished
single-sheaf triangle. Rotate it once, so its first and third terms are F₀[0] and
F₁[0][1]. Shift stability and distinguished extension closure give the property
of P[0]. Evaluate it at the requested shift n. Every comparison is the canonical
colimit.desc on the original legs; no choice of a colimit or telescope is needed.
-/
theorem integral_lfp_hom_continuity
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X) P)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (CondensedRing.integralCoeff ℓ E) X)) ℤ)
    (hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (n : ℤ) :
    IsIso (colimit.desc _
      ((condensedShiftedHom (CondensedRing.integralCoeff ℓ E) X
        ((DerivedCategory.singleFunctor _ 0).obj P) n).mapCocone (colimit.cocone N))) := by
  obtain ⟨F₁, F₀, f, g, w, hs, hF₁, hF₀⟩ :=
    integral_lfp_locallyFree_resolution X ℓ E P hP
  let D := N ⋙ DerivedCategory.Q
  let c := DerivedCategory.Q.mapCocone (colimit.cocone N)
  have h₁ : homColimitProperty D c ((DerivedCategory.singleFunctor _ 0).obj F₁) := by
    intro q
    exact condensed_finite_free_hom_continuity X _ F₁ hF₁ N hN q
  have h₀ : homColimitProperty D c ((DerivedCategory.singleFunctor _ 0).obj F₀) := by
    intro q
    exact condensed_finite_free_hom_continuity X _ F₀ hF₀ N hN q
  have ht := hs.singleTriangle_distinguished
  have hp := homColimitProperty_extensions D c hs.singleTriangle.rotate
    (Pretriangulated.rot_of_distTriang _ ht) h₀
    (homColimitProperty_shift D c _ h₁ (1 : ℤ))
  exact hp n

end AlgebraicGeometry.ProEtale
