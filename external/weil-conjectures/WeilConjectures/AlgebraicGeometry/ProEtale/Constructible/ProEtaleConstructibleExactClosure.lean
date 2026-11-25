/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre

/-!
# Exactness closure of globally constructible pro-etale sheaves

## References

* Stacks Project, Tags 09B5 and 093U, with the common global partition argument of Tag 03RZ
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Constructible module sheaves over a finite ring are closed under kernels,
cokernels and extensions, for the global finite-partition convention. -/
theorem constructibleProEtale_exactClosure
    (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    (∀ (F G : proEtaleRingModules Y (proEtaleConstantRing Y A)) (f : F ⟶ G),
      IsConstructibleProEtaleModuleSheaf Y A F →
      IsConstructibleProEtaleModuleSheaf Y A G →
      IsConstructibleProEtaleModuleSheaf Y A (kernel f) ∧
        IsConstructibleProEtaleModuleSheaf Y A (cokernel f)) ∧
    (∀ S : ShortComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)),
      S.ShortExact → IsConstructibleProEtaleModuleSheaf Y A S.X₁ →
      IsConstructibleProEtaleModuleSheaf Y A S.X₃ →
      IsConstructibleProEtaleModuleSheaf Y A S.X₂) := by
  have h (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
      IsConstructibleProEtaleModuleSheaf Y A F ↔
        IsConstructibleProEtaleCoefficientModuleSheaf Y (ULift.{u + 1, u} A) F :=
    (proEtaleModuleRestriction_constructible_iff Y A F).trans
      (CoefficientSerre.coefficient_constructible_iff Y (ULift.{u + 1, u} A) F).symm
  obtain ⟨hkc, hext⟩ := constructibleCoefficient_exactClosure Y (ULift.{u + 1, u} A)
  constructor
  · intro F G f hF hG
    obtain ⟨hk, hc⟩ := hkc F G f ((h F).mp hF) ((h G).mp hG)
    exact ⟨(h _).mpr hk, (h _).mpr hc⟩
  · intro S hS h₁ h₃
    exact (h _).mpr (hext S hS ((h _).mp h₁) ((h _).mp h₃))

end AlgebraicGeometry.Scheme
