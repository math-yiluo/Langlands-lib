/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization

/-!
# Finitely presented Zariski main finite factorization

## References

* Stacks Project, More on Morphisms, Tag 0F2N, with the quasi-compact and quasi-separated finite
  factor made explicit
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated quasi-finite morphism of finite presentation over a quasi-compact,
quasi-separated scheme factors through a finite, finitely presented, quasi-compact,
quasi-separated scheme by a quasi-compact open immersion. -/
theorem Scheme.Hom.exists_qcqs_finitePresentation_factorization
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (hq : f.IsQuasiFinite)
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (p : T ⟶ S),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsFinite p ∧
      LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p ∧
      j ≫ p = f ∧ CompactSpace T ∧ QuasiSeparatedSpace T := by
  have : LocallyQuasiFinite f := by
    apply locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
    intro s
    apply isDiscrete_iff_discreteTopology.mpr
    apply discreteTopology_iff_isOpen_singleton.mpr
    rintro ⟨x, hx⟩
    change f x = s at hx
    subst s
    have hopen := hq.2.2 x
    rw [← (f.fiberHomeo (f x)).isOpen_image] at hopen
    simpa only [Set.image_singleton, Scheme.Hom.asFiber,
      Homeomorph.apply_symm_apply] using hopen
  obtain ⟨T, j, p, hj, hjc, hp, hpfp, hjp⟩ :=
    f.exists_isOpenImmersion_isFinite_locallyOfFinitePresentation
  let := hp
  exact ⟨T, j, p, hj, hjc, hp, hpfp, inferInstance, inferInstance, hjp,
    QuasiCompact.compactSpace_of_compactSpace p, quasiSeparatedSpace_of_quasiSeparated p⟩

end AlgebraicGeometry
