/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootInvariants
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

import WeilConjectures.RingTheory.RootAlgebraRegularAtRoot
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootDomainEtale
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootTorsorUnique
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-! # The connected torsor properties of a strict local root cover

## References

* Stacks Project, Tag 0EYG, the strictly local root-algebra paragraph
* Tag 09EV, the roots of unity calculation
* Stacks Project, Tag 0EYG, the paragraph forming A[x]/(x^e-f), and Tag 09EV, roots of unity and the
  Kummer subextension calculation
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The puncture of the regular root algebra is a connected etale rotation torsor. -/
theorem strict_local_root_torsor_properties
    (H : Type u) [CommRing H] [IsStrictlyHenselianLocalRing H]
    [IsRegularLocalRing H] (h : H)
    [IsRegularLocalRing (H ⧸ Ideal.span {h})]
    (hh : IsSMulRegular H h) (hhm : h ∈ IsLocalRing.maximalIdeal H)
    (n : ℕ) (hn : 0 < n ∧ IsUnit (n : H)) :
    let C := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H C))
    let V : (Spec (CommRingCat.of C)).Opens := PrimeSpectrum.basicOpen (algebraMap H C h)
    IsDomain C ∧ Etale (V.ι ≫ q) ∧
    (∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
        a.comp (algebraMap H C) = b.comp (algebraMap H C) →
        a (algebraMap H C h) ≠ 0 →
        ∃! ζ : rootsOfUnity n H, a.comp (rootRotation H h n ζ).toRingHom = b) := by
  dsimp only
  obtain ⟨hdom, het⟩ := strict_local_root_domain_etale H h hh hhm n hn
  have huniq := strict_local_root_torsor_unique H h hh hhm n hn
  exact ⟨hdom, het, huniq⟩

end AlgebraicGeometry.Scheme
