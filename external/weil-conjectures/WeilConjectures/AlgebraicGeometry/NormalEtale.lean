/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.RingTheory.Etale.IntegrallyClosedLocalization

/-!
# Normality ascends along étale morphisms

If the local rings of a scheme `Y` are integrally closed domains, then so are the local rings
of every scheme étale over `Y` (Stacks `033C`, étale case). The local ring at a point `x` of an
étale `Y`-scheme `X` is the localization of an étale algebra over the ring of an affine open of
`Y`, at a prime whose contraction gives the local ring of `Y` at the image of `x`
(`Algebra.Etale.isDomain_and_isIntegrallyClosed_localization_of_comap`).

## Main statements

- `AlgebraicGeometry.IsAffineOpen.isDomain_and_isIntegrallyClosed_localization`
- `AlgebraicGeometry.Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If the local rings of `X` at the points of an affine open `U` are integrally closed domains,
then so are the localizations of `Γ(X, U)` at primes: the localization at `p` is the local ring
of `X` at the point of `U` corresponding to `p`. -/
theorem IsAffineOpen.isDomain_and_isIntegrallyClosed_localization {X : Scheme.{u}}
    {U : X.Opens} (hU : IsAffineOpen U)
    (hX : ∀ x ∈ U, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (p : Ideal Γ(X, U)) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  have hy : hU.fromSpec ⟨p, inferInstance⟩ ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact Set.mem_range_self _
  let := X.presheaf.algebra_section_stalk ⟨_, hy⟩
  have := hU.isLocalization_stalk' ⟨p, inferInstance⟩ hy
  obtain ⟨_, _⟩ := hX _ hy
  let e := (IsLocalization.algEquiv p.primeCompl
    (X.presheaf.stalk (hU.fromSpec ⟨p, inferInstance⟩)) (Localization.AtPrime p)).toRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, .of_equiv e⟩

/-- **Normality ascends along étale morphisms** (Stacks `033C`, étale case). If the local rings
of `Y` are integrally closed domains, then so are the local rings of a scheme `X` étale over
`Y`. (blueprint: `theorem-purity-real-sheaves-curves`, Step 0) -/
theorem Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Etale f]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (x : X) : IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ U from hxU)
      (f ⁻¹ᵁ U).isOpen
  have hφ := HasRingHomProperty.appLE @Etale f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  algebraize [(f.appLE U V hVU).hom]
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  set P := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  obtain ⟨_, _⟩ := Algebra.Etale.isDomain_and_isIntegrallyClosed_localization_of_comap
    (R := Γ(Y, U)) P (hU.isDomain_and_isIntegrallyClosed_localization (fun y _ ↦ hY y) _)
  let e := (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
    (X.presheaf.stalk x)).toRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, .of_equiv e⟩

end AlgebraicGeometry
