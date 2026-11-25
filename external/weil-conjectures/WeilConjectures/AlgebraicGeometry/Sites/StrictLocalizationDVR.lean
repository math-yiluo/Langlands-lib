/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation
public import WeilConjectures.AlgebraicGeometry.StrictLocalizationFieldExtension
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.RingTheory.StrictHenselizationDimension
public import WeilConjectures.RingTheory.StrictHenselizationNoetherian
public import WeilConjectures.RingTheory.StrictHenselizationRegular
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!

# The strict henselization of a discrete valuation ring

Let `S` be a scheme and `s : Spec Ω ⟶ S` a geometric point (`Ω` separably closed) whose image
has a local ring `𝒪_{S, s}` which is a discrete valuation ring. Then the strict henselization
`𝒪^{sh}_{S, s}` is a discrete valuation ring (an ingredient of SGA 4½ [Th. finitude] Lemme 3.3).

Algebraically, a strict henselization of a discrete valuation ring is noetherian (Stacks 06LJ),
regular (Stacks 06LN) and of dimension one (Stacks 06LK), hence a discrete valuation ring
(`Algebra.IsStrictHenselization.isDiscreteValuationRing`). Geometrically, the strict
henselization at `s` does not change when `Ω` is replaced by an algebraic closure
(`AlgebraicGeometry.Scheme.exists_strictLocalization_iso_of_precomp`), and for an algebraically
closed `Ω` it is a strict henselization of the local ring of an affine chart at the image of `s`
(`AlgebraicGeometry.Scheme.strictHenselization_chart_isStrictHenselization`), which is the
local ring `𝒪_{S, s}`.

## Main statements

- `Algebra.IsStrictHenselization.isDiscreteValuationRing`
- `AlgebraicGeometry.Scheme.isDiscreteValuationRing_strictHenselization`
- `AlgebraicGeometry.Scheme.isDomain_strictHenselization_of_isDiscreteValuationRing`

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace Algebra.IsStrictHenselization

variable {A K C : Type u} [CommRing A] [IsLocalRing A] [Field K]
  [Algebra (ResidueField A) K] [IsSepClosure (ResidueField A) K]
  [Algebra A K] [IsScalarTower A (ResidueField A) K]
  [CommRing C] [Algebra A C]

set_option linter.overlappingInstances false in
/-- **A strict henselization of a discrete valuation ring is a discrete valuation ring**: it is
noetherian (Stacks 06LJ), regular (Stacks 06LN) and of dimension one (Stacks 06LK). -/
theorem isDiscreteValuationRing (hC : IsStrictHenselization A K C) [IsDomain A]
    [IsDiscreteValuationRing A] : ∃ _ : IsDomain C, IsDiscreteValuationRing C := by
  have : IsNoetherianRing C := (isNoetherianRing_iff_isStrictHenselization A K C hC).1 inferInstance
  have : IsRegularLocalRing C :=
    (isRegularLocalRing_iff_strictHenselization A K C hC).1 inferInstance
  exact ⟨inferInstance, IsRegularLocalRing.isDiscreteValuationRing C
    ((ringKrullDim_eq_of_isStrictHenselization A K C hC).symm.trans
      (IsDiscreteValuationRing.ringKrullDim_eq_one A))⟩

end Algebra.IsStrictHenselization

namespace AlgebraicGeometry.Scheme

/-- A ring isomorphic to a discrete valuation ring is a domain and a discrete valuation ring. -/
lemma _root_.RingEquiv.exists_isDiscreteValuationRing {A B : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] (e : A ≃+* B) :
    ∃ _ : IsDomain B, IsDiscreteValuationRing B := by
  have : IsDomain B := e.symm.injective.isDomain e.symm.toRingHom
  exact ⟨this, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e⟩

/-- The strict henselization of `S` at a geometric point `xR ≫ i` with `Ω` algebraically closed
factoring through an affine open chart `i : Spec R ⟶ S`, at whose image the local ring of `S` is
a discrete valuation ring, is a discrete valuation ring. -/
lemma isDiscreteValuationRing_strictHenselization_chart {S : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (R : CommRingCat.{u}) (i : Spec R ⟶ S) [IsOpenImmersion i]
    (xR : Spec (.of Ω) ⟶ Spec R) {x : S} (hx : i (xR (closedPoint Ω)) = x)
    [IsDomain (S.presheaf.stalk x)] [IsDiscreteValuationRing (S.presheaf.stalk x)] :
    ∃ _ : IsDomain (strictHenselization (xR ≫ i)),
      IsDiscreteValuationRing (strictHenselization (xR ≫ i)) := by
  subst hx
  obtain ⟨q, _, K, _, _, _, _, _, _, b, rfl, -, -, hH⟩ :=
    strictHenselization_chart_isStrictHenselization R i xR
  let y := xR (closedPoint Ω)
  let : Algebra R ((Spec R).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  let e : S.presheaf.stalk (i y) ≃+* Localization.AtPrime y.asIdeal :=
    (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv.trans
      (IsLocalization.algEquiv y.asIdeal.primeCompl _ _).toRingEquiv
  obtain ⟨_, _⟩ := e.exists_isDiscreteValuationRing
  exact hH.isDiscreteValuationRing

/-- The strict henselization of `S` at a geometric point `s` with `Ω` algebraically closed, at
whose image the local ring of `S` is a discrete valuation ring, is a discrete valuation ring. -/
lemma isDiscreteValuationRing_strictHenselization_of_isAlgClosed {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) {x : S} (hx : s (closedPoint Ω) = x)
    [IsDomain (S.presheaf.stalk x)] [IsDiscreteValuationRing (S.presheaf.stalk x)] :
    ∃ _ : IsDomain (strictHenselization s), IsDiscreteValuationRing (strictHenselization s) := by
  obtain ⟨j, hj⟩ : ∃ j, x ∈ Set.range (S.affineOpenCover.f j) :=
    ⟨_, S.affineOpenCover.covers x⟩
  have hs : Set.range s ⊆ Set.range (S.affineOpenCover.f j) := by
    rintro _ ⟨p, rfl⟩
    rwa [Subsingleton.elim p (closedPoint Ω), hx]
  obtain ⟨xR, rfl⟩ : ∃ xR, xR ≫ S.affineOpenCover.f j = s :=
    ⟨_, IsOpenImmersion.lift_fac _ s hs⟩
  exact isDiscreteValuationRing_strictHenselization_chart _ _ xR
    (x := x) (by rwa [Scheme.Hom.comp_apply] at hx)

/-- **The strict henselization of a discrete valuation ring.** If the local ring of `S` at the
image of the geometric point `s` is a discrete valuation ring, then so is the strict
henselization `𝒪^{sh}_{S, s}` (SGA 4½ [Th. finitude] Lemme 3.3, Stacks 06LN, 06LK). -/
theorem isDiscreteValuationRing_strictHenselization {S : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) [IsDomain (S.presheaf.stalk (s (closedPoint Ω)))]
    [IsDiscreteValuationRing (S.presheaf.stalk (s (closedPoint Ω)))] :
    ∃ _ : IsDomain (strictHenselization s), IsDiscreteValuationRing (strictHenselization s) := by
  let a : Spec (.of (AlgebraicClosure Ω)) ⟶ Spec (.of Ω) :=
    Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
  obtain ⟨σ, -⟩ := exists_strictLocalization_iso_of_precomp s a
  obtain ⟨_, _⟩ := isDiscreteValuationRing_strictHenselization_of_isAlgClosed (a ≫ s)
    (x := s (closedPoint Ω)) (by rw [Scheme.Hom.comp_apply, Subsingleton.elim (a _)])
  let e : strictHenselization (a ≫ s) ≅ strictHenselization s :=
    { hom := Spec.preimage σ.inv
      inv := Spec.preimage σ.hom
      hom_inv_id := Spec.map_injective (by simp)
      inv_hom_id := Spec.map_injective (by simp) }
  exact e.commRingCatIsoToRingEquiv.exists_isDiscreteValuationRing

/-- If the local ring of `S` at the image of the geometric point `s` is a discrete valuation
ring, then the strict henselization `𝒪^{sh}_{S, s}` is a domain. -/
theorem isDomain_strictHenselization_of_isDiscreteValuationRing {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    [IsDomain (S.presheaf.stalk (s (closedPoint Ω)))]
    [IsDiscreteValuationRing (S.presheaf.stalk (s (closedPoint Ω)))] :
    IsDomain (strictHenselization s) :=
  (isDiscreteValuationRing_strictHenselization s).1

end AlgebraicGeometry.Scheme
