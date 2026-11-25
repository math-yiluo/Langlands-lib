/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# The coordinate sections `Tᵢ` of `𝒪(1)` on projective space

The homogeneous coordinate `Tᵢ` is a global section of the twisting sheaf `𝒪(1)` on
`ℙ(n; S)`. We construct it as the pullback along `toProjInt : ℙ(n; S) ⟶ Proj ℤ[Tᵢ]` of
multiplication by `Tᵢ` from `𝒪 ≅ 𝒪(0)` to `𝒪(1)` on the integral model, and show that its
non-vanishing locus, the complement of its zero scheme, is the standard open `D₊(Tᵢ)`.

## Main definitions

- `AlgebraicGeometry.Proj.unitToTwist`: the global section `f` of `𝒪(d)` on `Proj 𝒜` given by a
  homogeneous element `f` of degree `d`.
- `AlgebraicGeometry.ProjectiveSpace.coordinateSection`: the coordinate section `Tᵢ` of `𝒪(1)`
  on `ℙ(n; S)`.

## Main results

- `AlgebraicGeometry.Proj.compl_support_zeroLocus_unitToTwist`: on `Proj 𝒜`, if the `D₊(g)`
  with `g` of degree `1` cover, the section `f` of `𝒪(1)` vanishes exactly off `D₊(f)`.
- `AlgebraicGeometry.ProjectiveSpace.compl_support_zeroLocus_coordinateSection`: the
  non-vanishing locus of `Tᵢ` is the standard open `D₊(Tᵢ)`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry

namespace Proj

open ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜]

/-- **The non-vanishing locus of a section of degree one.** If the basic opens `D₊(g)` of the
elements `g` of degree `1` cover `Proj 𝒜`, then for `f` of degree `1` the zero scheme of the
section `f` of `𝒪(1)` is the complement of `D₊(f)`: on `D₊(g)` the section `g` is a free
generator of `𝒪(1)`, and `f = (f / g) • g`, which vanishes exactly where `f` does. -/
theorem compl_support_zeroLocus_unitToTwist
    (h : ∀ x : Proj 𝒜, ∃ g ∈ 𝒜 1, x ∈ Proj.basicOpen 𝒜 g) {f : A} (hf : f ∈ 𝒜 1) :
    (Scheme.Modules.Hom.zeroLocus (unitToTwist hf)).support.compl = Proj.basicOpen 𝒜 f := by
  have := isInvertible_twist 𝒜 (0 + ((1 : ℕ) : ℤ)) h
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (twist 𝒜 (0 + ((1 : ℕ) : ℤ)))
  have : SheafOfModules.IsInvertible.{u, u, u} (Scheme.Modules.unit (Proj 𝒜)) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ (Proj 𝒜).Modules)
  ext x
  obtain ⟨g, hg, hxg⟩ := h x
  let U : (Proj 𝒜).affineOpens := ⟨_, isAffineOpen_basicOpen 𝒜 g hg one_pos⟩
  obtain ⟨b, hb⟩ := (isFreeGenerator_unitToTwist hg).exists_smul_eq
    ((unitToTwist hf).app U.1 (1 : Γ(Proj 𝒜, U.1)))
  have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hval : (b.1 ⟨x, hxg⟩).val * ((1 : AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal).val *
      Localization.mk g 1) = (1 : AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal).val *
        Localization.mk f 1 :=
    congr((($hb).1 ⟨x, hxg⟩).1)
  rw [HomogeneousLocalization.val_one, one_mul, one_mul] at hval
  have hunit (a : A) : IsUnit (Localization.mk a 1 : Localization.AtPrime
      x.asHomogeneousIdeal.toIdeal) ↔ a ∉ x.asHomogeneousIdeal := by
    rw [Localization.mk_one_eq_algebraMap]
    exact IsLocalization.AtPrime.isUnit_to_map_iff _ _ a
  have key : x ∈ (Proj 𝒜).basicOpen b ↔ x ∈ Proj.basicOpen 𝒜 f := by
    rw [mem_basicOpen_iff_isUnit_val b hxg, Proj.mem_basicOpen, ← hunit, ← hval,
      IsUnit.mul_iff, and_iff_left ((hunit g).mpr hxg)]
  have hsupp : x ∈ (Scheme.Modules.Hom.zeroLocus (unitToTwist hf)).support ↔
      x ∉ (Proj 𝒜).basicOpen b := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) hxg,
      Scheme.Modules.Hom.ideal_zeroLocus _ U (Scheme.Modules.isFreeGenerator_one _)
        (isFreeGenerator_unitToTwist hg) hb.symm, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    rfl
  exact (not_congr hsupp).trans (not_not.trans key)

end Proj

namespace ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- `𝒪(m)` on `ℙ(n; S)` is invertible in the sense of `SheafOfModules.IsInvertible`. -/
instance sheafOfModules_isInvertible_twist (m : ℤ) :
    SheafOfModules.IsInvertible.{u, u, u} (twist n S m) :=
  Scheme.Modules.IsInvertible.sheafOfModules_isInvertible _

/-- **The coordinate section `Tᵢ` of `𝒪(1)`** on `ℙ(n; S)`: the pullback along
`toProjInt: ℙ(n; S) ⟶ Proj ℤ[Tᵢ]` of the global section `Tᵢ` of `𝒪(1)` on the integral model,
i.e. of multiplication by `Tᵢ` from `𝒪 ≅ 𝒪(0)` to `𝒪(1)`. -/
def coordinateSection (i : n) : 𝟙_ (ℙ(n; S)).Modules ⟶ twist n S 1 :=
  (Scheme.Modules.pullbackObjUnitIso (toProjInt n S)).inv ≫
    (Scheme.Modules.pullback (toProjInt n S)).map
      (Proj.unitToTwist (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i) ≫
        eqToHom (by rw [Nat.cast_one, zero_add]) :
        Scheme.Modules.unit _ ⟶ Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) 1)

/-- **The non-vanishing locus of `Tᵢ` is the standard open `D₊(Tᵢ)`**: the complement of the
zero scheme of the coordinate section `Tᵢ` of `𝒪(1)` is the standard
open `standardOpen n S i`. -/
theorem compl_support_zeroLocus_coordinateSection (i : n) :
    (Scheme.Modules.Hom.zeroLocus (coordinateSection n S i)).support.compl =
      standardOpen n S i := by
  have hX : MvPolynomial.X i ∈ MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ) 1 :=
    MvPolynomial.isHomogeneous_X _ i
  have hd : Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) (0 + ((1 : ℕ) : ℤ)) =
      Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) 1 := by
    rw [Nat.cast_one, zero_add]
  have hU : SheafOfModules.IsInvertible.{u, u, u}
      (Scheme.Modules.unit (Proj (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)))) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ _)
  have hT : SheafOfModules.IsInvertible.{u, u, u}
      (Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) 1) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible _
  let φ : Scheme.Modules.unit _ ⟶
      Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) 1 :=
    Proj.unitToTwist hX ≫ eqToHom hd
  have h₁ : (coordinateSection n S i).zeroLocus =
      ((Scheme.Modules.pullback (toProjInt n S)).map φ).zeroLocus :=
    Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _
      (Arrow.isoMk (Scheme.Modules.pullbackObjUnitIso _).symm (Iso.refl _)
        (Category.comp_id _).symm)
  have h₂ : φ.zeroLocus = (Proj.unitToTwist hX).zeroLocus :=
    (Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _
      (Arrow.isoMk (Iso.refl _) (eqToIso hd) (Category.id_comp _))).symm
  have h₃ : (coordinateSection n S i).zeroLocus =
      (Proj.unitToTwist hX).zeroLocus.comap (toProjInt n S) :=
    h₁.trans ((@Scheme.Modules.Hom.comap_zeroLocus _ _ _ hU hT _ (toProjInt n S) φ).symm.trans
      (congrArg (fun I ↦ I.comap (toProjInt n S)) h₂))
  rw [h₃]
  refine (congrArg TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support_comap
    (Proj.unitToTwist hX).zeroLocus (toProjInt n S))).trans ?_
  rw [standardOpen, ← Proj.compl_support_zeroLocus_unitToTwist
    (Proj.exists_mem_basicOpen_homogeneousSubmodule n _) hX]
  rfl

end ProjectiveSpace

end AlgebraicGeometry
