/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sheaf


/-!
# Multiplication maps between the twisting sheaves on a projective spectrum

The identification of `𝒪(0)` with the structure sheaf, and the multiplication maps
`𝒪(m) ⟶ 𝒪(m + d)` by a homogeneous element of degree `d`, which are isomorphisms over its basic
open.
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory Opposite TopologicalSpace TopCat HomogeneousLocalization

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ)

namespace ProjectiveSpectrum.Twist

variable {𝒜 m}
variable (𝒜 m)
variable {𝒜 m}
variable (𝒜 m)
variable {𝒜}

section Zero

/-- The canonical morphism of presheaves of abelian groups from the structure sheaf of `Proj 𝒜`
to the twisting presheaf `𝒪(0)`, given by `HomogeneousLocalization.degreePart.zeroEquiv` at
every point. -/
def unitToPresheafInAbZero :
    (PresheafOfModules.unit (Proj 𝒜).ringCatSheaf.obj).presheaf ⟶ presheafInAb 𝒜 0 where
  app _ := AddCommGrpCat.ofHom
    { toFun s := ⟨_, isLocallyFraction_zeroEquiv s⟩
      map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
      map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _) }
  naturality _ _ _ := rfl

/-- The map `𝒪 ⟶ 𝒪(0)` is `HomogeneousLocalization.degreePart.zeroEquiv` at every point. -/
@[simp]
theorem unitToPresheafInAbZero_app_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : (Proj 𝒜).ringCatSheaf.obj.obj U) (x : U.unop) :
    (unitToPresheafInAbZero.app U s).1 x = degreePart.zeroEquiv (s.1 x) :=
  rfl

/-- The inverse of the canonical map from the sections of the structure sheaf to those
of `𝒪(0)`, given by the inverse of `HomogeneousLocalization.degreePart.zeroEquiv` at every
point. -/
def sectionsZeroInv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (t : sections 𝒜 0 U) :
    (Proj 𝒜).ringCatSheaf.obj.obj U :=
  ⟨fun x ↦ degreePart.zeroEquiv.symm (t.1 x), by
    intro x
    obtain ⟨V, hxV, e, i, j, hij, ⟨a, ha⟩, ⟨b, hb⟩, hw, w⟩ := t.2 x
    obtain rfl : i = j := by omega
    refine ⟨V, hxV, e, i, ⟨a, ha⟩, ⟨b, hb⟩, hw, fun y ↦ ?_⟩
    refine (LinearEquiv.symm_apply_eq _).mpr ((w y).trans ?_)
    ext
    simp [val_mk]⟩

/-- `sectionsZeroInv` is a right inverse of `HomogeneousLocalization.degreePart.zeroEquiv`
at every point. -/
@[simp]
theorem zeroEquiv_sectionsZeroInv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (t : sections 𝒜 0 U) (x : U.unop) :
    degreePart.zeroEquiv ((sectionsZeroInv t).1 x) = t.1 x :=
  LinearEquiv.apply_symm_apply _ _

end Zero

section Mul

variable {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)

include hf

/-- Multiplication by a homogeneous element `f` of degree `d`, as a morphism of presheaves of
abelian groups from `𝒪(m)` to `𝒪(m + d)`. -/
def mulPresheafHom : presheafInAb 𝒜 m ⟶ presheafInAb 𝒜 (m + d) where
  app U := AddCommGrpCat.ofHom
    { toFun s := ⟨_, isLocallyFraction_mul rfl s.2
        (isLocallyFraction_mk (by simp) ⟨f, hf⟩ ⟨1, SetLike.one_mem_graded 𝒜⟩
          fun x ↦ (Ideal.ne_top_iff_one _).mp x.1.isPrime.ne_top)⟩
      map_zero' := Subtype.ext (funext fun _ ↦ Subtype.ext (zero_mul _))
      map_add' _ _ := Subtype.ext (funext fun _ ↦ Subtype.ext (add_mul _ _ _)) }
  naturality _ _ _ := rfl

/-- The map `𝒪(m) ⟶ 𝒪(m + d)` multiplies every value by `f`. -/
@[simp]
theorem val_mulPresheafHom_app_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : (presheafInAb 𝒜 m).obj U) (x : U.unop) :
    (((mulPresheafHom m hf).app U s).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * Localization.mk f 1 :=
  rfl

/-- On an open set `U` contained in `D₊(f)`, division by the homogeneous element `f` of
degree `d` maps the sections of `𝒪(m + d)` to those of `𝒪(m)`. -/
def divPresheafHomApp {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (presheafInAb 𝒜 (m + d)).obj U ⟶ (presheafInAb 𝒜 m).obj U :=
  AddCommGrpCat.ofHom
    { toFun s := ⟨_, isLocallyFraction_mul (add_neg_cancel_right m d) s.2
        (isLocallyFraction_mk (by simp) ⟨1, SetLike.one_mem_graded 𝒜⟩ ⟨f, hf⟩
          fun x ↦ hU x.2)⟩
      map_zero' := Subtype.ext (funext fun _ ↦ Subtype.ext (zero_mul _))
      map_add' _ _ := Subtype.ext (funext fun _ ↦ Subtype.ext (add_mul _ _ _)) }

/-- The map `𝒪(m + d) ⟶ 𝒪(m)` on `U ≤ D₊(f)` divides every value by `f`. -/
@[simp]
theorem val_divPresheafHomApp_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (s : (presheafInAb 𝒜 (m + d)).obj U)
    (x : U.unop) :
    ((divPresheafHomApp m hf hU s).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk 1 (⟨f, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
  rfl

/-- On an open set `U` contained in `D₊(f)`, multiplication by `f` is a bijection from the
sections of `𝒪(m)` to those of `𝒪(m + d)`. -/
theorem isIso_mulPresheafHom_app {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) : IsIso ((mulPresheafHom m hf).app U) := by
  have key (x : U.unop) :
      Localization.mk f 1 *
          Localization.mk 1 (⟨f, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) =
        (1 : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) := by
    rw [Localization.mk_mul, one_mul, mul_one]
    exact Localization.mk_self (⟨f, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  have key' (x : U.unop) := (mul_comm _ _).trans (key x)
  refine ⟨divPresheafHomApp m hf hU, ?_, ?_⟩ <;>
  · ext s : 2
    refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
    simp [mul_assoc, key, key']

end Mul

end ProjectiveSpectrum.Twist

end AlgebraicGeometry
