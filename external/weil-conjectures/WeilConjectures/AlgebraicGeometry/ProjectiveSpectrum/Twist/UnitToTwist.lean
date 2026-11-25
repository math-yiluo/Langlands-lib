/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules


/-!
# The twisting sheaves are locally free of rank one over basic opens

The morphism `𝒪 ⟶ 𝒪(d)` attached to a homogeneous element `f` of degree `d` is an isomorphism
over the basic open of `f`, which exhibits a free generator of `𝒪(d)` there.
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory Opposite TopologicalSpace TopCat HomogeneousLocalization

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ)

namespace Proj

open ProjectiveSpectrum.Twist

section Sections

variable {𝒜} {d : ℕ} {f g : A}

/-- The morphism `𝒪 ⟶ 𝒪(d)` on `Proj 𝒜` sending `1` to the homogeneous element `f` of
degree `d`. -/
def unitToTwist (hf : f ∈ 𝒜 d) : Scheme.Modules.unit (Proj 𝒜) ⟶ twist 𝒜 (0 + d) :=
  unitToTwistZero ≫ twistMul 0 hf

/-- The morphism `𝒪 ⟶ 𝒪(d)` given by `f` is an isomorphism on `D₊(f)`. -/
instance isIso_restrict_unitToTwist (hf : f ∈ 𝒜 d) :
    IsIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι).map (unitToTwist hf)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι).map
      (unitToTwistZero (𝒜 := 𝒜))) :=
    ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι).mapIso
      (unitIsoTwistZero (𝒜 := 𝒜))).isIso_hom
  rw [unitToTwist, Functor.map_comp]
  infer_instance

/-- The value of the global section `f` of `𝒪(d)` at a point is the fraction `f / 1`. -/
lemma val_unitToTwist_app_top (hf : f ∈ 𝒜 d) (x : (⊤ : (Proj 𝒜).Opens)) :
    (((Scheme.Modules.Hom.app (unitToTwist hf) ⊤ (1 : Γ(Proj 𝒜, ⊤))).1 x :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) = Localization.mk f 1 := by
  change ((degreePart.zeroEquiv (1 : HomogeneousLocalization.AtPrime 𝒜
    x.1.asHomogeneousIdeal.toIdeal) : degreePart 𝒜 x.1.asHomogeneousIdeal.toIdeal.primeCompl 0) :
    Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * Localization.mk f 1 = _
  rw [degreePart.coe_zeroEquiv_apply, HomogeneousLocalization.val_one, one_mul]

/-- **The transition rule** `f = (f / g) • g` on `D₊(g)`, for homogeneous `f` and `g` of the same
degree `d`, between the global sections `f` and `g` of `𝒪(d)`. -/
lemma map_unitToTwist_eq_smul (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) (hf' : f ∈ 𝒜 (1 • d)) :
    (twist 𝒜 (0 + d)).presheaf.map (homOfLE le_top : Proj.basicOpen 𝒜 g ⟶ ⊤).op
        (Scheme.Modules.Hom.app (unitToTwist hf) ⊤ (1 : Γ(Proj 𝒜, ⊤))) =
      Proj.awayToSection 𝒜 g (Away.mk 𝒜 hg 1 f hf') •
        (twist 𝒜 (0 + d)).presheaf.map (homOfLE le_top : Proj.basicOpen 𝒜 g ⟶ ⊤).op
          (Scheme.Modules.Hom.app (unitToTwist hg) ⊤ (1 : Γ(Proj 𝒜, ⊤))) := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  have h1 := val_unitToTwist_app_top hf ⟨x.1, trivial⟩
  have h2 := val_unitToTwist_app_top hg ⟨x.1, trivial⟩
  have h3 := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 g (Away.mk 𝒜 hg 1 f hf') x
  change _ = ((Proj.awayToSection 𝒜 g (Away.mk 𝒜 hg 1 f hf')).1 x).val *
    (((Scheme.Modules.Hom.app (unitToTwist hg) ⊤ (1 : Γ(Proj 𝒜, ⊤))).1 ⟨x.1, trivial⟩ :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal))
  rw [h2]
  refine (h1 : _).trans (Eq.trans ?_ (congrArg (· * Localization.mk g 1) h3.symm))
  simp only [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    RingHom.id_apply]
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
  simp [mul_comm]

section UnitToTwist

/-- A point `x` of an open `U` of `Proj 𝒜` lies in the basic open of a section `s` over `U` if
and only if the value of `s` at `x` is a unit of the localization `A_x`. -/
lemma mem_basicOpen_iff_isUnit_val {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) {x : Proj 𝒜}
    (hx : x ∈ U) : x ∈ (Proj 𝒜).basicOpen s ↔ IsUnit (s.1 ⟨x, hx⟩).val := by
  rw [Scheme.mem_basicOpen _ _ _ hx, HomogeneousLocalization.isUnit_iff_isUnit_val,
    ← Proj.stalkIso'_germ 𝒜 U x hx s]
  exact (isUnit_map_iff (stalkIso' 𝒜 x) _).symm

variable (hf : f ∈ 𝒜 d)

/-- The value of `unitToTwist hf` on a section `s` at a point `x` is `s x * f`. -/
lemma val_unitToTwist_app_apply {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) (x : U) :
    (((unitToTwist hf).app U s).1 x).1 = (s.1 x).val * Localization.mk f 1 :=
  rfl

/-- On an open contained in `D₊(f)`, the section `f` of `𝒪(d)` induces a bijection from the
functions to the sections of `𝒪(d)`. -/
lemma bijective_unitToTwist_app {V : (Proj 𝒜).Opens} (hV : V ≤ Proj.basicOpen 𝒜 f) :
    Function.Bijective ((unitToTwist hf).app V) := by
  have h₁ : Function.Bijective (Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := 𝒜)) V) :=
    ⟨fun s t h ↦ Subtype.ext (funext fun x ↦ degreePart.zeroEquiv.injective
      ((val_unitToTwistZero_app_apply V s x).symm.trans (congr($(h).1 x) |>.trans
        (val_unitToTwistZero_app_apply V t x)))), fun t ↦ ⟨sectionsZeroInv t, Subtype.ext
        (funext fun x ↦ (val_unitToTwistZero_app_apply _ _ _).trans
          (zeroEquiv_sectionsZeroInv t x))⟩⟩
  have h₂ := isIso_mulPresheafHom_app 0 hf (U := Opposite.op V) hV
  exact (ConcreteCategory.bijective_of_isIso ((mulPresheafHom 0 hf).app (Opposite.op V))).comp h₁

/-- The section `f` of `𝒪(d)` is a free generator of `𝒪(d)` on `D₊(f)`. -/
lemma isFreeGenerator_unitToTwist :
    Scheme.Modules.IsFreeGenerator
      ((unitToTwist hf).app (Proj.basicOpen 𝒜 f) (1 : Γ(Proj 𝒜, Proj.basicOpen 𝒜 f))) :=
  (Scheme.Modules.isFreeGenerator_one _).app_of_bijective _ fun _ hV ↦
    bijective_unitToTwist_app hf hV

end UnitToTwist

end Sections

end Proj

end AlgebraicGeometry
