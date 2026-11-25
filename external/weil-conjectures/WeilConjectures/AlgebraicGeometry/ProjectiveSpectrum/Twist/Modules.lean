/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Mul


/-!
# The twisting sheaves on a projective spectrum as modules

The twisting sheaves `AlgebraicGeometry.Proj.twist` as sheaves of modules on `Proj`, the
isomorphism `𝒪 ≅ 𝒪(0)`, and their invertibility when `Proj` is covered by the basic opens of
degree-one elements (`AlgebraicGeometry.Proj.isInvertible_twist`).
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

/-- **The twisting sheaf `𝒪(m)` on `Proj 𝒜`**, for `m : ℤ`: its sections over `U` are the
dependent functions `x ↦ s x ∈ (A_x)ₘ` which are locally fractions `a / b` of homogeneous
elements with `deg a = deg b + m`. -/
def twist : (Proj 𝒜).Modules :=
  ⟨presheafOfModules 𝒜 m, isSheaf_presheafInAb 𝒜 m⟩

variable {𝒜}

/-- The canonical morphism `𝒪 ⟶ 𝒪(0)` from the structure sheaf of `Proj 𝒜` to its zeroth
twisting sheaf. -/
def unitToTwistZero :
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules) ⟶ twist 𝒜 0 :=
  ⟨PresheafOfModules.homMk unitToPresheafInAbZero fun _ _ _ ↦
    Subtype.ext (funext fun _ ↦ Subtype.ext (val_mul _ _))⟩

/-- The morphism `𝒪 ⟶ 𝒪(0)` sends a section `s` of the structure sheaf to the section
`x ↦ s x` of `𝒪(0)`. -/
@[simp]
theorem val_unitToTwistZero_app_apply (U : (Proj 𝒜).Opens)
    (s : Γ((SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules), U)) (x : U) :
    ((Scheme.Modules.Hom.app unitToTwistZero U) s).1 x = degreePart.zeroEquiv (s.1 x) :=
  rfl

/-- The morphism `𝒪 ⟶ 𝒪(0)` is an isomorphism. -/
instance : IsIso (unitToTwistZero (𝒜 := 𝒜)) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U ↦ by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun s t h ↦ ?_, fun t ↦ ⟨sectionsZeroInv t, ?_⟩⟩
    · refine Subtype.ext (funext fun x ↦ degreePart.zeroEquiv.injective ?_)
      simpa using congr($(h).1 x)
    · exact Subtype.ext (funext fun x ↦ (val_unitToTwistZero_app_apply _ _ _).trans
        (zeroEquiv_sectionsZeroInv t x))

/-- **`𝒪(0)` is the structure sheaf**: the zeroth twisting sheaf of `Proj 𝒜` is isomorphic to
the structure sheaf. -/
def unitIsoTwistZero :
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules) ≅ twist 𝒜 0 :=
  asIso unitToTwistZero

variable {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)

/-- Multiplication by a homogeneous element `f` of degree `d` is a morphism of `𝒪`-modules
`𝒪(m) ⟶ 𝒪(m + d)` on `Proj 𝒜`. -/
def twistMul : twist 𝒜 m ⟶ twist 𝒜 (m + d) :=
  ⟨PresheafOfModules.homMk (mulPresheafHom m hf) fun _ _ _ ↦
    Subtype.ext (funext fun _ ↦ Subtype.ext (mul_assoc _ _ _))⟩

/-- On the basic open set `D₊(f)`, multiplication by `f` is an isomorphism `𝒪(m) ≅ 𝒪(m + d)`. -/
instance isIso_restrict_twistMul :
    IsIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι).map (twistMul m hf)) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun V ↦
    isIso_mulPresheafHom_app m hf ((Proj.basicOpen 𝒜 f).ι_image_le V)

/-- **`𝒪(m)` is locally trivial**: on the basic open set `D₊(f)` of a homogeneous element `f`
of degree `d`, multiplication by `f` is an isomorphism `𝒪(m)|_{D₊(f)} ≅ 𝒪(m + d)|_{D₊(f)}`. -/
def twistRestrictIso :
    (twist 𝒜 m).restrict (Proj.basicOpen 𝒜 f).ι ≅
      (twist 𝒜 (m + d)).restrict (Proj.basicOpen 𝒜 f).ι :=
  asIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι).map (twistMul m hf))

/-- Multiplications by two homogeneous elements of the same degree commute. -/
lemma twistMul_comp_twistMul {g : A} (hg : g ∈ 𝒜 d) :
    twistMul m hf ≫ twistMul (m + d) hg = twistMul m hg ≫ twistMul (m + d) hf := by
  ext U s : 3
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  exact mul_right_comm _ _ _

/-- **`𝒪(m)` is trivial on `D₊(f)`** for a homogeneous element `f` of degree `1`: composing
`twistRestrictIso` `|m|` times gives `𝒪(m)|_{D₊(f)} ≅ 𝒪(0)|_{D₊(f)}`, and `𝒪(0) ≅ 𝒪`. -/
lemma nonempty_restrict_twist_iso_unit (hf : f ∈ 𝒜 1) :
    Nonempty ((twist 𝒜 m).restrict (Proj.basicOpen 𝒜 f).ι ≅ SheafOfModules.unit _) := by
  have key (m : ℤ) : Nonempty ((twist 𝒜 m).restrict (Proj.basicOpen 𝒜 f).ι ≅
      (twist 𝒜 0).restrict (Proj.basicOpen 𝒜 f).ι) := by
    induction m using Int.induction_on with
    | zero => exact ⟨Iso.refl _⟩
    | succ k ih => exact ⟨(twistRestrictIso k hf).symm ≪≫ ih.some⟩
    | pred k ih =>
      have e := twistRestrictIso (-(k : ℤ) - 1) hf
      rw [show -(k : ℤ) - 1 + ((1 : ℕ) : ℤ) = -k by omega] at e
      exact ⟨e ≪≫ ih.some⟩
  exact ⟨(key m).some ≪≫ (Scheme.Modules.restrictFunctor _).mapIso unitIsoTwistZero.symm ≪≫
    Scheme.Modules.restrictUnitIso _⟩

variable (𝒜) in
/-- **`𝒪(m)` is invertible** on `Proj 𝒜` when the basic open sets `D₊(f)` of the homogeneous
elements `f` of degree `1` cover `Proj 𝒜`, e.g. when `𝒜` is generated in degree `1`. -/
lemma isInvertible_twist (h : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ Proj.basicOpen 𝒜 f) :
    (twist 𝒜 m).IsInvertible where
  exists_isoUnit x := by
    obtain ⟨f, hf, hx⟩ := h x
    obtain ⟨e⟩ := nonempty_restrict_twist_iso_unit m hf
    exact ⟨_, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback _).symm.app _ ≪≫ e⟩⟩

end Proj

end AlgebraicGeometry
