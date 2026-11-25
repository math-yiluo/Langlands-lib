/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.SectionwiseFiniteConstantLocalModel
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients

/-! # Concrete coefficients and the root-tower Tate line

The index is presentation data for the existing six admissible coefficients.
Every ring and every line below is constructed, not selected from an existence assertion.

## References

* Bhatt--Scholze, Section 6.8
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Presentations of exactly the six admissible coefficient types. The positive
finite exponent only records an annihilator; its choice does not alter the ring. -/
inductive Coefficient (ell : ℕ) [Fact ell.Prime] where
  | finite (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
      (annihilates : (ell ^ (n + 1) : A) = 0)
  | integers
  | rationals
  | integral (E : PadicAlgCl.FiniteIntermediateField ell)
  | rational (E : PadicAlgCl.FiniteIntermediateField ell)
  | closure

variable (ell : ℕ) [Fact ell.Prime]

/-- The actual condensed commutative ring, with continuous integral and field
coefficients and the finite-subextension-valued algebraic closure. -/
def Coefficient.ring : Coefficient ell →
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}
  | .finite A _ _ _ =>
      letI : TopologicalSpace A := ⊥
      letI : DiscreteTopology A := discreteTopology_bot A
      Profinite.continuousMapRingSheaf A
  | .integers => Profinite.padicIntCondensedRing ell
  | .rationals => Profinite.padicCondensedRing ell
  | .integral E => Profinite.padicIntegersCondensedRing ell E
  | .rational E => Profinite.padicSubfieldCondensedRing ell E
  | .closure => Profinite.padicAlgClCondensedRing ell

/-- The existing abelian ring object underlying the coefficient presentation. -/
abbrev Coefficient.obj (c : Coefficient ell) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (c.ring ell)

/-- Commutativity is pointwise, and at the closure is inherited from the recorded
finite-subextension coefficient. -/
instance Coefficient.comm (c : Coefficient ell) : IsCommMonObj (c.obj.{u} ell) := by
  cases c with
  | finite A fin n h =>
      let : TopologicalSpace A := ⊥
      have : DiscreteTopology A := discreteTopology_bot A
      exact Profinite.isCommMonObj_continuousMapRingObj A
  | integers => exact Profinite.isCommMonObj_continuousMapRingObj ℤ_[ell]
  | rationals => exact Profinite.isCommMonObj_continuousMapRingObj ℚ_[ell]
  | integral E => exact Profinite.isCommMonObj_padicIntegersRingObj ell E
  | rational E =>
      let := PadicAlgCl.normedFieldOfAlgebra ell E
      exact Profinite.isCommMonObj_continuousMapRingObj E
  | closure => exact Profinite.isCommMonObj_padicAlgClRingObj ell

/-- The canonical integral coefficient map, including the quotient map at a
finite coefficient ring. -/
def Coefficient.fromIntegers : (c : Coefficient ell) →
    Profinite.padicIntCondensedRing.{u} ell ⟶ c.ring ell
  | .finite A _ n h =>
      letI : TopologicalSpace A := ⊥
      letI : DiscreteTopology A := discreteTopology_bot A
      let q : ZMod (ell ^ (n + 1)) →+* A :=
        ZMod.castHom (ringChar.dvd (by simpa only [Nat.cast_pow] using h)) A
      Profinite.continuousMapRingSheafMap (q.comp (PadicInt.toZModPow (n + 1)))
        ((continuous_of_discreteTopology (f := q)).comp
          (PadicInt.continuous_toZModPow (n + 1)))
  | .integers => 𝟙 _
  | .rationals => Profinite.padicIntCondensedRingToPadicCondensedRing ell
  | .integral E => Profinite.padicIntCondensedRingToPadicIntegersCondensedRing ell E
  | .rational E => Profinite.padicIntCondensedRingToPadicCondensedRing ell ≫
      Profinite.padicCondensedRingToPadicSubfieldCondensedRing ell E
  | .closure => Profinite.padicIntCondensedRingToPadicAlgCl ell

/-- Its underlying internal ring homomorphism. -/
def Coefficient.integralMap (c : Coefficient ell) :
    Profinite.continuousMapRingObj.{u} ℤ_[ell] ⟶ c.obj ell :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map (c.fromIntegers ell)

/-- The integral coefficient map is a morphism of ring objects, being induced by a morphism of
ring sheaves. -/
instance Coefficient.isMonHom_integralMap (c : Coefficient ell) :
    IsMonHom (c.integralMap.{u} ell) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map (c.fromIntegers ell)))

/-- The root-tower line extended along the actual integral coefficient map.
For finite A this is A tensor mu at any annihilating positive level; for the
other coefficients it is the completed line followed by ordinary scalar extension. -/
def Coefficient.firstLine (c : Coefficient ell) (X : Scheme.{u}) :=
  (Mod.extendScalars (coefficientMap (c.integralMap ell) X)).obj (tateModule X ell)

/-- The positive Tate line, including the regular unit at d=0. -/
def Coefficient.line (c : Coefficient ell) (X : Scheme.{u}) :
    ℕ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X)
  | 0 => 𝟙_ _
  | d + 1 => c.line X d ⊗ c.firstLine ell X

/-- Ambient derived modules on the specified small pro-etale site. -/
abbrev Coefficient.derived (c : Coefficient ell) (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (c.obj ell) X))

/-- The recorded Dctf full subcategory, without changing its morphisms or
identifying the integral coefficient with a discrete constant ring. -/
abbrev Coefficient.ctf (c : Coefficient ell) (X : Scheme.{u}) :=
  ConstantModelConstructibleFiniteTor (c.obj ell) X

/-- The root-tower line in its prescribed cohomological degree. -/
def Coefficient.derivedLine (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ) :
    c.derived ell X :=
  ((DerivedCategory.singleFunctor _ 0).obj (c.line ell X d)) ⟦2 * (d : ℤ)⟧

/-- The actual ambient f* K(d)[2d] functor. -/
def Coefficient.smoothSource (c : Coefficient ell) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) : c.derived ell Y ⥤ c.derived ell X :=
  (CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor ⋙
    tensorRight (c.derivedLine ell X d)

/-- Every existing purity coefficient is an admissible localizing coefficient.
This certificate only supplies the empty coefficient change; its ring and topology
are the existing Coefficient.obj, independently of the site universe. -/
abbrev coefficientAdmissible (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell) :
    IsLocalizingAdmissibleCoefficient ell (c.obj.{u} ell) := by
  cases c with
  | finite A fin n hA =>
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := discreteTopology_bot A
    exact Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      fin, ⟨n + 1, fun x ↦ by simp only [nsmul_eq_mul, Nat.cast_pow, hA, zero_mul]⟩,
      ⟨Iso.refl _⟩⟩
  | integers => exact Or.inr (Or.inl ⟨Iso.refl _⟩)
  | rationals => exact Or.inr (Or.inr (Or.inl ⟨Iso.refl _⟩))
  | integral E => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  | rational E => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
  | closure => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))

end AlgebraicGeometry.ProEtale.PurityTransport
