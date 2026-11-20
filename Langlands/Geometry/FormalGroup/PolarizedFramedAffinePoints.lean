import Langlands.Geometry.FormalGroup.PolarizedOrderModule
import Langlands.Geometry.FormalGroup.RationalTorsionSimilitude
import Langlands.Geometry.FormalGroup.ModuleReduction

/-! # Polarized framed triples and their isomorphism classes on affine Nilp tests -/

noncomputable section

universe w

namespace Langlands.FormalGroup

open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry
open ModuleLaw Langlands.Shimura

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable (prime : ℕ) [Fact prime.Prime]
variable {W : Type} [CommRing W] [Algebra ℤ_[prime] W] (π : W)
variable {A : Type w} [Ring A] [Algebra ℤ_[prime] A] {star : AlgebraInvolution ℤ_[prime] A}

namespace PolarizedFramedAffinePoint

/-- The actual map from the residue coefficient ring to a reduced Nilp test. -/
def frameCoefficientMap (T : Nilp.{0, 0} W π) :
    ResidueRing W π →ₐ[ℤ_[prime]] ((Nilp.reductionFunctor W π).obj T).obj where
  __ := algebraMap (ResidueRing W π) (Nilp.Reduction π T.obj)
  commutes' _ := rfl

end PolarizedFramedAffinePoint

/-- A polarized coordinate object and an order-linear rigidifying quasi-isogeny
on its actual reduction. The p-adic multiplier is a property of the rigidification. -/
structure PolarizedFramedAffinePoint
    (frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime]))
    (T : Nilp.{0, 0} W π) where
  target : PolarizedOrderModule A star T.obj (prime : ℤ_[prime])
  rho : RationalSection ℚ_[prime]
    (frame.map (PolarizedFramedAffinePoint.frameCoefficientMap prime π T)).law
    (target.map (Nilp.quotientO ℤ_[prime] T)).law ⊤
  commutes : ∀ a : A, RationalSection.comp rho
      (RationalSection.ofHom
        ((frame.map (PolarizedFramedAffinePoint.frameCoefficientMap prime π T)).order.action a) ⊤) =
    RationalSection.comp
      (RationalSection.ofHom ((target.map (Nilp.quotientO ℤ_[prime] T)).order.action a) ⊤) rho
  similitude : ∃ c : ℚ_[prime]ˣ, RationalSection.HasPadicTorsionSimilitude prime
    (frame.map (PolarizedFramedAffinePoint.frameCoefficientMap prime π T)).polarization
    (target.map (Nilp.quotientO ℤ_[prime] T)).polarization rho c

namespace PolarizedFramedAffinePoint

variable {prime π}
variable {frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime])}
variable {T : Nilp.{0, 0} W π}
variable (X : PolarizedFramedAffinePoint prime π frame T)

/-- The framing source is the actual coefficient extension of the fixed frame. -/
abbrev source := frame.map (frameCoefficientMap prime π T)

/-- The framing target is the actual reduction of the polarized formal module. -/
abbrev reducedTarget : PolarizedOrderModule A star ((Nilp.reductionFunctor W π).obj T).obj
    (prime : ℤ_[prime]) :=
  X.target.map (Nilp.quotientO ℤ_[prime] T)

/-- The actual rational section of a triple is an actual local quasi-isogeny. -/
def localFraming : LocalQuasiIsogeny ℚ_[prime] (prime : ℤ_[prime])
    (source (frame := frame) (T := T)).law X.reducedTarget.law ⊤ where
  scalar_ne_zero := by
    simpa only [map_natCast] using (Nat.cast_ne_zero.mpr (Fact.out : prime.Prime).ne_zero :
      (prime : ℚ_[prime]) ≠ 0)
  source_divisible := (source (frame := frame) (T := T)).divisible
  target_divisible := X.reducedTarget.divisible
  val := X.rho
  isLocal := by
    obtain ⟨_, h⟩ := X.similitude
    exact RationalSection.HasLocalTorsionSimilitude.isLocallyScalarIsogeny h

@[simp]
theorem localFraming_val : X.localFraming.val = X.rho := rfl

/-- An isometry of the polarized targets induces the actual rational section on the reduction. -/
def reducedIsometrySection {Y : PolarizedFramedAffinePoint prime π frame T}
    (e : PolarizedOrderModule.Iso X.target Y.target) :
    RationalSection ℚ_[prime] X.reducedTarget.law Y.reducedTarget.law ⊤ :=
  RationalSection.ofHom (e.orderIso.hom.val.map (Nilp.quotientO ℤ_[prime] T)) ⊤

variable {X} {Y Z : PolarizedFramedAffinePoint prime π frame T}

/-- Isomorphisms preserve the actual polarization and the rigidifying map. -/
structure Iso (X Y : PolarizedFramedAffinePoint prime π frame T) where
  targetIso : PolarizedOrderModule.Iso X.target Y.target
  square : RationalSection.comp (X.reducedIsometrySection targetIso) X.rho = Y.rho

namespace Iso

/-- The identity of the polarized target fixes the framing. -/
def refl (X : PolarizedFramedAffinePoint prime π frame T) : Iso X X where
  targetIso := PolarizedOrderModule.Iso.refl X.target
  square := by
    change RationalSection.comp
      (RationalSection.ofHom ((Hom.id X.target.law).map (Nilp.quotientO ℤ_[prime] T)) ⊤) X.rho = X.rho
    rw [Hom.map_id, RationalSection.ofHom_id]
    exact RationalSection.id_comp X.rho

/-- Reverse the actual isometry and its framing square. -/
def symm (e : Iso X Y) : Iso Y X where
  targetIso := e.targetIso.symm
  square := by
    rw [← e.square, ← RationalSection.comp_assoc]
    have he : e.targetIso.orderIso.inv.val.comp e.targetIso.orderIso.hom.val = Hom.id X.target.law :=
      e.targetIso.orderIso.toModuleIso.inv_hom
    change RationalSection.comp (RationalSection.comp
      (RationalSection.ofHom (e.targetIso.orderIso.inv.val.map (Nilp.quotientO ℤ_[prime] T)) ⊤)
      (RationalSection.ofHom (e.targetIso.orderIso.hom.val.map (Nilp.quotientO ℤ_[prime] T)) ⊤))
      X.rho = _
    rw [RationalSection.comp_ofHom, ← Hom.map_comp, he, Hom.map_id, RationalSection.ofHom_id]
    exact RationalSection.id_comp X.rho

/-- Compose the actual isometries and their framing squares. -/
def trans (e : Iso X Y) (i : Iso Y Z) : Iso X Z where
  targetIso := e.targetIso.trans i.targetIso
  square := by
    change RationalSection.comp
      (RationalSection.ofHom ((i.targetIso.orderIso.hom.val.comp e.targetIso.orderIso.hom.val).map
        (Nilp.quotientO ℤ_[prime] T)) ⊤) X.rho = Z.rho
    rw [Hom.map_comp, ← RationalSection.comp_ofHom]
    change RationalSection.comp (RationalSection.comp (Y.reducedIsometrySection i.targetIso)
      (X.reducedIsometrySection e.targetIso)) X.rho = Z.rho
    exact (RationalSection.comp_assoc _ _ _).trans
      ((congrArg (RationalSection.comp (Y.reducedIsometrySection i.targetIso)) e.square).trans
        i.square)

end Iso

/-- Actual isomorphism classes of the affine framed triples. -/
def isoSetoid : Setoid (PolarizedFramedAffinePoint prime π frame T) where
  r X Y := Nonempty (Iso X Y)
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨i⟩ => ⟨e.trans i⟩⟩

abbrev IsomorphismClass := Quotient (isoSetoid (frame := frame) (T := T))

end PolarizedFramedAffinePoint

end Langlands.FormalGroup
