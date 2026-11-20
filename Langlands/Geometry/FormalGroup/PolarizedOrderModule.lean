import Langlands.Geometry.FormalGroup.TorsionPolarizationSimilitude
import Langlands.Geometry.FormalGroup.OrderIso

/-! # Polarized formal modules with an actual order action -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory _root_.AlgebraicGeometry Langlands.Shimura
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {π : O} {hM : M.IsPiDivisible π} {hN : N.IsPiDivisible π}

namespace Hom.IsTorsionSimilitude

/-- The inverse of an integral formal isometry preserves the actual pairing. -/
theorem inverse_isometry {e : ModuleLaw.Iso M N}
    {P : TorsionPrincipalPolarization hM} {Q : TorsionPrincipalPolarization hN}
    (he : e.hom.IsTorsionSimilitude P Q 1) : e.inv.IsTorsionSimilitude Q P 1 := by
  intro n T x y
  let f := e.hom.scalarTorsionSchemeMap hM hN n
  let g := e.inv.scalarTorsionSchemeMap hN hM n
  have hgf : g ≫ f = 𝟙 (hN.torsionSchemeInclusions.obj n) := by
    change e.inv.scalarTorsionSchemeMap hN hM n ≫ e.hom.scalarTorsionSchemeMap hM hN n = _
    rw [← scalarTorsionSchemeMap_comp, e.hom_inv, scalarTorsionSchemeMap_id]
  have hpts (t : T ⟶ (hN.torsionSchemeInclusions.obj n).X) :
      (t ≫ g.toMul.hom.hom) ≫ f.toMul.hom.hom = t := by
    rw [Category.assoc]
    have hh := congrArg (fun m => m.toMul.hom.hom) hgf
    change g.toMul.hom.hom ≫ f.toMul.hom.hom = 𝟙 _ at hh
    rw [hh, Category.comp_id]
  have h := he n T (x ≫ g.toMul.hom.hom) (y ≫ g.toMul.hom.hom)
  rw [scalarHom_one, scalarTorsionSchemeMap_id] at h ⊢
  change Q.toTorsionCartierDuality.pairing n
      ((x ≫ g.toMul.hom.hom) ≫ f.toMul.hom.hom)
      ((y ≫ g.toMul.hom.hom) ≫ f.toMul.hom.hom) =
    P.toTorsionCartierDuality.pairing n ((x ≫ g.toMul.hom.hom) ≫ 𝟙 _) (y ≫ g.toMul.hom.hom) at h
  change P.toTorsionCartierDuality.pairing n (x ≫ g.toMul.hom.hom) (y ≫ g.toMul.hom.hom) =
    Q.toTorsionCartierDuality.pairing n (x ≫ 𝟙 _) y
  simpa only [Category.comp_id, hpts] using h.symm

end Hom.IsTorsionSimilitude

/-- A coordinate formal module with an order action and an actual
order-antilinear principal polarization. -/
structure PolarizedOrderModule
    (A : Type w) [Ring A] [Algebra O A]
    (star : AlgebraInvolution O A) (R : Type v) [CommRing R] [Algebra O R] (π : O) where
  dimension : ℕ
  law : ModuleLaw O R (Fin dimension)
  order : OrderAction A law
  divisible : law.IsPiDivisible π
  polarization : TorsionPrincipalPolarization divisible
  adjoint : order.IsAntilinearTorsionPolarization star polarization

namespace PolarizedOrderModule

variable {A : Type w} [Ring A] [Algebra O A] {star : AlgebraInvolution O A}
variable {X Y Z : PolarizedOrderModule A star R π}

/-- Extend the actual formal law, its order action, and its principal polarization. -/
def map (X : PolarizedOrderModule A star R π) (φ : R →ₐ[O] S) :
    PolarizedOrderModule A star S π where
  dimension := X.dimension
  law := X.law.map φ
  order := X.order.map φ
  divisible := X.divisible.map φ
  polarization := X.polarization.baseChange φ
  adjoint := X.adjoint.baseChange φ

/-- An isomorphism of polarized order modules is an integral order isomorphism
preserving the actual polarization. -/
structure Iso (X Y : PolarizedOrderModule A star R π) where
  orderIso : OrderAction.Iso X.order Y.order
  preserves : orderIso.hom.val.IsTorsionSimilitude X.polarization Y.polarization 1

namespace Iso

/-- The actual identity is an isometry. -/
def refl (X : PolarizedOrderModule A star R π) : Iso X X where
  orderIso := OrderAction.Iso.refl X.order
  preserves := Hom.IsTorsionSimilitude.id X.polarization

/-- The actual inverse is also an isometry. -/
def symm (f : Iso X Y) : Iso Y X where
  orderIso := f.orderIso.symm
  preserves := Hom.IsTorsionSimilitude.inverse_isometry (e := f.orderIso.toModuleIso) f.preserves

/-- Composition of the actual order isomorphisms preserves the pairings. -/
def trans (f : Iso X Y) (g : Iso Y Z) : Iso X Z where
  orderIso := f.orderIso.trans g.orderIso
  preserves := by
    change (g.orderIso.hom.val.comp f.orderIso.hom.val).IsTorsionSimilitude
      X.polarization Z.polarization 1
    simpa only [one_mul] using g.preserves.comp f.preserves

/-- Extend an actual isometry and its inverse along the coefficient map. -/
def map (f : Iso X Y) (φ : R →ₐ[O] S) : Iso (X.map φ) (Y.map φ) where
  orderIso := f.orderIso.map φ
  preserves := f.preserves.baseChange φ

theorem nonempty_iso_refl (X : PolarizedOrderModule A star R π) : Nonempty (Iso X X) :=
  ⟨refl X⟩

end Iso

/-- The equivalence relation of actual integral polarized order isomorphisms. -/
def isoSetoid : Setoid (PolarizedOrderModule A star R π) where
  r X Y := Nonempty (Iso X Y)
  iseqv := ⟨Iso.nonempty_iso_refl, fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

end PolarizedOrderModule

end Langlands.FormalGroup.ModuleLaw
