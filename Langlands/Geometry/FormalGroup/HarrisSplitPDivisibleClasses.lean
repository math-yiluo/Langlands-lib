import Langlands.Geometry.FormalGroup.HarrisSplitPDivisiblePullback

/-! # Isomorphism classes of split polarized affine points -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v s

open CategoryTheory ValuativeRel AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

variable {R S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime] {A : Type u} [Ring A]
variable {F₀ : PDivisibleGroup (CommRingCat.of S) p}

/-- The actual tower data used to test an isomorphism of polarized framed points. -/
structure PolarizedFramedTower (a : A →+* End F₀) where
  target : PDivisibleGroup (CommRingCat.of R) p
  order : A →+* End target
  polarization : target.PrincipalPolarization
  rigidifier : OrderQuasiIsogeny a ((baseChangeEnd (S := S) target).comp order)

namespace PolarizedFramedTower

variable {a : A →+* End F₀}

local notation "BC" => baseChangeFunctor R S p

/-- An actual polarized order-linear target isomorphism that preserves the rigidifier. -/
structure Iso (X Y : PolarizedFramedTower (R := R) a) where
  targetIso : X.target ≅ Y.target
  order : ∀ t, X.order t ≫ targetIso.hom = targetIso.hom ≫ Y.order t
  pairing : ∀ (n : ℕ) (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ (X.target.inclusions.obj n).X),
    let f := (targetIso.hom.app n).toMul.hom.hom
    Y.polarization.evaluate n T (x ≫ f) (y ≫ f) = X.polarization.evaluate n T x y
  frame : RationalHom.comp X.rigidifier.val.hom (RationalHom.ofHom ((BC).map targetIso.hom)) =
    Y.rigidifier.val.hom

namespace Iso

variable {X Y Z : PolarizedFramedTower (R := R) a}

/-- Identity of the actual polarized framed data. -/
def refl (X : PolarizedFramedTower (R := R) a) : Iso X X where
  targetIso := CategoryTheory.Iso.refl _
  order _ := (Category.comp_id _).trans (Category.id_comp _).symm
  pairing n T x y := by
    change X.polarization.evaluate n T (x ≫ 𝟙 _) (y ≫ 𝟙 _) = _
    rw [Category.comp_id, Category.comp_id]
  frame := by
    change RationalHom.comp X.rigidifier.val.hom (RationalHom.ofHom ((BC).map (𝟙 X.target))) = _
    rw [(BC).map_id, RationalHom.ofHom_id, RationalHom.comp_id]

/-- Invert the actual polarized framed isomorphism. -/
def symm (e : Iso X Y) : Iso Y X where
  targetIso := e.targetIso.symm
  order t := by
    change Y.order t ≫ e.targetIso.inv = e.targetIso.inv ≫ X.order t
    apply (cancel_mono e.targetIso.hom).mp
    rw [Category.assoc, e.targetIso.inv_hom_id, Category.comp_id, Category.assoc,
      e.order t, ← Category.assoc, e.targetIso.inv_hom_id, Category.id_comp]
  pairing n T x y := by
    let f := (e.targetIso.hom.app n).toMul.hom.hom
    let g := (e.targetIso.inv.app n).toMul.hom.hom
    have h : g ≫ f = 𝟙 _ := congrArg (fun m : End Y.target => (m.app n).toMul.hom.hom)
      e.targetIso.inv_hom_id
    have he := e.pairing n T (x ≫ g) (y ≫ g)
    change Y.polarization.evaluate n T ((x ≫ g) ≫ f) ((y ≫ g) ≫ f) = _ at he
    rw [Category.assoc, Category.assoc, h, Category.comp_id, Category.comp_id] at he
    exact he.symm
  frame := by
    change RationalHom.comp Y.rigidifier.val.hom (RationalHom.ofHom ((BC).map e.targetIso.inv)) = _
    rw [← e.frame, RationalHom.comp_assoc, ← RationalHom.ofHom_comp, ← (BC).map_comp,
      e.targetIso.hom_inv_id, (BC).map_id, RationalHom.ofHom_id, RationalHom.comp_id]

/-- Compose the actual polarized framed isomorphisms. -/
def trans (e : Iso X Y) (f : Iso Y Z) : Iso X Z where
  targetIso := e.targetIso.trans f.targetIso
  order t := by
    change X.order t ≫ (e.targetIso.hom ≫ f.targetIso.hom) = (e.targetIso.hom ≫ f.targetIso.hom) ≫ Z.order t
    rw [← Category.assoc, e.order t, Category.assoc, f.order t, Category.assoc]
  pairing n T x y := by
    let i := (e.targetIso.hom.app n).toMul.hom.hom
    let j := (f.targetIso.hom.app n).toMul.hom.hom
    change Z.polarization.evaluate n T (x ≫ (i ≫ j)) (y ≫ (i ≫ j)) = _
    rw [← Category.assoc x, ← Category.assoc y]
    exact (f.pairing n T (x ≫ i) (y ≫ i)).trans (e.pairing n T x y)
  frame := by
    change RationalHom.comp X.rigidifier.val.hom
      (RationalHom.ofHom ((BC).map (e.targetIso.hom ≫ f.targetIso.hom))) = _
    rw [(BC).map_comp, RationalHom.ofHom_comp, ← RationalHom.comp_assoc, e.frame, f.frame]

end Iso

/-- Strict polarized isomorphism is an equivalence relation for the tower data. -/
def isoSetoid : Setoid (PolarizedFramedTower (R := R) a) where
  r X Y := Nonempty (Iso X Y)
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

end PolarizedFramedTower
end Langlands.PDivisibleGroup

namespace Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint

open LocalDivision GroupScheme.Cartier PDivisibleGroup

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {embedding : L →ₐ[K] D}
variable {W : Type v} [CommRing W] [Algebra 𝒪[K] W] {π : 𝒪[K]}
variable {p e : ℕ} [Fact p.Prime] {b : 𝒪[K]ˣ}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) («ι» := embedding)
  (R := ResidueRing W (algebraMap 𝒪[K] W π)) π}
variable {hp : (p : 𝒪[K]) = (b : 𝒪[K]) * π ^ e} {he : 0 < e}
variable {T : Nilp.{v, v} W (algebraMap 𝒪[K] W π)}

/-- The actual split point supplies the target, order, polarization and rigidifier. -/
def framedTower (X : SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he T)
    (hExact : FiniteCartierDualExactnessStatement.{v}) :
    PolarizedFramedTower (R := T.obj)
      ((baseChangeEnd (S := specialFibre (π := π) T) (Φ.splitPDivisibleGroup hp he hExact)).comp
        (Φ.splitPDivisibleAction hp he hExact)) where
  target := X.targetTower hExact
  order := X.orderAction hExact
  polarization := X.polarization hExact
  rigidifier := X.rigidifier hExact

/-- Two split points are equivalent when their actual polarized framed data are isomorphic. -/
def isoSetoid (hExact : FiniteCartierDualExactnessStatement.{v}) :
    Setoid (SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he T) :=
  Setoid.comap (fun X => X.framedTower hExact) PolarizedFramedTower.isoSetoid

/-- Isomorphism classes of the split presentation of the affine polarized points. -/
def IsomorphismClass (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) («ι» := embedding)
    (R := ResidueRing W (algebraMap 𝒪[K] W π)) π)
    (hp : (p : 𝒪[K]) = (b : 𝒪[K]) * π ^ e) (he : 0 < e)
    (T : Nilp.{v, v} W (algebraMap 𝒪[K] W π)) (hExact : FiniteCartierDualExactnessStatement.{v}) :=
  Quotient (isoSetoid (W := W) (π := π) (Φ := Φ) (hp := hp) (he := he) (T := T) hExact)

end Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint
