import Langlands.GroupScheme.Torus.FixedPointLifting

/-! # Twisted transporter actions and nilpotent lifting -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PointwiseSchemeAction

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- The actual left-right action `h • g = i₁(h) g i₂(h)⁻¹`. -/
def twistedTransporter (i₁ i₂ : H ⟶ G) : PointwiseSchemeAction H G.X where
  hom := (fst H.X G.X ≫ i₁.hom.hom) * snd H.X G.X *
    (fst H.X G.X ≫ i₂.hom.hom)⁻¹
  one_left g := by
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd,
      MonObj.one_comp, one_mul, inv_one, mul_one]
  mul_left h h' g := by
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd,
      MonObj.mul_comp, mul_inv_rev, mul_assoc]

@[simp] theorem twistedTransporter_act (i₁ i₂ : H ⟶ G) {T : Over S}
    (h : T ⟶ H.X) (g : T ⟶ G.X) :
    (twistedTransporter i₁ i₂).act h g =
      (h ≫ i₁.hom.hom) * g * (h ≫ i₂.hom.hom)⁻¹ := by
  simp only [act, twistedTransporter, MonObj.comp_mul, GrpObj.comp_inv,
    lift_fst_assoc, lift_snd]

/-- The all-test transporter relation between two homomorphisms. -/
def IsTransporter (i₁ i₂ : H ⟶ G) {T : Over S} (g : T ⟶ G.X) : Prop :=
  ∀ (T' : Over S) (b : T' ⟶ T) (h : T' ⟶ H.X),
    (h ≫ i₁.hom.hom) * (b ≫ g) = (b ≫ g) * (h ≫ i₂.hom.hom)

/-- Fixedness for the twisted action is precisely the transporter relation on
all refinements of the test scheme. -/
theorem twistedTransporter_isFixed_iff (i₁ i₂ : H ⟶ G) {T : Over S}
    (g : T ⟶ G.X) : (twistedTransporter i₁ i₂).IsFixed g ↔ IsTransporter i₁ i₂ g := by
  constructor
  · intro hg T' b h
    exact mul_inv_eq_iff_eq_mul.mp (by simpa only [twistedTransporter_act] using hg T' b h)
  · intro hg T' b h
    rw [twistedTransporter_act, hg T' b h, mul_inv_cancel_right]

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]

/-- Nilpotent lifting for the actual transporter relation of two diagonalizable
homomorphisms. -/
theorem exists_transporter_lift
    (i₁ i₂ : (Diagonalizable.groupScheme R M).toGrp ⟶ G)
    [Algebra.FormallySmooth R (AffineCoordinates.algebra G)]
    {C : CommAlgCat.{u} R} (I : Ideal C) (hI : IsNilpotent I)
    (x : (algSpec R).obj (op (CommAlgCat.of R (C ⧸ I))) ⟶ G.X)
    (hx : IsTransporter i₁ i₂ x) :
    ∃ y : (algSpec R).obj (op C) ⟶ G.X, IsTransporter i₁ i₂ y ∧
      (algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)).op ≫ y = x := by
  obtain ⟨y, hy, he⟩ := (twistedTransporter i₁ i₂).exists_fixed_lift I hI x
    ((twistedTransporter_isFixed_iff i₁ i₂ x).2 hx)
  exact ⟨y, (twistedTransporter_isFixed_iff i₁ i₂ y).1 hy, he⟩

end Langlands.GroupScheme.PointwiseSchemeAction
