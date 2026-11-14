import Langlands.Geometry.Building.CoordinateAffineRootJumps

/-! # Actual doubled-root jumps from supplied quadratic unitary coordinates -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

private def subgroupEquivOfImage {P : Type v} {Q : Type w} [Group P] [Group Q]
    (f : P →* Q) (hf : Function.Injective f) (H : Subgroup P) (K : Subgroup Q)
    (himage : ∀ q, q ∈ K ↔ ∃ p ∈ H, f p = q) : H ≃* K :=
  (H.equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (SetLike.ext fun q => (himage q).symm))

private theorem subgroupEquivOfImage_apply {P : Type v} {Q : Type w}
    [Group P] [Group Q]
    (f : P →* Q) (hf : Function.Injective f) (H : Subgroup P) (K : Subgroup Q)
    (himage : ∀ q, q ∈ K ↔ ∃ p ∈ H, f p = q) (p : H) :
    (subgroupEquivOfImage f hf H K himage p : Q) = f p.val :=
  rfl

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} {s : S.toGrp ⟶ Z}
  {a : characterLattice S}

/-- The supplied identification of the double-root subgroup restricts unitary coordinates
to an isomorphism from the literal central subgroup onto `U_{2a}(k)`. -/
def RootUnitaryCoordinates.centralEquivDouble (R : RootUnitaryCoordinates i j s a) :
    SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension) ≃*
      rootGroupPoints i (2 • a) :=
  subgroupEquivOfImage ((rootGroupPoints i a).subtype.comp R.equiv.toMonoidHom)
    (Subtype.val_injective.comp R.equiv.injective) _ _ R.double

@[simp] theorem RootUnitaryCoordinates.centralEquivDouble_apply
    (R : RootUnitaryCoordinates i j s a)
    (z : SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension)) :
    (R.centralEquivDouble z : rationalPoints G) = (R.equiv z.val : rationalPoints G) :=
  subgroupEquivOfImage_apply _ _ _ _ R.double z

variable [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- V4 determines the doubled-root depth from the supplied unitary depth formula. -/
theorem RootUnitaryCoordinates.depth_double_of_depthA
    (a : relativeRoots i) (R : RootUnitaryCoordinates i j s a)
    (h2a : 2 • (a : characterLattice S) ∈ relativeRoots i)
    (w : AddValuation R.extension (WithTop ℝ)) (x : D.Apartment)
    (hdepth : ∀ p, x.val a (R.equiv p) = SU3Root.Parameters.depthA w p)
    (z : SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension)) :
    x.val (2 • (a : characterLattice S)) (R.centralEquivDouble z) =
      SU3Root.Parameters.depthDouble w z := by
  rw [R.centralEquivDouble_apply,
    x.isValuation.double a a.property h2a _ ((R.double _).mpr ⟨z.val, z.property, rfl⟩),
    hdepth, SU3Root.Parameters.depthDouble_eq_double_depthA]
  cases h : SU3Root.Parameters.depthA w z.val using WithTop.recTopCoe with
  | top => simp only [two_nsmul, WithTop.top_add, SU3Root.doubleTop_top]
  | coe t =>
    simp only [two_nsmul, ← WithTop.coe_add, SU3Root.doubleTop_coe]
    congr 1
    ring

/-- In the absence of a quadruple relative root, the supplied unitary depth formula
identifies ordinary affine roots in the doubled direction with literal central depth jumps. -/
theorem RootUnitaryCoordinates.mem_affineRoots_double_iff_centralDepthJump
    (hS : IsSplitTorus S.toGrp) (a : relativeRoots i)
    (R : RootUnitaryCoordinates i j s a)
    (h2a : 2 • (a : characterLattice S) ∈ relativeRoots i)
    (hNo4 : 2 • (2 • (a : characterLattice S)) ∉ relativeRoots i)
    (w : AddValuation R.extension (WithTop ℝ)) (x : D.Apartment)
    (hdepth : ∀ p, x.val a (R.equiv p) = SU3Root.Parameters.depthA w p)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ}
    (hlin : ψ.linear = rootForm i ⟨2 • (a : characterLattice S), h2a⟩) :
    ψ ∈ D.affineRoots ↔
      ¬ {z : SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension) |
          ((ψ x : ℝ) : WithTop ℝ) ≤ SU3Root.Parameters.depthDouble w z} ⊆
        {z | ((ψ x : ℝ) : WithTop ℝ) < SU3Root.Parameters.depthDouble w z} := by
  have hdouble : ∀ g : rationalPoints G,
      g ∈ doubleRootGroupPoints i (2 • (a : characterLattice S)) ↔
        ∃ z ∈ (⊥ : Subgroup
          (SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension))),
          (R.centralEquivDouble z : rationalPoints G) = g := by
    intro g
    simp only [doubleRootGroupPoints, ite_eq_right hNo4, Subgroup.mem_bot]
    constructor
    · intro hg
      exact ⟨1, rfl, by simp [hg]⟩
    · rintro ⟨z, rfl, hz⟩
      simpa only [map_one, Subgroup.coe_one] using hz.symm
  rw [D.mem_affineRoots_iff_coordinateDepthJump
    (Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split hS i)
    ⟨2 • (a : characterLattice S), h2a⟩ R.centralEquivDouble
    (SU3Root.Parameters.depthDouble w) ⊥ x
    (R.depth_double_of_depthA D a h2a w x hdepth) hdouble hlin]
  change (¬ _ ⊆ _ * (1 : Set
    (SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension)))) ↔ _
  rw [mul_one]

end Langlands.Geometry.Building
