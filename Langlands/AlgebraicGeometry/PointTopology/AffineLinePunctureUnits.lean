import Langlands.AlgebraicGeometry.PointTopology.AffineLinePuncture
import Langlands.AlgebraicGeometry.PointTopology.Localization
import Mathlib.Topology.Algebra.Group.Units

/-! # The actual punctured-affine-line topology and units -/

noncomputable section

universe u v

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

namespace AlgPoint

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- A point of the coordinate localization gives both a unit and its inverse. -/
def polynomialAwayPointUnit
    (p : AlgPoint R (Localization.Away (MvPolynomial.X () : MvPolynomial Unit R)) S) :
    Sˣ where
  val := p (algebraMap _ _ (MvPolynomial.X () : MvPolynomial Unit R))
  inv := p (IsLocalization.Away.invSelf (MvPolynomial.X () : MvPolynomial Unit R))
  val_inv := by
    change p.toAlgHom _ * p.toAlgHom _ = 1
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  inv_val := by
    rw [mul_comm]
    change p.toAlgHom _ * p.toAlgHom _ = 1
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]

/-- Polynomial localization points are canonically the units of the value ring. -/
def polynomialAwayUnitEquiv :
    AlgPoint R (Localization.Away (MvPolynomial.X () : MvPolynomial Unit R)) S ≃ Sˣ where
  toFun := polynomialAwayPointUnit R S
  invFun u :=
    (localizationPointEquiv
      (R := R) (S := S)
      (L := Localization.Away (MvPolynomial.X () : MvPolynomial Unit R))
      (Submonoid.powers (MvPolynomial.X () : MvPolynomial Unit R))).symm
      ⟨ofAlgHom (MvPolynomial.aeval (fun _ : Unit => (u : S))),
        (unit_powers_iff _ _).mpr (by simp)⟩
  left_inv p := by
    apply (localizationPointEquiv
      (R := R) (S := S)
      (L := Localization.Away (MvPolynomial.X () : MvPolynomial Unit R))
      (Submonoid.powers (MvPolynomial.X () : MvPolynomial Unit R))).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    apply algHomEquiv.injective
    apply MvPolynomial.algHom_ext
    intro i
    cases i
    exact MvPolynomial.aeval_X _ _
  right_inv u := by
    apply Units.ext
    change (localizationPointEquiv
      (R := R) (S := S)
      (L := Localization.Away (MvPolynomial.X () : MvPolynomial Unit R))
      (Submonoid.powers (MvPolynomial.X () : MvPolynomial Unit R))).symm _
        (algebraMap _ _ (MvPolynomial.X () : MvPolynomial Unit R)) = _
    rw [localizationPointEquiv_symm_algebraMap]
    exact MvPolynomial.aeval_X _ _

@[simp] theorem polynomialAwayUnitEquiv_val
    (p : AlgPoint R (Localization.Away (MvPolynomial.X () : MvPolynomial Unit R)) S) :
    (polynomialAwayUnitEquiv R S p : S) =
      p (algebraMap _ _ (MvPolynomial.X () : MvPolynomial Unit R)) := rfl

@[simp] theorem polynomialAwayUnitEquiv_symm_algebraMap (u : Sˣ)
    (a : MvPolynomial Unit R) :
    (polynomialAwayUnitEquiv R S).symm u (algebraMap _ _ a) =
      MvPolynomial.aeval (fun _ : Unit => (u : S)) a :=
  localizationPointEquiv_symm_algebraMap _ _ a

variable [TopologicalSpace S] [IsTopologicalRing S]

/-- The localization has the value-and-inverse topology, with no subspace hypothesis. -/
def polynomialAwayUnitHomeomorph :
    AlgPoint R (Localization.Away (MvPolynomial.X () : MvPolynomial Unit R)) S ≃ₜ Sˣ where
  toEquiv := polynomialAwayUnitEquiv R S
  continuous_toFun := Units.continuous_iff.mpr
    ⟨continuous_eval _, continuous_eval _⟩
  continuous_invFun := by
    apply (AlgPoint.continuous_iff _).mpr
    intro b
    obtain ⟨n, a, hb⟩ := IsLocalization.Away.surj
      (MvPolynomial.X () : MvPolynomial Unit R) b
    have heq (u : Sˣ) :
        (polynomialAwayUnitEquiv R S).symm u b =
          MvPolynomial.aeval (fun _ : Unit => (u : S)) a *
            Units.val ((u ^ n)⁻¹) := by
      apply (Units.eq_mul_inv_iff_mul_eq (u ^ n)).mpr
      have h := congrArg ((polynomialAwayUnitEquiv R S).symm u).toAlgHom hb
      rw [map_mul, map_pow] at h
      change (polynomialAwayUnitEquiv R S).symm u b *
        ((polynomialAwayUnitEquiv R S).symm u
          (algebraMap _ _ (MvPolynomial.X () : MvPolynomial Unit R))) ^ n =
        (polynomialAwayUnitEquiv R S).symm u (algebraMap _ _ a) at h
      rw [polynomialAwayUnitEquiv_symm_algebraMap,
        polynomialAwayUnitEquiv_symm_algebraMap, MvPolynomial.aeval_X] at h
      exact h
    change Continuous (fun u : Sˣ => (polynomialAwayUnitEquiv R S).symm u b)
    simp_rw [heq]
    exact (((continuous_eval a).comp
      ((polynomialPointHomeomorph (R := R) (S := S) Unit).symm.continuous.comp
        (continuous_pi fun _ : Unit => Units.continuous_val))).mul
      (Units.continuous_coe_inv.comp (continuous_pow n)))

end AlgPoint

section Scheme

variable (R : Type u) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- The actual open subscheme D(t) is the relative spectrum of R[t,t⁻¹]. -/
def affineLinePunctureIsoAway :
    affineLinePuncture R ≅
      ringTest R (Localization.Away (MvPolynomial.X () : MvPolynomial Unit R)) :=
  Over.isoMk (basicOpenIsoSpecAway (R := CommRingCat.of (MvPolynomial Unit R))
    (MvPolynomial.X ())) (by
    let A := MvPolynomial Unit R
    let L := Localization.Away (MvPolynomial.X () : A)
    change (basicOpenIsoSpecAway (R := CommRingCat.of A) (MvPolynomial.X ())).hom ≫
      Spec.algebraMap R L =
        (affineLinePuncturedOpen R).ι ≫ Spec.algebraMap R A
    have hbase := Over.w (ringTestMap R (Algebra.algHom R A L))
    change Spec.algebraMap A L ≫ Spec.algebraMap R A = Spec.algebraMap R L at hbase
    rw [← hbase]
    change (basicOpenIsoSpecAway (R := CommRingCat.of A) (MvPolynomial.X ())).hom ≫
      (Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ Spec.algebraMap R A) = _
    rw [← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
    rfl)

@[simp] theorem affineLinePunctureIsoAway_hom_ι :
    (affineLinePunctureIsoAway R).hom ≫
      ringTestMap R (Algebra.algHom R (MvPolynomial Unit R)
        (Localization.Away (MvPolynomial.X () : MvPolynomial Unit R))) =
      affineLinePunctureι R := by
  ext1
  exact basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of (MvPolynomial Unit R))
    (MvPolynomial.X ())

instance affineLinePuncture_isAffine : IsAffine (affineLinePuncture R).left := by
  change IsAffine (Scheme.Opens.toScheme
    (X := Spec (CommRingCat.of (MvPolynomial Unit R)))
      (PrimeSpectrum.basicOpen (MvPolynomial.X ())))
  exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (MvPolynomial Unit R))
    (MvPolynomial.X ())

variable (S : Type u) [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S]

/-- Actual punctured-affine-line points carry the usual value-and-inverse units topology. -/
def affineLinePunctureUnitHomeomorph :
    RingPoint R (affineLinePuncture R) S ≃ₜ Sˣ :=
  ((affineSchemePointIsoHomeomorph R S (affineLinePunctureIsoAway R)).trans
    (spectrumAlgebraPointHomeomorph R S
      (Localization.Away (MvPolynomial.X () : MvPolynomial Unit R)))).trans
        (AlgPoint.polynomialAwayUnitHomeomorph R S)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem affineLinePunctureUnitHomeomorph_val
    (p : RingPoint R (affineLinePuncture R) S) :
    (affineLinePunctureUnitHomeomorph R S p : S) =
      affineLinePointEquiv R S (p ≫ affineLinePunctureι R) := by
  change spectrumAlgebraPointEquiv R S
    (Localization.Away (MvPolynomial.X () : MvPolynomial Unit R))
      (affineSchemePointIsoHomeomorph R S (affineLinePunctureIsoAway R) p)
        (algebraMap _ _ (MvPolynomial.X () : MvPolynomial Unit R)) = _
  rw [affineSchemePointIsoHomeomorph_apply, affineLinePointEquiv_apply,
    ← affineLinePunctureIsoAway_hom_ι, ← Category.assoc,
    spectrumAlgebraPointEquiv_natural]
  rfl

end Scheme

end Langlands.AlgebraicGeometry.PointTopology
