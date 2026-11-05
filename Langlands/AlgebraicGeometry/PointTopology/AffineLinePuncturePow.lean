import Langlands.AlgebraicGeometry.PointTopology.AffineLinePunctureUnits
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyComparisons
import Langlands.AlgebraicGeometry.PointTopology.AffineLineOrigin

/-! # The `n`th-power morphism of the actual punctured affine line -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The coordinate endomorphism `t ↦ t ^ n` of `R[t]`. -/
def affineLinePowAlgHom : MvPolynomial Unit R →ₐ[R] MvPolynomial Unit R :=
  MvPolynomial.aeval (fun _ : Unit => (MvPolynomial.X () : MvPolynomial Unit R) ^ n)

/-- The endomorphism `t ↦ t ^ n` of `R[t, t⁻¹]`. -/
def punctureAwayPowAlgHom :
    Localization.Away (MvPolynomial.X () : MvPolynomial Unit R) →ₐ[R]
      Localization.Away (MvPolynomial.X () : MvPolynomial Unit R) :=
  IsLocalization.liftAlgHom
    (M := Submonoid.powers (MvPolynomial.X () : MvPolynomial Unit R))
    (f := (Algebra.algHom R (MvPolynomial Unit R)
      (Localization.Away (MvPolynomial.X () : MvPolynomial Unit R))).comp
        (affineLinePowAlgHom R n)) (by
    rintro ⟨y, k, rfl⟩
    simp only [AlgHom.comp_apply, map_pow, affineLinePowAlgHom, MvPolynomial.aeval_X]
    exact ((IsLocalization.Away.algebraMap_isUnit
      (MvPolynomial.X () : MvPolynomial Unit R)).pow n).pow k)

theorem punctureAwayPowAlgHom_comp :
    (punctureAwayPowAlgHom R n).comp (Algebra.algHom R (MvPolynomial Unit R)
      (Localization.Away (MvPolynomial.X () : MvPolynomial Unit R))) =
    (Algebra.algHom R (MvPolynomial Unit R)
      (Localization.Away (MvPolynomial.X () : MvPolynomial Unit R))).comp
        (affineLinePowAlgHom R n) := by
  apply AlgHom.ext
  intro a
  exact IsLocalization.lift_eq _ a

/-- The actual morphism `t ↦ t ^ n` of the punctured affine line over `Spec R`. -/
def affineLinePuncturePow : affineLinePuncture R ⟶ affineLinePuncture R :=
  (affineLinePunctureIsoAway R).hom ≫ ringTestMap R (punctureAwayPowAlgHom R n) ≫
    (affineLinePunctureIsoAway R).inv

/-- The power morphism restricts the coordinate power map of the affine line. -/
theorem affineLinePuncturePow_ι :
    affineLinePuncturePow R n ≫ affineLinePunctureι R =
      affineLinePunctureι R ≫ ringTestMap R (affineLinePowAlgHom R n) := by
  rw [← affineLinePunctureIsoAway_hom_ι, affineLinePuncturePow, Category.assoc,
    Category.assoc, Iso.inv_hom_id_assoc, ← ringTestMap_comp, punctureAwayPowAlgHom_comp,
    ringTestMap_comp, Category.assoc]

variable (S : Type u) [CommRing S] [Algebra R S] [TopologicalSpace S] [IsTopologicalRing S]

/-- Under the identification of punctured-line points with units, the power morphism is
the `n`th-power map. -/
theorem affineLinePunctureUnitHomeomorph_pow (p : RingPoint R (affineLinePuncture R) S) :
    affineLinePunctureUnitHomeomorph R S (p ≫ affineLinePuncturePow R n) =
      affineLinePunctureUnitHomeomorph R S p ^ n := by
  apply Units.ext
  let p₀ : ringTest R S ⟶ affineLinePuncture R := p
  have key : (p₀ ≫ affineLinePuncturePow R n) ≫ affineLinePunctureι R =
      (p₀ ≫ affineLinePunctureι R) ≫ ringTestMap R (affineLinePowAlgHom R n) := by
    rw [Category.assoc, affineLinePuncturePow_ι, Category.assoc]
  let ev := spectrumAlgebraPointEquiv R S (MvPolynomial Unit R) (p₀ ≫ affineLinePunctureι R)
  calc (affineLinePunctureUnitHomeomorph R S (p ≫ affineLinePuncturePow R n) : S)
      = affineLinePointEquiv R S ((p₀ ≫ affineLinePuncturePow R n) ≫ affineLinePunctureι R) :=
        affineLinePunctureUnitHomeomorph_val R S _
    _ = affineLinePointEquiv R S
          ((p₀ ≫ affineLinePunctureι R) ≫ ringTestMap R (affineLinePowAlgHom R n)) :=
        congrArg _ key
    _ = ev (affineLinePowAlgHom R n (MvPolynomial.X ())) :=
        congrArg (fun q => q (MvPolynomial.X ()))
          (spectrumAlgebraPointEquiv_natural R S (affineLinePowAlgHom R n)
            (p₀ ≫ affineLinePunctureι R))
    _ = ev (MvPolynomial.X ()) ^ n := by
        rw [affineLinePowAlgHom, MvPolynomial.aeval_X]
        exact map_pow ev.toAlgHom _ _
    _ = (affineLinePunctureUnitHomeomorph R S p : S) ^ n :=
        congrArg (· ^ n) (affineLinePunctureUnitHomeomorph_val R S p).symm
    _ = _ := (Units.val_pow_eq_pow_val _ _).symm

end Langlands.AlgebraicGeometry.PointTopology
