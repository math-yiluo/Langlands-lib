import Langlands.GroupScheme.HomScheme.SplitTorusAffineExtension
import Langlands.GroupScheme.Torus.DiagonalizableAutomorphismLocality
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Torus.DiagonalizableTorsion

/-! # Coefficient and torsion projections for diagonalizable groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable

open GroupScheme TorsionDensity DiagonalizableCharacter

variable {R K : Type u} [CommRing R] [CommRing K]
  (M : Type u) [AddCommGroup M] (φ : R →+* K)

/-- The change-of-coefficients projection as a morphism over the original base. -/
def coefficientProjectionOver :
    (Over.map (Spec.map (CommRingCat.ofHom φ))).obj (groupScheme (CommRingCat.of K) M).X ⟶
      (groupScheme (CommRingCat.of R) M).X :=
  Over.homMk (coefficientProjection M φ) (by
    change Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom M φ)) ≫
        Spec.algebraMap R (AddMonoidAlgebra R M) =
      Spec.algebraMap K (AddMonoidAlgebra K M) ≫ Spec.map (CommRingCat.ofHom φ)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact AddMonoidAlgebra.mapRingHom_single φ 0 r)

set_option backward.isDefEq.respectTransparency false in
/-- The pullback projection from the scalar extension is the coefficient projection
in the canonical diagonalizable coordinates. -/
theorem baseChangeIso_inv_fst :
    (baseChangeIso (Spec.map (CommRingCat.ofHom φ)) M).inv.hom.hom.left ≫
      pullback.fst (groupScheme (CommRingCat.of R) M).X.hom
        (Spec.map (CommRingCat.ofHom φ)) = coefficientProjection M φ := by
  let A := CommRingCat.of R
  let B := CommRingCat.of K
  let b := Spec.map (CommRingCat.ofHom φ)
  let U := (groupScheme B M).X
  have h : baseChangePointsEquiv b (groupScheme A M).toGrp U
      (𝟙 U ≫ (baseChangeIso b M).inv.hom.hom) = coefficientProjectionOver M φ := by
    apply (characterPointsEquiv A M ((Over.map b).obj U)).injective
    change baseChangeCharacterPointsEquiv b M U (𝟙 U ≫ (baseChangeIso b M).inv.hom.hom) =
      characterPointsEquiv A M ((Over.map b).obj U) (coefficientProjectionOver M φ)
    rw [baseChangeCharacterPointsEquiv_baseChangeIso_inv]
    apply MonoidHom.ext
    intro m
    apply Units.ext
    change Units.val (characterPointsEquiv B M U (𝟙 U) (.ofAdd m.toAdd)) =
      Units.val (characterPointsEquiv A M ((Over.map b).obj U)
        (coefficientProjectionOver M φ) (.ofAdd m.toAdd))
    rw [characterPointsEquiv_val, characterPointsEquiv_val,
      lift_characterPointsEquiv_id, lift_characterPointsEquiv]
    let A' := CommRingCat.of (AddMonoidAlgebra R M)
    let B' := CommRingCat.of (AddMonoidAlgebra K M)
    apply (Scheme.ΓSpecIso B').commRingCatIsoToRingEquiv.injective
    change ((Scheme.ΓSpecIso B').inv ≫ (Scheme.ΓSpecIso B').hom)
        (AddMonoidAlgebra.single m.toAdd 1) =
      ((Scheme.ΓSpecIso A').inv ≫ (coefficientProjection M φ).appTop ≫
        (Scheme.ΓSpecIso B').hom) (AddMonoidAlgebra.single m.toAdd 1)
    rw [Iso.inv_hom_id, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    change AddMonoidAlgebra.single m.toAdd 1 =
      AddMonoidAlgebra.mapRingHom M φ (AddMonoidAlgebra.single m.toAdd 1)
    rw [AddMonoidAlgebra.mapRingHom_single, map_one]
  have hleft := congrArg (fun a => a.left) h
  simp only [baseChangePointsEquiv_left, Category.id_comp] at hleft
  change (baseChangeIso b M).inv.hom.hom.left ≫
    pullback.fst (groupScheme A M).X.hom b = coefficientProjection M φ at hleft
  exact hleft

variable (A : CommRingCat.{u})

/-- The canonical torsion isomorphism identifies inclusion with restriction of
characters along the quotient of the lattice. -/
theorem torsionIso_inv_comp_ι (n : ℕ) :
    (torsionIso A M n).inv ≫ torsionι (groupScheme A M).toGrp (n : ℤ) =
      restrictMap A (QuotientAddGroup.mk' (multiples M n)) := by
  apply hom_ext_points
  intro U x
  apply (characterPointsEquiv A M U).injective
  apply MonoidHom.ext
  intro m
  change characterPointsEquiv A M U
      (x ≫ (torsionIso A M n).inv.hom.hom ≫ (torsionι _ (n : ℤ)).hom.hom) m =
    characterPointsEquiv A M U
      (x ≫ (restrictMap A (QuotientAddGroup.mk' (multiples M n))).hom.hom) m
  have h := isoOfPointModels_inv
    (fun U : Over (Spec A) =>
      subgroupAnnihilator (FiniteCharacterSeparation.multiples (M := M) n) (Γ(U.left, ⊤))ˣ)
    (fun a => torsionAnnihilatorRestrict A M n a)
    (torsionCharacterPointsEquiv A M n)
    (torsionQuotientCharacterPointsEquiv A M n)
    (torsionCharacterPointsEquiv_naturality A M n)
    (torsionQuotientCharacterPointsEquiv_naturality A M n) U x
  rw [← Category.assoc]
  exact (congrArg (fun χ => χ.val m) h).trans
    (pointsEquiv_restrictMap A (QuotientAddGroup.mk' (multiples M n)) x m.toAdd).symm

/-- In split-torus coordinates the actual torsion inclusion is the spectrum of
reduction of exponents modulo the torsion order. -/
theorem torsionIso_inv_comp_ι_left (L : Type u) [Fintype L] (n : ℕ) :
    (torsionIso (CommRingCat.of R) (L → ℤ) n).inv.hom.hom.left ≫
      (torsionι (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp (n : ℤ)).hom.hom.left =
      torsionProjection L R n := by
  rw [← Over.comp_left]
  change (((torsionIso (CommRingCat.of R) (L → ℤ) n).inv ≫
    torsionι (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp (n : ℤ)).hom.hom.left) = _
  rw [torsionIso_inv_comp_ι, restrictMap_left]
  rfl

end Langlands.GroupScheme.Diagonalizable
