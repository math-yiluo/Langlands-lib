import Langlands.GroupScheme.Torus.HomFamilyLocality
import Langlands.GroupScheme.Torus.ExponentTransport
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Local exponent descriptions of actual split-torus homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {S S' : Scheme.{u}} {I J : Type u} [Fintype I] [Fintype J]

/-- The actual coordinate-normalized pullback of a split-torus homomorphism. -/
def pullHom (τ : splitTorus S I ⟶ splitTorus S J) (q : S' ⟶ S) :
    splitTorus S' I ⟶ splitTorus S' J :=
  (baseChangeIso q I).inv ≫ (GroupScheme.baseChange q).map τ ≫
    (baseChangeIso q J).hom

/-- The actual coordinate-normalized pullback of a split-torus isomorphism. -/
def pullIso (τ : splitTorus S I ≅ splitTorus S J) (q : S' ⟶ S) :
    splitTorus S' I ≅ splitTorus S' J :=
  (baseChangeIso q I).symm ≪≫ (GroupScheme.baseChange q).mapIso τ ≪≫
    baseChangeIso q J

/-- A homomorphism considered as a constant family over the terminal parameter. -/
def homFamily (τ : splitTorus S I ⟶ splitTorus S J) :
    ∀ U : Over S, (U ⟶ Over.mk (𝟙 S)) →
      (U ⟶ (splitTorus S I).X) → (U ⟶ (splitTorus S J).X) :=
  fun _ _ x => x ≫ τ.hom.hom

/-- Actual postcomposition is a multiplicative natural family. -/
theorem homFamily_isHomFamily (τ : splitTorus S I ⟶ splitTorus S J) :
    HomFamily.IsHomFamily (homFamily τ) where
  map_mul _ _ _ _ := MonObj.mul_comp _ _ _
  naturality _ _ _ := Category.assoc _ _ _

/-- Coordinate-normalized pullback has the original point action under the
actual pullback adjunction. -/
theorem pointsEquiv_pullHom (τ : splitTorus S I ⟶ splitTorus S J)
    (q : S' ⟶ S) (U : Over S') (x : U ⟶ (splitTorus S' I).X) :
    pointsEquiv J U (x ≫ (pullHom τ q).hom.hom) =
      pointsEquiv J ((Over.map q).obj U)
        (GroupScheme.baseChangePointsEquiv q (splitTorus S I) U
          (x ≫ (baseChangeIso q I).inv.hom.hom) ≫ τ.hom.hom) := by
  simp only [pullHom, Grp.comp_hom_hom, ← Category.assoc]
  rw [pointsEquiv_baseChangeIso_hom]
  change pointsEquiv J ((Over.map q).obj U)
    (GroupScheme.baseChangePointsEquiv q (splitTorus S J) U
      ((x ≫ (baseChangeIso q I).inv.hom.hom) ≫
        ((GroupScheme.baseChange q).map τ).hom.hom)) = _
  rw [GroupScheme.baseChangePointsEquiv_comp]

private theorem units_pullHom (τ : splitTorus S I ⟶ splitTorus S J)
    (q : S' ⟶ S) (U : Over S')
    (a : (Over.map q).obj U ⟶ Over.mk (𝟙 S))
    (x : I → (Γ(U.left, ⊤))ˣ) :
    HomFamily.famUnits (Iso.refl _) (Iso.refl _) (homFamily τ) a x =
      pointsEquiv J U
        ((pointsEquiv I U).symm x ≫ (pullHom τ q).hom.hom) := by
  rw [pointsEquiv_pullHom]
  have hi := pointsEquiv_baseChangeIso_hom q I U
    ((pointsEquiv I U).symm x ≫ (baseChangeIso q I).inv.hom.hom)
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id, MulEquiv.apply_symm_apply] at hi
  have hpoint : GroupScheme.baseChangePointsEquiv q (splitTorus S I) U
      ((pointsEquiv I U).symm x ≫ (baseChangeIso q I).inv.hom.hom) =
        (pointsEquiv I ((Over.map q).obj U)).symm x := by
    apply (pointsEquiv I ((Over.map q).obj U)).injective
    exact hi.symm.trans ((pointsEquiv I ((Over.map q).obj U)).apply_symm_apply x).symm
  rw [hpoint]
  simp [HomFamily.famUnits, homFamily]

/-- The family matrix condition on a subtest is exactly the pointwise formula
for the actual coordinate-normalized pullback. -/
theorem actsBy_iff_pullHom (τ : splitTorus S I ⟶ splitTorus S J)
    (q : S' ⟶ S) (m : Matrix J I ℤ) :
    HomFamily.ActsBy (Iso.refl _) (Iso.refl _) (homFamily τ) m
      (TorusConjugation.overHom (U := Over.mk (𝟙 S)) q) ↔
    ∀ (U : Over S') (x : U ⟶ (splitTorus S' I).X),
      pointsEquiv J U (x ≫ (pullHom τ q).hom.hom) =
        HomFamily.rectPow m (pointsEquiv I U x) := by
  constructor
  · intro h U x
    let a : (Over.map q).obj U ⟶ Over.mk q := Over.homMk U.hom (by simp)
    have ha := h ((Over.map q).obj U) a (pointsEquiv I U x)
    rw [units_pullHom τ q U, MulEquiv.symm_apply_apply] at ha
    exact ha
  · intro h
    apply HomFamily.actsBy_of_forall_affine (Iso.refl _) (Iso.refl _)
      (homFamily_isHomFamily τ)
    intro A s b x
    let U : Over S' := Over.mk b.left
    rw [HomFamily.famUnits_congr (Iso.refl _) (Iso.refl _) (homFamily τ)
      (b ≫ TorusConjugation.overHom (U := Over.mk (𝟙 S)) q)
      (TorusConjugation.overHom (U := Over.mk (𝟙 S)) (b.left ≫ q)) (by rfl)]
    rw [units_pullHom τ q U]
    simpa only [MulEquiv.apply_symm_apply] using h U ((pointsEquiv I U).symm x)

open Classical in
/-- The rows of a contravariant character map, in standard coordinates. -/
def weightMatrix (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) : Matrix J I ℤ :=
  fun j i => f (Pi.single j 1) i

/-- The character of a monomial map is given by its full linear weight map. -/
theorem rectPow_character {A : Type u} [CommRing A]
    (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (x : I → Aˣ) (m : J → ℤ) :
    ∏ j, HomFamily.rectPow (weightMatrix f) x j ^ m j =
      ∏ i, x i ^ f m i := by
  classical
  have hf (i : I) : f m i = ∑ j, f (Pi.single j 1) i * m j := by
    simpa only [LinearMap.toMatrix'_apply, Matrix.mulVec, dotProduct] using
      congrFun (LinearMap.toMatrix'_mulVec f m) i |>.symm
  simp only [HomFamily.rectPow, weightMatrix, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [hf]
  have hp (s : Finset J) :
      (∏ j ∈ s, x i ^ (f (Pi.single j 1) i * m j)) =
        x i ^ (∑ j ∈ s, f (Pi.single j 1) i * m j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  exact hp Finset.univ

/-- Testing the coordinate characters suffices for the entire character lattice. -/
theorem characters_iff_pullHom (τ : splitTorus S I ⟶ splitTorus S J)
    (q : S' ⟶ S) (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) :
    (∀ (U : Over S') (x : U ⟶ (splitTorus S' I).X) (m : J → ℤ),
      ∏ j, pointsEquiv J U (x ≫ (pullHom τ q).hom.hom) j ^ m j =
        ∏ i, pointsEquiv I U x i ^ f m i) ↔
    HomFamily.ActsBy (Iso.refl _) (Iso.refl _) (homFamily τ)
      (weightMatrix f) (TorusConjugation.overHom (U := Over.mk (𝟙 S)) q) := by
  classical
  rw [actsBy_iff_pullHom]
  constructor
  · intro h U x
    funext j
    simpa [Pi.single_apply, HomFamily.rectPow, weightMatrix] using h U x (Pi.single j 1)
  · intro h U x m
    rw [h U x]
    exact rectPow_character f (pointsEquiv I U x) m

/-- A supplied residue-field character map extends to an open neighbourhood
with its formula on every relative test scheme. -/
theorem exists_open_character_pullHom (τ : splitTorus S I ⟶ splitTorus S J)
    (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (x : S)
    (hx : ∀ (U : Over (Spec (S.residueField x)))
      (t : U ⟶ (splitTorus (Spec (S.residueField x)) I).X) (m : J → ℤ),
      ∏ j, pointsEquiv J U
          (t ≫ (pullHom τ (S.fromSpecResidueField x)).hom.hom) j ^ m j =
        ∏ i, pointsEquiv I U t i ^ f m i) :
    ∃ W : S.Opens, x ∈ W ∧
      ∀ (U : Over (W : Scheme)) (t : U ⟶ (splitTorus W I).X) (m : J → ℤ),
        ∏ j, pointsEquiv J U (t ≫ (pullHom τ W.ι).hom.hom) j ^ m j =
          ∏ i, pointsEquiv I U t i ^ f m i := by
  classical
  have hp : HomFamily.ActsAtPoint (Iso.refl _) (Iso.refl _) (homFamily τ)
      (weightMatrix f) x :=
    (characters_iff_pullHom τ (S.fromSpecResidueField x) f).mp hx
  have hloc := HomFamily.isLocallyConstant_actsAtPoint (Iso.refl _) (Iso.refl _)
    (homFamily_isHomFamily τ) (weightMatrix f)
  rw [IsLocallyConstant.iff_exists_open] at hloc
  obtain ⟨O, hO, hxO, hconst⟩ := hloc x
  let W : S.Opens := ⟨O, hO⟩
  refine ⟨W, hxO, (characters_iff_pullHom τ W.ι f).mpr ?_⟩
  apply HomFamily.actsBy_of_forall_actsAtPoint_on (Iso.refl _) (Iso.refl _)
    (homFamily_isHomFamily τ)
  intro y
  change HomFamily.ActsAtPoint (Iso.refl _) (Iso.refl _) (homFamily τ)
    (weightMatrix f) y.val
  rw [hconst y.val y.property]
  exact hp

end Langlands.GroupScheme.splitTorus
