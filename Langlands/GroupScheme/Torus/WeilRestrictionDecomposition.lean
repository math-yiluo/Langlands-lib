import Langlands.GroupScheme.Torus.WeilRestrictionCommutative
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Splitting Weil restriction from an algebra decomposition -/

set_option maxRecDepth 4000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

section Algebra

variable (A A' B R : Type u) [CommRing A] [CommRing A'] [CommRing B] [CommRing R]
  [Algebra A A'] [Algebra A B] [Algebra A' R] [Algebra A R] [IsScalarTower A A' R]
  (I : Type u) [Finite I] (e : A' ⊗[A] B ≃ₐ[A'] (I → A'))

/-- The tensor decomposition on an algebra over the new base. -/
def decompositionTensorEquiv : B ⊗[A] R ≃+* (I → R) :=
  (baseChangeTensorEquiv A A' B R).trans
    ((Algebra.TensorProduct.congr e (AlgEquiv.refl (R := A') (A₁ := R))).toRingEquiv.trans
      (piTensorEquiv (CommRingCat.of A') I R).toRingEquiv)

@[simp] theorem decompositionTensorEquiv_tmul (b : B) (r : R) :
    decompositionTensorEquiv A A' B R I e (b ⊗ₜ r) =
      fun i => e ((1 : A') ⊗ₜ b) i • r := by
  simp [decompositionTensorEquiv]
  rfl

end Algebra

section Scheme

variable (A A' : CommRingCat.{u}) [Algebra A A'] (B : Type u) [CommRing B]
  [Algebra A B] [Module.Finite A B] [Module.Projective A B]
  (I : Type u) [Finite I] (e : A' ⊗[A] B ≃ₐ[A'] (I → A'))

/-- An algebra decomposition gives the actual splitting of the base-changed group. -/
def decompositionIso :
    (GroupScheme.baseChange (baseMap A A')).obj (groupScheme A B) ≅
      splitTorus (Spec A') I :=
  algebraBaseChangeIso A A' B ≪≫ congrIso e ≪≫ splitIso A' I

/-- The same splitting in the commutative category. -/
def commDecompositionIso :
    (CommGroupScheme.baseChange (baseMap A A')).obj (commGroupScheme A B) ≅
      splitTorus.commGroupScheme (Spec A') I :=
  commAlgebraBaseChangeIso A B A' ≪≫ commCongrIso e ≪≫ commSplitIso A' I

/-- The splitting model on all test schemes. -/
def decompositionPointsEquiv (T : Over (Spec A')) :
    (T ⟶ ((CommGroupScheme.baseChange (baseMap A A')).obj (commGroupScheme A B)).X) ≃*
      (I → (Γ(T.left, ⊤))ˣ) :=
  (basePointsEquiv A A' B T).trans
    ((tensorUnitsEquiv e ((algΓ A').obj T).unop).trans
      ((Units.mapEquiv (piTensorEquiv A' I ((algΓ A').obj T).unop).toMulEquiv).trans
        MulEquiv.piUnits))

/-- On points, the splitting applies the algebra decomposition to the tensor units. -/
theorem commDecompositionIso_hom_points (T : Over (Spec A'))
    (x : T ⟶ ((CommGroupScheme.baseChange (baseMap A A')).obj (commGroupScheme A B)).X) :
    splitTorus.pointsEquiv I T
        (x ≫ (CommGroupScheme.groupHom (commDecompositionIso A A' B I e).hom).hom.hom) =
      decompositionPointsEquiv A A' B I e T x := by
  simp only [commDecompositionIso, Iso.trans_hom, comp_groupHom_comp]
  rw [comp_groupHom_comp
    (x ≫ (CommGroupScheme.groupHom (commAlgebraBaseChangeIso A B A').hom).hom.hom)
    (commCongrIso e).hom (commSplitIso A' I).hom]
  rw [commSplitIso_hom_points]
  change MulEquiv.piUnits (Units.map (piTensorEquiv A' I ((algΓ A').obj T).unop).toMonoidHom
    (commPointsEquiv A' (I → A') T
      ((x ≫ (CommGroupScheme.groupHom (commAlgebraBaseChangeIso A B A').hom).hom.hom) ≫
        (CommGroupScheme.groupHom (commCongrIso e).hom).hom.hom))) = _
  rw [commCongrIso_hom_points, commAlgebraBaseChangeIso_hom_points]
  rfl

/-- The decomposition is natural for all maps of test schemes. -/
theorem decompositionPointsEquiv_naturality {T T' : Over (Spec A')} (a : T' ⟶ T)
    (x : T ⟶ ((CommGroupScheme.baseChange (baseMap A A')).obj (commGroupScheme A B)).X) :
    decompositionPointsEquiv A A' B I e T' (a ≫ x) =
      splitTorus.unitsRestrict I a (decompositionPointsEquiv A A' B I e T x) := by
  rw [← commDecompositionIso_hom_points, Category.assoc,
    splitTorus.pointsEquiv_naturality, commDecompositionIso_hom_points]

end Scheme

section Lattices

variable (A : CommRingCat.{u}) (K : Type u) [Field K] [Algebra A K]
  (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Projective A B]
  (I : Type u) [Finite I] (e : K ⊗[A] B ≃ₐ[K] (I → K))

local notation "T_K" =>
  (Functor.obj (CommGroupScheme.baseChange (baseMap A (CommRingCat.of K)))
    (commGroupScheme A B))

/-- Characters in the coordinates supplied by the algebra decomposition. -/
def decompositionCharacterEquiv : characterLattice T_K ≃+ (I → ℤ) :=
  (characterLattice.congr (commDecompositionIso A (CommRingCat.of K) B I e)).trans
    (splitTorus.characterLatticeEquiv K I)

/-- Cocharacters in the same coordinates. -/
def decompositionCocharacterEquiv : cocharacterLattice T_K ≃+ (I → ℤ) :=
  (cocharacterLattice.congr (commDecompositionIso A (CommRingCat.of K) B I e)).trans
    (splitTorus.cocharacterLatticeEquiv K I)

theorem decompositionCharacterEquiv_symm_eq (m : I → ℤ) :
    (decompositionCharacterEquiv A K B I e).symm m =
      (commDecompositionIso A (CommRingCat.of K) B I e).hom ≫
        (splitTorus.characterLatticeEquiv K I).symm m := rfl

theorem decompositionCocharacterEquiv_symm_eq (m : I → ℤ) :
    (decompositionCocharacterEquiv A K B I e).symm m =
      (splitTorus.cocharacterLatticeEquiv K I).symm m ≫
        (commDecompositionIso A (CommRingCat.of K) B I e).inv := rfl

/-- A character is the monomial in the decomposition coordinates. -/
theorem decompositionCharacterEquiv_symm_points [Fintype I] (m : I → ℤ)
    (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (T_K).X) :
    Gm.pointsEquiv _ T
        (x ≫ (CommGroupScheme.groupHom ((decompositionCharacterEquiv A K B I e).symm m)).hom.hom) =
      ∏ i, decompositionPointsEquiv A (CommRingCat.of K) B I e T x i ^ m i := by
  rw [decompositionCharacterEquiv_symm_eq, comp_groupHom_comp,
    splitTorus.pointsEquiv_characterLatticeEquiv_symm, commDecompositionIso_hom_points]

/-- A cocharacter raises the parameter to the specified power in every coordinate. -/
theorem decompositionCocharacterEquiv_symm_points (m : I → ℤ)
    (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (Gm (Spec (CommRingCat.of K))).X) :
    decompositionPointsEquiv A (CommRingCat.of K) B I e T
        (x ≫ (CommGroupScheme.groupHom ((decompositionCocharacterEquiv A K B I e).symm m)).hom.hom) =
      fun i => Gm.pointsEquiv _ T x ^ m i := by
  rw [← commDecompositionIso_hom_points, ← comp_groupHom_comp,
    decompositionCocharacterEquiv_symm_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    splitTorus.pointsEquiv_cocharacterLatticeEquiv_symm]

/-- In these coordinates the pairing is the standard dot product. -/
theorem decomposition_latticePairing_eq_sum [Fintype I]
    (χ : characterLattice T_K) (ν : cocharacterLattice T_K) :
    latticePairing T_K χ ν =
      ∑ i, decompositionCharacterEquiv A K B I e χ i *
        decompositionCocharacterEquiv A K B I e ν i := by
  rw [← latticePairing_congr (commDecompositionIso A (CommRingCat.of K) B I e) χ ν,
    splitTorus.latticePairing_eq_sum]
  rfl

include I e in
/-- The splitting makes the actual character/cocharacter pairing perfect. -/
theorem decomposition_latticePairing_isPerfPair : (latticePairing T_K).IsPerfPair := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  have : (dotProductEquiv ℤ I : (I → ℤ) →ₗ[ℤ] Module.Dual ℤ (I → ℤ)).IsPerfPair :=
    LinearMap.IsPerfPair.of_bijective _ (dotProductEquiv ℤ I).bijective
  refine LinearMap.IsPerfPair.congr
    (decompositionCharacterEquiv A K B I e).toIntLinearEquiv
    (decompositionCocharacterEquiv A K B I e).toIntLinearEquiv (latticePairing T_K)
    (p := (dotProductEquiv ℤ I : (I → ℤ) →ₗ[ℤ] Module.Dual ℤ (I → ℤ))) ?_
  refine LinearMap.ext fun m => LinearMap.ext fun n => ?_
  change latticePairing T_K ((decompositionCharacterEquiv A K B I e).symm m)
    ((decompositionCocharacterEquiv A K B I e).symm n) = dotProduct m n
  rw [decomposition_latticePairing_eq_sum A K B I e, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  rfl

end Lattices

end Langlands.GroupScheme.WeilGm
