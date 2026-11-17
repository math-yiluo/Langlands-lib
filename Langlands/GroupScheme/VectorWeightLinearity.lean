import Langlands.GroupScheme.Reductive.LocalRootParametrizationRigidity
import Langlands.GroupScheme.VectorMatrixMap
import Langlands.GroupScheme.CorepresentedComultiplication

/-! # Positive scalar weights force linear vector-group maps over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.VectorGroup

variable {R : CommRingCat.{u}} {n m : ℕ}

/-- An additive point transformation, without type tags. -/
def additiveApp (f : functor R n ⟶ functor R m) (A : CommAlgCat.{u} R) :
    (Fin n → A) →+ (Fin m → A) where
  toFun x := Multiplicative.toAdd (α := Fin m → A) (f.app A (Multiplicative.ofAdd x))
  map_zero' := by
    change Multiplicative.toAdd (α := Fin m → A) (f.app A 1) = 0
    rw [map_one]
    rfl
  map_add' x y := by
    change Multiplicative.toAdd (α := Fin m → A)
      (f.app A (Multiplicative.ofAdd x * Multiplicative.ofAdd y)) = _
    rw [map_mul]
    rfl

/-- Commutation with a common positive-power scalar action on every algebra test. -/
def HasScalarWeight (f : functor R n ⟶ functor R m) (d : ℕ) : Prop :=
  ∀ (A : CommAlgCat.{u} R) (t : Aˣ) (x : Fin n → A),
    additiveApp f A ((t : A) ^ d • x) = (t : A) ^ d • additiveApp f A x

/-- One input coordinate line and one output coordinate give a natural scalar operation. -/
def coordinateLineOperation (f : functor R n ⟶ functor R m) (i : Fin m) (j : Fin n) :
    NaturalLine.Operation R where
  app A a := additiveApp f A (Pi.single j a) i
  naturality {A B} g a := by
    have h := ConcreteCategory.congr_hom (f.naturality g)
      (Multiplicative.ofAdd (Pi.single j a))
    change f.app B ((functor R n).map g (Multiplicative.ofAdd (Pi.single j a))) =
      (functor R m).map g (f.app A (Multiplicative.ofAdd (Pi.single j a))) at h
    have hs : (functor R n).map g (Multiplicative.ofAdd (Pi.single j a)) =
        Multiplicative.ofAdd (Pi.single j (g.hom a)) := by
      apply Multiplicative.toAdd.injective
      funext l
      change g.hom ((Pi.single j a : Fin n → A) l) =
        (Pi.single j (g.hom a) : Fin n → B) l
      by_cases hlj : l = j <;> simp [hlj]
    rw [hs] at h
    exact congrArg (fun x : Multiplicative (Fin m → B) => x.toAdd i) h

/-- The rectangular matrix obtained by evaluating the input coordinate vectors over the base. -/
def weightMatrix (f : functor R n ⟶ functor R m) : Matrix (Fin m) (Fin n) R :=
  fun i j => (coordinateLineOperation f i j).app (CommAlgCat.of R R) 1

/-- The scalar operation on each coordinate line satisfies the existing Laurent rigidity lemma. -/
theorem coordinateLineOperation_eq_mul {f : functor R n ⟶ functor R m} {d : ℕ}
    (hd : 0 < d) (hf : HasScalarWeight f d) (i : Fin m) (j : Fin n)
    (A : CommAlgCat.{u} R) (a : A) :
    (coordinateLineOperation f i j).app A a = algebraMap R A (weightMatrix f i j) * a := by
  apply NaturalLine.Operation.eq_mul_of_laurent hd
  let L : CommAlgCat.{u} R := CommAlgCat.of R (LaurentPolynomial R)
  have hs := hf L (LaurentPolynomial.isUnit_T (R := R) 1).unit (Pi.single j 1)
  have hs' : (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial R) ^ d •
      (Pi.single j 1 : Fin n → LaurentPolynomial R) =
      Pi.single j (LaurentPolynomial.T (d : ℤ)) := by
    ext l
    simp [Pi.single_apply, LaurentPolynomial.T_pow, apply_ite]
  rw [IsUnit.unit_spec, hs'] at hs
  have hnat := (coordinateLineOperation f i j).naturality
    (CommAlgCat.ofHom (Algebra.ofId R (LaurentPolynomial R))) 1
  have hone : (coordinateLineOperation f i j).app L 1 =
      LaurentPolynomial.C (weightMatrix f i j) := by
    simpa [weightMatrix, LaurentPolynomial.algebraMap_apply] using hnat
  change (additiveApp f L (Pi.single j (LaurentPolynomial.T (d : ℤ)))) i =
    LaurentPolynomial.T (d : ℤ) * LaurentPolynomial.C _
  have hi := congrFun hs i
  change (additiveApp f L (Pi.single j (LaurentPolynomial.T (d : ℤ)))) i = _ at hi
  rw [Pi.smul_apply, smul_eq_mul, LaurentPolynomial.T_pow] at hi
  simp only [mul_one] at hi
  exact hi.trans (congrArg (fun z => LaurentPolynomial.T (d : ℤ) * z) hone)

/-- Every coefficient-algebra map is given by the same base-ring matrix. -/
theorem additiveApp_eq_weightMatrix {f : functor R n ⟶ functor R m} {d : ℕ}
    (hd : 0 < d) (hf : HasScalarWeight f d) (A : CommAlgCat.{u} R) (x : Fin n → A) :
    additiveApp f A x = (weightMatrix f).map (algebraMap R A) *ᵥ x := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  funext i
  rw [Finset.sum_apply]
  change (∑ j, (coordinateLineOperation f i j).app A (x j)) =
    ∑ j, algebraMap R A (weightMatrix f i j) * x j
  exact Finset.sum_congr rfl fun j _ => coordinateLineOperation_eq_mul hd hf i j A (x j)

/-- The actual linear map on each coefficient algebra induced by the natural transformation. -/
def linearAppOfWeight (f : functor R n ⟶ functor R m) {d : ℕ}
    (hd : 0 < d) (hf : HasScalarWeight f d) (A : CommAlgCat.{u} R) :
    (Fin n → A) →ₗ[A] (Fin m → A) :=
  { additiveApp f A with
    map_smul' a x := by
      change additiveApp f A (a • x) = a • additiveApp f A x
      rw [additiveApp_eq_weightMatrix hd hf, additiveApp_eq_weightMatrix hd hf,
        Matrix.mulVec_smul] }

@[simp]
theorem linearAppOfWeight_apply (f : functor R n ⟶ functor R m) {d : ℕ}
    (hd : 0 < d) (hf : HasScalarWeight f d) (A : CommAlgCat.{u} R) (x : Fin n → A) :
    linearAppOfWeight f hd hf A x =
      Multiplicative.toAdd (α := Fin m → A) (f.app A (Multiplicative.ofAdd x)) := rfl

/-- A natural isomorphism of vector groups with a common positive scalar weight gives
an actual linear equivalence on each coefficient algebra. Only the forward weight is needed. -/
def linearEquivAppOfWeight (e : functor R n ≅ functor R m) {d : ℕ}
    (hd : 0 < d) (he : HasScalarWeight e.hom d) (A : CommAlgCat.{u} R) :
    (Fin n → A) ≃ₗ[A] (Fin m → A) :=
  { linearAppOfWeight e.hom hd he A with
    invFun := additiveApp e.inv A
    left_inv := fun x => by
      have h := congrArg (fun f : functor R n ⟶ functor R n => additiveApp f A x)
        e.hom_inv_id
      exact h
    right_inv := fun x => by
      have h := congrArg (fun f : functor R m ⟶ functor R m => additiveApp f A x)
        e.inv_hom_id
      exact h }

@[simp]
theorem linearEquivAppOfWeight_apply (e : functor R n ≅ functor R m) {d : ℕ}
    (hd : 0 < d) (he : HasScalarWeight e.hom d) (A : CommAlgCat.{u} R) (x : Fin n → A) :
    linearEquivAppOfWeight e hd he A x = additiveApp e.hom A x := rfl

/-- The map induced on actual vector group schemes is the matrix homomorphism on every test. -/
theorem groupSchemeMap_eq_matrixHom {f : functor R n ⟶ functor R m} {d : ℕ}
    (hd : 0 < d) (hf : HasScalarWeight f d) :
    Corepresented.groupSchemeMap (corepresentableBy R n) (corepresentableBy R m) f =
      matrixHom (weightMatrix f) := by
  apply hom_ext_points
  intro T x
  apply (coordinates R m T).injective
  apply Multiplicative.toAdd.injective
  rw [coordinates_matrixHom]
  change (Corepresented.pointsEquiv (functor R m) (corepresentableBy R m) T
    (x ≫ (Corepresented.groupSchemeMap (corepresentableBy R n)
      (corepresentableBy R m) f).hom.hom)).toAdd = _
  rw [Corepresented.groupSchemeMap_points]
  exact additiveApp_eq_weightMatrix hd hf ((algΓ R).obj T).unop
    (coordinates R n T x).toAdd

/-- The point transformation of an actual morphism of polynomial vector groups. -/
abbrev pointTransformation (φ : groupScheme R n ⟶ groupScheme R m) :
    functor R n ⟶ functor R m :=
  Corepresented.pointsTrans (corepresentableBy R n) (corepresentableBy R m) φ

/-- An actual common-weight group-scheme morphism has one coefficient matrix over the base. -/
theorem eq_matrixHom_of_hasScalarWeight (φ : groupScheme R n ⟶ groupScheme R m)
    {d : ℕ} (hd : 0 < d) (hφ : HasScalarWeight (pointTransformation φ) d) :
    φ = matrixHom (weightMatrix (pointTransformation φ)) := by
  exact (Corepresented.groupSchemeMap_pointsTrans (corepresentableBy R n)
    (corepresentableBy R m) φ).symm.trans (groupSchemeMap_eq_matrixHom hd hφ)

/-- The same matrix gives the morphism on every scheme test. -/
theorem coordinates_of_hasScalarWeight (φ : groupScheme R n ⟶ groupScheme R m)
    {d : ℕ} (hd : 0 < d) (hφ : HasScalarWeight (pointTransformation φ) d)
    (T : Over (Spec R)) (x : T ⟶ (groupScheme R n).X) :
    (coordinates R m T (x ≫ φ.hom.hom)).toAdd =
      (weightMatrix (pointTransformation φ)).map (scalarMap T) *ᵥ
        (coordinates R n T x).toAdd := by
  conv_lhs => rw [eq_matrixHom_of_hasScalarWeight φ hd hφ]
  exact coordinates_matrixHom _ _ _

/-- The actual linear map on a coefficient algebra extracted from a group-scheme morphism. -/
def linearMapOfWeight (φ : groupScheme R n ⟶ groupScheme R m) {d : ℕ}
    (hd : 0 < d) (hφ : HasScalarWeight (pointTransformation φ) d)
    (A : CommAlgCat.{u} R) : (Fin n → A) →ₗ[A] (Fin m → A) :=
  linearAppOfWeight (pointTransformation φ) hd hφ A

/-- Read an actual vector-group isomorphism as a natural isomorphism on coefficient algebras. -/
def pointTransformationIso (e : groupScheme R n ≅ groupScheme R m) :
    functor R n ≅ functor R m where
  hom := pointTransformation e.hom
  inv := pointTransformation e.inv
  hom_inv_id := by
    ext A x
    change (pointTransformation e.inv).app A ((pointTransformation e.hom).app A x) = x
    rw [pointTransformation, Corepresented.pointsTrans_app,
      pointTransformation, Corepresented.pointsTrans_app, MulEquiv.symm_apply_apply]
    rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id]
    simp
  inv_hom_id := by
    ext A x
    change (pointTransformation e.hom).app A ((pointTransformation e.inv).app A x) = x
    rw [pointTransformation, Corepresented.pointsTrans_app,
      pointTransformation, Corepresented.pointsTrans_app, MulEquiv.symm_apply_apply]
    rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id]
    simp

/-- A common positive scalar weight makes an actual vector-group isomorphism linear
over each coefficient algebra, without requiring equal ranks in the input. -/
def linearEquivOfWeight (e : groupScheme R n ≅ groupScheme R m) {d : ℕ}
    (hd : 0 < d) (he : HasScalarWeight (pointTransformation e.hom) d)
    (A : CommAlgCat.{u} R) : (Fin n → A) ≃ₗ[A] (Fin m → A) :=
  linearEquivAppOfWeight (pointTransformationIso e) hd he A

end Langlands.GroupScheme.VectorGroup
