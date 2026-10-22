import Langlands.Cohomology.Tate.TensorShifts
import Langlands.Cohomology.Tate.TransferDefinitions
import Mathlib.Algebra.Ring.NegOnePow

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The actual equivariant tensor pairing of two representations. -/
def tensorPairing (A B : Rep.{u} R G) : Pairing A B (A ⊗ B) where
  bilinear := TensorProduct.mk R A B
  equivariant _g a b := (TensorProduct.map_tmul _ _ a b).symm

/-- Transport in the integer degree of actual Tate cohomology. -/
def tateDegreeIso (A : Rep.{u} R G) {m n : ℤ} (h : m = n) :
    tateCohomology A m ≅ tateCohomology A n :=
  eqToIso (congrArg (tateCohomology A) h)

/-- The first tensor shift, with both degrees written using negative natural numbers. -/
def tensorShiftDownLeftNegativeIso (A B : Rep.{u} R G) (n : ℕ) :
    tateCohomology (A ⊗ B) (-(n + 1 : ℤ)) ≅
      tateCohomology (shiftDown A ⊗ B) (-(n : ℤ)) :=
  tensorShiftDownLeftIso A B (-(n + 1 : ℤ)) ≪≫ tateDegreeIso _ (by omega)

/-- Normalized tensor products with second degree zero and first degree nonnegative. -/
def tensorCupFirstNonneg : (p : ℕ) → (A B : Rep.{u} R G) →
    tateCohomology A p →ₗ[R] tateCohomology B 0 →ₗ[R] tateCohomology (A ⊗ B) p
  | 0, A, B => cupZero (tensorPairing A B)
  | p + 1, A, B =>
      ((tensorCupFirstNonneg p (shiftUp A) B).compl₁₂
        (shiftUpIso A p).symm.toLinearEquiv.toLinearMap LinearMap.id).compr₂
        (tensorShiftUpLeftIso A B p).toLinearEquiv.toLinearMap

/-- Normalized tensor products with second degree zero and first degree nonpositive. -/
def tensorCupFirstNonpos : (p : ℕ) → (A B : Rep.{u} R G) →
    tateCohomology A (-(p : ℤ)) →ₗ[R] tateCohomology B 0 →ₗ[R]
      tateCohomology (A ⊗ B) (-(p : ℤ))
  | 0, A, B => cupZero (tensorPairing A B)
  | p + 1, A, B =>
      ((tensorCupFirstNonpos p (shiftDown A) B).compl₁₂
        (shiftDownNegativeIso A p).toLinearEquiv.toLinearMap LinearMap.id).compr₂
        (tensorShiftDownLeftNegativeIso A B p).symm.toLinearEquiv.toLinearMap

/-- Tensor product with second degree zero, defined using actual connecting isomorphisms. -/
def tensorCupFirst (A B : Rep.{u} R G) : (p : ℤ) →
    tateCohomology A p →ₗ[R] tateCohomology B 0 →ₗ[R] tateCohomology (A ⊗ B) p
  | .ofNat p => tensorCupFirstNonneg p A B
  | .negSucc p => tensorCupFirstNonpos (p + 1) A B

/-- Tensor products with second degree nonnegative, including the second-boundary sign. -/
def tensorCupSecondNonneg (p : ℤ) : (q : ℕ) → (A B : Rep.{u} R G) →
    tateCohomology A p →ₗ[R] tateCohomology B q →ₗ[R]
      tateCohomology (A ⊗ B) (p + q)
  | 0, A, B =>
      (tensorCupFirst A B p).compr₂ (tateDegreeIso _ (by omega)).toLinearEquiv.toLinearMap
  | q + 1, A, B =>
      (p.negOnePow : ℤ) •
        (((tensorCupSecondNonneg p q A (shiftUp B)).compl₁₂ LinearMap.id
          (shiftUpIso B q).symm.toLinearEquiv.toLinearMap).compr₂
          (tensorShiftUpRightIso A B (p + q) ≪≫
            tateDegreeIso _ (by push_cast; omega)).toLinearEquiv.toLinearMap)

/-- Tensor products with second degree nonpositive, using the inverse tensor connecting map. -/
def tensorCupSecondNonpos (p : ℤ) : (q : ℕ) → (A B : Rep.{u} R G) →
    tateCohomology A p →ₗ[R] tateCohomology B (-(q : ℤ)) →ₗ[R]
      tateCohomology (A ⊗ B) (p + -(q : ℤ))
  | 0, A, B =>
      (tensorCupFirst A B p).compr₂ (tateDegreeIso _ (by omega)).toLinearEquiv.toLinearMap
  | q + 1, A, B =>
      (p.negOnePow : ℤ) •
        (((tensorCupSecondNonpos p q A (shiftDown B)).compl₁₂ LinearMap.id
          (shiftDownNegativeIso B q).toLinearEquiv.toLinearMap).compr₂
          (tateDegreeIso _ (show p + -(q : ℤ) = (p + -((q + 1 : ℕ) : ℤ)) + 1
              by push_cast; omega) ≪≫
            (tensorShiftDownRightIso A B (p + -((q + 1 : ℕ) : ℤ))).symm
            ).toLinearEquiv.toLinearMap)

/-- The bilinear tensor product family obtained from normalized scalar-split dimension shifting. -/
def tensorCup (A B : Rep.{u} R G) (p : ℤ) : (q : ℤ) →
    tateCohomology A p →ₗ[R] tateCohomology B q →ₗ[R]
      tateCohomology (A ⊗ B) (p + q)
  | .ofNat q => tensorCupSecondNonneg p q A B
  | .negSucc q => tensorCupSecondNonpos p (q + 1) A B

/-- An actual equivariant bilinear pairing induces a morphism from the tensor representation. -/
def Pairing.tensorHom {A B C : Rep.{u} R G} (φ : Pairing A B C) : A ⊗ B ⟶ C :=
  Rep.ofHom ⟨TensorProduct.lift φ.bilinear, fun g => by
    apply TensorProduct.ext'
    intro a b
    exact φ.equivariant g a b⟩

/-- Compose the tensor family with an equivariant coefficient pairing. -/
def cup {A B C : Rep.{u} R G} (φ : Pairing A B C) (p q : ℤ) :
    tateCohomology A p →ₗ[R] tateCohomology B q →ₗ[R] tateCohomology C (p + q) :=
  (tensorCup A B p q).compr₂ ((tateCohomologyFunctor (p + q)).map φ.tensorHom).hom

/-- Scalar multiplication paired with the actual trivial scalar representation. -/
def scalarPairing (A : Rep.{u} R G) : Pairing A (Rep.trivial R G R) A where
  bilinear := (LinearMap.lsmul R A).flip
  equivariant g a r := (map_smul (A.ρ g) r a).symm

/-- The ordinary degree-two class acts on Tate cohomology of the trivial scalar module. -/
def scalarH2Cup (A : Rep.{u} R G) (n : ℤ) :
    groupCohomology A 2 →ₗ[R]
      tateCohomology (Rep.trivial R G R) n →ₗ[R]
        tateCohomology A (n + 2) :=
  ((cup (scalarPairing A) 2 n).comp
    ((TateCohomology.isoGroupCohomology 2).app A).symm.toLinearEquiv.toLinearMap).compr₂
      (tateDegreeIso A (add_comm 2 n)).toLinearEquiv.toLinearMap

/-- The integral specialization uses the actual lifted integer ring and its trivial module. -/
abbrev integralH2Cup (A : Rep.{u} IntegralScalar.{u} G) (n : ℤ) :=
  scalarH2Cup A n

end Langlands.Tate
