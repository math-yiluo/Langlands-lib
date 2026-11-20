import Langlands.GroupScheme.Torus.OrderedProjectorScheme
import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.GeneralLinear

/-! # Diagonalizable group representations from complete matrix projectors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.OrderedProjectorScheme

variable {ι n : Type} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

section Matrix

variable {A B : Type u} [CommRing A] [CommRing B] (P : Family ι n A)

/-- Scalar multiplication by `c i` on the summand of the projector with label `i`. -/
def weightedMatrix (c : ι → A) : Matrix n n A := ∑ i, c i • P.matrix i

/-- Multiplication by a projector extracts the corresponding summand. -/
theorem weightedMatrix_mul (c : ι → A) (i : ι) :
    weightedMatrix P c * P.matrix i = c i • P.matrix i := by
  simp only [weightedMatrix, Finset.sum_mul, Matrix.smul_mul, P.mul_eq, smul_ite,
    smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Scaling by a family of scalars respects componentwise multiplication. -/
def weightedMatrixHom : (ι → A) →* Matrix n n A where
  toFun := weightedMatrix P
  map_one' := by simpa only [weightedMatrix, Pi.one_apply, one_smul] using P.sum_eq
  map_mul' c d := by
    change (∑ i, (c i * d i) • P.matrix i) = weightedMatrix P c * ∑ i, d i • P.matrix i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, weightedMatrix_mul, smul_smul, mul_comm (d i)]

/-- Unit scalars on the summands give an invertible matrix. -/
def weightedUnit : (ι → Aˣ) →* Matrix.GeneralLinearGroup n A :=
  (weightedMatrixHom P).comp (MonoidHom.pi fun i => (Units.coeHom A).comp (Pi.evalMonoidHom _ i))
    |>.toHomUnits

@[simp]
theorem weightedUnit_val (c : ι → Aˣ) :
    (weightedUnit P c : Matrix n n A) = weightedMatrix P (fun i => (c i : A)) := rfl

/-- The weighted matrix construction commutes with scalar extension. -/
theorem weightedUnit_map (f : A →+* B) (c : ι → Aˣ) :
    Matrix.GeneralLinearGroup.map f (weightedUnit P c) =
      weightedUnit (P.map f) (fun i => Units.map f.toMonoidHom (c i)) := by
  apply Units.ext
  ext a b
  change f ((weightedMatrix P (fun i => (c i : A))) a b) =
    weightedMatrix (P.map f) (fun i => (f (c i : A))) a b
  simp only [weightedMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul]
  rfl

end Matrix

section Representation

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
  (w : ι → Λ) (P : Family ι n R)

/-- The invertible universal matrix over the group algebra of the target weights. -/
def characterMatrix : Matrix.GeneralLinearGroup n (AddMonoidAlgebra R Λ) :=
  weightedUnit (P.map (algebraMap R _))
    (fun i => Diagonalizable.monomialUnits R Λ (.ofAdd (w i)))

private def characterNatTrans : Diagonalizable.functor R Λ ⟶ GeneralLinear.functor n R where
  app B := GrpCat.ofHom
    ((weightedUnit (P.map (algebraMap R B))).comp
      { toFun := fun (χ : Multiplicative Λ →* Bˣ) i => χ (.ofAdd (w i))
        map_one' := rfl
        map_mul' := fun _ _ => rfl })
  naturality B C f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    change Multiplicative Λ →* Bˣ at χ
    change weightedUnit (P.map (algebraMap R C))
      (fun i => Units.map f.hom.toRingHom.toMonoidHom (χ (.ofAdd (w i)))) =
        Matrix.GeneralLinearGroup.map f.hom.toRingHom
          (weightedUnit (P.map (algebraMap R B)) (fun i => χ (.ofAdd (w i))))
    rw [weightedUnit_map]
    have h : (P.map (algebraMap R B)).map f.hom.toRingHom = P.map (algebraMap R C) := by
      apply Family.ext
      funext i
      ext a b
      exact f.hom.commutes (P.matrix i a b)
    rw [h]

/-- The actual representation of the diagonalizable group with characters `w` on the
specified summands. -/
def representation : (Diagonalizable.groupScheme R Λ).toGrp ⟶ GeneralLinear.groupScheme n R :=
  Corepresented.groupSchemeMap (Diagonalizable.grpCorepresentation R Λ)
    (GeneralLinear.corepresentableBy n R) (characterNatTrans w P)

/-- The algebra map of the representation, given by the universal invertible matrix. -/
def coordinateMap : GeneralLinear.CoordinateRing n R →ₐ[R] AddMonoidAlgebra R Λ :=
  GeneralLinear.classify (characterMatrix w P)

/-- The representation is the spectrum of its classifying algebra map. -/
theorem representation_left :
    (representation w P).hom.hom.left = Spec.map (CommRingCat.ofHom (coordinateMap w P).toRingHom) :=
  rfl

/-- On affine points the representation is obtained by evaluating each character at the point. -/
theorem representation_affinePoints (B : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op B) ⟶ (Diagonalizable.groupScheme R Λ).X) :
    GeneralLinear.affinePointsEquiv n R B (x ≫ (representation w P).hom.hom) =
      weightedUnit (P.map (algebraMap R B))
        (fun i => (show Multiplicative Λ →* Bˣ from Corepresented.affinePointsEquiv
          (Diagonalizable.functor R Λ) (Diagonalizable.grpCorepresentation R Λ) B x)
            (.ofAdd (w i))) :=
  Corepresented.groupSchemeMap_affinePoints (Diagonalizable.grpCorepresentation R Λ)
    (GeneralLinear.corepresentableBy n R) (characterNatTrans w P) x

/-- A subalgebra containing the entries of a weighted matrix contains each of its scalars.
This uses the unit entry ideal of every projector. -/
private theorem scalar_mem_of_weightedMatrix {B : Type u} [CommRing B] [Algebra R B]
    (C : Subalgebra R B) (c : ι → B) (h : ∀ a b, weightedMatrix (P.map (algebraMap R B)) c a b ∈ C)
    (i : ι) : c i ∈ C := by
  let L := C.toSubmodule.comap (LinearMap.toSpanSingleton R B (c i))
  have hL : (entryIdeal (P.matrix i) : Submodule R R) ≤ L := by
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change P.matrix i a b • c i ∈ C
    have he := congrFun (congrFun (weightedMatrix_mul (P.map (algebraMap R B)) c i) a) b
    change (weightedMatrix (P.map (algebraMap R B)) c *
      (P.map (algebraMap R B)).matrix i) a b = c i * algebraMap R B (P.matrix i a b) at he
    rw [Algebra.smul_def, mul_comm, ← he, Matrix.mul_apply]
    exact Subalgebra.sum_mem C fun j _ => C.mul_mem (h a j) (C.algebraMap_mem (P.matrix i j b))
  have h1 : (1 : R) ∈ entryIdeal (P.matrix i) := by rw [P.entryIdeal_eq_top]; trivial
  have hmem : (1 : R) • c i ∈ C := hL h1
  simpa only [one_smul] using hmem

set_option maxHeartbeats 600000 in
/-- Generating weights give a surjective map of coordinate rings. -/
theorem coordinateMap_surjective (hw : AddSubgroup.closure (Set.range w) = ⊤) :
    Function.Surjective (coordinateMap w P) := by
  let f := coordinateMap w P
  let c (i : ι) : (AddMonoidAlgebra R Λ)ˣ := Diagonalizable.monomialUnits R Λ (.ofAdd (w i))
  have h : ∀ i, AddMonoidAlgebra.single (w i) (1 : R) ∈ f.range := by
    intro i
    apply scalar_mem_of_weightedMatrix P f.range (fun j => (c j : AddMonoidAlgebra R Λ)) _ i
    intro a b
    exact ⟨_, GeneralLinear.classify_entry (R := R) (characterMatrix w P) a b⟩
  have hInv : ∀ i, AddMonoidAlgebra.single (-w i) (1 : R) ∈ f.range := by
    intro i
    let Q := P.map (algebraMap R (AddMonoidAlgebra R Λ))
    have hi := scalar_mem_of_weightedMatrix P f.range
      (fun j => (((c j)⁻¹ : (AddMonoidAlgebra R Λ)ˣ) : AddMonoidAlgebra R Λ)) (fun a b => by
        have hinv : (characterMatrix w P)⁻¹ = weightedUnit Q c⁻¹ :=
          (map_inv (weightedUnit Q) c).symm
        change weightedUnit Q c⁻¹ a b ∈ f.range
        rw [← hinv]
        exact ⟨_, GeneralLinear.classify_inverseEntry (R := R) (characterMatrix w P) a b⟩) i
    change (↑((Diagonalizable.monomialUnits R Λ (.ofAdd (w i)))⁻¹) :
      AddMonoidAlgebra R Λ) ∈ f.range at hi
    rw [← map_inv, ← ofAdd_neg, Diagonalizable.monomialUnits_val] at hi
    exact hi
  let L : AddSubgroup Λ :=
    { carrier := {m | AddMonoidAlgebra.single m (1 : R) ∈ f.range ∧
        AddMonoidAlgebra.single (-m) (1 : R) ∈ f.range}
      zero_mem' := by
        change AddMonoidAlgebra.single (0 : Λ) (1 : R) ∈ f.range ∧
          AddMonoidAlgebra.single (- (0 : Λ)) (1 : R) ∈ f.range
        rw [neg_zero, ← AddMonoidAlgebra.one_def]
        exact ⟨f.range.one_mem, f.range.one_mem⟩
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, ?_⟩
        · simpa only [AddMonoidAlgebra.single_mul_single, one_mul] using f.range.mul_mem ha hb
        · simpa only [AddMonoidAlgebra.single_mul_single, one_mul, neg_add] using
            f.range.mul_mem ha' hb'
      neg_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨ha', by rwa [neg_neg]⟩ }
  have hL : ⊤ ≤ L := by
    rw [← hw]
    exact (AddSubgroup.closure_le L).mpr (by rintro _ ⟨i, rfl⟩; exact ⟨h i, hInv i⟩)
  intro x
  apply (AlgHom.mem_range f).mp
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => exact f.range.zero_mem
  | add a b ha hb => exact f.range.add_mem ha hb
  | single m r =>
    have hm : m ∈ L := hL (show m ∈ (⊤ : AddSubgroup Λ) from trivial)
    have hs : r • AddMonoidAlgebra.single m (1 : R) ∈ f.range := f.range.smul_mem hm.1 r
    simpa only [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one] using hs

/-- The resulting group homomorphism is closed when the weights generate the lattice. -/
theorem isClosedSubgroup_representation (hw : AddSubgroup.closure (Set.range w) = ⊤) :
    IsClosedSubgroup (representation w P) := by
  change IsClosedImmersion (representation w P).hom.hom.left
  rw [representation_left]
  exact IsClosedImmersion.spec_of_surjective _ (coordinateMap_surjective w P hw)

end Representation

end Langlands.GroupScheme.OrderedProjectorScheme
