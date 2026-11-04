import Langlands.GroupScheme.Rational.SplitTorusVectorExtension
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Additive polynomial points give actual vector-group homomorphisms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PolynomialPoint

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}

/-- Substitute a tuple into an actual polynomial point. -/
def evaluate (p : Lie.AffinePoints G (MvPolynomial (Fin n) k))
    {A : Type u} [CommRing A] [Algebra k A] (v : Fin n → A) : Lie.AffinePoints G A :=
  Lie.affineMap G (aeval v) p

/-- Additivity on the universal pair of tuples. -/
def IsAdditive (p : Lie.AffinePoints G (MvPolynomial (Fin n) k)) : Prop :=
  evaluate p (fun i => X (Sum.inl i) + X (Sum.inr i) : Fin n → MvPolynomial (Fin n ⊕ Fin n) k) =
    evaluate p (fun i => X (Sum.inl i) : Fin n → MvPolynomial (Fin n ⊕ Fin n) k) *
      evaluate p (fun i => X (Sum.inr i) : Fin n → MvPolynomial (Fin n ⊕ Fin n) k)

variable (p : Lie.AffinePoints G (MvPolynomial (Fin n) k))

/-- Substitution of an additive polynomial point preserves addition over every algebra. -/
theorem evaluate_add (hp : IsAdditive p)
    {A : Type u} [CommRing A] [Algebra k A] (v w : Fin n → A) :
    evaluate p (v + w) = evaluate p v * evaluate p w := by
  have h := congrArg (Lie.affineMap G (aeval (Sum.elim v w))) hp
  simp only [evaluate, map_mul, ← Lie.affineMap_comp, comp_aeval,
    map_add, aeval_X, Sum.elim_inl, Sum.elim_inr] at h
  exact h

/-- Additivity forces the value at the zero tuple to be the identity. -/
theorem evaluate_zero (hp : IsAdditive p)
    (A : Type u) [CommRing A] [Algebra k A] : evaluate p (0 : Fin n → A) = 1 := by
  have h := evaluate_add p hp (0 : Fin n → A) 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

/-- The affine point coordinates of a vector are the images of the polynomial variables. -/
def vectorCoordinates {A : Type u} [CommRing A] [Algebra k A]
    (v : Lie.AffinePoints (VectorGroup.groupScheme (CommRingCat.of k) n) A) : Fin n → A :=
  (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of k) n)
    (VectorGroup.corepresentableBy (CommRingCat.of k) n) (CommAlgCat.of k A) v).toAdd

/-- A vector point is the spectrum map classified by its tuple of coordinates. -/
theorem vectorPoint_eq_aeval {A : Type u} [CommRing A] [Algebra k A]
    (v : Lie.AffinePoints (VectorGroup.groupScheme (CommRingCat.of k) n) A) :
    v = (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (aeval (vectorCoordinates v))).op := by
  apply (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of k) n)
    (VectorGroup.corepresentableBy (CommRingCat.of k) n) (CommAlgCat.of k A)).injective
  rw [Corepresented.affinePointsEquiv_map]
  apply Multiplicative.toAdd.injective
  funext i
  exact (aeval_X _ _).symm

/-- Addition of vectors is pointwise addition of their affine coordinates. -/
theorem vectorCoordinates_mul {A : Type u} [CommRing A] [Algebra k A]
    (v w : Lie.AffinePoints (VectorGroup.groupScheme (CommRingCat.of k) n) A) :
    vectorCoordinates (v * w) = vectorCoordinates v + vectorCoordinates w := by
  simp only [vectorCoordinates, map_mul]
  rfl

/-- The underlying morphism of a polynomial point evaluates at vector coordinates. -/
theorem comp_polynomialPoint {A : Type u} [CommRing A] [Algebra k A]
    (v : Lie.AffinePoints (VectorGroup.groupScheme (CommRingCat.of k) n) A) :
    v ≫ p = evaluate p (vectorCoordinates v) := by
  exact congrArg (fun v => v ≫ p) (vectorPoint_eq_aeval v)

/-- Generic additivity gives multiplication preservation on every affine test. -/
theorem polynomialPoint_mul_affine (hp : IsAdditive p)
    {A : Type u} [CommRing A] [Algebra k A]
    (v w : Lie.AffinePoints (VectorGroup.groupScheme (CommRingCat.of k) n) A) :
    (v * w) ≫ p = (v ≫ p) * (w ≫ p) := by
  rw [comp_polynomialPoint, vectorCoordinates_mul, evaluate_add p hp,
    comp_polynomialPoint, comp_polynomialPoint]

/-- Multiplication preservation extends to all relative scheme tests. -/
theorem polynomialPoint_mul (hp : IsAdditive p)
    {T : Over (Spec (CommRingCat.of k))}
    (v w : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) :
    (v * w) ≫ p = (v ≫ p) * (w ≫ p) := by
  change (VectorGroup.groupScheme (CommRingCat.of k) n).X ⟶ G.X at p
  let V := (VectorGroup.groupScheme (CommRingCat.of k) n).X
  change T ⟶ V at v w
  change V ⟶ G.X at p
  have : IsAffine V.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) k))))
  have : IsAffineHom V.hom := isAffineHom_of_isAffine V.hom
  have hu : (fst V V * snd V V) ≫ p = (fst V V ≫ p) * (snd V V ≫ p) := by
    apply PointedCoordinateWeights.affine_hom_ext
    intro A _ _ x
    simp only [← Category.assoc, MonObj.comp_mul, polynomialPoint_mul_affine p hp]
  have hvw : v * w = lift v w ≫ (fst V V * snd V V) := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [hvw, Category.assoc, hu, MonObj.comp_mul]
  simp only [← Category.assoc, lift_fst, lift_snd]

/-- The actual vector-group homomorphism associated to an additive polynomial point. -/
def homOfAdditive (hp : IsAdditive p) : VectorGroup.groupScheme (CommRingCat.of k) n ⟶ G :=
  homOfPoints (fun _ => MonoidHom.mk' (· ≫ p) (polynomialPoint_mul p hp))
    (fun _ _ => by simp only [MonoidHom.mk'_apply, Category.assoc])

/-- The construction recovers the original polynomial morphism on every scheme test. -/
theorem comp_homOfAdditive (hp : IsAdditive p)
    {T : Over (Spec (CommRingCat.of k))}
    (v : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) :
    v ≫ (homOfAdditive p hp).hom.hom = v ≫ p := by
  rw [homOfAdditive, comp_homOfPoints, MonoidHom.mk'_apply]
  intro _ _ _ _
  simp only [MonoidHom.mk'_apply, Category.assoc]

/-- The underlying scheme morphism is the original polynomial point. -/
theorem homOfAdditive_hom (hp : IsAdditive p) : (homOfAdditive p hp).hom.hom = p := by
  simpa only [Category.id_comp] using comp_homOfAdditive p hp (𝟙 _)

end Langlands.GroupScheme.PolynomialPoint
