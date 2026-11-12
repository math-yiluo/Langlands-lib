import Langlands.GroupScheme.CentralSimpleNormOne

/-!
# Transport of reduced-norm-one groups under algebra isomorphisms

An algebra isomorphism preserves the unconditional reduced norm on every
commutative coefficient algebra. This gives an actual isomorphism of the
reduced-norm-one group schemes.
-/

noncomputable section

universe u v w

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.CentralSimple

variable {K A B : Type u} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]

/-- An algebra isomorphism preserves the reduced degree. -/
theorem reducedDegree_algEquiv (e : A ≃ₐ[K] B) : reducedDegree K A = reducedDegree K B := by
  exact congrArg Nat.sqrt e.toLinearEquiv.finrank_eq

variable [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K B] [Algebra.IsCentral K B] [IsSimpleRing B]

/-- The reduced norm coordinate polynomial is unchanged in the transported basis. -/
theorem reducedNormPolynomial_algEquiv {J : Type v} [Fintype J]
    (e : A ≃ₐ[K] B) (b : Module.Basis J K A) :
    reducedNormPolynomial K B (b.map e.toLinearEquiv) = reducedNormPolynomial K A b := by
  let L := finiteGaloisSplittingField K B
  let f := finiteGaloisSplittingChart K B
  let q := finCongr (reducedDegree_algEquiv e).symm
  let g : L ⊗[K] A ≃ₐ[L]
      Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e).trans f).trans
      (Matrix.reindexAlgEquiv L L q)
  apply MvPolynomial.map_injective (algebraMap K L)
    (FaithfulSMul.algebraMap_injective K L)
  rw [reducedNormPolynomial_map_chart K B (b.map e.toLinearEquiv) f,
    reducedNormPolynomial_map_chart K A b g]
  change (Langlands.ReducedNorm.genericMatrix
      (fun j => f (1 ⊗ₜ[K] (b.map e.toLinearEquiv) j))).det =
    (Langlands.ReducedNorm.genericMatrix (fun j => g (1 ⊗ₜ[K] b j))).det
  have hm : Langlands.ReducedNorm.genericMatrix (fun j => g (1 ⊗ₜ[K] b j)) =
      Matrix.reindex q q (Langlands.ReducedNorm.genericMatrix
        (fun j => f (1 ⊗ₜ[K] (b.map e.toLinearEquiv) j))) := by
    ext i j
    simp [Langlands.ReducedNorm.genericMatrix, g, Matrix.reindex_apply]
  rw [hm, Matrix.det_reindex_self]

/-- Algebra isomorphisms preserve the reduced norm on every coefficient algebra. -/
theorem reducedNorm_algEquiv (e : A ≃ₐ[K] B)
    (R : Type w) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    reducedNorm K B R (Algebra.TensorProduct.map (AlgHom.id R R) e.toAlgHom x) =
      reducedNorm K A R x := by
  let b := Module.finBasis K A
  rw [reducedNorm_eq_polynomialValue K B (b.map e.toLinearEquiv),
    reducedNormPolynomial_algEquiv e b, reducedNorm_eq_polynomialValue K A b]
  unfold Langlands.ReducedNorm.polynomialValue
  congr 1
  ext j
  induction x using TensorProduct.inductionOn with
  | tmul r a => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- Algebra isomorphisms preserve the reduced norm on tensor units. -/
theorem reducedNormUnits_algEquiv (e : A ≃ₐ[K] B)
    (R : Type w) [CommRing R] [Algebra K R] (x : (R ⊗[K] A)ˣ) :
    reducedNormUnits K B R (Units.map
        (Algebra.TensorProduct.map (AlgHom.id R R) e.toAlgHom).toMonoidHom x) =
      reducedNormUnits K A R x := by
  apply Units.ext
  exact reducedNorm_algEquiv e R x.val

/-- Tensoring an algebra isomorphism gives an isomorphism of the actual norm-one units. -/
def reducedNormOneAlgEquiv (e : A ≃ₐ[K] B)
    (R : Type w) [CommRing R] [Algebra K R] :
    reducedNormOne K A R ≃* reducedNormOne K B R where
  toFun x := ⟨Units.mapEquiv
      (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).toMulEquiv x.val, by
    change reducedNormUnits K B R (Units.map
      (Algebra.TensorProduct.map (AlgHom.id R R) e.toAlgHom).toMonoidHom x.val) = 1
    exact (reducedNormUnits_algEquiv e R x.val).trans x.property⟩
  invFun y := ⟨(Units.mapEquiv
      (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).toMulEquiv).symm y.val, by
    change reducedNormUnits K A R
      ((Units.mapEquiv
        (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).toMulEquiv).symm y.val) = 1
    rw [← reducedNormUnits_algEquiv e R]
    change reducedNormUnits K B R
      ((Units.mapEquiv
        (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).toMulEquiv)
        ((Units.mapEquiv
          (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).toMulEquiv).symm
            y.val)) = 1
    rw [MulEquiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext ((Units.mapEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).toMulEquiv).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((Units.mapEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).toMulEquiv).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

@[simp] theorem reducedNormOneAlgEquiv_val (e : A ≃ₐ[K] B)
    (R : Type w) [CommRing R] [Algebra K R] (x : reducedNormOne K A R) :
    (reducedNormOneAlgEquiv e R x).val = Units.map
      (Algebra.TensorProduct.map (AlgHom.id R R) e.toAlgHom).toMonoidHom x.val := rfl

end Langlands.CentralSimple

namespace Langlands.GroupScheme

/-- Natural point equivalences are represented with their forward and inverse formulas. -/
theorem exists_isoOfPoints_with_formulas {S : Scheme.{u}} {G H : GroupScheme S}
    (e : ∀ T : Over S, (T ⟶ G.X) ≃* (T ⟶ H.X))
    (he : ∀ {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G.X),
      e T' (a ≫ x) = a ≫ e T x) :
    ∃ f : G ≅ H,
      (∀ (T : Over S) (x : T ⟶ G.X), x ≫ f.hom.hom.hom = e T x) ∧
      (∀ (T : Over S) (y : T ⟶ H.X), y ≫ f.inv.hom.hom = (e T).symm y) :=
  ⟨isoOfPoints e he, comp_isoOfPoints_hom e he, comp_isoOfPoints_inv e he⟩

end Langlands.GroupScheme

namespace Langlands.GroupScheme.CentralSimpleUnits

variable {K A B : Type u} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K B] [Algebra.IsCentral K B] [IsSimpleRing B]

/-- Tensor transport of norm-one units commutes with every actual test restriction. -/
theorem normOneAlgEquiv_naturality (e : A ≃ₐ[K] B)
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : Langlands.CentralSimple.reducedNormOne K A ((algΓ (CommRingCat.of K)).obj T).unop) :
    Langlands.CentralSimple.reducedNormOneAlgEquiv e _ (normOneUnitsRestrict K A a x) =
      normOneUnitsRestrict K B a (Langlands.CentralSimple.reducedNormOneAlgEquiv e _ x) := by
  apply Subtype.ext
  apply Units.ext
  change Algebra.TensorProduct.map (AlgHom.id _ _) e.toAlgHom
      (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
        (AlgHom.id K A) x.val.val) =
    Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
      (AlgHom.id K B) (Algebra.TensorProduct.map (AlgHom.id _ _) e.toAlgHom x.val.val)
  induction x.val.val using TensorProduct.inductionOn with
  | tmul r z => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- The point comparison obtained by transporting the tensor algebra. -/
def normOneAlgEquivPoints (e : A ≃ₐ[K] B)
    (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (normOne K A).X) ≃*
      Langlands.CentralSimple.reducedNormOne K B ((algΓ (CommRingCat.of K)).obj T).unop :=
  (normOnePointsEquiv K A T).trans (Langlands.CentralSimple.reducedNormOneAlgEquiv e _)

/-- The transported norm-one point comparison is natural on all test schemes. -/
theorem normOneAlgEquivPoints_naturality (e : A ≃ₐ[K] B)
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) (x : T ⟶ (normOne K A).X) :
    normOneAlgEquivPoints e T' (a ≫ x) =
      normOneUnitsRestrict K B a (normOneAlgEquivPoints e T x) := by
  change Langlands.CentralSimple.reducedNormOneAlgEquiv e _
    (normOnePointsEquiv K A T' (a ≫ x)) = _
  rw [normOnePointsEquiv_naturality, normOneAlgEquiv_naturality]
  rfl

/-- The algebra isomorphism gives a multiplicative equivalence of actual point groups. -/
def normOneAlgEquivPointIso (e : A ≃ₐ[K] B)
    (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (normOne K A).X) ≃* (T ⟶ (normOne K B).X) :=
  (normOneAlgEquivPoints e T).trans (normOnePointsEquiv K B T).symm

/-- The equivalence of actual point groups commutes with all test restrictions. -/
theorem normOneAlgEquivPointIso_naturality (e : A ≃ₐ[K] B)
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) (x : T ⟶ (normOne K A).X) :
    normOneAlgEquivPointIso e T' (a ≫ x) = a ≫ normOneAlgEquivPointIso e T x := by
  apply (normOnePointsEquiv K B T').injective
  simp only [normOneAlgEquivPointIso, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    normOnePointsEquiv_naturality, normOneAlgEquivPoints_naturality]

/-- The algebra-induced point equivalence is represented by an actual isomorphism. -/
theorem exists_normOneAlgEquivIso (e : A ≃ₐ[K] B) :
    ∃ f : normOne K A ≅ normOne K B,
      (∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (normOne K A).X),
        x ≫ f.hom.hom.hom = normOneAlgEquivPointIso e T x) ∧
      (∀ (T : Over (Spec (CommRingCat.of K))) (y : T ⟶ (normOne K B).X),
        y ≫ f.inv.hom.hom = (normOneAlgEquivPointIso e T).symm y) :=
  exists_isoOfPoints_with_formulas (G := normOne K A) (H := normOne K B)
    (normOneAlgEquivPointIso e) (normOneAlgEquivPointIso_naturality e)

/-- The unique actual isomorphism inducing tensor transport on all point groups. -/
def normOneAlgEquivIso (e : A ≃ₐ[K] B) : normOne K A ≅ normOne K B :=
  Classical.choose (exists_normOneAlgEquivIso e)

end Langlands.GroupScheme.CentralSimpleUnits
