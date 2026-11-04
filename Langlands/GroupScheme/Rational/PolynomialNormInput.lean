import Langlands.GroupScheme.Rational.PolynomialNormCentral
import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.Rational.VectorGroupCoordinates

/-! # Central norm inputs from actual vector-group homomorphisms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PolynomialPoint

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}

/-- The standard polynomial vector point has its prescribed tuple as coordinates. -/
theorem vectorCoordinates_aeval {A : Type u} [CommRing A] [Algebra k A]
    (v : Fin n → A) :
    vectorCoordinates (k := k) (n := n)
      ((algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (aeval v : MvPolynomial (Fin n) k →ₐ[k] A)).op) = v := by
  have h := Corepresented.affinePointsEquiv_map
    (VectorGroup.functor (CommRingCat.of k) n)
    (VectorGroup.corepresentableBy (CommRingCat.of k) n) (CommAlgCat.of k A)
    (CommAlgCat.ofHom (aeval v : MvPolynomial (Fin n) k →ₐ[k] A))
  exact (congrArg Multiplicative.toAdd h).trans (funext (aeval_X (R := k) v))

/-- A morphism from a vector group is additive on the universal pair of tuples. -/
theorem isAdditive_hom (f : VectorGroup.groupScheme (CommRingCat.of k) n ⟶ G) :
    IsAdditive f.hom.hom := by
  let A := MvPolynomial (Fin n ⊕ Fin n) k
  let v : Fin n → A := fun i => X (Sum.inl i)
  let w : Fin n → A := fun i => X (Sum.inr i)
  let s (t : Fin n → A) : Lie.AffinePoints
      (VectorGroup.groupScheme (CommRingCat.of k) n) A :=
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (aeval t)).op
  have hs : s (v + w) = s v * s w := by
    rw [vectorPoint_eq_aeval (s v * s w), vectorCoordinates_mul]
    simp only [s, vectorCoordinates_aeval]
  change s (v + w) ≫ f.hom.hom = (s v ≫ f.hom.hom) * (s w ≫ f.hom.hom)
  rw [hs, MonObj.mul_comp]

/-- Iterated substitution is evaluation at the substituted tuple. -/
theorem evaluate_evaluate (p : Lie.AffinePoints G (MvPolynomial (Fin n) k))
    {m : ℕ} (v : Fin n → MvPolynomial (Fin m) k)
    {A : Type u} [CommRing A] [Algebra k A] (w : Fin m → A) :
    evaluate (evaluate p v) w = evaluate p (fun i => aeval w (v i)) := by
  simp only [evaluate, ← Lie.affineMap_comp, comp_aeval]

/-- Scalar substitution preserves the universal additive identity. -/
theorem isAdditive_scalar (p : Lie.AffinePoints G (MvPolynomial (Fin n) k))
    (hp : IsAdditive p) (a : k) :
    IsAdditive (evaluate p (fun i => C a * X i)) := by
  unfold IsAdditive
  simp only [evaluate_evaluate, map_mul, aeval_C, aeval_X, mul_add]
  exact evaluate_add p hp
    (fun i => C a * X (Sum.inl i) : Fin n → MvPolynomial (Fin n ⊕ Fin n) k)
    (fun i => C a * X (Sum.inr i))

/-- Scalar multiplication as an actual endomorphism of the standard vector group. -/
def scalarHom (a : k) : VectorGroup.groupScheme (CommRingCat.of k) n ⟶
    VectorGroup.groupScheme (CommRingCat.of k) n := by
  let V := VectorGroup.groupScheme (CommRingCat.of k) n
  have h : IsAdditive (G := V) (𝟙 V.X) := isAdditive_hom (𝟙 V)
  exact homOfAdditive (evaluate (G := V) (𝟙 V.X) (fun i => C a * X i))
    (isAdditive_scalar (𝟙 V.X) h a)

/-- The underlying scalar morphism is the spectrum map of the linear substitution. -/
theorem scalarHom_hom (a : k) :
    (scalarHom (n := n) a).hom.hom =
      (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (aeval (fun i : Fin n => C a * X i) :
          MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k)).op := by
  simp only [scalarHom, homOfAdditive_hom, evaluate, Lie.affineMap_apply]
  exact Category.comp_id _

variable (k) (L : Type u) [Field L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k)))

local notation "G_L" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

/-- Base-polynomial substitution is ordinary extension-field evaluation after restriction. -/
theorem substituteAlg_restrictScalars {I J : Type} (v : I → MvPolynomial J k) :
    substituteAlg k L v =
      (aeval (fun i => MvPolynomial.mapAlgHom (Algebra.ofId k L) (v i)) :
        MvPolynomial I L →ₐ[L] MvPolynomial J L).restrictScalars k := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [AlgHom.coe_toRingHom,
      substituteAlg_C, AlgHom.restrictScalars_apply, aeval_C,
      algebraMap_eq]
  · intro i
    simp only [AlgHom.coe_toRingHom,
      substituteAlg_X, AlgHom.restrictScalars_apply, aeval_X]

/-- The affine base-change comparison intertwines the two substitution operations. -/
theorem affineBaseChangeEquiv_substitute {I J : Type}
    (p : Lie.AffinePoints G_L (MvPolynomial I L)) (v : I → MvPolynomial J k) :
    Lie.affineMap G (substituteAlg k L v)
        (Lie.affineBaseChangeEquiv k L G (MvPolynomial I L) p) =
      Lie.affineBaseChangeEquiv k L G (MvPolynomial J L)
        (Lie.affineMap G_L
          (aeval (fun i => MvPolynomial.mapAlgHom (Algebra.ofId k L) (v i))) p) := by
  rw [Lie.affineBaseChangeEquiv_naturality, substituteAlg_restrictScalars]

/-- The affine base-change comparison preserves full-center membership. -/
theorem affineBaseChangeEquiv_mem_center
    {A : Type u} [CommRing A] [Algebra k A] [Algebra L A] [IsScalarTower k L A]
    {x : Lie.AffinePoints G_L A}
    (hx : x ∈ (center G_L).carrier
      ((algSpec (CommRingCat.of L)).obj (op (CommAlgCat.of L A)))) :
    Lie.affineBaseChangeEquiv k L G A x ∈ (center G).carrier
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))) := by
  rw [center_baseChange] at hx
  exact (center G).comp_mem (Lie.affineBaseTestIso k L A).inv hx

/-- A central homomorphism over the extension field gives a full-central polynomial point. -/
def centralInput {n : ℕ} (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) : centralAffinePoints k G (MvPolynomial (Fin n) L) :=
  ⟨Lie.affineBaseChangeEquiv k L G (MvPolynomial (Fin n) L) f.hom.hom,
    affineBaseChangeEquiv_mem_center k L G
      (by
        change f.hom.hom ∈ (center G_L).carrier
          (VectorGroup.groupScheme (CommRingCat.of L) n).X
        simpa only [Category.id_comp] using hf _ (𝟙 _))⟩

/-- The underlying polynomial point of the input is the actual base-change comparison. -/
@[simp] theorem centralInput_val {n : ℕ}
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) (hf : IsCentral f) :
    (centralInput k L G f hf).val =
      Lie.affineBaseChangeEquiv k L G (MvPolynomial (Fin n) L) f.hom.hom := rfl

/-- The input satisfies exactly the universal additive equation required by the norm. -/
theorem centralInput_mem_additive {n : ℕ}
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) (hf : IsCentral f) :
    centralInput k L G f hf ∈ centralAdditivePoints k G L n := by
  apply Subtype.ext
  change Lie.affineMap G _ (Lie.affineBaseChangeEquiv k L G _ f.hom.hom) =
    Lie.affineMap G _ (Lie.affineBaseChangeEquiv k L G _ f.hom.hom) *
      Lie.affineMap G _ (Lie.affineBaseChangeEquiv k L G _ f.hom.hom)
  rw [affineBaseChangeEquiv_substitute, affineBaseChangeEquiv_substitute,
    affineBaseChangeEquiv_substitute, ← map_mul]
  apply congrArg (Lie.affineBaseChangeEquiv k L G _)
  have h := isAdditive_hom f
  unfold IsAdditive evaluate at h
  simpa only [MvPolynomial.mapAlgHom_apply, map_add, map_X] using h

/-- The central input after precomposing by extension-field scalar multiplication. -/
def scalarCentralInput {n : ℕ}
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) (a : L) : centralAffinePoints k G (MvPolynomial (Fin n) L) :=
  centralInput k L G (scalarHom a ≫ f) (hf.comp _)

/-- The parameter acts on the original extension-field polynomial point before descent. -/
@[simp] theorem scalarCentralInput_val {n : ℕ}
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) (a : L) :
    (scalarCentralInput k L G f hf a).val =
      Lie.affineBaseChangeEquiv k L G (MvPolynomial (Fin n) L)
        (evaluate f.hom.hom (fun i => C a * X i)) := by
  simp only [scalarCentralInput, centralInput_val, Grp.comp_hom_hom, scalarHom_hom]
  rfl

/-- Every scalar parameter gives a valid central additive norm input. -/
theorem scalarCentralInput_mem_additive {n : ℕ}
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) (a : L) :
    scalarCentralInput k L G f hf a ∈ centralAdditivePoints k G L n :=
  centralInput_mem_additive k L G _ _

variable [IsAffine G.X.left] [FiniteDimensional k L] [IsGalois k L]

/-- The scalar-parametrized central norm of an actual extension-field vector homomorphism. -/
def normOfCentralHom {n : ℕ}
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) (a : L) : VectorGroup.groupScheme (CommRingCat.of k) n ⟶ G :=
  centralNormHom k G L (scalarCentralInput k L G f hf a)
    (scalarCentralInput_mem_additive k L G f hf a)

/-- The resulting actual homomorphism is central on every scheme test. -/
theorem normOfCentralHom_isCentral {n : ℕ}
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) (a : L) : IsCentral (normOfCentralHom k L G f hf a) :=
  centralNormHom_isCentral k L G _ _

/-- Extending the norm recovers the complete conjugate product of the scaled input. -/
theorem normOfCentralHom_extension {n : ℕ}
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) (a : L) :
    Lie.affineMap G (MvPolynomial.mapAlgHom (Algebra.ofId k L))
      (normOfCentralHom k L G f hf a).hom.hom =
        (centralConjugateProduct k G L (Fin n) (scalarCentralInput k L G f hf a)).val :=
  centralNormHom_extension k G L _ _

/-- Natural coordinates on an actual central subgroup supply the standard-vector input. -/
def normOfCentralVector {n : ℕ} {V : GroupScheme (Spec (CommRingCat.of L))}
    (e : ∀ T : Over (Spec (CommRingCat.of L)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))
    (he : RelativeRoot.IsNaturalVectorCoordinates e)
    (z : V ⟶ G_L) (hz : IsCentral z) (a : L) :
    VectorGroup.groupScheme (CommRingCat.of k) n ⟶ G :=
  normOfCentralHom k L G ((RelativeRoot.vectorGroupIso e he).inv ≫ z) (hz.comp _) a

/-- The norm from natural vector coordinates retains full centrality. -/
theorem normOfCentralVector_isCentral {n : ℕ} {V : GroupScheme (Spec (CommRingCat.of L))}
    (e : ∀ T : Over (Spec (CommRingCat.of L)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))
    (he : RelativeRoot.IsNaturalVectorCoordinates e)
    (z : V ⟶ G_L) (hz : IsCentral z) (a : L) :
    IsCentral (normOfCentralVector k L G e he z hz a) :=
  normOfCentralHom_isCentral k L G _ _ _

end Langlands.GroupScheme.PolynomialPoint
