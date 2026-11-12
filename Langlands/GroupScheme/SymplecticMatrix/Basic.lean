import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.Multiplicative
import Langlands.AbelianScheme.KernelBaseChange
import Mathlib.LinearAlgebra.SymplecticGroup

/-! # The split symplectic group scheme from explicit matrix coordinates

For a finite index type `l` and a commutative ring `R`, this module constructs the affine
group scheme `Sp_{2l}` over `Spec R` whose points with values in a commutative `R`-algebra `S`
are the symplectic matrices `g ∈ M_{l ⊕ l}(S)`, `g J gᵀ = J`, of Mathlib's
`Matrix.symplecticGroup l S`, for the standard alternating matrix `J = [[0, -1], [1, 0]]`.
Its coordinate ring is the polynomial ring in the matrix entries modulo the entries of
`g J gᵀ - J`; no inverse variables are needed, because a symplectic matrix is invertible with
inverse `-J gᵀ J`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.SymplecticMatrix

section Matrices

variable (l : Type) [Fintype l] [DecidableEq l]

/-- Entrywise application of a ring homomorphism, as a homomorphism of symplectic groups. -/
def map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    Matrix.symplecticGroup l A →* Matrix.symplecticGroup l B where
  toFun g := ⟨(g : Matrix (l ⊕ l) (l ⊕ l) A).map f, SymplecticGroup.map_mem g.2 f⟩
  map_one' := by
    apply Subtype.ext
    exact Matrix.map_one f (map_zero f) (map_one f)
  map_mul' g h := by
    apply Subtype.ext
    exact Matrix.map_mul

variable {l}

@[simp] theorem coe_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (g : Matrix.symplecticGroup l A) :
    ((map l f g : Matrix.symplecticGroup l B) : Matrix (l ⊕ l) (l ⊕ l) B) =
      (g : Matrix (l ⊕ l) (l ⊕ l) A).map f :=
  rfl

/-- A symplectic matrix as an invertible matrix. -/
def toGL {A : Type*} [CommRing A] : Matrix.symplecticGroup l A →* GL (l ⊕ l) A where
  toFun g :=
    { val := g
      inv := ((g⁻¹ : Matrix.symplecticGroup l A) : Matrix (l ⊕ l) (l ⊕ l) A)
      val_inv := by
        rw [← Submonoid.coe_mul]
        exact congrArg Subtype.val (mul_inv_cancel g)
      inv_val := by
        rw [← Submonoid.coe_mul]
        exact congrArg Subtype.val (inv_mul_cancel g) }
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

@[simp] theorem coe_toGL {A : Type*} [CommRing A] (g : Matrix.symplecticGroup l A) :
    ((toGL g : GL (l ⊕ l) A) : Matrix (l ⊕ l) (l ⊕ l) A) = g :=
  rfl

theorem ext {A : Type*} [CommRing A] {g h : Matrix.symplecticGroup l A}
    (H : ∀ i j, (g : Matrix (l ⊕ l) (l ⊕ l) A) i j = (h : Matrix (l ⊕ l) (l ⊕ l) A) i j) :
    g = h :=
  Subtype.ext (Matrix.ext H)

end Matrices

section Algebra

variable (l : Type) [Fintype l] [DecidableEq l] (R : Type u) [CommRing R]

/-- The matrix of independent polynomial entry variables. -/
def genericMatrix : Matrix (l ⊕ l) (l ⊕ l) (MvPolynomial ((l ⊕ l) × (l ⊕ l)) R) :=
  Matrix.of fun i j => X (i, j)

/-- The entries of `g J gᵀ - J` for the generic matrix `g`. -/
def relations : Set (MvPolynomial ((l ⊕ l) × (l ⊕ l)) R) :=
  Set.range fun p : (l ⊕ l) × (l ⊕ l) =>
    (genericMatrix l R * Matrix.J l (MvPolynomial ((l ⊕ l) × (l ⊕ l)) R) *
      (genericMatrix l R)ᵀ - Matrix.J l (MvPolynomial ((l ⊕ l) × (l ⊕ l)) R)) p.1 p.2

/-- The ideal imposing `g J gᵀ = J`. -/
def ideal : Ideal (MvPolynomial ((l ⊕ l) × (l ⊕ l)) R) :=
  Ideal.span (relations l R)

/-- The coordinate ring of the symplectic group. -/
abbrev CoordinateRing : Type u := MvPolynomial ((l ⊕ l) × (l ⊕ l)) R ⧸ ideal l R

/-- The quotient map to the symplectic coordinate ring. -/
abbrev quotient : MvPolynomial ((l ⊕ l) × (l ⊕ l)) R →ₐ[R] CoordinateRing l R :=
  Ideal.Quotient.mkₐ R (ideal l R)

variable {l R}

/-- An entry specialization kills the defining ideal exactly when its matrix is symplectic. -/
theorem ideal_le_ker {S : Type u} [CommRing S] [Algebra R S]
    (f : MvPolynomial ((l ⊕ l) × (l ⊕ l)) R →ₐ[R] S)
    (h : f.mapMatrix (genericMatrix l R) ∈ Matrix.symplecticGroup l S) :
    ideal l R ≤ RingHom.ker f := by
  rw [SymplecticGroup.mem_iff] at h
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨⟨i, j⟩, rfl⟩
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  change f.mapMatrix (genericMatrix l R * Matrix.J l _ * (genericMatrix l R)ᵀ -
    Matrix.J l _) i j = 0
  have hJ : f.mapMatrix (Matrix.J l (MvPolynomial ((l ⊕ l) × (l ⊕ l)) R)) = Matrix.J l S :=
    Matrix.map_J l f
  rw [map_sub, map_mul, map_mul, hJ, AlgHom.mapMatrix_apply _ (genericMatrix l R)ᵀ,
    Matrix.transpose_map, ← AlgHom.mapMatrix_apply, h, sub_self, Matrix.zero_apply]

variable (l R)

/-- The matrix of quotient entry coordinates is symplectic. -/
theorem quotient_mem :
    (quotient l R).mapMatrix (genericMatrix l R) ∈ Matrix.symplecticGroup l (CoordinateRing l R) := by
  rw [SymplecticGroup.mem_iff]
  have h : (quotient l R).mapMatrix (genericMatrix l R * Matrix.J l _ * (genericMatrix l R)ᵀ -
      Matrix.J l _) = 0 := by
    ext i j
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨(i, j), rfl⟩
  have hJ : (quotient l R).mapMatrix (Matrix.J l (MvPolynomial ((l ⊕ l) × (l ⊕ l)) R)) =
      Matrix.J l (CoordinateRing l R) :=
    Matrix.map_J l (quotient l R)
  rwa [map_sub, map_mul, map_mul, hJ, AlgHom.mapMatrix_apply _ (genericMatrix l R)ᵀ,
    Matrix.transpose_map, ← AlgHom.mapMatrix_apply, sub_eq_zero] at h

/-- The universal symplectic matrix. -/
def universal : Matrix.symplecticGroup l (CoordinateRing l R) :=
  ⟨(quotient l R).mapMatrix (genericMatrix l R), quotient_mem l R⟩

@[simp] theorem universal_apply (i j : l ⊕ l) :
    (universal l R : Matrix (l ⊕ l) (l ⊕ l) (CoordinateRing l R)) i j =
      quotient l R (X (i, j)) := rfl

variable {l R} {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Specialization of the universal symplectic matrix along an algebra map. -/
def point (f : CoordinateRing l R →ₐ[R] S) : Matrix.symplecticGroup l S :=
  map l f.toRingHom (universal l R)

@[simp] theorem point_apply (f : CoordinateRing l R →ₐ[R] S) (i j : l ⊕ l) :
    (point f : Matrix (l ⊕ l) (l ⊕ l) S) i j = f (quotient l R (X (i, j))) := rfl

/-- Specialization is natural in the target algebra. -/
theorem point_comp (f : CoordinateRing l R →ₐ[R] S) (g : S →ₐ[R] T) :
    point (g.comp f) = map l g.toRingHom (point f) := rfl

@[simp] theorem point_id : point (AlgHom.id R (CoordinateRing l R)) = universal l R := rfl

/-- The values of the entry variables at a symplectic matrix. -/
def values (g : Matrix.symplecticGroup l S) : (l ⊕ l) × (l ⊕ l) → S :=
  fun ij => (g : Matrix (l ⊕ l) (l ⊕ l) S) ij.1 ij.2

theorem aeval_mapMatrix_genericMatrix (g : Matrix.symplecticGroup l S) :
    (aeval (R := R) (values g)).mapMatrix (genericMatrix l R) =
      (g : Matrix (l ⊕ l) (l ⊕ l) S) := by
  ext i j
  simp [genericMatrix, values]

/-- The algebra map classifying a symplectic matrix. -/
def classify (g : Matrix.symplecticGroup l S) : CoordinateRing l R →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aeval (values g)) fun _ ha =>
    RingHom.mem_ker.mp <| ideal_le_ker _
      (by rw [aeval_mapMatrix_genericMatrix]; exact g.2) ha

theorem classify_comp_quotient (g : Matrix.symplecticGroup l S) :
    (classify (R := R) g).comp (quotient l R) = aeval (values g) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[simp] theorem classify_quotient (g : Matrix.symplecticGroup l S)
    (f : MvPolynomial ((l ⊕ l) × (l ⊕ l)) R) :
    classify g (quotient l R f) = aeval (values g) f :=
  AlgHom.congr_fun (classify_comp_quotient g) f

@[simp] theorem classify_entry (g : Matrix.symplecticGroup l S) (i j : l ⊕ l) :
    classify (R := R) g (quotient l R (X (i, j))) = (g : Matrix (l ⊕ l) (l ⊕ l) S) i j := by
  rw [classify_quotient, aeval_X]
  rfl

/-- Algebra maps out of the coordinate ring are exactly symplectic matrices. -/
def homEquiv : (CoordinateRing l R →ₐ[R] S) ≃ Matrix.symplecticGroup l S where
  toFun := point
  invFun := classify
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    rw [AlgHom.comp_apply, AlgHom.comp_apply, classify_entry]
    rfl
  right_inv g := ext fun i j => classify_entry g i j

@[simp] theorem classify_point (f : CoordinateRing l R →ₐ[R] S) : classify (point f) = f :=
  homEquiv.left_inv f

@[simp] theorem point_classify (g : Matrix.symplecticGroup l S) :
    point (classify (R := R) g) = g := homEquiv.right_inv g

/-- Classifying a coefficient-changed matrix is composing its classifying map. -/
theorem classify_map (g : Matrix.symplecticGroup l S) (f : S →ₐ[R] T) :
    classify (map l f.toRingHom g) = f.comp (classify (R := R) g) := by
  apply homEquiv.injective
  change point _ = point _
  rw [point_comp, point_classify, point_classify]

end Algebra

section Scheme

variable (l : Type) [Fintype l] [DecidableEq l] (R : CommRingCat.{u})

/-- The functor of symplectic matrices, with entrywise coefficient change. -/
def functor : CommAlgCat.{u} R ⥤ GrpCat.{u} where
  obj S := GrpCat.of (Matrix.symplecticGroup l S)
  map f := GrpCat.ofHom (map l f.hom.toRingHom)
  map_id S := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact ext fun i j => rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact ext fun i j => rfl

@[simp] theorem functor_obj (S : CommAlgCat.{u} R) :
    (functor l R).obj S = GrpCat.of (Matrix.symplecticGroup l S) := rfl

theorem functor_map_apply {S T : CommAlgCat.{u} R} (f : S ⟶ T)
    (g : Matrix.symplecticGroup l S) :
    (functor l R).map f g = map l f.hom.toRingHom g := rfl

/-- The symplectic coordinate ring as a base algebra. -/
abbrev coordinateAlgebra : CommAlgCat.{u} R := CommAlgCat.of R (CoordinateRing l R)

/-- The explicit coordinate ring corepresents the symplectic functor. -/
def corepresentableBy :
    (functor l R ⋙ forget GrpCat).CorepresentableBy (coordinateAlgebra l R) where
  homEquiv :=
    { toFun := fun f => point f.hom
      invFun := fun g => CommAlgCat.ofHom (classify g)
      left_inv := fun f => CommAlgCat.hom_ext (classify_point f.hom)
      right_inv := fun g => point_classify g }
  homEquiv_comp g f := point_comp f.hom g.hom

/-- The split symplectic group scheme `Sp_{2l}` over `Spec R`. -/
abbrev groupScheme : GroupScheme (Spec R) :=
  Corepresented.groupScheme (functor l R) (corepresentableBy l R)

@[simp] theorem groupScheme_X :
    (groupScheme l R).X = (algSpec R).obj (op (coordinateAlgebra l R)) := rfl

theorem groupScheme_left :
    (groupScheme l R).X.left = Spec (CommRingCat.of (CoordinateRing l R)) := rfl

theorem groupScheme_hom :
    (groupScheme l R).X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing l R))) := rfl

instance isAffine_groupScheme : IsAffine (groupScheme l R).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (CoordinateRing l R))))

instance isAffineHom_groupScheme : IsAffineHom (groupScheme l R).X.hom :=
  isAffineHom_of_isAffine _

/-- Scheme points over every relative test scheme are symplectic matrices over its global
sections. -/
def pointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme l R).X) ≃* Matrix.symplecticGroup l Γ(T.left, ⊤) :=
  Corepresented.pointsEquiv (functor l R) (corepresentableBy l R) T

variable {l R}

/-- Restriction of scheme points applies the pullback on global sections entrywise. -/
theorem pointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme l R).X) :
    pointsEquiv l R T' (a ≫ x) = map l a.left.appTop.hom (pointsEquiv l R T x) :=
  Corepresented.pointsEquiv_naturality _ _ a x

/-- A symplectic scheme point is determined by its matrix entries. -/
theorem points_ext {T : Over (Spec R)} {x y : T ⟶ (groupScheme l R).X}
    (h : ∀ i j, (pointsEquiv l R T x : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) i j =
      (pointsEquiv l R T y : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) i j) : x = y :=
  (pointsEquiv l R T).injective (ext h)

/-- Inclusion of symplectic matrices into invertible matrices is a natural map. -/
def toGeneralLinear : functor l R ⟶ GeneralLinear.functor (l ⊕ l) R where
  app S := GrpCat.ofHom toGL
  naturality S T f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Units.ext
    rfl

variable (l R) in
/-- The homomorphism from the symplectic group scheme into the general linear one. -/
def inclusion : groupScheme l R ⟶ GeneralLinear.groupScheme (l ⊕ l) R :=
  Corepresented.groupSchemeMap (corepresentableBy l R) (GeneralLinear.corepresentableBy (l ⊕ l) R)
    toGeneralLinear

/-- The inclusion on every test scheme is the usual inclusion of symplectic matrices. -/
theorem pointsEquiv_inclusion (T : Over (Spec R)) (x : T ⟶ (groupScheme l R).X) :
    GeneralLinear.pointsEquiv (l ⊕ l) R T (x ≫ (inclusion l R).hom.hom) =
      toGL (pointsEquiv l R T x) :=
  Corepresented.groupSchemeMap_points _ _ _ x

end Scheme

section BaseChange

variable (l : Type) [Fintype l] [DecidableEq l]
variable {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)

/-- On every test scheme, the pullback model and the model over the new base have the same
symplectic matrices of global sections. -/
def baseChangeModelPointsEquiv (T : Over (Spec R')) :
    (T ⟶ ((GroupScheme.baseChange b).obj (groupScheme l R)).X) ≃*
      (T ⟶ (groupScheme l R').X) :=
  ((baseChangePointsEquiv b (groupScheme l R) T).trans
    (pointsEquiv l R ((Over.map b).obj T))).trans (pointsEquiv l R' T).symm

theorem baseChangeModelPointsEquiv_naturality {T T' : Over (Spec R')}
    (a : T' ⟶ T) (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme l R)).X) :
    baseChangeModelPointsEquiv l b T' (a ≫ x) =
      a ≫ baseChangeModelPointsEquiv l b T x := by
  apply (pointsEquiv l R' T').injective
  simp only [baseChangeModelPointsEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality,
    pointsEquiv_naturality]
  rfl

/-- The split symplectic group commutes with arbitrary change of the affine base. -/
def baseChangeModelIso :
    (GroupScheme.baseChange b).obj (groupScheme l R) ≅ groupScheme l R' :=
  isoOfPoints (baseChangeModelPointsEquiv l b)
    (baseChangeModelPointsEquiv_naturality l b)

/-- The model comparison preserves all entries on every relative test scheme. -/
theorem pointsEquiv_baseChangeModelIso_hom (T : Over (Spec R'))
    (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme l R)).X) :
    pointsEquiv l R' T (x ≫ (baseChangeModelIso l b).hom.hom.hom) =
      pointsEquiv l R ((Over.map b).obj T) (baseChangePointsEquiv b _ T x) := by
  rw [baseChangeModelIso, comp_isoOfPoints_hom]
  exact (pointsEquiv l R' T).apply_symm_apply _

end BaseChange

end Langlands.GroupScheme.SymplecticMatrix
