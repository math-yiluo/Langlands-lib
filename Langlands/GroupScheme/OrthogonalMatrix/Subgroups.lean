import Langlands.GroupScheme.OrthogonalMatrix.Smooth
import Langlands.GroupScheme.SymplecticMatrix.Reductive

/-! # Levi and unipotent subgroups of the split orthogonal group

The Levi embedding `A ↦ diag(A, A⁻ᵀ)` of `GL_l` and the unipotent block matrices
`[[1, Y], [0, 1]]`, `[[1, 0], [Y, 1]]` with `Y` alternating land in the split orthogonal group.
They give homomorphisms of group schemes from `GL_l` and from `𝔾ₐ`, whose sources are connected
over a field, so the constant points they produce lie in the identity component.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l]

section Matrices

variable {n : Type*} {A : Type*} [CommRing A]

omit [Fintype l] [DecidableEq l] in
theorem IsAlt.transpose {M : Matrix n n A} (hM : IsAlt M) : IsAlt Mᵀ := by
  obtain ⟨U, rfl⟩ := hM
  exact ⟨Uᵀ, by rw [Matrix.transpose_sub, Matrix.transpose_transpose]⟩

omit [Fintype l] [DecidableEq l] in
theorem IsAlt.smul {M : Matrix n n A} (hM : IsAlt M) (t : A) : IsAlt (t • M) := by
  obtain ⟨U, rfl⟩ := hM
  exact ⟨t • U, by rw [Matrix.transpose_smul, smul_sub]⟩

omit [Fintype l] [DecidableEq l] in
theorem isAlt_fromBlocks₁₁ {M : Matrix l l A} (hM : IsAlt M) :
    IsAlt (Matrix.fromBlocks M 0 0 0 : Matrix (l ⊕ l) (l ⊕ l) A) := by
  obtain ⟨U, rfl⟩ := hM
  refine ⟨Matrix.fromBlocks U 0 0 0, ?_⟩
  rw [Matrix.fromBlocks_transpose]
  ext (i | i) (j | j) <;> simp

omit [Fintype l] [DecidableEq l] in
theorem isAlt_fromBlocks₂₂ {M : Matrix l l A} (hM : IsAlt M) :
    IsAlt (Matrix.fromBlocks 0 0 0 M : Matrix (l ⊕ l) (l ⊕ l) A) := by
  obtain ⟨U, rfl⟩ := hM
  refine ⟨Matrix.fromBlocks 0 0 0 U, ?_⟩
  rw [Matrix.fromBlocks_transpose]
  ext (i | i) (j | j) <;> simp

theorem levi_mem (g : GL l A) : SymplecticMatrix.levi g ∈ orthogonalGroup l A := by
  rw [mem_orthogonalGroup_iff]
  have h : defect (SymplecticMatrix.levi g) = 0 := by
    rw [defect, SymplecticMatrix.levi, formMatrix, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
      Matrix.transpose_zero, Matrix.transpose_transpose]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, sub_self]
  rw [h]
  exact isAlt_zero

theorem upper_mem {Y : Matrix l l A} (hY : IsAlt Y) :
    SymplecticMatrix.upper Y ∈ orthogonalGroup l A := by
  rw [mem_orthogonalGroup_iff]
  have h : defect (SymplecticMatrix.upper Y) = Matrix.fromBlocks Yᵀ 0 0 0 := by
    rw [defect, SymplecticMatrix.upper, formMatrix, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    ext (i | i) (j | j) <;> simp
  rw [h]
  exact isAlt_fromBlocks₁₁ hY.transpose

theorem lower_mem {Y : Matrix l l A} (hY : IsAlt Y) :
    SymplecticMatrix.lower Y ∈ orthogonalGroup l A := by
  rw [mem_orthogonalGroup_iff]
  have h : defect (SymplecticMatrix.lower Y) = Matrix.fromBlocks 0 0 0 Y := by
    rw [defect, SymplecticMatrix.lower, formMatrix, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    ext (i | i) (j | j) <;> simp
  rw [h]
  exact isAlt_fromBlocks₂₂ hY

end Matrices

section Homs

/-- The Levi embedding `A ↦ diag(A, A⁻ᵀ)` as a group homomorphism. -/
def leviHom (A : Type*) [CommRing A] : GL l A →* orthogonalGroup l A where
  toFun g := ⟨SymplecticMatrix.levi g, levi_mem g⟩
  map_one' := Subtype.ext (by simp [SymplecticMatrix.levi, fromBlocks_one])
  map_mul' g h := Subtype.ext (SymplecticMatrix.levi_mul g h)

@[simp] theorem coe_leviHom {A : Type*} [CommRing A] (g : GL l A) :
    ((leviHom A g : orthogonalGroup l A) : Matrix (l ⊕ l) (l ⊕ l) A) =
      SymplecticMatrix.levi g := rfl

/-- The upper unipotent homomorphism `t ↦ upper (t • φ(Y))` of an alternating matrix `Y`. -/
def upperHom {B : Type*} [CommRing B] {Y : Matrix l l B} (hY : IsAlt Y) {A : Type*}
    [CommRing A] (φ : B →+* A) : Multiplicative (Fin 1 → A) →* orthogonalGroup l A where
  toFun t := ⟨SymplecticMatrix.upper (t.toAdd 0 • Y.map φ), upper_mem ((hY.map φ).smul _)⟩
  map_one' := Subtype.ext (by simp [SymplecticMatrix.upper_zero])
  map_mul' s t := Subtype.ext (by simp [SymplecticMatrix.upper_mul_upper, add_smul])

/-- The lower unipotent homomorphism `t ↦ lower (t • φ(Y))` of an alternating matrix `Y`. -/
def lowerHom {B : Type*} [CommRing B] {Y : Matrix l l B} (hY : IsAlt Y) {A : Type*}
    [CommRing A] (φ : B →+* A) : Multiplicative (Fin 1 → A) →* orthogonalGroup l A where
  toFun t := ⟨SymplecticMatrix.lower (t.toAdd 0 • Y.map φ), lower_mem ((hY.map φ).smul _)⟩
  map_one' := Subtype.ext (by simp [SymplecticMatrix.lower_zero])
  map_mul' s t := Subtype.ext (by simp [SymplecticMatrix.lower_mul_lower, add_smul])

@[simp] theorem coe_upperHom {B : Type*} [CommRing B] {Y : Matrix l l B} (hY : IsAlt Y)
    {A : Type*} [CommRing A] (φ : B →+* A) (t : Multiplicative (Fin 1 → A)) :
    ((upperHom hY φ t : orthogonalGroup l A) : Matrix (l ⊕ l) (l ⊕ l) A) =
      SymplecticMatrix.upper (t.toAdd 0 • Y.map φ) := rfl

@[simp] theorem coe_lowerHom {B : Type*} [CommRing B] {Y : Matrix l l B} (hY : IsAlt Y)
    {A : Type*} [CommRing A] (φ : B →+* A) (t : Multiplicative (Fin 1 → A)) :
    ((lowerHom hY φ t : orthogonalGroup l A) : Matrix (l ⊕ l) (l ⊕ l) A) =
      SymplecticMatrix.lower (t.toAdd 0 • Y.map φ) := rfl

variable (R : CommRingCat.{u})

/-- The Levi embedding as a natural transformation. -/
def leviTrans : GeneralLinear.functor l R ⟶ functor l R where
  app A := GrpCat.ofHom (leviHom A)
  naturality A B f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    exact (SymplecticMatrix.map_levi f.hom.toRingHom g).symm

/-- The upper unipotent homomorphism of an alternating matrix as a natural transformation. -/
def upperTrans {Y : Matrix l l R} (hY : IsAlt Y) : VectorGroup.functor R 1 ⟶ functor l R where
  app A := GrpCat.ofHom (upperHom hY (algebraMap R A))
  naturality A B f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro t
    apply Subtype.ext
    exact (congrArg SymplecticMatrix.upper
      (SymplecticMatrix.smul_map_algebraMap R f (t.toAdd 0))).symm.trans
      (SymplecticMatrix.map_upper f.hom.toRingHom _).symm

/-- The lower unipotent homomorphism of an alternating matrix as a natural transformation. -/
def lowerTrans {Y : Matrix l l R} (hY : IsAlt Y) : VectorGroup.functor R 1 ⟶ functor l R where
  app A := GrpCat.ofHom (lowerHom hY (algebraMap R A))
  naturality A B f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro t
    apply Subtype.ext
    exact (congrArg SymplecticMatrix.lower
      (SymplecticMatrix.smul_map_algebraMap R f (t.toAdd 0))).symm.trans
      (SymplecticMatrix.map_lower f.hom.toRingHom _).symm

/-- The Levi embedding `GL_l → O_{2l}` of group schemes. -/
def leviMap : GeneralLinear.groupScheme l R ⟶ groupScheme l R :=
  Corepresented.groupSchemeMap (GeneralLinear.corepresentableBy l R) (corepresentableBy l R)
    (leviTrans R)

/-- The upper unipotent homomorphism `𝔾ₐ → O_{2l}` of an alternating matrix. -/
def upperMap {Y : Matrix l l R} (hY : IsAlt Y) :
    VectorGroup.groupScheme R 1 ⟶ groupScheme l R :=
  Corepresented.groupSchemeMap (VectorGroup.corepresentableBy R 1) (corepresentableBy l R)
    (upperTrans R hY)

/-- The lower unipotent homomorphism `𝔾ₐ → O_{2l}` of an alternating matrix. -/
def lowerMap {Y : Matrix l l R} (hY : IsAlt Y) :
    VectorGroup.groupScheme R 1 ⟶ groupScheme l R :=
  Corepresented.groupSchemeMap (VectorGroup.corepresentableBy R 1) (corepresentableBy l R)
    (lowerTrans R hY)

variable {R}

theorem pointsEquiv_leviMap (T : Over (Spec R)) (x : T ⟶ (GeneralLinear.groupScheme l R).X) :
    pointsEquiv l R T (x ≫ (leviMap R).hom.hom) =
      leviHom _ (GeneralLinear.pointsEquiv l R T x) :=
  Corepresented.groupSchemeMap_points _ _ _ x

theorem pointsEquiv_upperMap {Y : Matrix l l R} (hY : IsAlt Y) (T : Over (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    pointsEquiv l R T (x ≫ (upperMap R hY).hom.hom) =
      upperHom hY (scalarMap T) (VectorGroup.coordinates R 1 T x) :=
  Corepresented.groupSchemeMap_points _ _ _ x

theorem pointsEquiv_lowerMap {Y : Matrix l l R} (hY : IsAlt Y) (T : Over (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    pointsEquiv l R T (x ≫ (lowerMap R hY).hom.hom) =
      lowerHom hY (scalarMap T) (VectorGroup.coordinates R 1 T x) :=
  Corepresented.groupSchemeMap_points _ _ _ x

end Homs

section Identity

variable (l) in
/-- The instance `isAffineHom_groupScheme`, restated for bases `CommRingCat.of k`, which instance
search does not find. -/
instance isAffineHom_groupScheme_of (k : Type u) [Field k] :
    IsAffineHom (groupScheme l (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme (l := l) (R := CommRingCat.of k)

variable (l) in
/-- The instance `smooth_groupScheme`, restated for bases `CommRingCat.of k`. -/
instance smooth_groupScheme_of (k : Type u) [Field k] :
    Smooth (groupScheme l (CommRingCat.of k)).X.hom :=
  smooth_groupScheme l (CommRingCat.of k)

variable {K : Type u} [Field K]

/-- The orthogonal point obtained from an orthogonal matrix over the base field. -/
def constantPoint (T : Over (Spec (CommRingCat.of K))) (g : orthogonalGroup l K) :
    T ⟶ (groupScheme l (CommRingCat.of K)).X :=
  (pointsEquiv l _ T).symm (map l (scalarMap T) g)

@[simp] theorem pointsEquiv_constantPoint (T : Over (Spec (CommRingCat.of K)))
    (g : orthogonalGroup l K) :
    pointsEquiv l _ T (constantPoint T g) = map l (scalarMap T) g :=
  MulEquiv.apply_symm_apply _ _

/-- The constant point of a Levi matrix lies in the identity component. -/
theorem constantPoint_levi_mem (T : Over (Spec (CommRingCat.of K))) (g : GL l K) :
    constantPoint T (leviHom K g) ∈
      (SubgroupFunctor.range (identityComponentι (groupScheme l (CommRingCat.of K)))).carrier T := by
  let a : T ⟶ (GeneralLinear.groupScheme l (CommRingCat.of K)).X :=
    (GeneralLinear.pointsEquiv l _ T).symm (GeneralLinearGroup.map (scalarMap T) g)
  have h : constantPoint T (leviHom K g) = a ≫ (leviMap _).hom.hom := by
    apply (pointsEquiv l _ T).injective
    rw [pointsEquiv_constantPoint, pointsEquiv_leviMap]
    apply Subtype.ext
    simp only [a, MulEquiv.apply_symm_apply, coe_leviHom, coe_map]
    exact SymplecticMatrix.map_levi _ g
  rw [h]
  exact SymplecticMatrix.comp_mem_range_identityComponentι (leviMap _) a

/-- The vector-group point with coordinate `1`. -/
def onePoint (T : Over (Spec (CommRingCat.of K))) :
    T ⟶ (VectorGroup.groupScheme (CommRingCat.of K) 1).X :=
  (VectorGroup.coordinates _ 1 T).symm (Multiplicative.ofAdd fun _ => 1)

theorem onePoint_coord (T : Over (Spec (CommRingCat.of K))) :
    (VectorGroup.coordinates (CommRingCat.of K) 1 T (onePoint T)).toAdd 0 = 1 := by
  simp only [onePoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]

/-- The constant point of an upper unipotent matrix lies in the identity component. -/
theorem constantPoint_upper_mem (T : Over (Spec (CommRingCat.of K))) {Y : Matrix l l K}
    (hY : IsAlt Y) :
    constantPoint T ⟨SymplecticMatrix.upper Y, upper_mem hY⟩ ∈
      (SubgroupFunctor.range (identityComponentι (groupScheme l (CommRingCat.of K)))).carrier T := by
  have h : constantPoint T ⟨SymplecticMatrix.upper Y, upper_mem hY⟩ =
      onePoint T ≫ (upperMap (CommRingCat.of K) hY).hom.hom := by
    apply (pointsEquiv l _ T).injective
    rw [pointsEquiv_constantPoint, pointsEquiv_upperMap]
    apply Subtype.ext
    rw [coe_upperHom, onePoint_coord, one_smul, coe_map]
    exact SymplecticMatrix.map_upper _ Y
  rw [h]
  exact SymplecticMatrix.comp_mem_range_identityComponentι (upperMap _ hY) (onePoint T)

/-- The constant point of a lower unipotent matrix lies in the identity component. -/
theorem constantPoint_lower_mem (T : Over (Spec (CommRingCat.of K))) {Y : Matrix l l K}
    (hY : IsAlt Y) :
    constantPoint T ⟨SymplecticMatrix.lower Y, lower_mem hY⟩ ∈
      (SubgroupFunctor.range (identityComponentι (groupScheme l (CommRingCat.of K)))).carrier T := by
  have h : constantPoint T ⟨SymplecticMatrix.lower Y, lower_mem hY⟩ =
      onePoint T ≫ (lowerMap (CommRingCat.of K) hY).hom.hom := by
    apply (pointsEquiv l _ T).injective
    rw [pointsEquiv_constantPoint, pointsEquiv_lowerMap]
    apply Subtype.ext
    rw [coe_lowerHom, onePoint_coord, one_smul, coe_map]
    exact SymplecticMatrix.map_lower _ Y
  rw [h]
  exact SymplecticMatrix.comp_mem_range_identityComponentι (lowerMap _ hY) (onePoint T)

end Identity

end Langlands.GroupScheme.OrthogonalMatrix
