import Langlands.GroupScheme.OddOrthogonalMatrix.ShortSubgroups

/-! # The determinant-corrected even orthogonal inclusion -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

open Quaternionic.FirstKindInvolution Quaternionic.ScalarMatrixCoordinates

variable {l : Type} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R]

/-- The determinant of an even orthogonal matrix has square one over every
commutative coefficient ring. -/
theorem even_det_mul_self (g : OrthogonalMatrix.orthogonalGroup l R) :
    (g : Matrix (l ⊕ l) (l ⊕ l) R).det * (g : Matrix (l ⊕ l) (l ⊕ l) R).det = 1 := by
  have h := congrArg Matrix.det (OrthogonalMatrix.polar_mul_self g)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hJ : (OrthogonalMatrix.polarMatrix l R).det *
      (OrthogonalMatrix.polarMatrix l R).det = 1 := by
    rw [← Matrix.det_mul, OrthogonalMatrix.polarMatrix_mul_self, Matrix.det_one]
  calc
    _ = ((g : Matrix (l ⊕ l) (l ⊕ l) R).det *
        (g : Matrix (l ⊕ l) (l ⊕ l) R).det) *
        ((OrthogonalMatrix.polarMatrix l R).det * (OrthogonalMatrix.polarMatrix l R).det) := by
      rw [hJ, mul_one]
    _ = ((g : Matrix (l ⊕ l) (l ⊕ l) R).det *
        (OrthogonalMatrix.polarMatrix l R).det *
        (g : Matrix (l ⊕ l) (l ⊕ l) R).det) * (OrthogonalMatrix.polarMatrix l R).det := by ring
    _ = 1 := by rw [h, hJ]

/-- The even orthogonal matrix acts on the odd space by `diag(det g,g)`. -/
def evenBlock (g : OrthogonalMatrix.orthogonalGroup l R) : Matrix (Index l) (Index l) R :=
  Matrix.fromBlocks (fun _ _ : Unit => (g : Matrix (l ⊕ l) (l ⊕ l) R).det) 0 0 g

@[simp] theorem evenBlock_one : evenBlock (1 : OrthogonalMatrix.orthogonalGroup l R) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [evenBlock, Matrix.one_apply]

/-- The determinant-corrected block construction is multiplicative. -/
theorem evenBlock_mul (g h : OrthogonalMatrix.orthogonalGroup l R) :
    evenBlock (g * h) = evenBlock g * evenBlock h := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [evenBlock, Matrix.mul_apply, Matrix.det_mul]

/-- The determinant-corrected even block as an actual matrix-unit homomorphism. -/
def evenUnits : OrthogonalMatrix.orthogonalGroup l R →* (Matrix (Index l) (Index l) R)ˣ where
  toFun g :=
    { val := evenBlock g
      inv := evenBlock g⁻¹
      val_inv := by rw [← evenBlock_mul, mul_inv_cancel, evenBlock_one]
      inv_val := by rw [← evenBlock_mul, inv_mul_cancel, evenBlock_one] }
  map_one' := Units.ext evenBlock_one
  map_mul' g h := Units.ext (evenBlock_mul g h)

/-- The odd block has determinant one, including in characteristic two. -/
theorem det_evenBlock (g : OrthogonalMatrix.orthogonalGroup l R) : (evenBlock g).det = 1 := by
  rw [evenBlock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique]
  exact even_det_mul_self g

/-- The coefficient-ring construction commutes with every ring homomorphism. -/
theorem evenBlock_map {S : Type*} [CommRing S] (f : R →+* S)
    (g : OrthogonalMatrix.orthogonalGroup l R) :
    (evenBlock g).map f = evenBlock (OrthogonalMatrix.map l f g) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [evenBlock, Matrix.map_apply, RingHom.map_det]

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]

/-- The determinant-corrected even block preserves the actual odd form modulo
alternating matrices over every coefficient algebra. -/
theorem isAlt_evenBlock_defect (g : OrthogonalMatrix.orthogonalGroup l A) :
    OrthogonalMatrix.IsAlt (evenBlock g * (formMatrix l K).map (algebraMap K A) *
      (evenBlock g).transpose - (formMatrix l K).map (algebraMap K A)) := by
  obtain ⟨U, hU⟩ := g.property
  refine ⟨Matrix.fromBlocks (0 : Matrix Unit Unit A) 0 0 U, ?_⟩
  have hd := even_det_mul_self g
  have hmap : (formMatrix l K).map (algebraMap K A) =
      Matrix.fromBlocks (1 : Matrix Unit Unit A) 0 0 (OrthogonalMatrix.formMatrix l A) := by
    simp [formMatrix, Matrix.fromBlocks_map, OrthogonalMatrix.formMatrix_map]
  rw [hmap]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · cases i; cases j
    simpa [evenBlock, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      Matrix.mul_apply] using sub_eq_zero.mpr hd
  · simp [evenBlock, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose]
  · simp [evenBlock, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose]
  · have hh := congrFun (congrFun hU i) j
    simpa [evenBlock, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      OrthogonalMatrix.defect] using hh

variable (K : Type u) [Field K]

local notation "𝕌" => CentralSimpleUnits.groupScheme K (Matrix (Index l) (Index l) K)
local notation "𝕆" => OrthogonalMatrix.groupScheme l (CommRingCat.of K)

/-- The determinant-corrected even orthogonal action on actual ambient points. -/
def evenPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (𝕆).X) →* (T ⟶ (𝕌).X) :=
  (FiniteAlgebraUnits.pointsEquiv
    (Module.finBasis K (Matrix (Index l) (Index l) K)) T).symm.toMonoidHom.comp
      ((Units.mapEquiv (matrixEquiv (n := Index l) K
        ((algΓ (CommRingCat.of K)).obj T).unop).symm.toMulEquiv).toMonoidHom.comp
          (evenUnits.comp (OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) T).toMonoidHom))

/-- The actual coefficient matrix of the even orthogonal action. -/
theorem ambientMatrix_evenPoints (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (𝕆).X) :
    ambientMatrix K T (evenPoints K T x) =
      evenBlock (OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) T x) := by
  unfold ambientMatrix evenPoints
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  change matrixEquiv (n := Index l) K _ ((matrixEquiv (n := Index l) K _).symm _) = _
  exact (matrixEquiv (n := Index l) K _).apply_symm_apply _

/-- The even action is natural on all actual relative tests. -/
theorem evenPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (b : T' ⟶ T)
    (x : T ⟶ (𝕆).X) : evenPoints K T' (b ≫ x) = b ≫ evenPoints K T x := by
  apply ambientMatrix_injective K T'
  rw [ambientMatrix_naturality, ambientMatrix_evenPoints, ambientMatrix_evenPoints,
    OrthogonalMatrix.pointsEquiv_naturality]
  change evenBlock (OrthogonalMatrix.map l b.left.appTop.hom
    (OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) T x)) =
      (evenBlock (OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) T x)).map b.left.appTop.hom
  exact (evenBlock_map _ _).symm

/-- The actual determinant-corrected even orthogonal morphism into ambient units. -/
def ambientEvenMap : 𝕆 ⟶ 𝕌 := homOfPoints (evenPoints K) (evenPoints_naturality K)

/-- The coefficient matrix of the actual even morphism. -/
theorem ambientMatrix_ambientEvenMap {T : Over (Spec (CommRingCat.of K))} (x : T ⟶ (𝕆).X) :
    ambientMatrix K T (x ≫ (ambientEvenMap (l := l) K).hom.hom) =
      evenBlock (OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) T x) := by
  rw [ambientEvenMap, comp_homOfPoints, ambientMatrix_evenPoints]

instance mono_ambientEvenMap : Mono (ambientEvenMap (l := l) K).hom.hom := by
  constructor
  intro T x y h
  apply (OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) T).injective
  apply Subtype.ext
  funext i j
  have hm := congrArg (ambientMatrix K T) h
  rw [ambientMatrix_ambientEvenMap, ambientMatrix_ambientEvenMap] at hm
  exact congrArg (fun M : Matrix (Index l) (Index l) Γ(T.left, ⊤) =>
    M (Sum.inr i) (Sum.inr j)) hm

/-- The entire even orthogonal group factors through the odd norm-one group. -/
theorem exists_evenMap : ∃ f : 𝕆 ⟶ groupScheme l K,
    f ≫ (scalar K).normOneIsometryAmbientι (form l K) = ambientEvenMap K := by
  let j := ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom
  have hmem : (ambientEvenMap K).hom.hom ∈
      (SubgroupFunctor.range ((scalar K).normOneIsometryAmbientι (form l K))).carrier (𝕆).X := by
    rw [Quaternionic.ScalarMatrixCoordinates.mem_range_normOneIsometryAmbientι_iff K
      (form l K) (formMatrix l K) rfl]
    change OrthogonalMatrix.IsAlt (ambientMatrix K (𝕆).X (ambientEvenMap K).hom.hom *
      (formMatrix l K).map (algebraMap K _) *
      (ambientMatrix K (𝕆).X (ambientEvenMap K).hom.hom).transpose -
      (formMatrix l K).map (algebraMap K _)) ∧
      (ambientMatrix K (𝕆).X (ambientEvenMap K).hom.hom).det = 1
    have hm := ambientMatrix_ambientEvenMap K (𝟙 (𝕆).X)
    simp only [Category.id_comp] at hm
    rw [hm]
    exact ⟨isAlt_evenBlock_defect _, det_evenBlock _⟩
  obtain ⟨f, hf⟩ := SubgroupFunctor.mem_range.mp hmem
  let : IsMonHom f :=
    { one_hom := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hf, IsMonHom.one_hom, IsMonHom.one_hom]
      mul_hom := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hf, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
          CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc, hf] }
  exact ⟨Grp.homMk f, Grp.hom_ext _ _ hf⟩

/-- The actual determinant-corrected inclusion of the even group in the odd group. -/
def evenMap : 𝕆 ⟶ groupScheme l K := Classical.choose (exists_evenMap (l := l) K)

@[reassoc (attr := simp)] theorem evenMap_comp :
    evenMap K ≫ (scalar K).normOneIsometryAmbientι (form l K) = ambientEvenMap K :=
  Classical.choose_spec (exists_evenMap K)

instance mono_evenMap : Mono (evenMap (l := l) K).hom.hom := by
  have hm : Mono (evenMap K ≫
      (scalar K).normOneIsometryAmbientι (form l K)).hom.hom := by
    rw [evenMap_comp]
    infer_instance
  change Mono ((evenMap K).hom.hom ≫
    ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom) at hm
  exact mono_of_mono _ ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom

end Langlands.GroupScheme.OddOrthogonalMatrix
