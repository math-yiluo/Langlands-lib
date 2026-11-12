import Langlands.GroupScheme.Quaternionic.SymplecticCocharacter
import Langlands.GroupScheme.Quaternionic.UnitaryMatrices
import Langlands.GroupScheme.CentralSimpleBinaryGeneration
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.ImproperParabolic
import Langlands.GroupScheme.Rational.EndpointReductions

/-!
# Rational points of quaternionic symplectic groups as matrices

The rational points of the symplectic group `G = σ.symplecticGroup H` embed into `GL_n(D)` by
`rationalMatrix`, with image in the isometries of `H`. If the cocharacter with weight
`w = pairWeight a b` factors through `G` (`symplecticCocharacter`), every isometry `u ∈ GL_n(D)` of
contracting shape for `w` is the matrix of a rational point of `G` in the dynamic unipotent
subgroup of this cocharacter: its point in the unit group of `M_n(D)` contracts by
`mem_unipotent_of_contracting`, it lies in the unitary group, and its reduced norm is a
contracting point of `𝔾_m` for the trivial cocharacter, hence `1`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic

open FiniteAlgebraUnits FiniteAlgebraUnits.WeightedRoot CentralSimpleUnits.BinaryRoot
  GaloisPointComparison

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ### The base affine test -/

/-- The rational/affine comparison is precomposition with the canonical test isomorphism. -/
theorem rationalCoeffEquiv_eq_comp' {G : GroupScheme (Spec (CommRingCat.of K))}
    (x : rationalPoints G) :
    rationalCoeffEquiv K G x =
      (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso K).hom ≫ x := by
  apply Over.OverMorphism.ext
  rw [rationalCoeffEquiv_left, Over.comp_left]
  exact (Category.id_comp _).symm

/-- A rational point lies in a subgroup functor exactly when its base affine point does. -/
theorem mem_carrier_iff_rationalCoeffEquiv {G : GroupScheme (Spec (CommRingCat.of K))}
    (F : SubgroupFunctor G) (x : rationalPoints G) :
    x ∈ F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ↔
      rationalCoeffEquiv K G x ∈ F.carrier (baseAffineTest K) := by
  rw [rationalCoeffEquiv_eq_comp']
  constructor
  · exact F.comp_mem _
  · intro h
    have h' := F.comp_mem (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso K).inv h
    rwa [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h'

omit [Algebra.IsCentral K D] [Nonempty n] in
/-- The base affine unit coordinates agree with the section matrix coordinates. -/
theorem affine_base_matrix_eq (y : baseAffineTest K ⟶ (FirstKindInvolution.ambientUnits K D n).X) :
    Units.map (Algebra.TensorProduct.lid K (Matrix n n D)).toMonoidHom
        (affinePointsEquiv (Module.finBasis K (Matrix n n D))
          (CommAlgCat.of (CommRingCat.of K) K) y) =
      Units.map (RingHom.mapMatrix (baseSectionsTensorEquiv K D).toRingHom).toMonoidHom
        (MatrixPoints.tensorMatrixEquiv K D (Module.finBasis K (Matrix n n D))
          (baseAffineTest K) y) := by
  let S := CommAlgCat.of (CommRingCat.of K) K
  let f := (Corepresented.affineSectionsIso S).hom.hom
  have hp := Corepresented.map_affineSectionsIso_pointsEquiv
    (FiniteAlgebraUnits.functor K (Matrix n n D))
    (corepresentableBy (Module.finBasis K (Matrix n n D))) S y
  apply Units.ext
  have hpv := congrArg Units.val hp
  change Algebra.TensorProduct.map f (AlgHom.id K (Matrix n n D))
      (pointsEquiv (Module.finBasis K (Matrix n n D)) (baseAffineTest K) y :
        ((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop ⊗[K] Matrix n n D) =
    (affinePointsEquiv (Module.finBasis K (Matrix n n D)) S y : K ⊗[K] Matrix n n D) at hpv
  change Algebra.TensorProduct.lid K (Matrix n n D)
      (affinePointsEquiv (Module.finBasis K (Matrix n n D)) S y : K ⊗[K] Matrix n n D) =
    (MatrixPoints.coefficientEquiv K D _
      (pointsEquiv (Module.finBasis K (Matrix n n D)) (baseAffineTest K) y :
        ((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop ⊗[K]
          Matrix n n D)).map (baseSectionsTensorEquiv K D)
  rw [← hpv, ← MatrixPoints.coefficientEquiv_lid, MatrixPoints.coefficientEquiv_naturality]
  rfl

omit [Algebra.IsCentral K D] [Nonempty n] in
/-- The rational unit of a rational point is its base section matrix. -/
theorem rationalPointsEquiv_eq (z : rationalPoints (FirstKindInvolution.ambientUnits K D n)) :
    rationalPointsEquiv (Module.finBasis K (Matrix n n D)) z =
      Units.map (RingHom.mapMatrix (baseSectionsTensorEquiv K D).toRingHom).toMonoidHom
        (MatrixPoints.tensorMatrixEquiv K D (Module.finBasis K (Matrix n n D))
          (baseAffineTest K) (rationalCoeffEquiv K _ z)) :=
  affine_base_matrix_eq _

namespace FirstKindInvolution

variable (σ : FirstKindInvolution K D)

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
/-- The base section comparison intertwines the involutions. -/
theorem baseSectionsTensorEquiv_baseChange
    (x : ((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop ⊗[K] D) :
    baseSectionsTensorEquiv K D
        (σ.baseChange ((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop x) =
      σ (baseSectionsTensorEquiv K D x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r d =>
    rw [baseChange_tmul]
    change Algebra.TensorProduct.lid K D (_ ⊗ₜ[K] σ d) =
      σ (Algebra.TensorProduct.lid K D (_ ⊗ₜ[K] d))
    rw [Algebra.TensorProduct.lid_tmul, Algebra.TensorProduct.lid_tmul, map_smul]
  | add x y hx hy =>
    rw [map_add, _root_.map_add, hx, hy, _root_.map_add, map_add]

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
theorem baseSectionsTensorEquiv_includeRight (d : D) :
    baseSectionsTensorEquiv K D
      ((Algebra.TensorProduct.includeRight :
        D →ₐ[K] ((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop ⊗[K] D) d) = d := by
  rw [Algebra.TensorProduct.includeRight_apply, baseSectionsTensorEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.lid_tmul]
  simp

omit [Algebra.IsCentral K D] [Nonempty n] in
/-- A base affine point lies in the unitary group exactly when its section matrix is an
isometry of `H`. -/
theorem mem_range_unitaryGroupι_baseAffine_iff (H : Matrix n n D)
    (y : baseAffineTest K ⟶ (ambientUnits K D n).X) :
    y ∈ (SubgroupFunctor.range (σ.unitaryGroupι H)).carrier (baseAffineTest K) ↔
      ((Units.map (RingHom.mapMatrix (baseSectionsTensorEquiv K D).toRingHom).toMonoidHom
          (MatrixPoints.tensorMatrixEquiv K D (Module.finBasis K (Matrix n n D))
            (baseAffineTest K) y) : (Matrix n n D)ˣ) : Matrix n n D) * H *
        σ.matrix n ((Units.map
          (RingHom.mapMatrix (baseSectionsTensorEquiv K D).toRingHom).toMonoidHom
          (MatrixPoints.tensorMatrixEquiv K D (Module.finBasis K (Matrix n n D))
            (baseAffineTest K) y) : (Matrix n n D)ˣ) : Matrix n n D) = H := by
  rw [mem_range_unitaryGroupι_iff, isometry_iff_coefficientEquiv, ← tensorMatrixEquiv_val_eq]
  set X := ((MatrixPoints.tensorMatrixEquiv K D (Module.finBasis K (Matrix n n D))
    (baseAffineTest K) y : Matrix.GeneralLinearGroup n
      (((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop ⊗[K] D)) :
      Matrix n n (((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop ⊗[K] D))
  set Φ := RingHom.mapMatrix (m := n) (baseSectionsTensorEquiv K D).toRingHom
  have hΦ : Function.Injective Φ := fun M N h => by
    ext i j
    exact (baseSectionsTensorEquiv K D).injective (congrFun (congrFun h i) j)
  have hH : Φ (H.map (Algebra.TensorProduct.includeRight :
      D →ₐ[K] ((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop ⊗[K] D)) = H := by
    ext i j
    exact baseSectionsTensorEquiv_includeRight _
  have hσ : Φ ((σ.baseChange ((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop).matrix n X) =
      σ.matrix n (Φ X) := by
    ext i j
    exact σ.baseSectionsTensorEquiv_baseChange _
  rw [← hΦ.eq_iff, _root_.map_mul, _root_.map_mul, hH, hσ]
  rfl

/-- The matrix of a rational point of the symplectic group. -/
def rationalMatrix (H : Matrix n n D) : rationalPoints (σ.symplecticGroup H) →* (Matrix n n D)ˣ :=
  (rationalPointsEquiv (Module.finBasis K (Matrix n n D))).toMonoidHom.comp
    (rationalPoints.map (σ.symplecticAmbientι H))

theorem rationalMatrix_apply (H : Matrix n n D) (x : rationalPoints (σ.symplecticGroup H)) :
    σ.rationalMatrix H x =
      rationalPointsEquiv (Module.finBasis K (Matrix n n D))
        (x ≫ (σ.symplecticAmbientι H).hom.hom) :=
  rfl

theorem rationalMatrix_injective (H : Matrix n n D) : Function.Injective (σ.rationalMatrix H) := by
  intro x y h
  exact (cancel_mono (σ.symplecticAmbientι H).hom.hom).1 ((rationalPointsEquiv _).injective h)

/-- The matrix of a rational point is an isometry of `H`. -/
theorem rationalMatrix_mem (H : Matrix n n D) (x : rationalPoints (σ.symplecticGroup H)) :
    σ.rationalMatrix H x ∈ σ.unitaryMatrixGroup H := by
  rw [mem_unitaryMatrixGroup, rationalMatrix_apply, rationalPointsEquiv_eq,
    ← mem_range_unitaryGroupι_baseAffine_iff, ← mem_carrier_iff_rationalCoeffEquiv]
  exact ((σ.mem_range_symplecticAmbientι_iff H _).1 (SubgroupFunctor.mem_range.2 ⟨x, rfl⟩)).1

/-- **Contracting rational points.** An isometry of `H₀` of contracting shape for the weight
`pairWeight a b` is the matrix of a rational point of the symplectic group lying in the dynamic
unipotent subgroup of the corresponding cocharacter. -/
theorem exists_rationalMatrix_eq_of_contracting (H₀ : Matrix n n D) (a b : n) (hab : a ≠ b)
    (hH : ∀ i j, H₀ i j ≠ 0 → pairWeight a b i + pairWeight a b j = 0)
    (u : (Matrix n n D)ˣ) (hu : u ∈ σ.unitaryMatrixGroup H₀)
    (hc : IsContracting (pairWeight a b) (u : Matrix n n D)) :
    ∃ y ∈ (Dynamic.unipotent (σ.symplecticCocharacter H₀ a b hH)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of K)))),
      σ.rationalMatrix H₀ y = u := by
  have : IsSeparated (Gm (Spec (CommRingCat.of K))).X.hom := by
    have : IsSeparated Gm.overSpecZ.{u}.hom := by
      change IsSeparated (Spec.map _)
      infer_instance
    change IsSeparated (Limits.pullback.snd _ (Gm.toSpecZ _))
    infer_instance
  set z := (rationalPointsEquiv (Module.finBasis K (Matrix n n D))).symm u with hzdef
  have hz : rationalPointsEquiv (Module.finBasis K (Matrix n n D)) z = u :=
    MulEquiv.apply_symm_apply _ _
  set M₁ := MatrixPoints.tensorMatrixEquiv K D (Module.finBasis K (Matrix n n D))
    (baseAffineTest K) (rationalCoeffEquiv K _ z) with hM₁
  have hM : Units.map (RingHom.mapMatrix (baseSectionsTensorEquiv K D).toRingHom).toMonoidHom
      M₁ = u := by
    rw [← hz, rationalPointsEquiv_eq]
  have hshape : ∀ i j, pairWeight a b i ≤ pairWeight a b j →
      (M₁ : Matrix n n (((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop ⊗[K] D)) i j =
        (1 : Matrix n n (((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop ⊗[K] D)) i j := by
    intro i j hij
    apply (baseSectionsTensorEquiv K D).injective
    have h1 : baseSectionsTensorEquiv K D
        ((M₁ : Matrix n n (((algΓ (CommRingCat.of K)).obj (baseAffineTest K)).unop ⊗[K] D)) i j) =
        (u : Matrix n n D) i j := by
      rw [← hM]
      rfl
    rw [h1, hc i j hij]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, _root_.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, _root_.map_zero]
  have hzdyn : z ∈ (Dynamic.unipotent (ambientCocharacter K D (pairWeight a b))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
    rw [mem_carrier_iff_rationalCoeffEquiv]
    have h := mem_unipotent_of_contracting (b := Module.finBasis K (Matrix n n D))
      (pairWeight_mem hab) M₁ hshape
    rwa [hM₁, MulEquiv.symm_apply_apply] at h
  have hzU : z ∈ (SubgroupFunctor.range (σ.unitaryGroupι H₀)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
    rw [mem_carrier_iff_rationalCoeffEquiv, mem_range_unitaryGroupι_baseAffine_iff, ← hM₁, hM]
    exact σ.mem_unitaryMatrixGroup.1 hu
  obtain ⟨zU, hzU'⟩ := SubgroupFunctor.mem_range.1 hzU
  set χ := σ.symplecticCocharacter H₀ a b hH
  have hχ : (χ ≫ σ.symplecticGroupι H₀) ≫ σ.unitaryGroupι H₀ =
      ambientCocharacter K D (pairWeight a b) := by
    rw [Category.assoc]
    exact σ.symplecticCocharacter_comp H₀ a b hH
  have hzUdyn : zU ∈ (Dynamic.unipotent (χ ≫ σ.symplecticGroupι H₀)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
    rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup (χ ≫ σ.symplecticGroupι H₀)
      (σ.unitaryGroupι H₀) (σ.isClosedSubgroup_unitaryGroupι H₀), SubgroupFunctor.mem_comap, hχ,
      hzU']
    exact hzdyn
  have htriv : (χ ≫ σ.symplecticGroupι H₀) ≫
      (σ.unitaryGroupι H₀ ≫ CentralSimpleUnits.reducedNormHom K (Matrix n n D)) =
      Dynamic.trivialCocharacter (Gm (Spec (CommRingCat.of K))).toGrp := by
    apply hom_ext_points
    intro T x
    rw [Dynamic.comp_trivialCocharacter]
    have h := (σ.mem_range_symplecticGroupι_iff H₀
      ((x ≫ χ.hom.hom) ≫ (σ.symplecticGroupι H₀).hom.hom)).1
      (SubgroupFunctor.mem_range.2 ⟨x ≫ χ.hom.hom, rfl⟩)
    simpa only [Grp.comp_hom_hom, Category.assoc] using h
  have hN : zU ≫ (σ.unitaryGroupι H₀ ≫
      CentralSimpleUnits.reducedNormHom K (Matrix n n D)).hom.hom = 1 := by
    have h1 := Dynamic.unipotent_le_comap (χ ≫ σ.symplecticGroupι H₀)
      (σ.unitaryGroupι H₀ ≫ CentralSimpleUnits.reducedNormHom K (Matrix n n D)) _ hzUdyn
    rw [SubgroupFunctor.mem_comap, htriv, Dynamic.unipotent_trivialCocharacter,
      SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at h1
    exact h1
  have hzS := (σ.mem_range_symplecticGroupι_iff H₀ zU).2 (by
    rw [Grp.comp_hom_hom] at hN
    exact hN)
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hzS
  refine ⟨y, ?_, ?_⟩
  · rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup χ (σ.symplecticGroupι H₀)
      (σ.isClosedSubgroup_symplecticGroupι H₀), SubgroupFunctor.mem_comap, hy]
    exact hzUdyn
  · rw [rationalMatrix_apply, symplecticAmbientι, Grp.comp_hom_hom, ← Category.assoc, hy, hzU',
      hz]

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
