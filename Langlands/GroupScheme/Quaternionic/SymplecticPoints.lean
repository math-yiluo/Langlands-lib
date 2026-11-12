import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.RepresentedSubgroupTransport
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.FiniteAlgebraMatrixPoints

/-!
# Points of the quaternionic symplectic group in the matrix-algebra unit group

For an involution of the first kind `σ` of a central division algebra `D` over a field `K` and
a Gram matrix `H ∈ M_n(D)`, the symplectic group `σ.symplecticGroup H` is a closed subgroup of
the unit group scheme of `M_n(D)` through `symplecticAmbientι`. On every test scheme `T`, with
coefficient algebra `R`, a point `x` of the unit group lies in it exactly when its unit
`X ∈ (R ⊗ M_n(D))ˣ` satisfies `X (1 ⊗ H) ᵗX^σ = 1 ⊗ H` and its reduced norm is `1`.

Conjugation by a constant unit `P` of `M_n(D)` is an automorphism of the unit group scheme. It
carries the symplectic group of `H` onto that of `P H ᵗP^σ`, which gives an isomorphism of
group schemes `symplecticGroupCongr`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution

section Algebra

variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B] (τ : FirstKindInvolution R B)

/-- Conjugation by a unit `q` carries isometries of `h` to isometries of `q h τ(q)`. -/
theorem conj_isometry_iff (q x : Bˣ) (h : B) :
    ((q * x * q⁻¹ : Bˣ) : B) * (q * h * τ q) * τ ((q * x * q⁻¹ : Bˣ) : B) = q * h * τ q ↔
      (x : B) * h * τ x = h := by
  have hτ' : τ (q : B) * τ ((q⁻¹ : Bˣ) : B) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have c : ∀ z : B, ((q⁻¹ : Bˣ) : B) * (q * z * τ q) * τ ((q⁻¹ : Bˣ) : B) = z := by
    intro z
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [hτ', mul_one]
  have e : ((q * x * q⁻¹ : Bˣ) : B) * (q * h * τ q) * τ ((q * x * q⁻¹ : Bˣ) : B) =
      q * ((x : B) * h * τ x) * τ q := by
    simp only [Units.val_mul, map_mul, mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc (τ (q : B)), hτ', one_mul]
  rw [e]
  constructor
  · intro h1
    calc (x : B) * h * τ x
        = ((q⁻¹ : Bˣ) : B) * (q * ((x : B) * h * τ x) * τ q) * τ ((q⁻¹ : Bˣ) : B) := (c _).symm
      _ = ((q⁻¹ : Bˣ) : B) * (q * h * τ q) * τ ((q⁻¹ : Bˣ) : B) := by rw [h1]
      _ = h := c h
  · intro h1
    rw [h1]

end Algebra

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]
  [Nonempty n]

variable (K D n) in
/-- The unit group scheme of `M_n(D)`, with its canonical coordinates. -/
abbrev ambientUnits : GroupScheme (Spec (CommRingCat.of K)) :=
  CentralSimpleUnits.groupScheme K (Matrix n n D)

/-- The inclusion of the symplectic group in the unit group scheme of `M_n(D)`. -/
def symplecticAmbientι (H : Matrix n n D) : σ.symplecticGroup H ⟶ ambientUnits K D n :=
  σ.symplecticGroupι H ≫ σ.unitaryGroupι H

instance mono_unitaryGroupι (H : Matrix n n D) : Mono (σ.unitaryGroupι H).hom.hom := by
  have : IsClosedImmersion (σ.unitaryGroupι H).hom.hom.left :=
    σ.isClosedSubgroup_unitaryGroupι H
  exact Over.mono_of_mono_left _

instance mono_symplecticAmbientι (H : Matrix n n D) :
    Mono (σ.symplecticAmbientι H).hom.hom := by
  have : Mono (σ.symplecticGroupι H).hom.hom := kernelι_mono _
  rw [symplecticAmbientι, Grp.comp_hom_hom]
  infer_instance

theorem isClosedSubgroup_symplecticGroupι (H : Matrix n n D) :
    IsClosedSubgroup (σ.symplecticGroupι H) := by
  have : IsSeparated (Gm (Spec (CommRingCat.of K))).X.hom := by
    have : IsSeparated Gm.overSpecZ.{u}.hom := by
      change IsSeparated (Spec.map _)
      infer_instance
    change IsSeparated (Limits.pullback.snd _ (Gm.toSpecZ _))
    infer_instance
  exact kernelι_isClosedImmersion _

theorem isClosedSubgroup_symplecticAmbientι (H : Matrix n n D) :
    IsClosedSubgroup (σ.symplecticAmbientι H) :=
  (σ.isClosedSubgroup_symplecticGroupι H).comp (σ.isClosedSubgroup_unitaryGroupι H)

theorem isRepresentedBy_symplecticAmbientι (H : Matrix n n D) :
    (SubgroupFunctor.range (σ.symplecticAmbientι H)).IsRepresentedBy (σ.symplecticAmbientι H) :=
  ⟨inferInstance, rfl⟩

/-- A point of the unitary group lies in the symplectic group exactly when its reduced norm
is one. -/
theorem mem_range_symplecticGroupι_iff (H : Matrix n n D) {T : Over (Spec (CommRingCat.of K))}
    (y : T ⟶ (σ.unitaryGroup H).X) :
    y ∈ (SubgroupFunctor.range (σ.symplecticGroupι H)).carrier T ↔
      y ≫ (σ.unitaryGroupι H).hom.hom ≫
        (CentralSimpleUnits.reducedNormHom K (Matrix n n D)).hom.hom = 1 := by
  have h := mem_range_kernelι_iff
    (σ.unitaryGroupι H ≫ CentralSimpleUnits.reducedNormHom K (Matrix n n D)) y
  rw [Grp.comp_hom_hom] at h
  exact h

/-- A point of the unit group lies in the symplectic group exactly when it lies in the unitary
group and has reduced norm one. -/
theorem mem_range_symplecticAmbientι_iff (H : Matrix n n D)
    {T : Over (Spec (CommRingCat.of K))} (x : T ⟶ (ambientUnits K D n).X) :
    x ∈ (SubgroupFunctor.range (σ.symplecticAmbientι H)).carrier T ↔
      x ∈ (SubgroupFunctor.range (σ.unitaryGroupι H)).carrier T ∧
        x ≫ (CentralSimpleUnits.reducedNormHom K (Matrix n n D)).hom.hom = 1 := by
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range, symplecticAmbientι,
    Grp.comp_hom_hom]
  constructor
  · rintro ⟨y, rfl⟩
    have hk := (σ.mem_range_symplecticGroupι_iff H (y ≫ (σ.symplecticGroupι H).hom.hom)).1
      (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)
    refine ⟨⟨y ≫ (σ.symplecticGroupι H).hom.hom, (Category.assoc _ _ _)⟩, ?_⟩
    simpa only [Category.assoc] using hk
  · rintro ⟨⟨y, rfl⟩, hN⟩
    have hk := (σ.mem_range_symplecticGroupι_iff H y).2 (by
      rw [← Category.assoc]
      exact hN)
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 hk
    exact ⟨z, (Category.assoc _ _ _).symm⟩

/-! ### Matrix coordinates of the isometry equation -/

section Coefficients

open FiniteAlgebraUnits.MatrixPoints

variable (R : Type u) [CommRing R] [Algebra K R]

omit [FiniteDimensional K D] [Algebra.IsCentral K D] [Nonempty n] in
/-- The matrix comparison `R ⊗ M_n(D) ≃ M_n(R ⊗ D)` intertwines the involutions. -/
theorem coefficientEquiv_matrix_baseChange (x : R ⊗[K] Matrix n n D) :
    coefficientEquiv K D R ((σ.matrix n).baseChange R x) =
      (σ.baseChange R).matrix n (coefficientEquiv K D R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    ext i j
    rw [baseChange_tmul, matrix_apply, coefficientEquiv_tmul, coefficientEquiv_tmul,
      matrix_apply, baseChange_tmul]
  | add x y hx hy =>
    simp only [_root_.map_add, hx, hy]

omit [FiniteDimensional K D] [Algebra.IsCentral K D] [Nonempty n] in
theorem coefficientEquiv_one_tmul_eq_map (M : Matrix n n D) :
    coefficientEquiv K D R ((1 : R) ⊗ₜ[K] M) =
      M.map (Algebra.TensorProduct.includeRight : D →ₐ[K] R ⊗[K] D) := by
  ext i j
  rw [coefficientEquiv_tmul, Matrix.map_apply, Algebra.TensorProduct.includeRight_apply]

omit [FiniteDimensional K D] [Algebra.IsCentral K D] [Nonempty n] in
/-- The isometry equation in `R ⊗ M_n(D)` is the isometry equation of the corresponding matrix
over `R ⊗ D`. -/
theorem isometry_iff_coefficientEquiv (H : Matrix n n D) (X : R ⊗[K] Matrix n n D) :
    X * ((1 : R) ⊗ₜ[K] H) * (σ.matrix n).baseChange R X = (1 : R) ⊗ₜ[K] H ↔
      coefficientEquiv K D R X *
          H.map (Algebra.TensorProduct.includeRight : D →ₐ[K] R ⊗[K] D) *
          (σ.baseChange R).matrix n (coefficientEquiv K D R X) =
        H.map (Algebra.TensorProduct.includeRight : D →ₐ[K] R ⊗[K] D) := by
  rw [← (coefficientEquiv (m := n) K D R).injective.eq_iff, _root_.map_mul, _root_.map_mul,
    coefficientEquiv_matrix_baseChange, coefficientEquiv_one_tmul_eq_map]

end Coefficients

/-! ### Conjugation by a constant unit -/

section Conjugation

/-- Conjugation does not change a value in the multiplicative group. -/
theorem conj_comp_gm_eq_one_iff {G : GroupScheme (Spec (CommRingCat.of K))}
    (f : G ⟶ (Gm (Spec (CommRingCat.of K))).toGrp) {T : Over (Spec (CommRingCat.of K))}
    (p x : T ⟶ G.X) : (p * x * p⁻¹) ≫ f.hom.hom = 1 ↔ x ≫ f.hom.hom = 1 := by
  have e : (p * x * p⁻¹) ≫ f.hom.hom = x ≫ f.hom.hom := by
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    apply (Gm.pointsEquiv (Spec (CommRingCat.of K)) T).injective
    rw [_root_.map_mul, _root_.map_mul, _root_.map_inv]
    exact mul_inv_cancel_comm _ _
  rw [e]

variable (P : (Matrix n n D)ˣ)

/-- The constant point `1 ⊗ P` of the unit group of `M_n(D)` on every test. -/
def constPoint (T : Over (Spec (CommRingCat.of K))) : T ⟶ (ambientUnits K D n).X :=
  (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T).symm
    (Units.map (Algebra.TensorProduct.includeRight :
      Matrix n n D →ₐ[K] ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D).toMonoidHom P)

omit [Algebra.IsCentral K D] [Nonempty n] in
theorem pointsEquiv_constPoint (T : Over (Spec (CommRingCat.of K))) :
    FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T (constPoint P T) =
      Units.map (Algebra.TensorProduct.includeRight :
        Matrix n n D →ₐ[K] ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D).toMonoidHom
        P :=
  MulEquiv.apply_symm_apply _ _

omit [Algebra.IsCentral K D] [Nonempty n] in
theorem comp_constPoint {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) :
    a ≫ constPoint P T = constPoint P T' := by
  apply (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T').injective
  rw [FiniteAlgebraUnits.pointsEquiv_naturality, pointsEquiv_constPoint, pointsEquiv_constPoint]
  apply Units.ext
  change Algebra.TensorProduct.map _ (AlgHom.id K (Matrix n n D)) (1 ⊗ₜ[K] (P : Matrix n n D)) =
    1 ⊗ₜ[K] (P : Matrix n n D)
  rw [Algebra.TensorProduct.map_tmul, _root_.map_one, AlgHom.id_apply]

/-- Conjugation by the constant point `1 ⊗ P` on every point group. -/
def conjPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (ambientUnits K D n).X) ≃* (T ⟶ (ambientUnits K D n).X) :=
  MulAut.conj (constPoint P T)

omit [Algebra.IsCentral K D] [Nonempty n] in
theorem conjPoints_apply {T : Over (Spec (CommRingCat.of K))} (x : T ⟶ (ambientUnits K D n).X) :
    conjPoints P T x = constPoint P T * x * (constPoint P T)⁻¹ :=
  rfl

omit [Algebra.IsCentral K D] [Nonempty n] in
theorem conjPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (ambientUnits K D n).X) :
    conjPoints P T' (a ≫ x) = a ≫ conjPoints P T x := by
  rw [conjPoints_apply, conjPoints_apply, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
    comp_constPoint]

/-- Conjugation by `P`, an automorphism of the unit group scheme of `M_n(D)`. -/
def conjIso : ambientUnits K D n ≅ ambientUnits K D n :=
  isoOfPoints (conjPoints P) (conjPoints_naturality P)

omit [Algebra.IsCentral K D] [Nonempty n] in
theorem comp_conjIso_hom {T : Over (Spec (CommRingCat.of K))} (x : T ⟶ (ambientUnits K D n).X) :
    x ≫ (conjIso P).hom.hom.hom = constPoint P T * x * (constPoint P T)⁻¹ :=
  comp_isoOfPoints_hom _ _ T x

/-- Conjugation by `P` carries the symplectic group of `H` onto that of `P H ᵗP^σ`. -/
theorem comap_conjIso (H : Matrix n n D) :
    (SubgroupFunctor.range
        (σ.symplecticAmbientι ((P : Matrix n n D) * H * σ.matrix n (P : Matrix n n D)))).comap
        (conjIso P).hom =
      SubgroupFunctor.range (σ.symplecticAmbientι H) := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.mem_comap, comp_conjIso_hom, mem_range_symplecticAmbientι_iff,
    mem_range_symplecticAmbientι_iff, mem_range_unitaryGroupι_iff, mem_range_unitaryGroupι_iff,
    conj_comp_gm_eq_one_iff]
  refine and_congr ?_ Iff.rfl
  rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, pointsEquiv_constPoint]
  have e : (1 : ((algΓ (CommRingCat.of K)).obj T).unop) ⊗ₜ[K]
      ((P : Matrix n n D) * H * σ.matrix n (P : Matrix n n D)) =
      ((Units.map (Algebra.TensorProduct.includeRight : Matrix n n D →ₐ[K]
          ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D).toMonoidHom P :
          (((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D)ˣ) :
        ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D) * (1 ⊗ₜ[K] H) *
      (σ.matrix n).baseChange ((algΓ (CommRingCat.of K)).obj T).unop
        ((Units.map (Algebra.TensorProduct.includeRight : Matrix n n D →ₐ[K]
          ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D).toMonoidHom P :
          (((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D)ˣ) :
        ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D) := by
    change _ = (1 ⊗ₜ[K] (P : Matrix n n D)) * (1 ⊗ₜ[K] H) *
      (σ.matrix n).baseChange _ (1 ⊗ₜ[K] (P : Matrix n n D))
    rw [baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, one_mul]
  rw [e]
  exact conj_isometry_iff _ _ _ _

/-- The symplectic groups of `H` and of `P H ᵗP^σ` are isomorphic, compatibly with conjugation by
`P` in the unit group of `M_n(D)`. -/
def symplecticGroupCongr (H : Matrix n n D) :
    σ.symplecticGroup H ≅
      σ.symplecticGroup ((P : Matrix n n D) * H * σ.matrix n (P : Matrix n n D)) :=
  SubgroupFunctor.IsRepresentedBy.isoOfComap (σ.isRepresentedBy_symplecticAmbientι H)
    (σ.isRepresentedBy_symplecticAmbientι _) (conjIso P) (σ.comap_conjIso P H)

end Conjugation

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
