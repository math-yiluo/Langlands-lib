import Langlands.GroupScheme.EvenOrthogonalForm.TwistedAlgebra
import Langlands.GroupScheme.SpecialLinearInnerForm.NormOneChart
import Langlands.GroupScheme.Quaternionic.IsometryCut
import Langlands.GroupScheme.LocalGroupIso

/-! # The isometry group of the descended involution through a split orthogonal chart

Let `A` be a finite-dimensional `K`-algebra with an involution of the first kind `τ`, and let
`ε : L ⊗[K] A ≃ₐ[L] M_{2n}(L)` be a splitting carrying `τ` to the orthogonal involution
`τ₀ x = J xᵀ J` of the split hyperbolic form. For a base point `a₀ ∈ A` whose image
`ε(1 ⊗ a₀)` is congruent to the projection `p = [[1, 0], [0, 0]]` modulo the alternating
elements of `τ₀`, this module shows:

* along every coefficient map `f : L → R`, the extended chart carries a unit `u` of
  `R ⊗[K] A` with `u a₀ τ(u) - a₀ ∈ R ⊗ {a - τ a}` exactly to an orthogonal matrix of the split
  form (`chartIsometryEquiv`);
* these identifications form a local isomorphism, over the points of `Spec L`, from Tits's
  isometry group scheme `IsometryCut.groupScheme` of `(A, τ, a₀)` to the split orthogonal group
  scheme (`chartLocalIso`).

For the fixed algebra of a twisted Galois action `θ_γ(x) = g_γ⁻¹ γ(x) g_γ` built from
similitudes `g_γ` (module `TwistedAlgebra`), with its descended involution and base point,
this gives `twistedChartLocalIso`, and changing the point of `Spec N` by `γ` conjugates the
chart matrices by `g_γ` (`twistedChartLocalIso_galois`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.EvenOrthogonalForm

open OrthogonalMatrix Quaternionic Langlands.CentralSimple
open SpecialLinearInnerForm (chartAlong chartAlong_tmul chartAlong_bijective chartAlong_congr
  chartAlong_naturality pointScalars pointScalars_comp_algebraMap pointScalars_comp
  pointScalars_comp_ringTestMap)

/-! ### Alternating elements of the orthogonal involution -/

section Matrices

variable {R : Type u} [CommRing R] {l : Type} [Fintype l] [DecidableEq l]

/-- The alternating elements of `τ₀` are stable under `W ↦ X W τ₀(X)`. -/
theorem mul_mul_orthogonalInvolution_mem {W : Matrix (l ⊕ l) (l ⊕ l) R}
    (hW : W ∈ (orthogonalInvolution R l).alternatingSubspace) (X : Matrix (l ⊕ l) (l ⊕ l) R) :
    X * W * orthogonalInvolution R l X ∈ (orthogonalInvolution R l).alternatingSubspace := by
  rw [FirstKindInvolution.mem_alternatingSubspace] at hW ⊢
  obtain ⟨V, rfl⟩ := hW
  refine ⟨X * V * orthogonalInvolution R l X, ?_⟩
  simp only [FirstKindInvolution.map_mul, FirstKindInvolution.apply_apply]
  noncomm_ring

/-- Entrywise application of a ring homomorphism preserves the alternating elements. -/
theorem map_mem_alternatingSubspace {S : Type u} [CommRing S] (f : R →+* S)
    {W : Matrix (l ⊕ l) (l ⊕ l) R}
    (hW : W ∈ (orthogonalInvolution R l).alternatingSubspace) :
    W.map f ∈ (orthogonalInvolution S l).alternatingSubspace := by
  rw [FirstKindInvolution.mem_alternatingSubspace] at hW ⊢
  obtain ⟨V, rfl⟩ := hW
  refine ⟨V.map f, ?_⟩
  rw [← orthogonalInvolution_map]
  ext i j
  simp

/-- If `P ≡ p` modulo the alternating elements, then `X P τ₀(X) - P` is alternating exactly
when `X` is orthogonal. -/
theorem defect_mem_alternatingSubspace_iff {P : Matrix (l ⊕ l) (l ⊕ l) R}
    (hP : P - leftProjection R l ∈ (orthogonalInvolution R l).alternatingSubspace)
    (X : Matrix (l ⊕ l) (l ⊕ l) R) :
    X * P * orthogonalInvolution R l X - P ∈ (orthogonalInvolution R l).alternatingSubspace ↔
      X ∈ orthogonalGroup l R := by
  rw [mem_orthogonalGroup_iff_projection]
  have hd : (X * P * orthogonalInvolution R l X - P) -
      (X * leftProjection R l * orthogonalInvolution R l X - leftProjection R l) =
        X * (P - leftProjection R l) * orthogonalInvolution R l X -
          (P - leftProjection R l) := by
    noncomm_ring
  have hmem : X * (P - leftProjection R l) * orthogonalInvolution R l X -
      (P - leftProjection R l) ∈ (orthogonalInvolution R l).alternatingSubspace :=
    Submodule.sub_mem _ (mul_mul_orthogonalInvolution_mem hP X) hP
  constructor
  · intro h
    have h' := Submodule.sub_mem _ h hmem
    rwa [← hd, sub_sub_cancel] at h'
  · intro h
    have h' := Submodule.add_mem _ hmem h
    rwa [← hd, sub_add_cancel] at h'

end Matrices

/-! ### The chart along a coefficient map -/

section Chart

variable {K : Type u} [Field K] {A : Type u} [Ring A] [Algebra K A]
  {L : Type u} [Field L] [Algebra K L]
  {l : Type} [Fintype l] [DecidableEq l]
  {τ : FirstKindInvolution K A}
  (ε : L ⊗[K] A ≃ₐ[L] Matrix (l ⊕ l) (l ⊕ l) L)
  (he : ∀ x, ε (τ.baseChange L x) = orthogonalInvolution L l (ε x))
  {R : Type u} [CommRing R] [Algebra K R] (f : L →+* R)
  (hf : f.comp (algebraMap K L) = algebraMap K R)

include he in
/-- Through the extended chart, the extended involution is `τ₀`. -/
theorem chartAlong_baseChange (x : R ⊗[K] A) :
    chartAlong ε f hf (τ.baseChange R x) = orthogonalInvolution R l (chartAlong ε f hf x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [FirstKindInvolution.baseChange_tmul, chartAlong_tmul, chartAlong_tmul,
      FirstKindInvolution.map_smul]
    congr 1
    have h := he (1 ⊗ₜ[K] a)
    rw [FirstKindInvolution.baseChange_tmul] at h
    rw [h, orthogonalInvolution_map]
  | add x y hx hy =>
    rw [FirstKindInvolution.map_add, map_add, hx, hy, map_add, FirstKindInvolution.map_add]

include he in
/-- The extended chart carries `R ⊗ {a - τ a}` onto the alternating elements of `τ₀`. -/
theorem mem_alternatingSubspace_baseChange_iff (y : R ⊗[K] A) :
    y ∈ τ.alternatingSubspace.baseChange R ↔
      chartAlong ε f hf y ∈ (orthogonalInvolution R l).alternatingSubspace := by
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    FirstKindInvolution.mem_alternatingSubspace, FirstKindInvolution.mem_alternatingSubspace]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨chartAlong ε f hf z, by rw [map_sub, chartAlong_baseChange ε he]⟩
  · rintro ⟨W, hW⟩
    obtain ⟨z, rfl⟩ := (chartAlong_bijective ε f hf).2 W
    refine ⟨z, (chartAlong_bijective ε f hf).1 ?_⟩
    rw [map_sub, chartAlong_baseChange ε he, hW]

include he in
/-- The chart of the defect `y a₀ τ(y) - a₀`. -/
theorem chartAlong_defect (a₀ : A) (y : R ⊗[K] A) :
    chartAlong ε f hf (IsometryCut.defect τ a₀ y) =
      chartAlong ε f hf y * (ε (1 ⊗ₜ[K] a₀)).map f *
          orthogonalInvolution R l (chartAlong ε f hf y) -
        (ε (1 ⊗ₜ[K] a₀)).map f := by
  rw [IsometryCut.defect, map_sub, map_mul, map_mul, chartAlong_baseChange ε he,
    chartAlong_tmul, one_smul]

include he in
/-- For a base point `a₀` congruent to `p` through the chart, the isometry condition
`y a₀ τ(y) - a₀ ∈ R ⊗ {a - τ a}` is orthogonality of the chart matrix. -/
theorem defect_mem_iff {a₀ : A}
    (ha₀ : ε (1 ⊗ₜ[K] a₀) - leftProjection L l ∈ (orthogonalInvolution L l).alternatingSubspace)
    (y : R ⊗[K] A) :
    IsometryCut.defect τ a₀ y ∈ τ.alternatingSubspace.baseChange R ↔
      chartAlong ε f hf y ∈ orthogonalGroup l R := by
  rw [mem_alternatingSubspace_baseChange_iff ε he f hf, chartAlong_defect ε he f hf]
  apply defect_mem_alternatingSubspace_iff
  have h := map_mem_alternatingSubspace f ha₀
  rwa [Matrix.map_sub _ (map_sub f), leftProjection_map] at h

/-- The extended chart identifies the isometry units with the orthogonal matrices. -/
def chartIsometryEquiv {a₀ : A}
    (ha₀ : ε (1 ⊗ₜ[K] a₀) - leftProjection L l ∈ (orthogonalInvolution L l).alternatingSubspace) :
    IsometryCut.isometrySubgroup (τ := τ) IsometryCut.isStable_alternatingSubspace a₀ R ≃*
      orthogonalGroup l R where
  toFun y := ⟨chartAlong ε f hf (y : (R ⊗[K] A)ˣ), (defect_mem_iff ε he f hf ha₀ _).1 y.2⟩
  invFun X := ⟨Units.map
      (AlgEquiv.ofBijective (chartAlong ε f hf) (chartAlong_bijective ε f hf)).symm.toMonoidHom
      (toGL X), by
    rw [IsometryCut.mem_isometrySubgroup, defect_mem_iff ε he f hf ha₀]
    change chartAlong ε f hf ((AlgEquiv.ofBijective (chartAlong ε f hf)
      (chartAlong_bijective ε f hf)).symm (X : Matrix (l ⊕ l) (l ⊕ l) R)) ∈ _
    rw [← AlgEquiv.ofBijective_apply _ (chartAlong_bijective ε f hf),
      AlgEquiv.apply_symm_apply]
    exact X.2⟩
  left_inv y := by
    apply Subtype.ext
    apply Units.ext
    exact (AlgEquiv.ofBijective (chartAlong ε f hf)
      (chartAlong_bijective ε f hf)).symm_apply_apply _
  right_inv X := by
    apply Subtype.ext
    exact (AlgEquiv.ofBijective (chartAlong ε f hf)
      (chartAlong_bijective ε f hf)).apply_symm_apply _
  map_mul' x y := by
    apply Subtype.ext
    exact _root_.map_mul (chartAlong ε f hf) _ _

@[simp] theorem chartIsometryEquiv_coe {a₀ : A}
    (ha₀ : ε (1 ⊗ₜ[K] a₀) - leftProjection L l ∈ (orthogonalInvolution L l).alternatingSubspace)
    (y : IsometryCut.isometrySubgroup (τ := τ) IsometryCut.isStable_alternatingSubspace a₀ R) :
    (chartIsometryEquiv ε he f hf ha₀ y : Matrix (l ⊕ l) (l ⊕ l) R) =
      chartAlong ε f hf ((y : (R ⊗[K] A)ˣ) : R ⊗[K] A) :=
  rfl

end Chart

/-! ### The local isomorphism over the points of `Spec L` -/

section Points

variable {K : Type u} [Field K] {A : Type u} [Ring A] [Algebra K A] [FiniteDimensional K A]
  {L : Type u} [Field L] [Algebra K L]
  {l : Type} [Fintype l] [DecidableEq l]
  {τ : FirstKindInvolution K A}

variable (τ) in
/-- Points of Tits's isometry group scheme of `(A, τ, a₀)` are the isometry units over the
global sections. -/
def cutPointsEquiv (a₀ : A) (V : Over (Spec (CommRingCat.of K))) :
    (V ⟶ (IsometryCut.groupScheme (τ := τ) IsometryCut.isStable_alternatingSubspace a₀).X) ≃*
      IsometryCut.isometrySubgroup (τ := τ) IsometryCut.isStable_alternatingSubspace a₀
        ((algΓ (CommRingCat.of K)).obj V).unop :=
  Corepresented.pointsEquiv
    (Corepresented.cutFunctor (IsometryCut.isCutOutBy IsometryCut.isStable_alternatingSubspace a₀))
    (Corepresented.cutCorepresentableBy
      (IsometryCut.isCutOutBy IsometryCut.isStable_alternatingSubspace a₀)) V

/-- Restricting a point applies the pullback of global sections to its isometry unit. -/
theorem cutPointsEquiv_naturality (a₀ : A) {V W : Over (Spec (CommRingCat.of K))} (t : W ⟶ V)
    (x : V ⟶ (IsometryCut.groupScheme (τ := τ) IsometryCut.isStable_alternatingSubspace a₀).X) :
    ((cutPointsEquiv τ a₀ W (t ≫ x) : (((algΓ (CommRingCat.of K)).obj W).unop ⊗[K] A)ˣ) :
        ((algΓ (CommRingCat.of K)).obj W).unop ⊗[K] A) =
      Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map t).unop.hom (AlgHom.id K A)
        ((cutPointsEquiv τ a₀ V x : (((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A)ˣ) :
          ((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A) := by
  have h := Corepresented.pointsEquiv_naturality
    (Corepresented.cutFunctor (IsometryCut.isCutOutBy IsometryCut.isStable_alternatingSubspace a₀))
    (Corepresented.cutCorepresentableBy
      (IsometryCut.isCutOutBy IsometryCut.isStable_alternatingSubspace a₀)) t x
  exact congrArg (fun y => (((y.1 : (((algΓ (CommRingCat.of K)).obj W).unop ⊗[K] A)ˣ)) :
    ((algΓ (CommRingCat.of K)).obj W).unop ⊗[K] A)) h

variable (ε : L ⊗[K] A ≃ₐ[L] Matrix (l ⊕ l) (l ⊕ l) L)
  (he : ∀ x, ε (τ.baseChange L x) = orthogonalInvolution L l (ε x))
  {a₀ : A}
  (ha₀ : ε (1 ⊗ₜ[K] a₀) - leftProjection L l ∈ (orthogonalInvolution L l).alternatingSubspace)

/-- Points of the isometry group over a point `s` of `Spec L`, as orthogonal matrices through
the chart along the scalars of `s`. -/
def chartPoints {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L) :
    (V ⟶ (IsometryCut.groupScheme (τ := τ) IsometryCut.isStable_alternatingSubspace a₀).X) ≃*
      orthogonalGroup l ((algΓ (CommRingCat.of K)).obj V).unop :=
  (cutPointsEquiv τ a₀ V).trans
    (chartIsometryEquiv ε he (pointScalars s) (pointScalars_comp_algebraMap s) ha₀)

theorem chartPoints_coe {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L)
    (x : V ⟶ (IsometryCut.groupScheme (τ := τ) IsometryCut.isStable_alternatingSubspace a₀).X) :
    (chartPoints ε he ha₀ s x : Matrix (l ⊕ l) (l ⊕ l) ((algΓ (CommRingCat.of K)).obj V).unop) =
      chartAlong ε (pointScalars s) (pointScalars_comp_algebraMap s)
        ((cutPointsEquiv τ a₀ V x : (((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A)ˣ) :
          ((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A) :=
  rfl

/-- The chart points are natural in the relative test scheme. -/
theorem chartPoints_naturality {V W : Over (Spec (CommRingCat.of K))} (t : W ⟶ V)
    (s : V ⟶ ringTest K L)
    (x : V ⟶ (IsometryCut.groupScheme (τ := τ) IsometryCut.isStable_alternatingSubspace a₀).X) :
    chartPoints ε he ha₀ (t ≫ s) (t ≫ x) =
      OrthogonalMatrix.map l t.left.appTop.hom (chartPoints ε he ha₀ s x) := by
  apply Subtype.ext
  have h := chartAlong_naturality ε (pointScalars s) (pointScalars_comp_algebraMap s)
    ((algΓ (CommRingCat.of K)).map t).unop.hom
    ((cutPointsEquiv τ a₀ V x : (((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A)ˣ) :
      ((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] A)
  have hs : pointScalars (t ≫ s) =
      ((((algΓ (CommRingCat.of K)).map t).unop.hom : _ →+* _)).comp (pointScalars s) :=
    pointScalars_comp t s
  rw [chartPoints_coe, OrthogonalMatrix.coe_map, chartPoints_coe, cutPointsEquiv_naturality]
  refine Eq.trans ?_ h
  rw [chartAlong_congr ε _ hs]

/-- The chart identifications, as a local isomorphism over the points of `Spec L` from Tits's
isometry group scheme of `(A, τ, a₀)` to the split orthogonal group scheme. -/
def chartLocalIso :
    LocalGroupIso (IsometryCut.groupScheme (τ := τ) IsometryCut.isStable_alternatingSubspace a₀)
      (OrthogonalMatrix.groupScheme l (CommRingCat.of K)) (ringTest K L) where
  toFun {V} s := (chartPoints ε he ha₀ s).trans
    (OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) V).symm
  naturality {V W} t s x := by
    apply (OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) W).injective
    change OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) W
        ((OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) W).symm
          (chartPoints ε he ha₀ (t ≫ s) (t ≫ x))) =
      OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) W
        (t ≫ (OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) V).symm
          (chartPoints ε he ha₀ s x))
    rw [MulEquiv.apply_symm_apply, OrthogonalMatrix.pointsEquiv_naturality,
      MulEquiv.apply_symm_apply, chartPoints_naturality]

/-- The orthogonal matrix of a chart point is its chart matrix. -/
theorem pointsEquiv_chartLocalIso {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L)
    (x : V ⟶ (IsometryCut.groupScheme (τ := τ) IsometryCut.isStable_alternatingSubspace a₀).X) :
    OrthogonalMatrix.pointsEquiv l (CommRingCat.of K) V ((chartLocalIso ε he ha₀).toFun s x) =
      chartPoints ε he ha₀ s x :=
  MulEquiv.apply_symm_apply _ _

end Points

/-! ### The twisted fixed algebra and its Galois law -/

section Twisted

variable {K N : Type u} [Field K] [Field N] [Algebra K N] {n : ℕ}
  (g : (N ≃ₐ[K] N) → GL (Fin n ⊕ Fin n) N)
  (hcoc : ∀ σ ρ x, twistMatrix g σ (twistMatrix g ρ x) = twistMatrix g (σ * ρ) x)
  [FiniteDimensional K N] [IsGalois K N]

/-- Along `f ∘ σ`, the chart of the fixed algebra is the chart along `f` conjugated by the
image of `g_σ`. -/
theorem chartAlong_galois {R : Type u} [CommRing R] [Algebra K R] (f : N →+* R)
    (hf : f.comp (algebraMap K N) = algebraMap K R) (σ : N ≃ₐ[K] N)
    (hf' : (f.comp (σ : N →+* N)).comp (algebraMap K N) = algebraMap K R)
    (x : R ⊗[K] (twistedAction g hcoc).fixed) :
    chartAlong (twistedAction g hcoc).descentEquiv (f.comp (σ : N →+* N)) hf' x =
      (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map f *
          chartAlong (twistedAction g hcoc).descentEquiv f hf x *
        (↑(g σ)⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map f := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [chartAlong_tmul, chartAlong_tmul, SemilinearGaloisAction.descentEquiv_one_tmul,
      Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have h : (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (f.comp (σ : N →+* N)) =
        ((a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map σ).map f := by
      ext i j
      rfl
    rw [h, map_galois_fixed g hcoc σ a, Matrix.map_mul, Matrix.map_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, Matrix.mul_add, Matrix.add_mul]

variable (hsim : ∀ σ, ∃ c : Nˣ, IsAlt ((g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) *
    formMatrix (Fin n) N * (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N)ᵀ -
      (c : N) • formMatrix (Fin n) N))

include hsim in
/-- Through the descent chart, the base point is congruent to `p` modulo the alternating
elements of `τ₀`. -/
theorem descentEquiv_basePoint_sub_mem :
    (twistedAction g hcoc).descentEquiv (1 ⊗ₜ[K] basePoint g hcoc) -
        leftProjection N (Fin n) ∈ (orthogonalInvolution N (Fin n)).alternatingSubspace := by
  rw [SemilinearGaloisAction.descentEquiv_one_tmul]
  exact basePoint_sub_mem g hcoc hsim

/-- The chart local isomorphism from Tits's isometry group scheme of the descended involution
and the base point to the split orthogonal group, over the points of `Spec N`. -/
def twistedChartLocalIso :
    LocalGroupIso
      (IsometryCut.groupScheme (τ := descendedInvolution g hcoc hsim)
        (M := (descendedInvolution g hcoc hsim).alternatingSubspace)
        IsometryCut.isStable_alternatingSubspace (basePoint g hcoc))
      (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of K)) (ringTest K N) :=
  chartLocalIso (twistedAction g hcoc).descentEquiv
    (descentEquiv_descendedInvolution g hcoc hsim) (descentEquiv_basePoint_sub_mem g hcoc hsim)

/-- The orthogonal matrix of a twisted chart point is the chart along the point's scalars of its
isometry unit. -/
theorem pointsEquiv_twistedChartLocalIso {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N)
    (x : V ⟶ (IsometryCut.groupScheme (τ := descendedInvolution g hcoc hsim)
      (M := (descendedInvolution g hcoc hsim).alternatingSubspace)
      IsometryCut.isStable_alternatingSubspace (basePoint g hcoc)).X) :
    @Eq (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ(V.left, ⊤))
      (OrthogonalMatrix.pointsEquiv (Fin n) (CommRingCat.of K) V
        ((twistedChartLocalIso g hcoc hsim).toFun s x))
      (chartAlong (twistedAction g hcoc).descentEquiv (pointScalars s)
        (pointScalars_comp_algebraMap s)
        ((cutPointsEquiv (descendedInvolution g hcoc hsim) (basePoint g hcoc) V x :
          (((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] (twistedAction g hcoc).fixed)ˣ) :
            ((algΓ (CommRingCat.of K)).obj V).unop ⊗[K] (twistedAction g hcoc).fixed)) :=
  congrArg Subtype.val (pointsEquiv_chartLocalIso (twistedAction g hcoc).descentEquiv
    (descentEquiv_descendedInvolution g hcoc hsim) (descentEquiv_basePoint_sub_mem g hcoc hsim)
    s x)

/-- The scalars `N → Γ(V, 𝒪)` of a point `s` of `Spec N`, with codomain written as the global
sections of `V` (the same map as `pointScalars s`). -/
abbrev chartScalars {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N) :
    N →+* Γ(V.left, ⊤) :=
  pointScalars s

/-- **Galois law.** Moving the point `s` of `Spec N` by `σ` conjugates the chart matrices by
the image of the similitude `g_σ`. -/
theorem twistedChartLocalIso_galois (σ : N ≃ₐ[K] N) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N)
    (x : V ⟶ (IsometryCut.groupScheme (τ := descendedInvolution g hcoc hsim)
      (M := (descendedInvolution g hcoc hsim).alternatingSubspace)
      IsometryCut.isStable_alternatingSubspace (basePoint g hcoc)).X) :
    (OrthogonalMatrix.pointsEquiv (Fin n) (CommRingCat.of K) V
        ((twistedChartLocalIso g hcoc hsim).toFun (s ≫ ringTestMap K σ.toAlgHom) x) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ(V.left, ⊤)) =
      (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (chartScalars s) *
          (OrthogonalMatrix.pointsEquiv (Fin n) (CommRingCat.of K) V
            ((twistedChartLocalIso g hcoc hsim).toFun s x) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ(V.left, ⊤)) *
        (↑(g σ)⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (chartScalars s) := by
  rw [pointsEquiv_twistedChartLocalIso, pointsEquiv_twistedChartLocalIso,
    chartAlong_congr _ _ (pointScalars_comp_ringTestMap s σ)]
  exact chartAlong_galois g hcoc (pointScalars s) (pointScalars_comp_algebraMap s) σ _ _

include hcoc hsim in
/-- The descended data, packaged: a central simple `K`-algebra with an orthogonal-type
involution `τ` split by `N` compatibly with `J`, a base point `a₀` with `a₀ + τ a₀ = 1`, and a
chart local isomorphism from Tits's isometry group scheme of `(A, τ, a₀)` to the split
orthogonal group over the points of `Spec N`, obeying the Galois law for `g`. -/
theorem exists_twistedChart [NeZero n] :
    ∃ (A : Type u) (_ : Ring A) (_ : Algebra K A) (_ : FiniteDimensional K A)
      (_ : Algebra.IsCentral K A) (_ : IsSimpleRing A) (τ : FirstKindInvolution K A)
      (e : N ⊗[K] A ≃ₐ[N] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N),
      (∀ x, e (τ.baseChange N x) * polarMatrix (Fin n) N =
        polarMatrix (Fin n) N * (e x)ᵀ) ∧
      ∃ a₀ : A, a₀ + τ a₀ = 1 ∧
        ∃ χ : LocalGroupIso
            (IsometryCut.groupScheme (IsometryCut.isStable_alternatingSubspace (τ := τ)) a₀)
            (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of K)) (ringTest K N),
          ∀ (σ : N ≃ₐ[K] N) {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N)
            (u : V ⟶ (IsometryCut.groupScheme
              (IsometryCut.isStable_alternatingSubspace (τ := τ)) a₀).X),
            (OrthogonalMatrix.pointsEquiv (Fin n) (CommRingCat.of K) V
                (χ.toFun (s ≫ ringTestMap K σ.toAlgHom) u) :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ(V.left, ⊤)) =
              (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (chartScalars s) *
                (OrthogonalMatrix.pointsEquiv (Fin n) (CommRingCat.of K) V (χ.toFun s u) :
                  Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ(V.left, ⊤)) *
                (↑(g σ)⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (chartScalars s) :=
  ⟨(twistedAction g hcoc).fixed, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, descendedInvolution g hcoc hsim, (twistedAction g hcoc).descentEquiv,
    descentEquiv_descendedInvolution_mul_polar g hcoc hsim, basePoint g hcoc,
    basePoint_add_descendedInvolution g hcoc hsim, twistedChartLocalIso g hcoc hsim,
    fun σ _ s u => twistedChartLocalIso_galois g hcoc hsim σ s u⟩

end Twisted

end Langlands.GroupScheme.EvenOrthogonalForm
