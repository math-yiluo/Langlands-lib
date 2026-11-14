import Langlands.GroupScheme.SymplecticInnerForm.AlgebraTransport
import Langlands.GroupScheme.Quaternionic.GroupSchemes

/-!
# Transport of quadratic pairs to division-form quadratic forms

Let `τ` be an involution of the first kind of a `K`-algebra `A`, and let `φ : A ≃ₐ[K] M_m(D)`
carry `τ` to the adjoint involution of an invertible `σ`-hermitian matrix `H`:
`φ (τ x) * H = H * ᵗ(φ x)^σ`. For `a₀ ∈ A`, the matrix `Q = φ(a₀) * H` defines Tits's
`σ`-quadratic form `q = [Q]`. If `a₀ + τ a₀ = 1`, the polar matrix of `q` is `H`, so `q` is
nondegenerate. For every `a₀`, the group scheme of units `u` with `u a₀ τ(u) - a₀ ∈ {a - τ a}`
is isomorphic, by tensor transport along `φ`, to the isometry group `O(q)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.OrthogonalInnerForm

open Quaternionic

section Algebra

variable {K A D : Type u} [Field K] [Ring A] [Algebra K A] [DivisionRing D] [Algebra K D]
  (τ : FirstKindInvolution K A) (σ : FirstKindInvolution K D)
  {m : Type} [Fintype m] [DecidableEq m]
  (φ : A ≃ₐ[K] Matrix m m D) (H : Matrix m m D)
  (hφ : ∀ x, φ (τ x) * H = H * σ.matrix m (φ x))

include hφ

/-- If `a₀ + τ a₀ = 1` and `H` is hermitian, the polar matrix of `[φ(a₀) * H]` is `H`. -/
theorem polar_mk_mul (hHσ : σ.matrix m H = H) {a₀ : A} (ha₀ : a₀ + τ a₀ = 1) :
    σ.polar (Submodule.Quotient.mk (φ a₀ * H) : σ.QuadraticForms m) = H := by
  rw [FirstKindInvolution.polar_mk, FirstKindInvolution.map_mul, hHσ, ← hφ, ← add_mul,
    ← _root_.map_add, ha₀, _root_.map_one, one_mul]

/-- If `a₀ + τ a₀ = 1` and `H` is hermitian and invertible, `[φ(a₀) * H]` is nondegenerate. -/
theorem isNondegenerateQuadratic_mk_mul (hHσ : σ.matrix m H = H) (hH : IsUnit H) {a₀ : A}
    (ha₀ : a₀ + τ a₀ = 1) :
    σ.IsNondegenerateQuadratic (Submodule.Quotient.mk (φ a₀ * H) : σ.QuadraticForms m) := by
  rw [FirstKindInvolution.IsNondegenerateQuadratic, polar_mk_mul τ σ φ H hφ hHσ ha₀]
  exact hH

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Over every coefficient algebra, tensor transport along `φ` carries the defect
`y a₀ τ(y) - a₀` to the defect of `φ(a₀) * H`, multiplied on the right by `H`. -/
theorem defect_tensor_map (a₀ : A) (y : R ⊗[K] A) :
    IsometryCut.defect (σ.matrix m) (φ a₀ * H)
        (Algebra.TensorProduct.map (AlgHom.id R R) φ.toAlgHom y) =
      Algebra.TensorProduct.map (AlgHom.id R R) φ.toAlgHom (IsometryCut.defect τ a₀ y) *
        ((1 : R) ⊗ₜ[K] H) := by
  set E := Algebra.TensorProduct.map (AlgHom.id R R) φ.toAlgHom with hE
  have h1 : ((1 : R) ⊗ₜ[K] (φ a₀ * H)) = E ((1 : R) ⊗ₜ[K] a₀) * ((1 : R) ⊗ₜ[K] H) := by
    rw [hE, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h2 : ((1 : R) ⊗ₜ[K] H) * (σ.matrix m).baseChange R (E y) =
      E (τ.baseChange R y) * ((1 : R) ⊗ₜ[K] H) :=
    (SymplecticInnerForm.tensor_adjoint_compatibility τ (σ.matrix m) φ H hφ R y).symm
  rw [IsometryCut.defect, IsometryCut.defect, h1, _root_.map_sub, _root_.map_mul,
    _root_.map_mul]
  calc E y * (E ((1 : R) ⊗ₜ[K] a₀) * ((1 : R) ⊗ₜ[K] H)) * (σ.matrix m).baseChange R (E y) -
        E ((1 : R) ⊗ₜ[K] a₀) * ((1 : R) ⊗ₜ[K] H)
      = E y * E ((1 : R) ⊗ₜ[K] a₀) *
            (((1 : R) ⊗ₜ[K] H) * (σ.matrix m).baseChange R (E y)) -
          E ((1 : R) ⊗ₜ[K] a₀) * ((1 : R) ⊗ₜ[K] H) := by noncomm_ring
    _ = (E y * E ((1 : R) ⊗ₜ[K] a₀) * E (τ.baseChange R y) - E ((1 : R) ⊗ₜ[K] a₀)) *
          ((1 : R) ⊗ₜ[K] H) := by rw [h2]; noncomm_ring

/-- For hermitian invertible `H`, right multiplication by `H` after tensor transport along `φ`
identifies `R ⊗ {a - τ a}` with `R ⊗ {x - ᵗx^σ}`, Tits's subspace of `M_m(D)`. -/
theorem tensor_map_mul_mem_baseChange_iff (hHσ : σ.matrix m H = H) (hH : IsUnit H)
    (z : R ⊗[K] A) :
    Algebra.TensorProduct.map (AlgHom.id R R) φ.toAlgHom z * ((1 : R) ⊗ₜ[K] H) ∈
        (σ.quadraticKernel m).baseChange R ↔
      z ∈ τ.alternatingSubspace.baseChange R := by
  set E := Algebra.TensorProduct.map (AlgHom.id R R) φ.toAlgHom with hE
  let eR := Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) φ
  have hER : ∀ y, eR y = E y := fun _ => rfl
  have hHR : IsUnit ((1 : R) ⊗ₜ[K] H) :=
    hH.map (Algebra.TensorProduct.includeRight : Matrix m m D →ₐ[K] R ⊗[K] Matrix m m D)
  have key : ∀ v : R ⊗[K] A, E (v - τ.baseChange R v) * ((1 : R) ⊗ₜ[K] H) =
      E v * ((1 : R) ⊗ₜ[K] H) - (σ.matrix m).baseChange R (E v * ((1 : R) ⊗ₜ[K] H)) := by
    intro v
    rw [FirstKindInvolution.map_mul, FirstKindInvolution.baseChange_tmul, hHσ,
      ← SymplecticInnerForm.tensor_adjoint_compatibility τ (σ.matrix m) φ H hφ R v,
      _root_.map_sub, sub_mul]
  rw [FirstKindInvolution.quadraticKernel, IsometryCut.alternatingSubspace_baseChange,
    IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, FirstKindInvolution.mem_alternatingSubspace,
    FirstKindInvolution.mem_alternatingSubspace]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨eR.symm (w * ↑hHR.unit⁻¹), ?_⟩
    have hw' : E (eR.symm (w * ↑hHR.unit⁻¹)) * ((1 : R) ⊗ₜ[K] H) = w := by
      rw [← hER, AlgEquiv.apply_symm_apply, mul_assoc, hHR.val_inv_mul, mul_one]
    rw [← hw', ← key] at hw
    apply eR.injective
    rw [hER, hER]
    exact hHR.mul_right_cancel hw
  · rintro ⟨v, rfl⟩
    exact ⟨E v * ((1 : R) ⊗ₜ[K] H), (key v).symm⟩

end Algebra

section GroupScheme

variable {K A D : Type u} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
  [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  (τ : FirstKindInvolution K A) (σ : FirstKindInvolution K D)
  {m : Type} [Fintype m] [DecidableEq m]
  (φ : A ≃ₐ[K] Matrix m m D) (H : Matrix m m D) (hHσ : σ.matrix m H = H) (hH : IsUnit H)
  (hφ : ∀ x, φ (τ x) * H = H * σ.matrix m (φ x)) (a₀ : A)

/-- The inclusion of the isometry cut of `a₀` modulo `{a - τ a}` represents its range. -/
theorem isRepresentedBy_inclusion_alternatingSubspace :
    (SubgroupFunctor.range
        (IsometryCut.inclusion (IsometryCut.isStable_alternatingSubspace (τ := τ)) a₀)).IsRepresentedBy
      (IsometryCut.inclusion (IsometryCut.isStable_alternatingSubspace (τ := τ)) a₀) :=
  ⟨by
    have : IsClosedImmersion
        (IsometryCut.inclusion (IsometryCut.isStable_alternatingSubspace (τ := τ)) a₀).hom.hom.left :=
      IsometryCut.isClosedSubgroup_inclusion _ a₀
    exact Over.mono_of_mono_left _, rfl⟩

/-- The inclusion of `O(q)` into the unit group of `M_m(D)` represents its range. -/
theorem isRepresentedBy_isometryGroupι (q : σ.QuadraticForms m) :
    (SubgroupFunctor.range (σ.isometryGroupι q)).IsRepresentedBy (σ.isometryGroupι q) :=
  ⟨by
    have : IsClosedImmersion (σ.isometryGroupι q).hom.hom.left :=
      σ.isClosedSubgroup_isometryGroupι q
    exact Over.mono_of_mono_left _, rfl⟩

include hHσ hH hφ

/-- Tensor transport along `φ` identifies the isometry cut of `a₀` modulo `{a - τ a}` with
the subgroup functor of `O([φ(a₀) * H])` on every relative test scheme. -/
theorem comap_algEquivIso_isometryGroupι :
    (SubgroupFunctor.range
        (σ.isometryGroupι (Submodule.Quotient.mk (φ a₀ * H) : σ.QuadraticForms m))).comap
        (FiniteAlgebraUnits.algEquivIso φ).hom =
      SubgroupFunctor.range
        (IsometryCut.inclusion (IsometryCut.isStable_alternatingSubspace (τ := τ)) a₀) := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.mem_comap, σ.mem_range_isometryGroupι_iff _ (φ a₀ * H) rfl,
    IsometryCut.mem_range_inclusion_iff, FiniteAlgebraUnits.pointsEquiv_comp_algEquivIso_hom,
    Units.coe_map]
  change IsometryCut.defect (σ.matrix m) (φ a₀ * H)
      (Algebra.TensorProduct.map (AlgHom.id _ _) φ.toAlgHom _) ∈ _ ↔ _
  rw [defect_tensor_map τ σ φ H hφ, tensor_map_mul_mem_baseChange_iff τ σ φ H hφ _ hHσ hH]

/-- **Transport of the quadratic pair.** The group scheme of units `u` of `A` with
`u a₀ τ(u) - a₀ ∈ {a - τ a}` is isomorphic to the isometry group of the `σ`-quadratic form
`[φ(a₀) * H]`. -/
def isometryCutAlgEquivIso :
    IsometryCut.groupScheme (IsometryCut.isStable_alternatingSubspace (τ := τ)) a₀ ≅
      σ.isometryGroup (Submodule.Quotient.mk (φ a₀ * H) : σ.QuadraticForms m) :=
  SubgroupFunctor.IsRepresentedBy.isoOfComap
    (isRepresentedBy_inclusion_alternatingSubspace τ a₀)
    (isRepresentedBy_isometryGroupι σ _)
    (FiniteAlgebraUnits.algEquivIso φ)
    (comap_algEquivIso_isometryGroupι τ σ φ H hHσ hH hφ a₀)

/-- The comparison intertwines the two inclusions with tensor transport along `φ`. -/
@[reassoc] theorem isometryCutAlgEquivIso_hom_comp :
    (isometryCutAlgEquivIso τ σ φ H hHσ hH hφ a₀).hom ≫
        σ.isometryGroupι (Submodule.Quotient.mk (φ a₀ * H) : σ.QuadraticForms m) =
      IsometryCut.inclusion (IsometryCut.isStable_alternatingSubspace (τ := τ)) a₀ ≫
        (FiniteAlgebraUnits.algEquivIso φ).hom :=
  SubgroupFunctor.IsRepresentedBy.isoOfComap_hom_comp _ _ _ _

end GroupScheme

end Langlands.GroupScheme.OrthogonalInnerForm
