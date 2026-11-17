import Langlands.Algebra.CoalgebraLocalSplit
import Mathlib.LinearAlgebra.Dual.BaseChange

/-! # The convolution dual of a scalar-extended coalgebra -/

noncomputable section

universe u v w

open Coalgebra WithConv Module TensorProduct
open scoped TensorProduct

namespace Langlands.CoalgebraBaseChangeDual

variable {R : Type u} [CommRing R] {S : Type w} [CommRing S] [Algebra R S]
  {C : Type v} [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- The coordinate basis, regarded as convolution functionals. -/
def coordinateBasis {ι : Type*} [Fintype ι] (b : Basis ι R C) :
    Basis ι R (WithConv (C →ₗ[R] R)) := by
  classical
  exact b.dualBasis.map (WithConv.linearEquiv R (C →ₗ[R] R)).symm

omit [Coalgebra R C] in
@[simp]
theorem coordinateBasis_apply {ι : Type*} [Fintype ι] (b : Basis ι R C)
    (i : ι) (x : C) : coordinateBasis b i x = b.repr x i := by
  classical
  exact b.dualBasis_apply i x

/-- The coordinates of a finite group-like basis are complete orthogonal
idempotents in the actual convolution dual. -/
theorem coordinateBasis_completeOrthogonalIdempotents {ι : Type*} [Fintype ι]
    (b : Basis ι R C) (hb : ∀ i, IsGroupLikeElem R (b i)) :
    CompleteOrthogonalIdempotents (coordinateBasis b) := by
  classical
  refine ⟨OrthogonalIdempotents.iff_mul_eq.mpr ?_, ?_⟩
  · intro i j
    apply WithConv.ext
    apply b.ext
    intro k
    by_cases hij : i = j
    · subst j
      by_cases hki : k = i
      · subst k
        simp [LinearMap.convMul_apply, hb, Basis.repr_self]
      · simp [LinearMap.convMul_apply, hb, hki, Basis.repr_self]
    · by_cases hki : k = i
      · subst k
        simp [LinearMap.convMul_apply, hb, hij, Basis.repr_self]
      · simp [LinearMap.convMul_apply, hb, hij, hki, Basis.repr_self, Finsupp.single_apply]
  · apply WithConv.ext
    apply b.ext
    intro k
    simp [hb, Basis.repr_self, Finsupp.single_apply]

/-- Restriction to `1 ⊗ x` identifies scalar-extended convolution duals with
scalar-valued convolution functionals on the original coalgebra. -/
def restriction : WithConv (S ⊗[R] C →ₗ[S] S) ≃ₐ[S] WithConv (C →ₗ[R] S) where
  toFun f := toConv (f.ofConv.restrictScalars R ∘ₗ TensorProduct.mk R S C 1)
  invFun f := toConv (AlgebraTensorModule.lift (LinearMap.toSpanSingleton S _ f.ofConv))
  left_inv f := by
    apply WithConv.ext
    apply AlgebraTensorModule.ext
    intro s x
    change s • f.ofConv (1 ⊗ₜ[R] x) = f.ofConv (s ⊗ₜ[R] x)
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  right_inv f := by
    ext x
    change (1 : S) • f x = f x
    exact one_smul S (f x)
  map_add' _ _ := rfl
  map_mul' f g := by
    ext x
    change (f * g) (1 ⊗ₜ[R] x) = _
    rw [(Repr.arbitrary R x).convMul_apply]
    simp [LinearMap.convMul_apply, TensorProduct.comul_tmul,
      ← (Repr.arbitrary R x).eq, TensorProduct.tmul_sum]
  commutes' s := by
    ext x
    simp [Algebra.smul_def]

@[simp]
theorem restriction_apply (f : WithConv (S ⊗[R] C →ₗ[S] S)) (x : C) :
    restriction (R := R) (S := S) (C := C) f x = f (1 ⊗ₜ[R] x) := rfl

/-- Restricting the coordinates of a scalar-extended basis gives an
`S`-basis of the quotient-valued convolution dual. -/
def restrictedCoordinateBasis {ι : Type*} [Fintype ι] (b : Basis ι S (S ⊗[R] C)) :
    Basis ι S (WithConv (C →ₗ[R] S)) :=
  (coordinateBasis b).map (restriction (R := R) (S := S) (C := C)).toLinearEquiv

@[simp]
theorem restrictedCoordinateBasis_apply {ι : Type*} [Fintype ι]
    (b : Basis ι S (S ⊗[R] C)) (i : ι) (x : C) :
    restrictedCoordinateBasis b i x = b.repr (1 ⊗ₜ[R] x) i := by
  change restriction (R := R) (S := S) (C := C) (coordinateBasis b i) x = _
  rw [restriction_apply, coordinateBasis_apply]

/-- Restriction preserves the complete orthogonal coordinate family. -/
theorem restrictedCoordinateBasis_completeOrthogonalIdempotents
    {ι : Type*} [Fintype ι] (b : Basis ι S (S ⊗[R] C))
    (hb : ∀ i, IsGroupLikeElem S (b i)) :
    CompleteOrthogonalIdempotents (restrictedCoordinateBasis b) := by
  exact (coordinateBasis_completeOrthogonalIdempotents b hb).map
    (restriction (R := R) (S := S) (C := C)).toRingHom

/-- Surjectivity of the scalar map makes these coordinates span over `R`. -/
theorem restrictedCoordinateBasis_span {ι : Type*} [Fintype ι]
    (b : Basis ι S (S ⊗[R] C)) (hS : Function.Surjective (algebraMap R S)) :
    Submodule.span R (Set.range (restrictedCoordinateBasis b)) = ⊤ := by
  let : IsScalarTower R S (WithConv (C →ₗ[R] S)) :=
    ⟨fun r s f => by ext x; exact smul_assoc r s (f x)⟩
  rw [← Submodule.restrictScalars_span R S hS,
    (restrictedCoordinateBasis b).span_eq, Submodule.restrictScalars_top]

/-- A finite group-like basis of the actual reduced coalgebra supplies a
finite group-like basis before nilpotent reduction over a local ring. -/
def groupLikeBasisOfReducedBasis [IsLocalRing R] [Module.Finite R C] [Module.Flat R C]
    (I : Ideal R) (hI : IsNilpotent I) {ι : Type v} [Fintype ι]
    (b : Basis ι (R ⧸ I) ((R ⧸ I) ⊗[R] C))
    (hb : ∀ i, IsGroupLikeElem (R ⧸ I) (b i)) :
    Σ κ : Type v, Σ _ : Fintype κ, {b : Basis κ R C // ∀ i, IsGroupLikeElem R (b i)} :=
  CoalgebraLocalSplit.groupLikeBasisOfNilpotentReduction I hI
    (restrictedCoordinateBasis b)
    (restrictedCoordinateBasis_completeOrthogonalIdempotents b hb)
    (restrictedCoordinateBasis_span b Ideal.Quotient.mk_surjective)

/-- The group-like elements span before reduction if the actual reduced
coalgebra has a finite group-like basis. -/
theorem span_groupLike_eq_top_of_reduced_basis
    [IsLocalRing R] [Module.Finite R C] [Module.Flat R C]
    (I : Ideal R) (hI : IsNilpotent I) {ι : Type v} [Fintype ι]
    (b : Basis ι (R ⧸ I) ((R ⧸ I) ⊗[R] C))
    (hb : ∀ i, IsGroupLikeElem (R ⧸ I) (b i)) :
    Submodule.span R {x : C | IsGroupLikeElem R x} = ⊤ := by
  obtain ⟨κ, inst, b', hb'⟩ := groupLikeBasisOfReducedBasis I hI b hb
  apply top_unique
  rw [← b'.span_eq]
  exact Submodule.span_mono (Set.range_subset_iff.mpr hb')

end Langlands.CoalgebraBaseChangeDual
