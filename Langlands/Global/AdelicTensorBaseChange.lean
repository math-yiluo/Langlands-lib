import Langlands.Global.ArithmeticExceptionalSets
import Langlands.Global.CurvePlaceAdeleDiagonal
import Langlands.Global.CurvePlaceCompletionExtension

/-!
# Canonical maps from base-changed adeles to adeles of an extension

For a finite extension `L/K` of global fields, the canonical `L`-algebra map
`L ⊗[K] A_K → A_L` sends `a ⊗ x` to `a · ι(x)`, where `ι : A_K → A_L` views an adele of `K`
as an adele of `L`. For function fields, this module also constructs `ι`.
-/

noncomputable section

universe u

open IsDedekindDomain Filter Topology
open scoped TensorProduct RestrictedProduct
open Langlands.Global.CurvePlaceCompletionExtension (completionMap continuous_completionMap
  completionMap_algebraMap)

namespace Langlands.Global

section Curve

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]

/-- The completed embedding at an upper place maps completed integers to completed
integers. -/
theorem curvePlaceCompletionMap_mem_integers (p : AlgebraicCurve.Place k K)
    (q : CurvePlacesAbove k L p) {x : curvePlaceCompletion p}
    (hx : x ∈ curvePlaceCompletionIntegers p) :
    completionMap p q x ∈ curvePlaceCompletionIntegers q.1 := by
  have hclosed : IsClosed {y : curvePlaceCompletion p |
      completionMap p q y ∈ curvePlaceCompletionIntegers q.1} :=
    (Valued.isClosed_valuationSubring _).preimage (continuous_completionMap p q)
  have hopen : IsOpen (curvePlaceCompletionIntegers p : Set (curvePlaceCompletion p)) :=
    Valued.isOpen_valuationSubring _
  have hdense : DenseRange (algebraMap K (curvePlaceCompletion p)) :=
    p.heightOneSpectrum.denseRange_algebraMap K
  refine hclosed.closure_subset_iff.mpr ?_ (Dense.open_subset_closure_inter hdense hopen hx)
  rintro _ ⟨hy, y, rfl⟩
  show completionMap p q (algebraMap K (curvePlaceCompletion p) y) ∈
    curvePlaceCompletionIntegers q.1
  rw [completionMap_algebraMap]
  have hyp : y ∈ p.toValuationSubring := (curvePlaceCompletion_mem_integers_iff p y).mp hy
  exact (curvePlaceCompletion_mem_integers_iff q.1 (algebraMap K L y)).mpr
    ((CurvePlaceCompletionExtension.mem_iff p q y).mpr hyp)

variable [IsScalarTower k K L] [FiniteDimensional K L]

/-- An upper place lies above its restriction. -/
def curvePlaceAboveRestriction (q : AlgebraicCurve.Place k L) :
    CurvePlacesAbove k L (curvePlaceRestriction (K := K) q) :=
  ⟨q, (curvePlaceRestriction_valuationSubring q).symm⟩

variable (k K L)

/-- The inclusion `A_K → A_L` of curve-place adeles: the coordinate at an upper place is the
completed embedding of the coordinate at its restriction. -/
def curvePlaceAdeleInclusion : CurvePlaceAdeleRing k K →+* CurvePlaceAdeleRing k L :=
  RestrictedProduct.mapAlongRingHom _ _ (curvePlaceRestriction (K := K))
    curvePlaceRestriction_tendsto_cofinite
    (fun q => completionMap (curvePlaceRestriction (K := K) q) (curvePlaceAboveRestriction q))
    (Eventually.of_forall fun q _ hx =>
      curvePlaceCompletionMap_mem_integers _ (curvePlaceAboveRestriction q) hx)

variable {k K L}

@[simp] theorem curvePlaceAdeleInclusion_apply (x : CurvePlaceAdeleRing k K)
    (q : AlgebraicCurve.Place k L) :
    curvePlaceAdeleInclusion k K L x q =
      completionMap (curvePlaceRestriction (K := K) q) (curvePlaceAboveRestriction q)
        (x (curvePlaceRestriction q)) := rfl

theorem continuous_curvePlaceAdeleInclusion :
    Continuous (curvePlaceAdeleInclusion k K L) := by
  unfold curvePlaceAdeleInclusion
  exact RestrictedProduct.mapAlong_continuous
    (fun v : AlgebraicCurve.Place k K => curvePlaceCompletion v)
    (fun v : AlgebraicCurve.Place k L => curvePlaceCompletion v) _
    curvePlaceRestriction_tendsto_cofinite
    (fun q => ⇑(completionMap (curvePlaceRestriction (K := K) q) (curvePlaceAboveRestriction q)))
    (Eventually.of_forall fun q _ hx =>
      curvePlaceCompletionMap_mem_integers _ (curvePlaceAboveRestriction q) hx)
    fun q => continuous_completionMap _ (curvePlaceAboveRestriction q)

variable [PerfectField k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
  [FunctionField k L]

/-- The inclusion maps the principal adele of `x` to the principal adele of its image. -/
@[simp] theorem curvePlaceAdeleInclusion_diagonal (x : K) :
    curvePlaceAdeleInclusion k K L (curvePlaceAdeleDiagonal k K x) =
      curvePlaceAdeleDiagonal k L (algebraMap K L x) := by
  apply RestrictedProduct.ext
  intro q
  exact completionMap_algebraMap _ (curvePlaceAboveRestriction q) x

variable (k K L)

/-- The canonical `L`-algebra map `L ⊗[K] A_K → A_L` for curve-place adeles. -/
def curvePlaceAdeleTensorMap :
    L ⊗[K] CurvePlaceAdeleRing k K →ₐ[L] CurvePlaceAdeleRing k L := by
  letI : Algebra K (CurvePlaceAdeleRing k L) :=
    ((algebraMap L (CurvePlaceAdeleRing k L)).comp (algebraMap K L)).toAlgebra
  letI : IsScalarTower K L (CurvePlaceAdeleRing k L) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.TensorProduct.lift (Algebra.ofId L (CurvePlaceAdeleRing k L))
    { curvePlaceAdeleInclusion k K L with
      commutes' := fun x => curvePlaceAdeleInclusion_diagonal x }
    (fun _ _ => Commute.all _ _)

variable {k K L}

@[simp] theorem curvePlaceAdeleTensorMap_tmul (a : L) (x : CurvePlaceAdeleRing k K) :
    curvePlaceAdeleTensorMap k K L (a ⊗ₜ[K] x) =
      algebraMap L (CurvePlaceAdeleRing k L) a * curvePlaceAdeleInclusion k K L x := rfl

theorem curvePlaceAdeleTensorMap_tmul_one (a : L) :
    curvePlaceAdeleTensorMap k K L (a ⊗ₜ[K] 1) = algebraMap L (CurvePlaceAdeleRing k L) a := by
  rw [curvePlaceAdeleTensorMap_tmul, map_one, mul_one]

theorem curvePlaceAdeleTensorMap_one_tmul (x : CurvePlaceAdeleRing k K) :
    curvePlaceAdeleTensorMap k K L (1 ⊗ₜ[K] x) = curvePlaceAdeleInclusion k K L x := by
  rw [curvePlaceAdeleTensorMap_tmul, map_one, one_mul]

/-- The coordinate formula at an upper place. -/
theorem curvePlaceAdeleTensorMap_tmul_apply (a : L) (x : CurvePlaceAdeleRing k K)
    (q : AlgebraicCurve.Place k L) :
    curvePlaceAdeleTensorMap k K L (a ⊗ₜ[K] x) q =
      algebraMap L ((curvePlaceAboveRestriction (K := K) q).1.heightOneSpectrum.adicCompletion L) a *
        completionMap (curvePlaceRestriction (K := K) q) (curvePlaceAboveRestriction q)
          (x (curvePlaceRestriction q)) := rfl

end Curve

section NumberField

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The canonical `L`-algebra map `L ⊗[K] A_K → A_L` for number-field adeles, including every
infinite place. -/
def numberFieldAdeleTensorMap : L ⊗[K] Adeles K →ₐ[L] Adeles L := by
  letI : Algebra K (Adeles L) := ((algebraMap L (Adeles L)).comp (algebraMap K L)).toAlgebra
  letI : IsScalarTower K L (Adeles L) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.TensorProduct.lift (Algebra.ofId L (Adeles L))
    { AdelicFunctoriality.adeleInclusion (K := K) (L := L) with
      commutes' := fun x => AdelicFunctoriality.adeleInclusion_diagonal x }
    (fun _ _ => Commute.all _ _)

variable {K L}

@[simp] theorem numberFieldAdeleTensorMap_tmul (a : L) (x : Adeles K) :
    numberFieldAdeleTensorMap K L (a ⊗ₜ[K] x) =
      algebraMap L (Adeles L) a * AdelicFunctoriality.adeleInclusion x := rfl

theorem numberFieldAdeleTensorMap_tmul_one (a : L) :
    numberFieldAdeleTensorMap K L (a ⊗ₜ[K] 1) = algebraMap L (Adeles L) a := by
  rw [numberFieldAdeleTensorMap_tmul, map_one, mul_one]

theorem numberFieldAdeleTensorMap_one_tmul (x : Adeles K) :
    numberFieldAdeleTensorMap K L (1 ⊗ₜ[K] x) = AdelicFunctoriality.adeleInclusion x := by
  rw [numberFieldAdeleTensorMap_tmul, map_one, one_mul]

/-- The coordinate formula at an infinite place of `L`. -/
theorem numberFieldAdeleTensorMap_tmul_infinite (a : L) (x : Adeles K)
    (w : NumberField.InfinitePlace L) :
    (numberFieldAdeleTensorMap K L (a ⊗ₜ[K] x)).1 w =
      algebraMap L w.Completion a *
        AdelicFunctoriality.infiniteCompletionMap (algebraMap K L) w
          (x.1 (w.comap (algebraMap K L))) := rfl

/-- The coordinate formula at a finite place of `L`. -/
theorem numberFieldAdeleTensorMap_tmul_finite (a : L) (x : Adeles K)
    (q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    (numberFieldAdeleTensorMap K L (a ⊗ₜ[K] x)).2 q =
      algebraMap L (q.adicCompletion L) a *
        AdelicFunctoriality.FiniteExtension.completionMap
          (q.under (NumberField.RingOfIntegers K)) q
          (x.2 (q.under (NumberField.RingOfIntegers K))) := rfl

end NumberField

end Langlands.Global
