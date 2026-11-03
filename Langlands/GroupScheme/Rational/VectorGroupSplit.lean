import Langlands.GroupScheme.Rational.VectorGroupDimension
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Fin.Tuple.Basic

/-! # Finite additive-group series for vector groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.VectorGroup

variable {k : Type u} [Field k] (n : ℕ)

/-- The first coordinate is primitive for the standard additive group. -/
theorem firstCoordinate_primitive :
    IsPrimitiveFamily (corepresentableBy (CommRingCat.of k) (n + 1))
      (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin (n + 1)) k)) := by
  intro A x y i
  change Multiplicative (Fin (n + 1) → A) at x y
  change
    (aeval (R := CommRingCat.of k) (x * y).toAdd) (X 0) =
      (aeval (R := CommRingCat.of k) x.toAdd) (X 0) +
        (aeval (R := CommRingCat.of k) y.toAdd) (X 0)
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rfl

/-- The homomorphism to the one-dimensional vector group given by the first
coordinate. -/
def firstCoordinate :
    groupScheme (CommRingCat.of k) (n + 1) ⟶ groupScheme (CommRingCat.of k) 1 :=
  quotientMap (firstCoordinate_primitive (k := k) n)

theorem coordinates_firstCoordinate {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (groupScheme (CommRingCat.of k) (n + 1)).X) (i : Fin 1) :
    (coordinates (CommRingCat.of k) 1 T
      (x ≫ (firstCoordinate (k := k) n).hom.hom)).toAdd i =
        (coordinates (CommRingCat.of k) (n + 1) T x).toAdd 0 := by
  exact coordinates_quotientMap_eq_appTop (firstCoordinate_primitive (k := k) n) x i

private def firstTailEquiv : Fin 1 ⊕ ULift.{u} (Fin n) ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) (fun i => i.down.succ)
  invFun := Fin.cases (Sum.inl 0) (fun i => Sum.inr (ULift.up i))
  left_inv := by
    intro i
    cases i with
    | inl i =>
      have : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    | inr i => cases i; rfl
  right_inv := by
    intro i
    exact Fin.cases rfl (fun _ => rfl) i

private theorem firstTail_bijective :
    Function.Bijective
      (aeval (Sum.elim (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin (n + 1)) k))
        (fun i : ULift.{u} (Fin n) => X i.down.succ)) :
          MvPolynomial (Fin 1 ⊕ ULift.{u} (Fin n)) k →ₐ[k]
            MvPolynomial (Fin (n + 1)) k) := by
  have h :
      (aeval (Sum.elim (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin (n + 1)) k))
        (fun i : ULift.{u} (Fin n) => X i.down.succ)) :
          MvPolynomial (Fin 1 ⊕ ULift.{u} (Fin n)) k →ₐ[k]
            MvPolynomial (Fin (n + 1)) k) =
        (renameEquiv k (firstTailEquiv n)).toAlgHom := by
    ext i
    cases i <;> simp [firstTailEquiv]
  rw [h]
  exact (renameEquiv k (firstTailEquiv n)).bijective

/-- Projection onto the first coordinate is an actual represented fppf
quotient by its scheme kernel. -/
theorem isFppfQuotient_firstCoordinate :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι (firstCoordinate (k := k) n)))
      (firstCoordinate (k := k) n) :=
  ⟨flat_quotientMap (firstCoordinate_primitive (k := k) n) (firstTail_bijective (k := k) n),
    surjective_quotientMap (firstCoordinate_primitive (k := k) n) (firstTail_bijective (k := k) n),
    locallyOfFinitePresentation_quotientMap (firstCoordinate_primitive (k := k) n)
      (firstTail_bijective (k := k) n), rfl⟩

private def pointKernelCoordinates (T : Over (Spec (CommRingCat.of k))) :
    (((yonedaGrp.map (firstCoordinate (k := k) n)).app (.op T)).hom.ker) ≃*
      Multiplicative (Fin n → Γ(T.left, ⊤)) where
  toFun x := Multiplicative.ofAdd fun i =>
    (coordinates (CommRingCat.of k) (n + 1) T x.val).toAdd i.succ
  invFun v := ⟨(coordinates (CommRingCat.of k) (n + 1) T).symm
    (Multiplicative.ofAdd (Fin.cons 0 v.toAdd)), by
      change (coordinates (CommRingCat.of k) (n + 1) T).symm
        (Multiplicative.ofAdd (Fin.cons 0 v.toAdd)) ≫
          (firstCoordinate (k := k) n).hom.hom = 1
      apply points_ext
      intro i
      rw [coordinates_firstCoordinate, MulEquiv.apply_symm_apply, map_one]
      rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply points_ext
    intro i
    change
      (coordinates (CommRingCat.of k) (n + 1) T
        ((coordinates (CommRingCat.of k) (n + 1) T).symm
          (Multiplicative.ofAdd (Fin.cons 0
            (fun j => (coordinates (CommRingCat.of k) (n + 1) T x.val).toAdd j.succ))))).toAdd i =
        (coordinates (CommRingCat.of k) (n + 1) T x.val).toAdd i
    rw [MulEquiv.apply_symm_apply]
    refine Fin.cases ?_ (fun j => ?_) i
    · have hx : x.val ≫ (firstCoordinate (k := k) n).hom.hom = 1 := x.property
      have hc := coordinates_firstCoordinate (k := k) n
        (x.val : T ⟶ (groupScheme (CommRingCat.of k) (n + 1)).X) 0
      rw [hx, map_one] at hc
      exact hc
    · rfl
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    change (coordinates (CommRingCat.of k) (n + 1) T
      ((coordinates (CommRingCat.of k) (n + 1) T).symm
        (Multiplicative.ofAdd (Fin.cons 0 v.toAdd)))).toAdd i.succ = v.toAdd i
    rw [MulEquiv.apply_symm_apply]
    rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    change (coordinates (CommRingCat.of k) (n + 1) T (x.val * y.val)).toAdd i.succ =
      (coordinates (CommRingCat.of k) (n + 1) T x.val).toAdd i.succ +
        (coordinates (CommRingCat.of k) (n + 1) T y.val).toAdd i.succ
    exact congrFun (coordinates_mul
      (x.val : T ⟶ (groupScheme (CommRingCat.of k) (n + 1)).X)
      (y.val : T ⟶ (groupScheme (CommRingCat.of k) (n + 1)).X)) i.succ

/-- Tail coordinates identify the actual first-coordinate kernel with an
`n`-dimensional vector group on every scheme test. -/
def firstCoordinateKernelCoordinates (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (kernel (firstCoordinate (k := k) n)).X) ≃*
      Multiplicative (Fin n → Γ(T.left, ⊤)) :=
  (kernelPointsEquiv (firstCoordinate (k := k) n) T).trans (pointKernelCoordinates n T)

/-- The tail coordinates are natural for all test morphisms. -/
theorem firstCoordinateKernelCoordinates_natural :
    RelativeRoot.IsNaturalVectorCoordinates (firstCoordinateKernelCoordinates (k := k) n) := by
  intro T W f x
  funext i
  change (coordinates (CommRingCat.of k) (n + 1) W
      ((f ≫ x) ≫ (kernelι (firstCoordinate (k := k) n)).hom.hom)).toAdd i.succ =
    f.left.appTop ((coordinates (CommRingCat.of k) (n + 1) T
      (x ≫ (kernelι (firstCoordinate (k := k) n)).hom.hom)).toAdd i.succ)
  rw [Category.assoc, coordinates_comp]

theorem isVectorGroupOfDimension_firstCoordinateKernel :
    RelativeRoot.IsVectorGroupOfDimension (kernel (firstCoordinate (k := k) n)) n :=
  ⟨firstCoordinateKernelCoordinates n, firstCoordinateKernelCoordinates_natural n⟩

/-- A standard vector group has a finite normal additive-group series with
length exactly its coordinate dimension. -/
theorem hasSplitSeries :
    RelativeRoot.HasSplitSeries n (groupScheme (CommRingCat.of k) n) := by
  induction n with
  | zero =>
    exact RelativeRoot.IsVectorGroupOfDimension.range_eq_bot_of_dim_zero
      ⟨coordinates (CommRingCat.of k) 0, isNaturalVectorCoordinates⟩ _
  | succ n ih =>
    have hv : RelativeRoot.IsVectorGroupOfDimension
        (groupScheme (CommRingCat.of k) 1) 1 :=
      ⟨coordinates (CommRingCat.of k) 1, isNaturalVectorCoordinates⟩
    let : IsAffineHom (groupScheme (CommRingCat.of k) 1).X.hom := hv.isAffineHom
    have hk := isVectorGroupOfDimension_firstCoordinateKernel (k := k) n
    refine ⟨kernel (firstCoordinate (k := k) n), groupScheme (CommRingCat.of k) 1,
      kernelι (firstCoordinate (k := k) n), firstCoordinate (k := k) n, ?_,
      hk.smooth, hk.connectedSpace, ?_, isFppfQuotient_firstCoordinate n,
      hv, ih.of_iso hk.iso.symm⟩
    · exact inferInstanceAs (IsClosedImmersion (kernelι (firstCoordinate (k := k) n)).hom.hom.left)
    · intro T g x _ hx
      have hvn : RelativeRoot.IsVectorGroupOfDimension
          (groupScheme (CommRingCat.of k) (n + 1)) (n + 1) :=
        ⟨coordinates (CommRingCat.of k) (n + 1), isNaturalVectorCoordinates⟩
      rw [(hvn.points_commute g x).eq, mul_inv_cancel_right]
      exact hx

end Langlands.GroupScheme.VectorGroup

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}

/-- Natural vector coordinates supply a finite normal Ga-series of the same
length as the coordinate dimension. -/
theorem IsVectorGroupOfDimension.hasSplitSeries (h : IsVectorGroupOfDimension V n) :
    HasSplitSeries n V :=
  (VectorGroup.hasSplitSeries (k := k) n).of_iso h.iso.symm

/-- Every finite-dimensional vector group is split unipotent in the actual
represented-fppf-quotient definition. -/
theorem IsVectorGroupOfDimension.isSplitUnipotent (h : IsVectorGroupOfDimension V n) :
    IsSplitUnipotent V :=
  ⟨n, h.hasSplitSeries⟩

/-- Split unipotence also follows when the vector-group dimension is not
specified. -/
theorem IsVectorGroup.isSplitUnipotent (h : IsVectorGroup V) : IsSplitUnipotent V := by
  obtain ⟨n, hn⟩ := h
  exact hn.isSplitUnipotent

end Langlands.GroupScheme.RelativeRoot
