import Langlands.GroupScheme.Examples.QuasiSplitUnitaryUniversalMatrix
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankCoefficients
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryWeightSupport
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankKernel
import Langlands.GroupScheme.Reductive.Basic

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme.QuasiSplitUnitary

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)
variable (I : Type u) [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of F)) I ⟶ groupScheme b c)

/-- The actual universal matrix has orthogonal idempotent coefficient matrices. -/
theorem universalMatrix_coeff_mul (a d : I → ℤ) :
    RankCoefficients.matrixCoeff (splitTorusUniversalMatrix b c I i).val a *
      RankCoefficients.matrixCoeff (splitTorusUniversalMatrix b c I i).val d =
      if a = d then RankCoefficients.matrixCoeff (splitTorusUniversalMatrix b c I i).val a else 0 := by
  apply RankCoefficients.matrixCoeff_mul
  let f : (I → ℤ) →+ ((I → ℤ) × (I → ℤ)) :=
    { toFun := fun m => (m, 0), map_zero' := rfl, map_add' := fun _ _ => by simp }
  let g : (I → ℤ) →+ ((I → ℤ) × (I → ℤ)) :=
    { toFun := fun m => (0, m), map_zero' := rfl, map_add' := fun _ _ => by simp }
  have h := universalMatrix_map_add b c I i f g
  have hd : AddMonoidAlgebra.mapDomainAlgHom E E (f + g) =
      RankCoefficients.diagonalMap E (I → ℤ) := by
    unfold RankCoefficients.diagonalMap
    congr 1
    ext m <;> simp [f, g]
  rw [hd] at h
  exact h

private theorem coeff_mapDomain_neg {M : Type u} [AddCommGroup M]
    (p : AddMonoidAlgebra E M) (m : M) :
    (AddMonoidAlgebra.mapDomainAlgHom E E (-AddMonoidHom.id M) p).coeff m =
      p.coeff (-m) := by
  change (Finsupp.mapDomain (fun a : M => -a) p.coeff) m = _
  simpa using Finsupp.mapDomain_apply_of_injective
    (neg_injective : Function.Injective (fun a : M => -a)) p.coeff (-m)

/-- Unitarity pairs the coefficient at a weight with the conjugate reversed transpose. -/
theorem universalMatrix_coeff_neg (a : I → ℤ) (j k : Fin 2) :
    RankCoefficients.matrixCoeff (splitTorusUniversalMatrix b c I i).val (-a) j k =
      c (RankCoefficients.matrixCoeff (splitTorusUniversalMatrix b c I i).val a k.rev j.rev) := by
  have h := congrArg (fun P : Matrix (Fin 2) (Fin 2) (AddMonoidAlgebra E (I → ℤ)) =>
    (P j k).coeff a) (universalMatrix_map_neg b c I i)
  simp only [Matrix.map_apply, coeff_mapDomain_neg] at h
  fin_cases j <;> fin_cases k <;>
    simpa [RankCoefficients.matrixCoeff,
      adjoint, AddMonoidAlgebra.coeff_mapAlgHom] using h

/-- All weights of the actual two-dimensional representation lie in one opposite pair. -/
theorem universalMatrix_support_in_pair :
    ∃ a : I → ℤ, ∀ d ∈ projectionSupport
      (RankCoefficients.matrixCoeff (splitTorusUniversalMatrix b c I i).val), d = a ∨ d = -a := by
  let C := RankCoefficients.matrixCoeff (splitTorusUniversalMatrix b c I i).val
  obtain ⟨hfin, hcard⟩ := projectionSupport_finite_and_card C
    (universalMatrix_coeff_mul b c I i)
  apply two_weights_in_neg_pair _ hfin (by simpa using hcard)
  intro a ha
  exact (RankCoefficients.neg_ne_zero_iff C c (map_zero c) Fin.rev
    (universalMatrix_coeff_neg b c I i) a).mpr ha

/-- Group-algebra matrix coordinates distinguish actual affine points. -/
theorem groupAlgebraMatrixCoordinates_injective (M : Type u) [AddCommMonoid M] :
    Function.Injective (groupAlgebraMatrixCoordinates b c M) := by
  intro x y h
  apply affineMatrixCoordinates_injective b c (AddMonoidAlgebra F M)
  apply Units.ext
  apply Matrix.ext
  intro j k
  apply (AddMonoidAlgebra.scalarTensorEquiv F E (M := M)).injective
  exact congrArg (fun g : GL (Fin 2) (AddMonoidAlgebra E M) => g j k) h

/-- Exponent maps that vanish on every occurring weight give the constant specialization. -/
theorem universalMatrix_map_eq_zeroMap {M : Type u} [AddCommMonoid M]
    (f : (I → ℤ) →+ M)
    (hf : ∀ a ∈ projectionSupport
      (RankCoefficients.matrixCoeff (splitTorusUniversalMatrix b c I i).val), f a = 0) :
    (splitTorusUniversalMatrix b c I i).val.map (AddMonoidAlgebra.mapDomainAlgHom E E f) =
      (splitTorusUniversalMatrix b c I i).val.map
        (AddMonoidAlgebra.mapDomainAlgHom E E (0 : (I → ℤ) →+ M)) := by
  apply Matrix.ext
  intro j k
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain f ((splitTorusUniversalMatrix b c I i).val j k).coeff =
    Finsupp.mapDomain (fun _ => 0) ((splitTorusUniversalMatrix b c I i).val j k).coeff
  apply Finsupp.mapDomain_congr
  intro a ha
  apply hf a
  intro hz
  have hentry := congrArg (fun P : Matrix (Fin 2) (Fin 2) E => P j k) hz
  exact (Finsupp.mem_support_iff.mp ha) hentry

/-- A zero exponent map specializes the universal point to the identity. -/
theorem universalPoint_exponentMap_zero {M : Type u} [AddCommMonoid M] :
    Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F (0 : (I → ℤ) →+ M))
      (splitTorus.universalPoint (R := CommRingCat.of F) I) = 1 := by
  apply (splitTorus.algebraPointsEquiv I _).injective
  rw [splitTorus.algebraPointsEquiv_naturality, map_one,
    splitTorus.algebraPointsEquiv_universalPoint]
  funext j
  apply Units.ext
  change AddMonoidAlgebra.mapDomainAlgHom F F (0 : (I → ℤ) →+ M)
    (AddMonoidAlgebra.single (Pi.single j 1) 1) = 1
  simp [AddMonoidAlgebra.one_def]

/-- A point specialized to the identity has zero exponents in each coordinate. -/
theorem universalPoint_exponentMap_eq_one {M : Type u} [AddCommMonoid M]
    (f : (I → ℤ) →+ M)
    (hf : Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F f)
      (splitTorus.universalPoint (R := CommRingCat.of F) I) = 1) (j : I) :
    f (Pi.single j 1) = 0 := by
  have h := congrArg (fun x => splitTorus.algebraPointsEquiv I (AddMonoidAlgebra F M) x j) hf
  simp only [splitTorus.algebraPointsEquiv_naturality,
    map_one, Pi.one_apply] at h
  simp only [splitTorus.universalPoint, MulEquiv.apply_symm_apply] at h
  have hval := congrArg Units.val h
  change AddMonoidAlgebra.mapDomainAlgHom F F f
    (AddMonoidAlgebra.single (Pi.single j 1) 1) = 1 at hval
  have h' := congrArg AddMonoidAlgebra.coeff hval
  apply Finsupp.single_left_injective (one_ne_zero : (1 : F) ≠ 0)
  simpa [AddMonoidAlgebra.one_def] using h' 

/-- Every closed split torus in U(1,1) has rank at most one. -/
theorem splitTorus_rank_le_one
    (hi : IsClosedSubgroup i) : Nat.card I ≤ 1 := by
  by_contra hI
  obtain ⟨a, ha⟩ := universalMatrix_support_in_pair b c I i
  obtain ⟨m, hm, ham⟩ := exists_ne_zero_sum_mul_eq_zero (by omega) a
  let f : (I → ℤ) →+ ULift.{u} ℤ :=
    { toFun := fun d => ULift.up (∑ j, d j * m j)
      map_zero' := by apply ULift.ext; simp
      map_add' := fun d e => by apply ULift.ext; simp [add_mul, Finset.sum_add_distrib] }
  have hf : ∀ d ∈ projectionSupport
      (RankCoefficients.matrixCoeff (splitTorusUniversalMatrix b c I i).val), f d = 0 := by
    intro d hd
    rcases ha d hd with rfl | rfl
    · exact congrArg ULift.up ham
    · change ULift.up (∑ j, (-a) j * m j) = ULift.up 0
      simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_eq_zero] using
        congrArg ULift.up (neg_eq_zero.mpr ham)
  have hmat := universalMatrix_map_eq_zeroMap b c I i f hf
  have hn (q : (I → ℤ) →+ ULift.{u} ℤ) :=
    groupAlgebraMatrixCoordinates_naturality b c q (splitTorus.universalPoint I ≫ i.hom.hom)
  have hp : Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F f)
      (splitTorus.universalPoint (R := CommRingCat.of F) I ≫ i.hom.hom) =
      Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F (0 : (I → ℤ) →+ ULift.{u} ℤ))
        (splitTorus.universalPoint I ≫ i.hom.hom) := by
    apply groupAlgebraMatrixCoordinates_injective b c
    rw [hn, hn]
    apply Units.ext
    exact hmat
  have hp' : (Lie.affineMap _ (AddMonoidAlgebra.mapDomainAlgHom F F f)
      (splitTorus.universalPoint (R := CommRingCat.of F) I)) ≫ i.hom.hom =
      (1 : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of F)) I)
        (AddMonoidAlgebra F (ULift.{u} ℤ))) ≫ i.hom.hom := by
    have hz := universalPoint_exponentMap_zero (F := F) I (M := ULift.{u} ℤ)
    simp only [Lie.affineMap_apply, ← Category.assoc] at hp hz ⊢
    rw [hz] at hp
    exact hp
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have heq := (cancel_mono i.hom.hom).mp hp'
  apply hm
  funext j
  have hj := universalPoint_exponentMap_eq_one (F := F) I f heq j
  have hj' := congrArg ULift.down hj
  simpa [f, Pi.single_apply] using hj'

end Langlands.GroupScheme.QuasiSplitUnitary
