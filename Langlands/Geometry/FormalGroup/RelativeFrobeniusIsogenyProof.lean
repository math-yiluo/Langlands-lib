import Langlands.Geometry.FormalGroup.RelativeFrobeniusIsogenyStatement
import Langlands.Geometry.FormalGroup.FiniteKernelComposition
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PiTensorProduct

/-! # The relative Frobenius isogeny and its represented kernel rank -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory FiniteKernelComposition
open scoped TensorProduct

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace RelativeFrobenius

section RootAlgebra

variable {A B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {σ : Type}

private def rootIdeal (q : ℕ) (a : σ → A) : Ideal (MvPolynomial σ A) :=
  Ideal.span (Set.range fun i => MvPolynomial.X i ^ q - MvPolynomial.C (a i))

/-- The algebra obtained by imposing one monic power relation in each coordinate. -/
private abbrev RootAlgebra (q : ℕ) (a : σ → A) := MvPolynomial σ A ⧸ rootIdeal q a

private def root (q : ℕ) (a : σ → A) (i : σ) : RootAlgebra q a :=
  Ideal.Quotient.mkₐ A (rootIdeal q a) (MvPolynomial.X i)

private theorem root_pow (q : ℕ) (a : σ → A) (i : σ) :
    root q a i ^ q = algebraMap A (RootAlgebra q a) (a i) := by
  apply sub_eq_zero.mp
  let π := Ideal.Quotient.mkₐ A (rootIdeal q a)
  change π (MvPolynomial.X i) ^ q - π (MvPolynomial.C (a i)) = 0
  rw [← map_pow, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

private def rootLift (q : ℕ) (a : σ → A) (x : σ → B)
    (h : ∀ i, x i ^ q = algebraMap A B (a i)) : RootAlgebra q a →ₐ[A] B :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x) (by
    have hle : rootIdeal q a ≤ RingHom.ker (MvPolynomial.aeval x) := by
      rw [rootIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, h i, sub_self]
    exact fun _ hy => RingHom.mem_ker.mp (hle hy))

private theorem rootLift_root (q : ℕ) (a : σ → A) (x : σ → B)
    (h : ∀ i, x i ^ q = algebraMap A B (a i)) (i : σ) : rootLift q a x h (root q a i) = x i := by
  rw [root, ← AlgHom.comp_apply, rootLift, Ideal.Quotient.liftₐ_comp, MvPolynomial.aeval_X]

private theorem rootHom_ext {q : ℕ} {a : σ → A} {f g : RootAlgebra q a →ₐ[A] B}
    (h : ∀ i, f (root q a i) = g (root q a i)) : f = g :=
  Ideal.Quotient.algHom_ext A (MvPolynomial.algHom_ext h)

private theorem rootAlgebra_finitePresentation [Finite σ] (q : ℕ) (a : σ → A) :
    Algebra.FinitePresentation A (RootAlgebra q a) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

private abbrev rootPolynomial (q : ℕ) (a : A) : Polynomial A := Polynomial.X ^ q - Polynomial.C a

private theorem adjoinRoot_pow (q : ℕ) (a : A) :
    AdjoinRoot.root (rootPolynomial q a) ^ q = algebraMap A (AdjoinRoot (rootPolynomial q a)) a := by
  apply sub_eq_zero.mp
  simpa only [rootPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, ← AdjoinRoot.algebraMap_eq] using AdjoinRoot.eval₂_root (rootPolynomial q a)

private abbrev RootTensor (q : ℕ) (a : σ → A) := ⨂[A] i : σ, AdjoinRoot (rootPolynomial q (a i))

private def tensorRoot [DecidableEq σ] (q : ℕ) (a : σ → A) (i : σ) : RootTensor q a :=
  PiTensorProduct.singleAlgHom i (AdjoinRoot.root (rootPolynomial q (a i)))

private theorem tensorRoot_pow [DecidableEq σ] (q : ℕ) (a : σ → A) (i : σ) :
    tensorRoot q a i ^ q = algebraMap A (RootTensor q a) (a i) := by
  rw [tensorRoot, ← map_pow, adjoinRoot_pow, AlgHom.commutes]

private def tensorLift [Fintype σ] {q : ℕ} {a : σ → A}
    (f : ∀ i, AdjoinRoot (rootPolynomial q (a i)) →ₐ[A] B) : RootTensor q a →ₐ[A] B :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra A σ B).compLinearMap fun i => (f i).toLinearMap)
    (by simp [MultilinearMap.mkPiAlgebra_apply])
    (by
      intro x y
      simp [MultilinearMap.mkPiAlgebra_apply, Finset.prod_mul_distrib])

private theorem tensorLift_single [Fintype σ] [DecidableEq σ] {q : ℕ} {a : σ → A}
    (f : ∀ i, AdjoinRoot (rootPolynomial q (a i)) →ₐ[A] B) (i : σ)
    (x : AdjoinRoot (rootPolynomial q (a i))) :
    tensorLift f (PiTensorProduct.singleAlgHom i x) = f i x := by
  change PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra A σ B).compLinearMap fun i => (f i).toLinearMap)
    (PiTensorProduct.tprod A (Pi.mulSingle i x)) = f i x
  simp only [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply]
  rw [Finset.prod_eq_single i]
  · rw [Pi.mulSingle_eq_same]
  · intro j _ hji
    rw [Pi.mulSingle_eq_of_ne hji, map_one]
  · simp

/-- The quotient is the tensor product of the individual monic root algebras. -/
private def rootTensorEquiv [Finite σ] (q : ℕ) (a : σ → A) : RootAlgebra q a ≃ₐ[A] RootTensor q a := by
  classical
  letI := Fintype.ofFinite σ
  let toTensor := rootLift q a (tensorRoot q a) (tensorRoot_pow q a)
  let fromFactor (i : σ) : AdjoinRoot (rootPolynomial q (a i)) →ₐ[A] RootAlgebra q a :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (root q a i) (by
      change (rootPolynomial q (a i)).eval₂ (algebraMap A (RootAlgebra q a)) (root q a i) = 0
      simp only [rootPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, root_pow, sub_self])
  let fromTensor := tensorLift fromFactor
  have hFrom (i : σ) : fromTensor (tensorRoot q a i) = root q a i := by
    rw [tensorRoot]
    change tensorLift fromFactor (PiTensorProduct.singleAlgHom i _) = _
    rw [tensorLift_single]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hTo (i : σ) : toTensor (root q a i) = tensorRoot q a i := rootLift_root _ _ _ _ _
  refine AlgEquiv.ofAlgHom toTensor fromTensor ?_ ?_
  · apply PiTensorProduct.algHom_ext
    intro i
    apply AdjoinRoot.algHom_ext
    change toTensor (fromTensor (tensorRoot q a i)) = tensorRoot q a i
    rw [hFrom, hTo]
  · apply rootHom_ext
    intro i
    change fromTensor (toTensor (root q a i)) = root q a i
    rw [hTo, hFrom]

/-- A power basis indexed by `Fin q`, also over a trivial coefficient ring. -/
private def factorBasis (q : ℕ) [NeZero q] (a : A) :
    Module.Basis (Fin q) A (AdjoinRoot (rootPolynomial q a)) := by
  classical
  by_cases h : Nontrivial A
  · letI := h
    have hm := Polynomial.monic_X_pow_sub_C a (NeZero.ne q)
    have hd : (rootPolynomial q a).natDegree = q := Polynomial.natDegree_X_pow_sub_C
    exact (AdjoinRoot.powerBasis' hm).basis.reindex (finCongr hd)
  · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp h
    have := Module.subsingleton A (AdjoinRoot (rootPolynomial q a))
    exact Module.Basis.ofEquivFun (LinearEquiv.ofSubsingleton _ _)

private def rootBasis [Finite σ] (q : ℕ) [NeZero q] (a : σ → A) :
    Module.Basis (σ → Fin q) A (RootAlgebra q a) :=
  (Basis.piTensorProduct fun i => factorBasis q (a i)).map
    (rootTensorEquiv q a).symm.toLinearEquiv

private theorem rootAlgebra_faithfullyFlat [Finite σ] (q : ℕ) [NeZero q] (a : σ → A) :
    Module.FaithfullyFlat A (RootAlgebra q a) :=
  Module.FaithfullyFlat.of_linearEquiv _ _ (rootBasis q a).repr

end RootAlgebra

section FormalPoints

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]
variable (M : ModuleLaw O R σ) (p n : ℕ) [ExpChar R p]
variable (θ : R →ₐ[O] R) (hθ : θ.toRingHom = iterateFrobenius R p n)

/-- The actual Frobenius takes the `p^n`-th power of each nilpotent coordinate. -/
private theorem coord_frobenius {A : CommAlgCat.{v} R} (x : M.AlgebraPoint A) (i : σ) :
    coord (M.map θ) ((M.frobeniusHom p n θ hθ).onAlgebraPoints x) i = coord M x i ^ (p ^ n) := by
  let z : SeriesPoint A σ Empty := x
  change MvPowerSeries.constantCoeff (MvPowerSeries.subst z.val
    (((CoordinateMap.frobeniusPow (R := R) (σ := σ) p n).map (algebraMap R A)).series i)) = _
  rw [CoordinateMap.map_series, CoordinateMap.frobeniusPow_series, map_pow, MvPowerSeries.map_X,
    MvPowerSeries.subst_pow z.property, MvPowerSeries.subst_X z.property, map_pow]
  rfl

private theorem frobenius_point_eq_zero_iff {A : CommAlgCat.{v} R} (x : M.AlgebraPoint A) :
    (M.frobeniusHom p n θ hθ).onAlgebraPoints x = 0 ↔ ∀ i, coord M x i ^ (p ^ n) = 0 := by
  constructor
  · intro h i
    rw [← coord_frobenius M p n θ hθ, h, coord_zero]
  · intro h
    apply ext_coord
    intro i
    rw [coord_frobenius M p n θ hθ, coord_zero, h i]

private theorem frobenius_lifts : (M.frobeniusHom p n θ hθ).IsFppfLocallySurjective := by
  intro A y
  let : NeZero (p ^ n) := ⟨pow_ne_zero n (expChar_ne_zero R p)⟩
  let a : σ → A := coord (M.map θ) y
  let B : CommAlgCat.{v} R := CommAlgCat.of R (RootAlgebra (p ^ n) a)
  let φ : A ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)
  let x : M.AlgebraPoint B := (M.algebraPointEquiv B).symm
    ⟨root (p ^ n) a, fun i => IsNilpotent.of_pow (m := p ^ n) (by
      rw [root_pow]
      exact (coord_isNilpotent y i).map (algebraMap A (RootAlgebra (p ^ n) a)))⟩
  refine ⟨B, φ, ?_, ?_, x, ?_⟩
  · exact RingHom.faithfullyFlat_algebraMap_iff.mpr (rootAlgebra_faithfullyFlat _ a)
  · exact RingHom.finitePresentation_algebraMap.mpr (rootAlgebra_finitePresentation _ a)
  · apply ext_coord
    intro i
    rw [coord_frobenius M p n θ hθ, coord_algebraMapPoints]
    have hx : coord M x i = root (p ^ n) a i := by
      simp [coord, x]
    rw [hx]
    exact root_pow (p ^ n) a i

private def frobeniusKernelRepresents :
    (M.frobeniusHom p n θ hθ).kernelSetFunctor.CorepresentableBy
      (CommAlgCat.of R (RootAlgebra (p ^ n) (0 : σ → R))) := by
  let f := M.frobeniusHom p n θ hθ
  let X : CommAlgCat.{v} R := CommAlgCat.of R (RootAlgebra (p ^ n) (0 : σ → R))
  let r : σ → X := root (p ^ n) (0 : σ → R)
  have hr (i : σ) : r i ^ (p ^ n) = 0 := by
    simpa only [r, Pi.zero_apply, map_zero] using root_pow (p ^ n) (0 : σ → R) i
  let tuple : {t : σ → X // ∀ i, IsNilpotent (t i)} := ⟨r, fun i => ⟨p ^ n, hr i⟩⟩
  let x₀ : M.AlgebraPoint X := (M.algebraPointEquiv X).symm tuple
  have hx₀ (i : σ) : coord M x₀ i = r i :=
    congrArg (fun t => t.val i) ((M.algebraPointEquiv X).apply_symm_apply tuple)
  have coord_map_x₀ {A : CommAlgCat.{v} R} (ψ : X ⟶ A) (i : σ) :
      coord M (M.algebraMapPoints ψ.hom x₀) i = ψ.hom (r i) :=
    (coord_algebraMapPoints (A := X) (B := A) ψ.hom x₀ i).trans
      (congrArg (fun t => ψ.hom t) (hx₀ i))
  have hx₀_zero : f.onAlgebraPoints x₀ = 0 :=
    (frobenius_point_eq_zero_iff M p n θ hθ x₀).mpr fun i => by rw [hx₀, hr]
  have hpower (A : CommAlgCat.{v} R) (x : f.kernelSetFunctor.obj A) (i : σ) :
      coord M (kernelVal x) i ^ (p ^ n) = algebraMap R A ((0 : σ → R) i) := by
    simpa only [Pi.zero_apply, map_zero] using
      (frobenius_point_eq_zero_iff M p n θ hθ (kernelVal x)).mp (kernelVal_property x) i
  let classify (A : CommAlgCat.{v} R) (x : f.kernelSetFunctor.obj A) : X ⟶ A :=
    CommAlgCat.ofHom (rootLift (p ^ n) (0 : σ → R) (coord M (kernelVal x)) (hpower A x))
  have hclassify (A : CommAlgCat.{v} R) (x : f.kernelSetFunctor.obj A) (i : σ) :
      (classify A x).hom (r i) = coord M (kernelVal x) i :=
    rootLift_root (p ^ n) (0 : σ → R) (coord M (kernelVal x)) (hpower A x) i
  change f.kernelSetFunctor.CorepresentableBy X
  refine {
    homEquiv := fun {A} => {
      toFun := fun ψ => kernelMk f (M.algebraMapPoints ψ.hom x₀) (by
        rw [← Hom.onAlgebraPoints_natural, hx₀_zero, map_zero])
      invFun := classify A
      left_inv := fun ψ => by
        apply CommAlgCat.hom_ext
        apply rootHom_ext
        intro i
        change (classify A (kernelMk f (M.algebraMapPoints ψ.hom x₀) _)).hom (r i) = ψ.hom (r i)
        rw [hclassify, kernelVal_kernelMk]
        exact coord_map_x₀ ψ i
      right_inv := fun x => by
        apply kernelVal_injective
        apply ext_coord
        intro i
        change coord M (M.algebraMapPoints (classify A x).hom x₀) i = coord M (kernelVal x) i
        exact (coord_map_x₀ (classify A x) i).trans (hclassify A x i) }
    homEquiv_comp := fun ψ χ => by
      apply kernelVal_injective
      change M.algebraMapPoints (χ ≫ ψ).hom x₀ =
        M.algebraMapPoints ψ.hom (M.algebraMapPoints χ.hom x₀)
      rw [CommAlgCat.hom_comp, algebraMapPoints_comp] }

end FormalPoints

end RelativeFrobenius

open RelativeFrobenius in
/-- The actual relative Frobenius is an isogeny with kernel rank `p^(n * Nat.card σ)`. -/
theorem relativeFrobeniusIsogeny {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
    {σ : Type} [Finite σ] (M : ModuleLaw O R σ) (p n : ℕ) [ExpChar R p] :
    RelativeFrobeniusIsogenyStatement M p n := by
  classical
  intro θ hθ
  let : NeZero (p ^ n) := ⟨pow_ne_zero n (expChar_ne_zero R p)⟩
  let : Fintype σ := Fintype.ofFinite σ
  let b := rootBasis (p ^ n) (0 : σ → R)
  let K : Hom.FiniteKernelModel (M.frobeniusHom p n θ hθ) := {
    coordinateAlgebra := CommAlgCat.of R (RootAlgebra (p ^ n) (0 : σ → R))
    finite := Module.Finite.of_basis b
    projective := by
      let := Module.Free.of_basis b
      infer_instance
    represents := frobeniusKernelRepresents M p n θ hθ }
  refine ⟨⟨frobenius_lifts M p n θ hθ, ⟨K⟩⟩, K, fun x => ?_⟩
  let := x.nontrivial
  let : Module.Free R K.coordinateAlgebra := Module.Free.of_basis b
  change Module.rankAtStalk (R := R) K.coordinateAlgebra x = p ^ (n * Nat.card σ)
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis b, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_eq_nat_card, pow_mul]
  rfl

end Langlands.FormalGroup.ModuleLaw
