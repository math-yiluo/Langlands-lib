import Langlands.GroupScheme.Reductive.WeilChartAlgebra
import Langlands.AlgebraicGeometry.FiniteEtaleChartDescentStatement

/-! # Naturality of the canonical coefficient isomorphisms in the test algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option maxRecDepth 4000

namespace Langlands.GroupScheme.WeilChart

open Langlands.Algebra.GraphIdempotent

variable {A A' C : Type u} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A' C]

section CoeffMap

variable {T T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)

/-- The map `T ⊗[A', f] C → T₁ ⊗[A', χ ∘ f] C` of coefficient algebras induced by a map
`χ : T ⟶ T₁` of test algebras. -/
def coeffMap (f : A' →ₐ[A] T) : ChartCoeff C f →+* ChartCoeff C (χ.hom.comp f) :=
  letI := chartAlgebra f
  letI := chartAlgebra (χ.hom.comp f)
  (Algebra.TensorProduct.map ({ χ.hom.toRingHom with commutes' := fun _ => rfl } : T →ₐ[A'] T₁)
    (AlgHom.id A' C)).toRingHom

theorem coeffMap_tmul (f : A' →ₐ[A] T) (t : T) (c : C) :
    coeffMap χ f (show ChartCoeff C f from letI := chartAlgebra f; t ⊗ₜ[A'] c) =
      (show ChartCoeff C (χ.hom.comp f) from
        letI := chartAlgebra (χ.hom.comp f); χ.hom t ⊗ₜ[A'] c) :=
  rfl

theorem coeffMap_algebraMap (f : A' →ₐ[A] T) (t : T) :
    coeffMap χ f (algebraMap T (ChartCoeff C f) t) =
      algebraMap T₁ (ChartCoeff C (χ.hom.comp f)) (χ.hom t) :=
  rfl

/-- A test algebra over `T₁`, regarded as a test algebra over `T` through `χ`. -/
abbrev resT (X : CommAlgCat.{u} (CommRingCat.of T₁)) : CommAlgCat.{u} (CommRingCat.of T) :=
  letI : Algebra T X := ((algebraMap T₁ X).comp χ.hom.toRingHom).toAlgebra
  CommAlgCat.of (CommRingCat.of T) X

/-- The identity of a test algebra over `T₁`, as a map of `A`-algebras from its restriction to
`T`. -/
def resTestHom (X : CommAlgCat.{u} (CommRingCat.of T₁)) : testA (resT χ X) ⟶ testA X :=
  CommAlgCat.ofHom (X := testA (resT χ X)) (Y := testA X)
    { toFun := fun x => (x : X)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun a => by
        change algebraMap T₁ X (χ.hom (algebraMap A T a)) = algebraMap T₁ X (algebraMap A T₁ a)
        rw [χ.hom.commutes] }

theorem chartX_resTestHom (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T₁)) :
    chartX (χ.hom.comp f) X = (resTestHom χ X).hom.comp (chartX f (resT χ X)) := by
  apply AlgHom.ext
  intro r
  rfl

/-- The map `(T ⊗[A', f] C) ⊗[T] X → (T₁ ⊗[A', χ ∘ f] C) ⊗[T₁] X` for a test algebra `X` over
`T₁`, through the cancellation isomorphisms. -/
def coeffTensorMap (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T₁)) :
    ChartCoeff C f ⊗[T] resT χ X →+* ChartCoeff C (χ.hom.comp f) ⊗[T₁] X :=
  (cancelEquiv (χ.hom.comp f) X).symm.toRingHom.comp
    (((letI := chartAlgebra (A := A) (T := testA (resT χ X)) (chartX f (resT χ X))
      letI := chartAlgebra (A := A) (T := testA X) (chartX (χ.hom.comp f) X)
      Algebra.TensorProduct.lTensor (S := C) C
        (chartMap' (resTestHom χ X) (chartX f (resT χ X)) (chartX (χ.hom.comp f) X)
          (chartX_resTestHom χ f X))).toRingHom).comp
      (cancelEquiv f (resT χ X)).toRingHom)

theorem cancelEquiv_coeffTensorMap (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T₁))
    (y : ChartCoeff C f ⊗[T] resT χ X) :
    cancelEquiv (χ.hom.comp f) X (coeffTensorMap χ f X y) =
      (letI := chartAlgebra (A := A) (T := testA (resT χ X)) (chartX f (resT χ X))
       letI := chartAlgebra (A := A) (T := testA X) (chartX (χ.hom.comp f) X)
       Algebra.TensorProduct.lTensor (S := C) C
        (chartMap' (resTestHom χ X) (chartX f (resT χ X)) (chartX (χ.hom.comp f) X)
          (chartX_resTestHom χ f X)) (cancelEquiv f (resT χ X) y)) := by
  rw [coeffTensorMap, RingHom.comp_apply, RingHom.comp_apply]
  exact RingEquiv.apply_symm_apply _ _

theorem coeffTensorMap_tmul (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T₁))
    (b : ChartCoeff C f) (x : X) :
    coeffTensorMap χ f X (b ⊗ₜ[T] (x : resT χ X)) = coeffMap χ f b ⊗ₜ[T₁] x := by
  apply (cancelEquiv (χ.hom.comp f) X).injective
  rw [cancelEquiv_coeffTensorMap]
  letI := chartAlgebra f
  induction b using TensorProduct.inductionOn with
  | tmul t c =>
    rw [cancelEquiv_tmul, coeffMap_tmul, cancelEquiv_tmul]
    rfl
  | add b b' hb hb' =>
    rw [TensorProduct.add_tmul, map_add, map_add, hb, hb', map_add, TensorProduct.add_tmul,
      map_add]

theorem coeffTensorMap_one_tmul (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T₁))
    (x : X) :
    coeffTensorMap χ f X ((1 : ChartCoeff C f) ⊗ₜ[T] (x : resT χ X)) =
      (1 : ChartCoeff C (χ.hom.comp f)) ⊗ₜ[T₁] x := by
  rw [coeffTensorMap_tmul, map_one]

/-- An algebra map out of `T₁ ⊗[A', χ ∘ f] C`, composed with `coeffMap`, as a map of
`T`-algebras. -/
def coeffAlgHom (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T₁))
    (ψ : ChartCoeff C (χ.hom.comp f) →ₐ[T₁] X) : ChartCoeff C f →ₐ[T] resT χ X :=
  { ψ.toRingHom.comp (coeffMap χ f) with
    commutes' := fun t => by
      change ψ (coeffMap χ f (algebraMap T (ChartCoeff C f) t)) = algebraMap T₁ X (χ.hom t)
      rw [coeffMap_algebraMap, ψ.commutes] }

theorem graphMul_coeffTensorMap (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T₁))
    (ψ : ChartCoeff C (χ.hom.comp f) →ₐ[T₁] X) (y : ChartCoeff C f ⊗[T] resT χ X) :
    graphMul ψ (coeffTensorMap χ f X y) = graphMul (coeffAlgHom χ f X ψ) y := by
  induction y using TensorProduct.inductionOn with
  | tmul b x =>
    rw [coeffTensorMap_tmul, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add]

theorem exists_coeffTensorMap_eq (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T₁))
    (b : ChartCoeff C (χ.hom.comp f)) :
    ∃ y : ChartCoeff C f ⊗[T] resT χ X, coeffTensorMap χ f X y = b ⊗ₜ[T₁] (1 : X) := by
  letI := chartAlgebra (χ.hom.comp f)
  induction b using TensorProduct.inductionOn with
  | tmul t c =>
    refine ⟨(show ChartCoeff C f from letI := chartAlgebra f; (1 : T) ⊗ₜ[A'] c) ⊗ₜ[T]
      (algebraMap T₁ X t : resT χ X), ?_⟩
    rw [coeffTensorMap_tmul, coeffMap_tmul, map_one, Algebra.algebraMap_eq_smul_one,
      ← TensorProduct.smul_tmul]
    congr 1
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add b b' hb hb' =>
    obtain ⟨y, hy⟩ := hb
    obtain ⟨y', hy'⟩ := hb'
    exact ⟨y + y', by rw [map_add, hy, hy', TensorProduct.add_tmul]⟩

/-- Graph idempotents over `T` push forward to graph idempotents over `T₁`. -/
theorem isGraphIdempotent_coeffTensorMap (f : A' →ₐ[A] T)
    (X : CommAlgCat.{u} (CommRingCat.of T₁)) {ψ : ChartCoeff C (χ.hom.comp f) →ₐ[T₁] X}
    {δ : ChartCoeff C f ⊗[T] resT χ X} (hδ : IsGraphIdempotent (coeffAlgHom χ f X ψ) δ) :
    IsGraphIdempotent ψ (coeffTensorMap χ f X δ) where
  isIdempotentElem := hδ.isIdempotentElem.map (coeffTensorMap χ f X)
  graphMul_eq_one := by rw [graphMul_coeffTensorMap, hδ.graphMul_eq_one]
  tmul_one_mul b := by
    obtain ⟨y, hy⟩ := exists_coeffTensorMap_eq χ f X b
    rw [← hy, ← map_mul, hδ.mul_eq y, map_mul, coeffTensorMap_one_tmul,
      ← graphMul_coeffTensorMap, hy, Algebra.TensorProduct.productMap_apply_tmul,
      AlgHom.id_apply, mul_one]

end CoeffMap

/-- Two algebra maps agree if the graph idempotent of the first is sent to `1` by the
multiplication map of the second. -/
theorem algHom_eq_of_graphMul_eq_one {R B X : Type u} [CommRing R] [CommRing B] [CommRing X]
    [Algebra R B] [Algebra R X] {φ ψ : B →ₐ[R] X} {e : B ⊗[R] X}
    (he : IsGraphIdempotent φ e) (hψ : graphMul ψ e = 1) : φ = ψ := by
  ext b
  have h := congrArg (graphMul ψ) (he.tmul_one_mul b)
  rw [map_mul, map_mul, hψ, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply, AlgHom.id_apply, map_one] at h
  simpa using h.symm

section Naturality

variable [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]
  {G : GroupScheme (Spec (CommRingCat.of A))}
  {H : GroupScheme (Spec (CommRingCat.of C))} [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (P : (GroupScheme.baseChange (Spec.algebraMap A A')).obj G ≅ AffineWeil.groupScheme A' C H)
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive H) (hsimple : ∀ s, IsAlmostSimple (geometricFiber H s))
  {T T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)

/-- The chart transfer of idempotents commutes with `coeffTensorMap`. -/
theorem chartIdemMap_coeffTensorMap (f₁ f₂ : A' →ₐ[A] T)
    (X : CommAlgCat.{u} (CommRingCat.of T₁)) {e : ChartCoeff C f₁ ⊗[T] resT χ X}
    (he : IsIdempotentElem e) :
    chartIdemMap P hR hred hsimple (χ.hom.comp f₁) (χ.hom.comp f₂) X
        (coeffTensorMap χ f₁ X e) =
      coeffTensorMap χ f₂ X (chartIdemMap P hR hred hsimple f₁ f₂ (resT χ X) e) := by
  apply (cancelEquiv (χ.hom.comp f₂) X).injective
  rw [chartIdemMap, RingEquiv.apply_symm_apply, cancelEquiv_coeffTensorMap,
    cancelEquiv_coeffTensorMap, chartIdemMap, RingEquiv.apply_symm_apply]
  exact chartTransfer_map' P hR hred hsimple (resTestHom χ X) (chartX f₁ (resT χ X))
    (chartX f₂ (resT χ X)) (chartX (χ.hom.comp f₁) X) (chartX (χ.hom.comp f₂) X)
    (chartX_resTestHom χ f₁ X) (chartX_resTestHom χ f₂ X)
    (he.map (cancelEquiv f₁ (resT χ X)))

/-- The defining property of the canonical isomorphisms, tested against an algebra map out of
`T₁ ⊗[A', χ ∘ f₁] C`. -/
theorem coeffAlgHom_comp_chartAlgEquiv (f₁ f₂ : A' →ₐ[A] T)
    (X : CommAlgCat.{u} (CommRingCat.of T₁)) (ψ : ChartCoeff C (χ.hom.comp f₁) →ₐ[T₁] X) :
    (coeffAlgHom χ f₁ X ψ).comp
        (chartAlgEquiv P hR hred hsimple f₁ f₂ : ChartCoeff C f₂ →ₐ[T] ChartCoeff C f₁) =
      coeffAlgHom χ f₂ X (ψ.comp
        (chartAlgEquiv P hR hred hsimple (χ.hom.comp f₁) (χ.hom.comp f₂) :
          ChartCoeff C (χ.hom.comp f₂) →ₐ[T₁] ChartCoeff C (χ.hom.comp f₁))) := by
  obtain ⟨δ, hδ⟩ := exists_isGraphIdempotent (A := T) (B := ChartCoeff C f₁) (T := resT χ X)
    (coeffAlgHom χ f₁ X ψ)
  have h1 := isGraphIdempotent_coeffTensorMap χ f₁ X hδ
  have h2 := (chartIdemTransfer P hR hred hsimple (χ.hom.comp f₁) (χ.hom.comp f₂)).algEquiv_spec
    X ψ _ h1
  have h3 := (chartIdemTransfer P hR hred hsimple f₁ f₂).algEquiv_spec (resT χ X)
    (coeffAlgHom χ f₁ X ψ) δ hδ
  have h4 := chartIdemMap_coeffTensorMap P hR hred hsimple χ f₁ f₂ X hδ.isIdempotentElem
  refine algHom_eq_of_graphMul_eq_one h3 ?_
  rw [← graphMul_coeffTensorMap]
  change graphMul _ (coeffTensorMap χ f₂ X
    (chartIdemMap P hR hred hsimple f₁ f₂ (resT χ X) δ)) = 1
  rw [← h4]
  exact h2.graphMul_eq_one

/-- **Naturality** of the canonical coefficient isomorphisms along a map of test algebras. -/
theorem chartAlgEquiv_coeffMap (f₁ f₂ : A' →ₐ[A] T) (x : ChartCoeff C f₂) :
    chartAlgEquiv P hR hred hsimple (χ.hom.comp f₁) (χ.hom.comp f₂) (coeffMap χ f₂ x) =
      coeffMap χ f₁ (chartAlgEquiv P hR hred hsimple f₁ f₂ x) := by
  have h := coeffAlgHom_comp_chartAlgEquiv P hR hred hsimple χ f₁ f₂
    (CommAlgCat.of (CommRingCat.of T₁) (ChartCoeff C (χ.hom.comp f₁)))
    (AlgHom.id T₁ (ChartCoeff C (χ.hom.comp f₁)))
  exact (DFunLike.congr_fun h x).symm

/-- The canonical coefficient isomorphisms satisfy the hypotheses of
`FiniteEtaleChartDescentStatement`, so the coefficient algebra descends. -/
theorem exists_chartDescent [Algebra.Etale A A']
    (hK : Langlands.AlgebraicGeometry.FiniteEtaleChartDescentStatement.{u})
    (hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A A')))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B)
      (_ : Module.Projective A B) (_ : Algebra.Etale A B) (e : A' ⊗[A] B ≃ₐ[A'] C),
      ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : A' →ₐ[A] T) (b : B),
        chartAlgEquiv P hR hred hsimple f₁ f₂
            (show ChartCoeff C f₂ from letI := chartAlgebra f₂; (1 : T) ⊗ₜ[A'] e (1 ⊗ₜ[A] b)) =
          (show ChartCoeff C f₁ from letI := chartAlgebra f₁; (1 : T) ⊗ₜ[A'] e (1 ⊗ₜ[A] b)) :=
  hK A A' C hsurj (fun _ f₁ f₂ => chartAlgEquiv P hR hred hsimple f₁ f₂)
    (fun _ f => chartAlgEquiv_self P hR hred hsimple f)
    (fun _ f₁ f₂ f₃ => chartAlgEquiv_trans P hR hred hsimple f₁ f₂ f₃)
    (fun _ _ χ f₁ f₂ x => chartAlgEquiv_coeffMap P hR hred hsimple χ f₁ f₂ x)

end Naturality

end Langlands.GroupScheme.WeilChart
