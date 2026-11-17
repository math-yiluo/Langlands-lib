import Langlands.GroupScheme.Reductive.WeilChartTransfer
import Langlands.GroupScheme.Reductive.WeilFactorIdemTransfer

/-! # The canonical algebra isomorphisms between chart coefficient algebras -/

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

variable {A A' C : Type u} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A' C]
  [Module.Finite A' C] [Module.Projective A' C]
  {G : GroupScheme (Spec (CommRingCat.of A))}
  {H : GroupScheme (Spec (CommRingCat.of C))} [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (P : (GroupScheme.baseChange (Spec.algebraMap A A')).obj G ≅ AffineWeil.groupScheme A' C H)

section MapGeneral

variable {T T₁ : CommAlgCat.{u} (CommRingCat.of A)}

/-- A map of test algebras, as a map of `A'`-algebras for chart maps that agree after
composition. -/
def chartMap' (χ : T ⟶ T₁) (f : A' →ₐ[A] T) (g : A' →ₐ[A] T₁) (h : g = χ.hom.comp f) :
    letI := chartAlgebra f
    letI := chartAlgebra g
    T →ₐ[A'] T₁ :=
  letI := chartAlgebra f
  letI := chartAlgebra g
  { χ.hom.toRingHom with
    commutes' := fun r => by
      change χ.hom (f r) = g r
      rw [h]
      rfl }

variable [Algebra.Etale A' C] (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive H) (hsimple : ∀ s, IsAlmostSimple (geometricFiber H s))

/-- The chart transfer is natural along a map of test algebras, for chart maps that agree after
composition. -/
theorem chartTransfer_map' (χ : T ⟶ T₁) (f₁ f₂ : A' →ₐ[A] T) (g₁ g₂ : A' →ₐ[A] T₁)
    (h₁ : g₁ = χ.hom.comp f₁) (h₂ : g₂ = χ.hom.comp f₂)
    {e : letI := chartAlgebra f₁; C ⊗[A'] T} (he : IsIdempotentElem e) :
    chartTransfer P hR hred hsimple g₁ g₂
        (letI := chartAlgebra f₁
         letI := chartAlgebra g₁
         Algebra.TensorProduct.lTensor (S := C) C (chartMap' χ f₁ g₁ h₁) e) =
      (letI := chartAlgebra f₂
       letI := chartAlgebra g₂
       Algebra.TensorProduct.lTensor (S := C) C (chartMap' χ f₂ g₂ h₂)
        (chartTransfer P hR hred hsimple f₁ f₂ e)) := by
  subst h₁ h₂
  exact chartTransfer_map P hR hred hsimple χ f₁ f₂ he

end MapGeneral

section Coeff

variable {T : CommAlgCat.{u} (CommRingCat.of A)} (f : A' →ₐ[A] T)

variable (C) in
/-- The coefficient algebra `T ⊗[A', f] C` of a chart map `f : A' → T`, as a `T`-algebra. -/
def ChartCoeff : Type u := letI := chartAlgebra f; T ⊗[A'] C

instance : CommRing (ChartCoeff C f) :=
  letI := chartAlgebra f; (inferInstance : CommRing (T ⊗[A'] C))

instance : Algebra T (ChartCoeff C f) :=
  letI := chartAlgebra f; (inferInstance : Algebra T (T ⊗[A'] C))

instance : Module.Finite T (ChartCoeff C f) :=
  letI := chartAlgebra f; (inferInstance : Module.Finite T (T ⊗[A'] C))

instance : Module.Projective T (ChartCoeff C f) :=
  letI := chartAlgebra f; (inferInstance : Module.Projective T (T ⊗[A'] C))

instance [Algebra.Etale A' C] : Algebra.Etale T (ChartCoeff C f) :=
  letI := chartAlgebra f; (inferInstance : Algebra.Etale T (T ⊗[A'] C))

end Coeff

section Cancel

variable {T : CommAlgCat.{u} (CommRingCat.of A)} (f : A' →ₐ[A] T)
  (X : CommAlgCat.{u} (CommRingCat.of T))

/-- A test algebra over `T`, regarded as an `A`-algebra. -/
abbrev testA : CommAlgCat.{u} (CommRingCat.of A) :=
  letI : Algebra A X := Algebra.compHom X (algebraMap A T)
  CommAlgCat.of (CommRingCat.of A) X

/-- The chart map of a test algebra over `T`. -/
def chartX : A' →ₐ[A] testA X :=
  { (algebraMap T X).comp f.toRingHom with
    commutes' := fun a => by
      change algebraMap T X (f (algebraMap A A' a)) = algebraMap T X (algebraMap A T a)
      rw [f.commutes] }

/-- Cancellation of the test ring: `(T ⊗[A', f] C) ⊗[T] X ≃ C ⊗[A', f_X] X`. -/
def cancelEquiv :
    ChartCoeff C f ⊗[T] X ≃+*
      (letI := chartAlgebra (A := A) (T := testA X) (chartX f X); C ⊗[A'] testA X) :=
  letI := chartAlgebra f
  letI : Algebra A' X := chartAlgebra (A := A) (T := testA X) (chartX f X)
  haveI : IsScalarTower A' T X := IsScalarTower.of_algebraMap_eq' rfl
  ((Algebra.TensorProduct.comm T (T ⊗[A'] C) X).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange A' T T X C).toRingEquiv).trans
      (Algebra.TensorProduct.comm A' X C).toRingEquiv

omit [Module.Finite A' C] [Module.Projective A' C] in
theorem cancelEquiv_tmul (t : T) (c : C) (x : X) :
    cancelEquiv f X ((show ChartCoeff C f from letI := chartAlgebra f; t ⊗ₜ[A'] c) ⊗ₜ[T] x) =
      (letI := chartAlgebra (A := A) (T := testA X) (chartX f X)
       c ⊗ₜ[A'] (algebraMap T X t * x : X)) := by
  letI := chartAlgebra f
  letI : Algebra A' X := chartAlgebra (A := A) (T := testA X) (chartX f X)
  haveI : IsScalarTower A' T X := IsScalarTower.of_algebraMap_eq' rfl
  change Algebra.TensorProduct.comm A' X C (Algebra.TensorProduct.cancelBaseChange A' T T X C
    (Algebra.TensorProduct.comm T (T ⊗[A'] C) X ((t ⊗ₜ[A'] c) ⊗ₜ[T] x))) = _
  rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
    Algebra.TensorProduct.comm_tmul, Algebra.smul_def]

end Cancel

section Transfer

variable {T : CommAlgCat.{u} (CommRingCat.of A)}

/-- A map of test algebras over `T`, as a map of `A`-algebras. -/
def testHom {X Y : CommAlgCat.{u} (CommRingCat.of T)} (χ : X ⟶ Y) : testA X ⟶ testA Y :=
  letI : Algebra A X := Algebra.compHom X (algebraMap A T)
  letI : Algebra A Y := Algebra.compHom Y (algebraMap A T)
  CommAlgCat.ofHom (X := X) (Y := Y)
    { χ.hom.toRingHom with commutes' := fun a => χ.hom.commutes (algebraMap A T a) }

theorem chartX_testHom (f : A' →ₐ[A] T) {X Y : CommAlgCat.{u} (CommRingCat.of T)} (χ : X ⟶ Y) :
    chartX f Y = (testHom χ).hom.comp (chartX f X) := by
  apply AlgHom.ext
  intro r
  exact (χ.hom.commutes (f r)).symm

omit [Module.Finite A' C] [Module.Projective A' C] in
/-- The cancellation is natural in the test algebra. -/
theorem cancelEquiv_lT (f : A' →ₐ[A] T) {X Y : CommAlgCat.{u} (CommRingCat.of T)} (χ : X ⟶ Y)
    (e : ChartCoeff C f ⊗[T] X) :
    cancelEquiv f Y (WeilFactor.lT (B := ChartCoeff C f) χ e) =
      (letI := chartAlgebra (A := A) (T := testA X) (chartX f X)
       letI := chartAlgebra (A := A) (T := testA Y) (chartX f Y)
       Algebra.TensorProduct.lTensor (S := C) C
        (chartMap' (testHom χ) (chartX f X) (chartX f Y) (chartX_testHom f χ))
        (cancelEquiv f X e)) := by
  letI := chartAlgebra f
  letI := chartAlgebra (A := A) (T := testA X) (chartX f X)
  letI := chartAlgebra (A := A) (T := testA Y) (chartX f Y)
  induction e using TensorProduct.inductionOn with
  | tmul b x =>
    induction b using TensorProduct.inductionOn with
    | tmul t c =>
      rw [WeilFactor.lT_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        cancelEquiv_tmul, cancelEquiv_tmul, Algebra.TensorProduct.map_tmul]
      congr 1
      change algebraMap T Y t * χ.hom x = χ.hom (algebraMap T X t * x)
      rw [map_mul, χ.hom.commutes]
    | add b b' hb hb' =>
      simp only [TensorProduct.add_tmul, map_add, hb, hb']
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Transfer

section IdemTransfer

variable [Algebra.Etale A' C] (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive H) (hsimple : ∀ s, IsAlmostSimple (geometricFiber H s))
  {T : CommAlgCat.{u} (CommRingCat.of A)}

/-- The chart transfer of idempotents of `(T ⊗[A', f₁] C) ⊗[T] X`, for a test algebra `X`
over `T`. -/
def chartIdemMap (f₁ f₂ : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T))
    (e : ChartCoeff C f₁ ⊗[T] X) : ChartCoeff C f₂ ⊗[T] X :=
  (cancelEquiv f₂ X).symm
    (chartTransfer P hR hred hsimple (chartX f₁ X) (chartX f₂ X) (cancelEquiv f₁ X e))

theorem chartIdemMap_idem (f₁ f₂ : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T))
    {e : ChartCoeff C f₁ ⊗[T] X} (he : IsIdempotentElem e) :
    IsIdempotentElem (chartIdemMap P hR hred hsimple f₁ f₂ X e) :=
  (chartTransfer_isIdempotentElem P hR hred hsimple (chartX f₁ X) (chartX f₂ X)
    (he.map (cancelEquiv f₁ X))).map (cancelEquiv f₂ X).symm

theorem chartIdemMap_lT (f₁ f₂ : A' →ₐ[A] T) {X Y : CommAlgCat.{u} (CommRingCat.of T)}
    (χ : X ⟶ Y) {e : ChartCoeff C f₁ ⊗[T] X} (he : IsIdempotentElem e) :
    chartIdemMap P hR hred hsimple f₁ f₂ Y (WeilFactor.lT (B := ChartCoeff C f₁) χ e) =
      WeilFactor.lT (B := ChartCoeff C f₂) χ (chartIdemMap P hR hred hsimple f₁ f₂ X e) := by
  apply (cancelEquiv f₂ Y).injective
  rw [chartIdemMap, RingEquiv.apply_symm_apply, cancelEquiv_lT, cancelEquiv_lT, chartIdemMap,
    RingEquiv.apply_symm_apply]
  exact chartTransfer_map' P hR hred hsimple (testHom χ) (chartX f₁ X) (chartX f₂ X)
    (chartX f₁ Y) (chartX f₂ Y) (chartX_testHom f₁ χ) (chartX_testHom f₂ χ)
    (he.map (cancelEquiv f₁ X))

theorem chartIdemMap_mul (f₁ f₂ : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T))
    {e e' : ChartCoeff C f₁ ⊗[T] X} (he : IsIdempotentElem e) (he' : IsIdempotentElem e') :
    chartIdemMap P hR hred hsimple f₁ f₂ X (e' * e) =
      chartIdemMap P hR hred hsimple f₁ f₂ X e' * chartIdemMap P hR hred hsimple f₁ f₂ X e := by
  rw [chartIdemMap, chartIdemMap, chartIdemMap, map_mul (cancelEquiv f₁ X),
    chartTransfer_mul P hR hred hsimple (chartX f₁ X) (chartX f₂ X) (he.map (cancelEquiv f₁ X))
      (he'.map (cancelEquiv f₁ X)), map_mul]

theorem chartIdemMap_zero (f₁ f₂ : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T)) :
    chartIdemMap P hR hred hsimple f₁ f₂ X 0 = 0 := by
  rw [chartIdemMap, map_zero, chartTransfer_zero, map_zero]

theorem chartIdemMap_chartIdemMap (f₁ f₂ : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T))
    {e : ChartCoeff C f₁ ⊗[T] X} (he : IsIdempotentElem e) :
    chartIdemMap P hR hred hsimple f₂ f₁ X (chartIdemMap P hR hred hsimple f₁ f₂ X e) = e := by
  rw [chartIdemMap, chartIdemMap, RingEquiv.apply_symm_apply,
    chartTransfer_trans P hR hred hsimple (chartX f₁ X) (chartX f₂ X) (chartX f₁ X)
      (he.map (cancelEquiv f₁ X)),
    chartTransfer_self P hR hred hsimple (chartX f₁ X) (he.map (cancelEquiv f₁ X)),
    RingEquiv.symm_apply_apply]

/-- The chart transfer between the coefficient algebras of two chart maps, as a transfer of
idempotents over every test algebra. -/
def chartIdemTransfer (f₁ f₂ : A' →ₐ[A] T) :
    WeilFactor.IdemTransfer T (ChartCoeff C f₁) (ChartCoeff C f₂) where
  map := chartIdemMap P hR hred hsimple f₁ f₂
  inv := chartIdemMap P hR hred hsimple f₂ f₁
  map_idem X _ he := chartIdemMap_idem P hR hred hsimple f₁ f₂ X he
  inv_idem X _ he := chartIdemMap_idem P hR hred hsimple f₂ f₁ X he
  map_lT χ _ he := chartIdemMap_lT P hR hred hsimple f₁ f₂ χ he
  inv_lT χ _ he := chartIdemMap_lT P hR hred hsimple f₂ f₁ χ he
  map_mul X _ _ he hf := chartIdemMap_mul P hR hred hsimple f₁ f₂ X he hf
  inv_mul X _ _ he hf := chartIdemMap_mul P hR hred hsimple f₂ f₁ X he hf
  map_zero X := chartIdemMap_zero P hR hred hsimple f₁ f₂ X
  inv_zero X := chartIdemMap_zero P hR hred hsimple f₂ f₁ X
  inv_map X _ he := chartIdemMap_chartIdemMap P hR hred hsimple f₁ f₂ X he
  map_inv X _ he := chartIdemMap_chartIdemMap P hR hred hsimple f₂ f₁ X he

/-- **The canonical coefficient isomorphism** between two chart maps `f₁ f₂ : A' → T`. -/
def chartAlgEquiv (f₁ f₂ : A' →ₐ[A] T) : ChartCoeff C f₂ ≃ₐ[T] ChartCoeff C f₁ :=
  (chartIdemTransfer P hR hred hsimple f₁ f₂).algEquiv

theorem chartIdemMap_trans (f₁ f₂ f₃ : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T))
    {e : ChartCoeff C f₁ ⊗[T] X} (he : IsIdempotentElem e) :
    chartIdemMap P hR hred hsimple f₂ f₃ X (chartIdemMap P hR hred hsimple f₁ f₂ X e) =
      chartIdemMap P hR hred hsimple f₁ f₃ X e := by
  rw [chartIdemMap, chartIdemMap, RingEquiv.apply_symm_apply,
    chartTransfer_trans P hR hred hsimple (chartX f₁ X) (chartX f₂ X) (chartX f₃ X)
      (he.map (cancelEquiv f₁ X)), chartIdemMap]

theorem chartIdemMap_self (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T))
    {e : ChartCoeff C f ⊗[T] X} (he : IsIdempotentElem e) :
    chartIdemMap P hR hred hsimple f f X e = e := by
  rw [chartIdemMap, chartTransfer_self P hR hred hsimple (chartX f X) (he.map (cancelEquiv f X)),
    RingEquiv.symm_apply_apply]

/-- The canonical coefficient isomorphism of a chart map with itself is the identity. -/
theorem chartAlgEquiv_self (f : A' →ₐ[A] T) :
    chartAlgEquiv P hR hred hsimple f f = AlgEquiv.refl := by
  symm
  apply WeilFactor.IdemTransfer.algEquiv_unique
  intro X φ e he
  have hm : (chartIdemTransfer P hR hred hsimple f f).map X e = e :=
    chartIdemMap_self P hR hred hsimple f X he.isIdempotentElem
  rw [hm]
  have hφ : φ.comp ((AlgEquiv.refl : ChartCoeff C f ≃ₐ[T] ChartCoeff C f) :
      ChartCoeff C f →ₐ[T] ChartCoeff C f) = φ := by
    ext
    rfl
  rw [hφ]
  exact he

/-- **Cocycle condition** for the canonical coefficient isomorphisms. -/
theorem chartAlgEquiv_trans (f₁ f₂ f₃ : A' →ₐ[A] T) :
    (chartAlgEquiv P hR hred hsimple f₂ f₃).trans (chartAlgEquiv P hR hred hsimple f₁ f₂) =
      chartAlgEquiv P hR hred hsimple f₁ f₃ := by
  apply WeilFactor.IdemTransfer.algEquiv_unique
  intro X φ e he
  have hm : (chartIdemTransfer P hR hred hsimple f₁ f₃).map X e =
      (chartIdemTransfer P hR hred hsimple f₂ f₃).map X
        ((chartIdemTransfer P hR hred hsimple f₁ f₂).map X e) :=
    (chartIdemMap_trans P hR hred hsimple f₁ f₂ f₃ X he.isIdempotentElem).symm
  rw [hm]
  exact (chartIdemTransfer P hR hred hsimple f₂ f₃).algEquiv_spec X _ _
    ((chartIdemTransfer P hR hred hsimple f₁ f₂).algEquiv_spec X φ e he)

end IdemTransfer

end Langlands.GroupScheme.WeilChart
