import Langlands.GroupScheme.Reductive.WeilChartNaturality

/-! # The diagonal idempotent of a descended coefficient algebra through a chart -/

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

variable {A A' C B : Type u} [CommRing A] [CommRing A'] [CommRing C] [CommRing B]
  [Algebra A A'] [Algebra A' C] [Algebra A B] (e : A' ⊗[A] B ≃ₐ[A'] C)

section Diag

variable {T : CommAlgCat.{u} (CommRingCat.of A)}

theorem chartAlgebra_isScalarTower (f : A' →ₐ[A] T) :
    letI := chartAlgebra f
    IsScalarTower A A' T :=
  letI := chartAlgebra f
  IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm

/-- The algebra map `C ≃ A' ⊗[A] B → T`, `a' ⊗ b ↦ f a' * φ b`, of a chart map `f` and an
algebra map `φ : B → T`. -/
def diagMap (φ : B →ₐ[A] T) (f : A' →ₐ[A] T) :
    letI := chartAlgebra f
    C →ₐ[A'] T :=
  letI := chartAlgebra f
  haveI := chartAlgebra_isScalarTower f
  (Algebra.TensorProduct.lift (Algebra.ofId A' T) φ fun _ _ => Commute.all _ _).comp
    (e.symm : C →ₐ[A'] A' ⊗[A] B)

theorem diagMap_tmul (φ : B →ₐ[A] T) (f : A' →ₐ[A] T) (a : A') (b : B) :
    diagMap e φ f (e (a ⊗ₜ[A] b)) = f a * φ b := by
  letI := chartAlgebra f
  haveI := chartAlgebra_isScalarTower f
  change Algebra.TensorProduct.lift (Algebra.ofId A' T) φ (fun _ _ => Commute.all _ _)
    (e.symm (e (a ⊗ₜ[A] b))) = _
  rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul]
  rfl

theorem diagMap_map {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) (φ : B →ₐ[A] T)
    (f : A' →ₐ[A] T) :
    (letI := chartAlgebra f
     letI := chartAlgebra (χ.hom.comp f)
     (chartMap f χ).comp (diagMap e φ f)) = diagMap e (χ.hom.comp φ) (χ.hom.comp f) := by
  letI := chartAlgebra f
  letI := chartAlgebra (χ.hom.comp f)
  apply AlgHom.ext
  intro c
  obtain ⟨x, rfl⟩ := e.surjective c
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [AlgHom.comp_apply, diagMap_tmul, diagMap_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

variable [Algebra.Etale A' C]

/-- The graph idempotent of `diagMap e φ f` in `C ⊗[A', f] T`. -/
def diagIdem (φ : B →ₐ[A] T) (f : A' →ₐ[A] T) : letI := chartAlgebra f; C ⊗[A'] T :=
  letI := chartAlgebra f
  Classical.choose (exists_isGraphIdempotent (A := A') (B := C) (T := T) (diagMap e φ f))

theorem diagIdem_spec (φ : B →ₐ[A] T) (f : A' →ₐ[A] T) :
    letI := chartAlgebra f
    IsGraphIdempotent (diagMap e φ f) (diagIdem e φ f) :=
  letI := chartAlgebra f
  Classical.choose_spec (exists_isGraphIdempotent (A := A') (B := C) (T := T) (diagMap e φ f))

theorem diagIdem_isIdempotentElem (φ : B →ₐ[A] T) (f : A' →ₐ[A] T) :
    letI := chartAlgebra f
    IsIdempotentElem (diagIdem e φ f) :=
  letI := chartAlgebra f
  (diagIdem_spec e φ f).isIdempotentElem

theorem diagIdem_map {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) (φ : B →ₐ[A] T)
    (f : A' →ₐ[A] T) :
    (letI := chartAlgebra f
     letI := chartAlgebra (χ.hom.comp f)
     Algebra.TensorProduct.lTensor (S := C) C (chartMap f χ) (diagIdem e φ f)) =
      diagIdem e (χ.hom.comp φ) (χ.hom.comp f) := by
  letI := chartAlgebra f
  letI := chartAlgebra (χ.hom.comp f)
  have h := (diagIdem_spec e φ f).map (chartMap f χ)
  rw [diagMap_map] at h
  exact h.unique (diagIdem_spec e (χ.hom.comp φ) (χ.hom.comp f))

end Diag

section Cancel

variable {T : CommAlgCat.{u} (CommRingCat.of A)}

theorem chartCoeff_tmul_eq (f : A' →ₐ[A] T) {X : Type u} [CommRing X] [Algebra T X]
    (ρ : ChartCoeff C f →ₐ[T] X) (t : T) (c : C) :
    ρ (show ChartCoeff C f from letI := chartAlgebra f; t ⊗ₜ[A'] c) =
      algebraMap T X t * ρ (show ChartCoeff C f from letI := chartAlgebra f; (1 : T) ⊗ₜ[A'] c) := by
  letI := chartAlgebra f
  rw [← ρ.commutes, ← map_mul]
  congr 1
  change t ⊗ₜ[A'] c = (t ⊗ₜ[A'] (1 : C)) * ((1 : T) ⊗ₜ[A'] c)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The restriction to `C` of an algebra map out of `T ⊗[A', f] C`, as a map of
`A'`-algebras into a test algebra over `T`. -/
def coeffRestrict (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T))
    (ρ : ChartCoeff C f →ₐ[T] X) :
    letI := chartAlgebra (A := A) (T := testA X) (chartX f X)
    C →ₐ[A'] testA X :=
  letI := chartAlgebra f
  letI := chartAlgebra (A := A) (T := testA X) (chartX f X)
  { ρ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := A') (A := T) (B := C)).toRingHom with
    commutes' := fun a => by
      change ρ ((1 : T) ⊗ₜ[A'] algebraMap A' C a) = algebraMap T X (f a)
      rw [← ρ.commutes]
      congr 1
      change (1 : T) ⊗ₜ[A'] algebraMap A' C a = f a ⊗ₜ[A'] (1 : C)
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      rfl }

theorem coeffRestrict_apply (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T))
    (ρ : ChartCoeff C f →ₐ[T] X) (c : C) :
    coeffRestrict f X ρ c =
      ρ (show ChartCoeff C f from letI := chartAlgebra f; (1 : T) ⊗ₜ[A'] c) :=
  rfl

theorem graphMul_cancelEquiv (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T))
    (ρ : ChartCoeff C f →ₐ[T] X) (y : ChartCoeff C f ⊗[T] X) :
    (letI := chartAlgebra (A := A) (T := testA X) (chartX f X)
     graphMul (coeffRestrict f X ρ) (cancelEquiv f X y)) = graphMul ρ y := by
  letI := chartAlgebra (A := A) (T := testA X) (chartX f X)
  induction y using TensorProduct.inductionOn with
  | tmul b x =>
    letI := chartAlgebra f
    induction b using TensorProduct.inductionOn with
    | tmul t c =>
      rw [cancelEquiv_tmul, Algebra.TensorProduct.productMap_apply_tmul,
        Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply, AlgHom.id_apply,
        coeffRestrict_apply, chartCoeff_tmul_eq f ρ t c]
      change ρ _ * (algebraMap T X t * x) = algebraMap T X t * ρ _ * x
      ring
    | add b b' hb hb' =>
      rw [TensorProduct.add_tmul, map_add, map_add, hb, hb', map_add]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add]

/-- The cancellation isomorphism sends graph idempotents to graph idempotents. -/
theorem isGraphIdempotent_cancelEquiv (f : A' →ₐ[A] T) (X : CommAlgCat.{u} (CommRingCat.of T))
    {ρ : ChartCoeff C f →ₐ[T] X} {δ : ChartCoeff C f ⊗[T] X} (hδ : IsGraphIdempotent ρ δ) :
    letI := chartAlgebra (A := A) (T := testA X) (chartX f X)
    IsGraphIdempotent (coeffRestrict f X ρ) (cancelEquiv f X δ) := by
  letI := chartAlgebra (A := A) (T := testA X) (chartX f X)
  refine ⟨hδ.isIdempotentElem.map (cancelEquiv f X), ?_, fun c => ?_⟩
  · rw [graphMul_cancelEquiv, hδ.graphMul_eq_one]
  · have h1 : c ⊗ₜ[A'] (1 : testA X) = cancelEquiv f X
        ((show ChartCoeff C f from letI := chartAlgebra f; (1 : T) ⊗ₜ[A'] c) ⊗ₜ[T] (1 : X)) := by
      rw [cancelEquiv_tmul, map_one, mul_one]
    have h2 : ∀ x : X, (1 : C) ⊗ₜ[A'] (x : testA X) =
        cancelEquiv f X ((1 : ChartCoeff C f) ⊗ₜ[T] x) := by
      intro x
      letI := chartAlgebra f
      change _ = cancelEquiv f X ((show ChartCoeff C f from (1 : T) ⊗ₜ[A'] (1 : C)) ⊗ₜ[T] x)
      rw [cancelEquiv_tmul, map_one, one_mul]
    rw [h1, ← map_mul, hδ.mul_eq, map_mul, ← h2, Algebra.TensorProduct.productMap_apply_tmul,
      AlgHom.id_apply, mul_one, coeffRestrict_apply]

end Cancel

section Invariance

variable {T : CommAlgCat.{u} (CommRingCat.of A)}

/-- A test algebra, regarded as an algebra over itself. -/
abbrev selfAlg (T : CommAlgCat.{u} (CommRingCat.of A)) : CommAlgCat.{u} (CommRingCat.of T) :=
  CommAlgCat.of (CommRingCat.of T) T

/-- The identity of `T`, as a map of `A`-algebras from `testA (selfAlg T)`. -/
def selfHom (T : CommAlgCat.{u} (CommRingCat.of A)) : testA (selfAlg T) ⟶ T :=
  ConcreteCategory.ofHom (C := CommAlgCat.{u} (CommRingCat.of A)) (X := testA (selfAlg T)) (Y := T)
    (@AlgHom.mk (CommRingCat.of A) (testA (selfAlg T)) T _ _ _
      (CommAlgCat.algebra (testA (selfAlg T))) (CommAlgCat.algebra T) (RingHom.id T)
      (fun _ => rfl))

theorem selfHom_apply (T : CommAlgCat.{u} (CommRingCat.of A)) (x : T) :
    (selfHom T).hom x = x :=
  rfl

/-- `f = χ ∘ g`, for chart maps `g` and `f` and a map `χ` of test algebras. -/
def IsChartComp {T₀ T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T₀ ⟶ T₁)
    (g : A' →ₐ[A] T₀) (f : A' →ₐ[A] T₁) : Prop :=
  f = χ.hom.comp g

theorem eq_comp_of_apply {T₀ T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T₀ ⟶ T₁)
    (g : A' →ₐ[A] T₀) (f : A' →ₐ[A] T₁) (h : ∀ r, χ.hom (g r) = f r) : IsChartComp χ g f := by
  apply AlgHom.ext
  intro r
  exact (h r).symm

theorem isChartComp_selfHom (f : A' →ₐ[A] T) :
    IsChartComp (selfHom T) (chartX f (selfAlg T)) f :=
  eq_comp_of_apply _ _ _ fun _ => rfl


/-- The element `t ⊗ c` of `T ⊗[A', f] C`. -/
def coeffTmul (f : A' →ₐ[A] T) (t : T) (c : C) : ChartCoeff C f :=
  letI := chartAlgebra f
  t ⊗ₜ[A'] c

theorem coeffTmul_eq (f : A' →ₐ[A] T) {X : Type u} [CommRing X] [Algebra T X]
    {F : Type u} [FunLike F (ChartCoeff C f) X] [AlgHomClass F T (ChartCoeff C f) X]
    (ρ : F) (t : T) (c : C) :
    ρ (coeffTmul f t c) = algebraMap T X t * ρ (coeffTmul f 1 c) :=
  chartCoeff_tmul_eq f (AlgHom.ofClass ρ) t c

theorem coeffTmul_smul (f : A' →ₐ[A] T) (a : A') (y : C) :
    coeffTmul f 1 (a • y) = algebraMap T (ChartCoeff C f) (f a) * coeffTmul f 1 y := by
  letI := chartAlgebra f
  change _ = (f a ⊗ₜ[A'] (1 : C)) * ((1 : T) ⊗ₜ[A'] y)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, coeffTmul, ← TensorProduct.smul_tmul,
    Algebra.smul_def, mul_one]
  rfl

theorem coeffTmul_add (f : A' →ₐ[A] T) (y y' : C) :
    coeffTmul f 1 (y + y') = coeffTmul f 1 y + coeffTmul f 1 y' := by
  letI := chartAlgebra f
  exact TensorProduct.tmul_add _ _ _

/-- The `T`-point of `T ⊗[A', f] C` extending `diagMap e φ f`. -/
def coeffPoint (φ : B →ₐ[A] T) (f : A' →ₐ[A] T) : ChartCoeff C f →ₐ[T] selfAlg T :=
  letI := chartAlgebra f
  Algebra.TensorProduct.lift (AlgHom.id T T) (diagMap e φ f) fun _ _ => Commute.all _ _

theorem coeffPoint_one_tmul (φ : B →ₐ[A] T) (f : A' →ₐ[A] T) (c : C) :
    coeffPoint e φ f (coeffTmul f 1 c) = diagMap e φ f c := by
  letI := chartAlgebra f
  change Algebra.TensorProduct.lift (AlgHom.id T T) (diagMap e φ f) (fun _ _ => Commute.all _ _)
    ((1 : T) ⊗ₜ[A'] c) = _
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, one_mul]

theorem descentEquiv_tmul (a : A') (b : B) : e (a ⊗ₜ[A] b) = a • e (1 ⊗ₜ[A] b) := by
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]
  {G : GroupScheme (Spec (CommRingCat.of A))}
  {H : GroupScheme (Spec (CommRingCat.of C))} [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (P : (GroupScheme.baseChange (Spec.algebraMap A A')).obj G ≅ AffineWeil.groupScheme A' C H)
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive H) (hsimple : ∀ s, IsAlmostSimple (geometricFiber H s))

theorem coeffPoint_comp_chartAlgEquiv (φ : B →ₐ[A] T) (f₁ f₂ : A' →ₐ[A] T)
    (hinv : ∀ b : B, chartAlgEquiv P hR hred hsimple f₁ f₂ (coeffTmul f₂ 1 (e (1 ⊗ₜ[A] b))) =
      coeffTmul f₁ 1 (e (1 ⊗ₜ[A] b))) :
    (coeffPoint e φ f₁).comp
        (chartAlgEquiv P hR hred hsimple f₁ f₂ : ChartCoeff C f₂ →ₐ[T] ChartCoeff C f₁) =
      coeffPoint e φ f₂ := by
  have hone : ∀ c : C, coeffPoint e φ f₁ (chartAlgEquiv P hR hred hsimple f₁ f₂
      (coeffTmul f₂ 1 c)) = coeffPoint e φ f₂ (coeffTmul f₂ 1 c) := by
    intro c
    obtain ⟨y, rfl⟩ := e.surjective c
    induction y using TensorProduct.inductionOn with
    | tmul a b =>
      rw [coeffPoint_one_tmul, diagMap_tmul, descentEquiv_tmul, coeffTmul_smul, map_mul, AlgEquiv.commutes,
        hinv, map_mul, AlgHom.commutes, coeffPoint_one_tmul, diagMap_tmul, map_one, one_mul]
      rfl
    | add y y' hy hy' =>
      rw [map_add, coeffTmul_add, map_add, map_add, hy, hy', map_add]
  apply AlgHom.ext
  intro x
  letI := chartAlgebra f₂
  induction x using TensorProduct.inductionOn with
  | tmul t c =>
    change coeffPoint e φ f₁ (chartAlgEquiv P hR hred hsimple f₁ f₂ (coeffTmul f₂ t c)) =
      coeffPoint e φ f₂ (coeffTmul f₂ t c)
    rw [coeffTmul_eq f₂ (chartAlgEquiv P hR hred hsimple f₁ f₂),
      coeffTmul_eq f₂ (coeffPoint e φ f₂), map_mul, AlgHom.commutes, hone c]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx']

omit [Module.Finite A' C] [Module.Projective A' C] in
theorem lTensor_cancelEquiv_eq_diagIdem (φ : B →ₐ[A] T) (f : A' →ₐ[A] T)
    (h : IsChartComp (selfHom T) (chartX f (selfAlg T)) f)
    {δ : ChartCoeff C f ⊗[T] selfAlg T} (hδ : IsGraphIdempotent (coeffPoint e φ f) δ) :
    (letI := chartAlgebra (A := A) (T := testA (selfAlg T)) (chartX f (selfAlg T))
     letI := chartAlgebra f
     Algebra.TensorProduct.lTensor (S := C) C (chartMap' (selfHom T) (chartX f (selfAlg T)) f h)
      (cancelEquiv f (selfAlg T) δ)) = diagIdem e φ f := by
  letI := chartAlgebra (A := A) (T := testA (selfAlg T)) (chartX f (selfAlg T))
  letI := chartAlgebra f
  have h1 := (isGraphIdempotent_cancelEquiv f (selfAlg T) hδ).map
    (chartMap' (selfHom T) (chartX f (selfAlg T)) f h)
  have hc : (chartMap' (selfHom T) (chartX f (selfAlg T)) f h).comp
      (coeffRestrict f (selfAlg T) (coeffPoint e φ f)) = diagMap e φ f := by
    apply AlgHom.ext
    intro c
    exact coeffPoint_one_tmul e φ f c
  rw [hc] at h1
  exact h1.unique (diagIdem_spec e φ f)

/-- **Chart independence** of the diagonal idempotent: the chart transfer carries the diagonal
idempotent through `f₁` to the diagonal idempotent through `f₂`. -/
theorem chartTransfer_diagIdem (φ : B →ₐ[A] T) (f₁ f₂ : A' →ₐ[A] T)
    (hinv : ∀ b : B, chartAlgEquiv P hR hred hsimple f₁ f₂ (coeffTmul f₂ 1 (e (1 ⊗ₜ[A] b))) =
      coeffTmul f₁ 1 (e (1 ⊗ₜ[A] b))) :
    chartTransfer P hR hred hsimple f₁ f₂ (diagIdem e φ f₁) = diagIdem e φ f₂ := by
  obtain ⟨δ₁, hδ₁⟩ := exists_isGraphIdempotent (A := T) (B := ChartCoeff C f₁) (T := selfAlg T)
    (coeffPoint e φ f₁)
  obtain ⟨δ₂, hδ₂⟩ := exists_isGraphIdempotent (A := T) (B := ChartCoeff C f₂) (T := selfAlg T)
    (coeffPoint e φ f₂)
  have h1 := (chartIdemTransfer P hR hred hsimple f₁ f₂).algEquiv_spec (selfAlg T)
    (coeffPoint e φ f₁) δ₁ hδ₁
  have h2 : chartIdemMap P hR hred hsimple f₁ f₂ (selfAlg T) δ₁ = δ₂ := by
    have h := coeffPoint_comp_chartAlgEquiv e P hR hred hsimple φ f₁ f₂ hinv
    change IsGraphIdempotent ((coeffPoint e φ f₁).comp
      (chartAlgEquiv P hR hred hsimple f₁ f₂ : ChartCoeff C f₂ →ₐ[T] ChartCoeff C f₁)) _ at h1
    rw [h] at h1
    exact h1.unique hδ₂
  have h3 : chartTransfer P hR hred hsimple (chartX f₁ (selfAlg T)) (chartX f₂ (selfAlg T))
      (cancelEquiv f₁ (selfAlg T) δ₁) = cancelEquiv f₂ (selfAlg T) δ₂ := by
    rw [← h2, chartIdemMap, RingEquiv.apply_symm_apply]
  have h4 := chartTransfer_map' P hR hred hsimple (selfHom T) (chartX f₁ (selfAlg T))
    (chartX f₂ (selfAlg T)) f₁ f₂ (isChartComp_selfHom f₁)
    (isChartComp_selfHom f₂) (hδ₁.isIdempotentElem.map (cancelEquiv f₁ (selfAlg T)))
  rw [h3, lTensor_cancelEquiv_eq_diagIdem e φ f₁ (isChartComp_selfHom f₁) hδ₁,
    lTensor_cancelEquiv_eq_diagIdem e φ f₂ (isChartComp_selfHom f₂) hδ₂] at h4
  exact h4

/-- The chart factor projections of the diagonal idempotents through two chart maps agree. -/
theorem chartFactor_diagIdem (φ : B →ₐ[A] T) (f₁ f₂ : A' →ₐ[A] T)
    (hinv : ∀ b : B, chartAlgEquiv P hR hred hsimple f₁ f₂ (coeffTmul f₂ 1 (e (1 ⊗ₜ[A] b))) =
      coeffTmul f₁ 1 (e (1 ⊗ₜ[A] b))) :
    chartFactor P f₁ (diagIdem e φ f₁) (diagIdem_isIdempotentElem e φ f₁) =
      chartFactor P f₂ (diagIdem e φ f₂) (diagIdem_isIdempotentElem e φ f₂) := by
  rw [← chartFactor_chartTransfer P hR hred hsimple f₁ f₂ (diagIdem_isIdempotentElem e φ f₁)]
  congr 1
  exact chartTransfer_diagIdem e P hR hred hsimple φ f₁ f₂ hinv

end Invariance

end Langlands.GroupScheme.WeilChart
