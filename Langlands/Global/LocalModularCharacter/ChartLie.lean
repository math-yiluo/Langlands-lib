import Langlands.Global.LocalModularCharacter.RegularFamily
import Langlands.GroupScheme.Lie.Adjoint
import Langlands.GroupScheme.Lie.AffineCoordinates
import Langlands.GroupScheme.Lie.AffineModule
import Langlands.GroupScheme.AffinePointTopologicalGroup
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Chart derivatives of the group law and of conjugation

Let `G` be an affine group scheme over a field `F`, `K` a nontrivially normed field that is an
`F`-algebra, `G(K)` carry a topology with continuous multiplication, and `φ` a chart of `G(K)` at
the identity given by regular functions. The chart
expression of the group law is strictly differentiable at the origin, with derivative the identity
on the second factor. The chart expression of conjugation by `g` is strictly differentiable at the
origin, and its derivative is a linear automorphism with the same determinant as the adjoint
action of `g` on the dual-number Lie kernel. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry Filter Topology
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Global.LocalModularCharacter

section Jet

variable (F : Type*) [CommSemiring F] {K : Type*} [NontriviallyNormedField K] [Algebra F K]
  {T : Type*} [NormedAddCommGroup T] [NormedSpace K T]

theorem differentiableAt_of_mem_strictDiffSubalgebra {t₀ : T} (h : strictDiffSubalgebra F K t₀) :
    DifferentiableAt K (h : T → K) t₀ := by
  obtain ⟨L, hL⟩ := h.2
  exact hL.differentiableAt

/-- The first-order jet at `t₀` in the direction `v`, with values in the dual numbers. -/
def jet (t₀ v : T) : strictDiffSubalgebra F K t₀ →ₐ[F] DualNumber K where
  toFun h := TrivSqZeroExt.inl ((h : T → K) t₀) + TrivSqZeroExt.inr (fderiv K (h : T → K) t₀ v)
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' h₁ h₂ := by
    have e : ((h₁ * h₂ : strictDiffSubalgebra F K t₀) : T → K) = (h₁ : T → K) * h₂ := rfl
    have hd := fderiv_mul (differentiableAt_of_mem_strictDiffSubalgebra F h₁)
      (differentiableAt_of_mem_strictDiffSubalgebra F h₂)
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [e]
    · simp only [e, hd, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_inr, _root_.add_apply, _root_.smul_apply,
        Pi.mul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
        zero_add, add_zero]
      ring
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' h₁ h₂ := by
    have e : ((h₁ + h₂ : strictDiffSubalgebra F K t₀) : T → K) = (h₁ : T → K) + h₂ := rfl
    have hd := fderiv_add (differentiableAt_of_mem_strictDiffSubalgebra F h₁)
      (differentiableAt_of_mem_strictDiffSubalgebra F h₂)
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [e, hd]
  commutes' r := by
    have e : ((algebraMap F (strictDiffSubalgebra F K t₀) r) : T → K) =
        fun _ => algebraMap F K r := rfl
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [e, TrivSqZeroExt.algebraMap_eq_inl']

variable {F}

@[simp] theorem jet_fst (t₀ v : T) (h : strictDiffSubalgebra F K t₀) :
    (jet F t₀ v h).fst = (h : T → K) t₀ := by
  simp [jet]

@[simp] theorem jet_snd (t₀ v : T) (h : strictDiffSubalgebra F K t₀) :
    (jet F t₀ v h).snd = fderiv K (h : T → K) t₀ v := by
  simp [jet]

end Jet

section Tangent

variable {F : Type u} [Field F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
variable {K : Type u} [NontriviallyNormedField K] [Algebra F K]
  {T : Type u} [NormedAddCommGroup T] [NormedSpace K T]

/-- The tangent vector at `t₀` in the direction `v` of a family of points with strictly
differentiable coordinates, as a dual-number point. -/
def familyTangent (t₀ v : T) (f : T → Lie.AffinePoints G K)
    (hf : IsRegularFamily G (strictDiffSubalgebra F K t₀) f) :
    Lie.AffinePoints G (DualNumber K) :=
  Lie.affineMap G (jet F t₀ v) (liftFamily G _ f hf)

theorem affinePointEvaluation_familyTangent (t₀ v : T) (f : T → Lie.AffinePoints G K)
    (hf : IsRegularFamily G (strictDiffSubalgebra F K t₀) f) (a : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) (familyTangent G t₀ v f hf) a =
      TrivSqZeroExt.inl (familyValue G f a t₀) +
        TrivSqZeroExt.inr (fderiv K (familyValue G f a) t₀ v) := by
  rw [familyTangent, affinePointEvaluation_affineMap, affinePointEvaluation_liftFamily]
  rfl

omit [IsAffine G.X.left] in
theorem affinePointEvaluation_constant {A : Type u} [CommRing A] [Algebra F A]
    (g : Lie.AffinePoints G A) (a : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber A)) (Lie.constant G g) a =
      TrivSqZeroExt.inl (G.affinePointEvaluation (CommAlgCat.of F A) g a) :=
  affinePointEvaluation_affineMap G _ g a

omit [IsAffine G.X.left] in
theorem affinePointEvaluation_reduction {A : Type u} [CommRing A] [Algebra F A]
    (x : Lie.AffinePoints G (DualNumber A)) (a : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation (CommAlgCat.of F A) (Lie.reduction G x) a =
      (G.affinePointEvaluation (CommAlgCat.of F (DualNumber A)) x a).fst :=
  affinePointEvaluation_affineMap G _ x a

theorem reduction_familyTangent (t₀ v : T) (f : T → Lie.AffinePoints G K)
    (hf : IsRegularFamily G (strictDiffSubalgebra F K t₀) f) :
    Lie.reduction G (familyTangent G t₀ v f hf) = f t₀ := by
  apply G.affinePointEvaluation_injective (CommAlgCat.of F K)
  funext a
  change G.affinePointEvaluation (CommAlgCat.of F K) (Lie.reduction G _) a = familyValue G f a t₀
  rw [affinePointEvaluation_reduction, affinePointEvaluation_familyTangent]
  simp

theorem familyTangent_mul (t₀ v : T) {f₁ f₂ : T → Lie.AffinePoints G K}
    (hf₁ : IsRegularFamily G (strictDiffSubalgebra F K t₀) f₁)
    (hf₂ : IsRegularFamily G (strictDiffSubalgebra F K t₀) f₂) :
    familyTangent G t₀ v (fun t => f₁ t * f₂ t) (hf₁.mul hf₂) =
      familyTangent G t₀ v f₁ hf₁ * familyTangent G t₀ v f₂ hf₂ := by
  rw [familyTangent, liftFamily_mul, map_mul]
  rfl

theorem familyTangent_const (t₀ v : T) (g : Lie.AffinePoints G K) :
    familyTangent G t₀ v (fun _ => g)
        (isRegularFamily_const (const_mem_strictDiffSubalgebra t₀) g) =
      Lie.constant G g := by
  apply G.affinePointEvaluation_injective (CommAlgCat.of F (DualNumber K))
  funext a
  change G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) (familyTangent G t₀ v _ _) a =
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) (Lie.constant G g) a
  rw [affinePointEvaluation_familyTangent, affinePointEvaluation_constant]
  have e : familyValue G (fun _ : T => g) a =
      fun _ => G.affinePointEvaluation (CommAlgCat.of F K) g a := rfl
  simp [e]

/-- Families that agree near `t₀` have the same tangent vectors at `t₀`. -/
theorem familyTangent_congr (t₀ v : T) {f₁ f₂ : T → Lie.AffinePoints G K}
    (hf₁ : IsRegularFamily G (strictDiffSubalgebra F K t₀) f₁)
    (hf₂ : IsRegularFamily G (strictDiffSubalgebra F K t₀) f₂) (h : f₁ =ᶠ[𝓝 t₀] f₂) :
    familyTangent G t₀ v f₁ hf₁ = familyTangent G t₀ v f₂ hf₂ := by
  apply G.affinePointEvaluation_injective (CommAlgCat.of F (DualNumber K))
  funext a
  change G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) (familyTangent G t₀ v _ _) a =
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) (familyTangent G t₀ v _ _) a
  have ha : familyValue G f₁ a =ᶠ[𝓝 t₀] familyValue G f₂ a :=
    h.mono fun t ht => by simp only [familyValue, ht]
  rw [affinePointEvaluation_familyTangent, affinePointEvaluation_familyTangent, ha.fderiv_eq,
    ha.eq_of_nhds]

omit [IsAffine G.X.left] in
/-- Precomposition with a strictly differentiable map preserves regularity. -/
theorem IsRegularFamily.comp_hasStrictFDerivAt {T' : Type u} [NormedAddCommGroup T']
    [NormedSpace K T'] {t₀ : T} {f : T → Lie.AffinePoints G K}
    (hf : IsRegularFamily G (strictDiffSubalgebra F K t₀) f) {σ : T' → T} {σ' : T' →L[K] T}
    {t₁ : T'} (hσ : HasStrictFDerivAt σ σ' t₁) (h : σ t₁ = t₀) :
    IsRegularFamily G (strictDiffSubalgebra F K t₁) (f ∘ σ) := by
  subst h
  exact hf.comp _ σ fun _ ⟨L, hL⟩ => ⟨L.comp σ', hL.comp t₁ hσ⟩

/-- The chain rule for tangent vectors of families. -/
theorem familyTangent_comp {T' : Type u} [NormedAddCommGroup T'] [NormedSpace K T'] {t₀ : T}
    {f : T → Lie.AffinePoints G K} (hf : IsRegularFamily G (strictDiffSubalgebra F K t₀) f)
    {σ : T' → T} {σ' : T' →L[K] T} {t₁ : T'} (hσ : HasStrictFDerivAt σ σ' t₁) (h : σ t₁ = t₀)
    (v : T') :
    familyTangent G t₁ v (f ∘ σ) (hf.comp_hasStrictFDerivAt G hσ h) =
      familyTangent G t₀ (σ' v) f hf := by
  subst h
  apply G.affinePointEvaluation_injective (CommAlgCat.of F (DualNumber K))
  funext a
  change G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) (familyTangent G t₁ v _ _) a =
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) (familyTangent G _ _ _ _) a
  rw [affinePointEvaluation_familyTangent, affinePointEvaluation_familyTangent]
  have e : familyValue G (f ∘ σ) a = familyValue G f a ∘ σ := rfl
  obtain ⟨L, hL⟩ := hf a
  rw [e, fderiv_comp t₁ hL.differentiableAt hσ.differentiableAt, hσ.hasFDerivAt.fderiv]
  rfl

end Tangent

section Coordinates

variable {F : Type u} [Field F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [IsAffineHom G.X.hom]

/-- The comparison from global sections to the chosen coordinate algebra, given by the
universal point of the coordinate algebra. -/
def coordinateComparison : AffineCoordinateRing F G.X →ₐ[F] Lie.coordinateAlgebra G :=
  (affineSchemePointEquiv F G.X (Lie.coordinateAlgebra G)
    ((Lie.pointCoordinates G).symm (AlgHom.id _ _))).toAlgHom

/-- Evaluating a global section at a point is evaluating its comparison coordinate. -/
theorem affinePointEvaluation_eq_pointCoordinates {A : Type u} [CommRing A] [Algebra F A]
    (y : Lie.AffinePoints G A) (a : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation (CommAlgCat.of F A) y a =
      Lie.pointCoordinates G y (coordinateComparison G a) := by
  let u : Lie.AffinePoints G (Lie.coordinateAlgebra G) :=
    (Lie.pointCoordinates G).symm (AlgHom.id _ _)
  have hy : y = Lie.affineMap G (Lie.pointCoordinates G y) u := by
    apply (Lie.pointCoordinates G).injective
    rw [Lie.pointCoordinates_naturality, Equiv.apply_symm_apply]
    rfl
  have hu : coordinateComparison G a =
      G.affinePointEvaluation (CommAlgCat.of F (Lie.coordinateAlgebra G)) u a :=
    G.affineSchemePointEquiv_evaluation _ u a
  conv_lhs => rw [hy]
  rw [affinePointEvaluation_affineMap, hu]

variable {K : Type u} [CommRing K] [Algebra F K]

local instance chartLieKernelCommGroup : CommGroup (lieKernel G K) := lieKernelCommGroup G

local instance chartLieKernelModule : Module K (Additive (lieKernel G K)) := lieKernelModule G

attribute [local instance] Lie.coordinateOriginAlgebra

/-- The coordinates of an identity-kernel point at a family of global sections. -/
def kernelCoordinateMap {n : ℕ} (c : Fin n → AffineCoordinateRing F G.X) :
    Additive (lieKernel G K) →ₗ[K] (Fin n → K) where
  toFun y j := Lie.kernelDerivationEquiv G y.toMul (coordinateComparison G (c j))
  map_add' y z := by
    funext j
    change Lie.kernelDerivationEquiv G (y.toMul * z.toMul) _ = _
    rw [Lie.kernelDerivationEquiv_mul]
    rfl
  map_smul' r y := by
    funext j
    change Lie.kernelDerivationEquiv G (lieKernelScale G r y.toMul) _ = _
    rw [Lie.kernelDerivationEquiv_scale]
    rfl

theorem kernelCoordinateMap_apply {n : ℕ} (c : Fin n → AffineCoordinateRing F G.X)
    (y : Additive (lieKernel G K)) (j : Fin n) :
    kernelCoordinateMap G c y j =
      (G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) y.toMul.val (c j)).snd := by
  rw [affinePointEvaluation_eq_pointCoordinates]
  rfl

/-- If the only derivation at the identity killed by `R'` along `c` is zero, then `R'` composed
with the kernel coordinates is injective. -/
theorem injective_kernelCoordinateMap {n d : ℕ} (c : Fin n → AffineCoordinateRing F G.X)
    (R' : (Fin n → K) →ₗ[K] (Fin d → K))
    (hinj : ∀ D : AffineCoordinateRing F G.X →ₗ[F] K,
      (∀ a b, D (a * b) = G.affinePointEvaluation (CommAlgCat.of F K) 1 a * D b +
        G.affinePointEvaluation (CommAlgCat.of F K) 1 b * D a) →
      R' (fun j => D (c j)) = 0 → D = 0) :
    Function.Injective (R' ∘ₗ kernelCoordinateMap G c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  let D : AffineCoordinateRing F G.X →ₗ[F] K :=
    (Lie.kernelDerivationEquiv G y.toMul).toLinearMap ∘ₗ (coordinateComparison G).toLinearMap
  have hD (a : AffineCoordinateRing F G.X) :
      D a = (G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) y.toMul.val a).snd := by
    change Lie.kernelDerivationEquiv G y.toMul (coordinateComparison G a) = _
    rw [affinePointEvaluation_eq_pointCoordinates]
    rfl
  have hfst (a : AffineCoordinateRing F G.X) :
      (G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) y.toMul.val a).fst =
        G.affinePointEvaluation (CommAlgCat.of F K) 1 a := by
    rw [← affinePointEvaluation_reduction, y.toMul.property]
  have hD0 : D = 0 := by
    refine hinj D (fun a b => ?_) ?_
    · rw [hD, hD, hD, ← hfst, ← hfst]
      rw [map_mul, TrivSqZeroExt.snd_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
        smul_eq_mul]
      ring
    · have : (fun j => D (c j)) = kernelCoordinateMap G c y := by
        funext j
        rw [hD, kernelCoordinateMap_apply]
      rw [this]
      exact hy
  apply Additive.toMul.injective
  apply Subtype.ext
  apply G.affinePointEvaluation_injective (CommAlgCat.of F (DualNumber K))
  funext a
  change G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) y.toMul.val a =
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) (1 : Lie.AffinePoints G _) a
  rw [← (Lie.constant G).map_one, affinePointEvaluation_constant]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [hfst]
    rfl
  · rw [← hD, hD0]
    rfl

end Coordinates

section Chart

variable {F : Type u} [Field F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
variable {K : Type u} [NontriviallyNormedField K] [Algebra F K]
variable [TopologicalSpace (Lie.AffinePoints G K)] [ContinuousMul (Lie.AffinePoints G K)]
variable {d n : ℕ} (φ : OpenPartialHomeomorph (Lie.AffinePoints G K) (Fin d → K))
  (c : Fin n → AffineCoordinateRing F G.X) {R : (Fin n → K) → (Fin d → K)}
  {R' : (Fin n → K) →L[K] (Fin d → K)}

omit [IsAffine G.X.left] [ContinuousMul (Lie.AffinePoints G K)] in
/-- The chart expression of a regular family through the identity is strictly differentiable,
with derivative computed by the chain rule from the derivatives of its coordinates. -/
theorem hasStrictFDerivAt_chart_comp
    (hR : HasStrictFDerivAt R R' (fun j => G.affinePointEvaluation (CommAlgCat.of F K) 1 (c j)))
    (hφ : ∀ x ∈ φ.source,
      φ x = R (fun j => G.affinePointEvaluation (CommAlgCat.of F K) x (c j)))
    {T : Type u} [NormedAddCommGroup T] [NormedSpace K T] {t₀ : T}
    {f : T → Lie.AffinePoints G K} (hf : IsRegularFamily G (strictDiffSubalgebra F K t₀) f)
    (hf1 : f t₀ = 1) (hfs : ∀ᶠ t in 𝓝 t₀, f t ∈ φ.source) :
    HasStrictFDerivAt (fun t => φ (f t))
      (R'.comp (ContinuousLinearMap.pi fun j => fderiv K (familyValue G f (c j)) t₀)) t₀ := by
  have hcoord : HasStrictFDerivAt (fun t j => familyValue G f (c j) t)
      (ContinuousLinearMap.pi fun j => fderiv K (familyValue G f (c j)) t₀) t₀ := by
    refine hasStrictFDerivAt_pi.2 fun j => ?_
    obtain ⟨L, hL⟩ := hf (c j)
    rw [hL.hasFDerivAt.fderiv]
    exact hL
  have hval : (fun j => familyValue G f (c j) t₀) =
      fun j => G.affinePointEvaluation (CommAlgCat.of F K) 1 (c j) := by
    funext j
    simp only [familyValue, hf1]
  rw [← hval] at hR
  refine (hR.comp t₀ hcoord).congr_of_eventuallyEq ?_
  filter_upwards [hfs] with t ht
  exact (hφ (f t) ht).symm

variable [IsAffineHom G.X.hom]

attribute [local instance] chartLieKernelCommGroup chartLieKernelModule
  Lie.coordinateOriginAlgebra

/-- **Chart derivatives at the identity.** Let `φ` be a chart of `G(K)` at the identity whose
inverse has strictly differentiable regular-function values at `0`, and which is given near the
identity by a strictly differentiable function `R` of finitely many regular functions `c`, such
that no nonzero derivation at the identity is killed by `R'` along `c`. Then the chart expression
of the group law is strictly differentiable at the origin with derivative the identity on the
second factor, and for every `g` the chart expression of conjugation by `g` is strictly
differentiable at the origin with derivative a linear automorphism whose determinant is the
determinant of the adjoint action of `g`. -/
theorem chart_derivatives
    (h1 : (1 : Lie.AffinePoints G K) ∈ φ.source) (h0 : φ 1 = 0)
    (hR : HasStrictFDerivAt R R' (fun j => G.affinePointEvaluation (CommAlgCat.of F K) 1 (c j)))
    (hφ : ∀ x ∈ φ.source,
      φ x = R (fun j => G.affinePointEvaluation (CommAlgCat.of F K) x (c j)))
    (hreg : ∀ a : AffineCoordinateRing F G.X, ∃ L : (Fin d → K) →L[K] K,
      HasStrictFDerivAt (fun s => G.affinePointEvaluation (CommAlgCat.of F K) (φ.symm s) a) L 0)
    (hinj : ∀ D : AffineCoordinateRing F G.X →ₗ[F] K,
      (∀ a b, D (a * b) = G.affinePointEvaluation (CommAlgCat.of F K) 1 a * D b +
        G.affinePointEvaluation (CommAlgCat.of F K) 1 b * D a) →
      R' (fun j => D (c j)) = 0 → D = 0) :
    (∃ L : (Fin d → K) × (Fin d → K) →L[K] (Fin d → K),
      HasStrictFDerivAt (fun p : (Fin d → K) × (Fin d → K) => φ (φ.symm p.1 * φ.symm p.2)) L 0 ∧
        ∀ w, L (0, w) = w) ∧
    ∀ g : Lie.AffinePoints G K, ∃ A : (Fin d → K) ≃L[K] (Fin d → K),
      HasStrictFDerivAt (fun z => φ (g * φ.symm z * g⁻¹)) (A : (Fin d → K) →L[K] (Fin d → K)) 0 ∧
      LinearMap.det (A.toLinearEquiv : (Fin d → K) →ₗ[K] (Fin d → K)) =
        LinearMap.det (adjoint G K g) := by
  have h0t : (0 : Fin d → K) ∈ φ.target := h0 ▸ φ.map_source h1
  have hΨ0 : φ.symm 0 = 1 := by rw [← h0, φ.left_inv h1]
  have hΨ : IsRegularFamily G (strictDiffSubalgebra F K (0 : Fin d → K)) φ.symm := hreg
  have hΨc : ContinuousAt φ.symm 0 := φ.continuousAt_symm h0t
  have hsrc : φ.source ∈ 𝓝 (1 : Lie.AffinePoints G K) := φ.open_source.mem_nhds h1
  have hconst (h : Lie.AffinePoints G K) :
      IsRegularFamily G (strictDiffSubalgebra F K (0 : Fin d → K)) (fun _ => h) :=
    isRegularFamily_const (const_mem_strictDiffSubalgebra (0 : Fin d → K)) h
  refine ⟨?_, fun g => ?_⟩
  · -- the group law
    have hfst : IsRegularFamily G (strictDiffSubalgebra F K (0 : (Fin d → K) × (Fin d → K)))
        (φ.symm ∘ Prod.fst) :=
      hΨ.comp_hasStrictFDerivAt G hasStrictFDerivAt_fst Prod.fst_zero
    have hsnd : IsRegularFamily G (strictDiffSubalgebra F K (0 : (Fin d → K) × (Fin d → K)))
        (φ.symm ∘ Prod.snd) :=
      hΨ.comp_hasStrictFDerivAt G hasStrictFDerivAt_snd Prod.snd_zero
    have hm1 : φ.symm (0 : (Fin d → K) × (Fin d → K)).1 *
        φ.symm (0 : (Fin d → K) × (Fin d → K)).2 = 1 := by
      rw [Prod.fst_zero, Prod.snd_zero, hΨ0, mul_one]
    have hmc : ContinuousAt (fun p : (Fin d → K) × (Fin d → K) => φ.symm p.1 * φ.symm p.2) 0 :=
      (hΨc.comp_of_eq continuousAt_fst Prod.fst_zero).mul
        (hΨc.comp_of_eq continuousAt_snd Prod.snd_zero)
    have hms : ∀ᶠ p in 𝓝 (0 : (Fin d → K) × (Fin d → K)),
        φ.symm p.1 * φ.symm p.2 ∈ φ.source :=
      hmc.preimage_mem_nhds (by rw [hm1]; exact hsrc)
    have hT := hasStrictFDerivAt_chart_comp G φ c hR hφ (hfst.mul hsnd) hm1 hms
    refine ⟨_, hT, fun w => ?_⟩
    have hcomp := hT.hasFDerivAt.comp (0 : Fin d → K)
      (hasFDerivAt_prodMk_right (0 : Fin d → K) (0 : Fin d → K))
    have heq : (fun w : Fin d → K => φ (φ.symm ((0 : Fin d → K), w).1 *
        φ.symm ((0 : Fin d → K), w).2)) =ᶠ[𝓝 0] id := by
      filter_upwards [φ.eventually_right_inverse h0t] with w hw
      simp only [hΨ0, one_mul, hw, id]
    have hu := hcomp.unique ((hasFDerivAt_id (0 : Fin d → K)).congr_of_eventuallyEq heq)
    exact congrArg (fun M : (Fin d → K) →L[K] (Fin d → K) => M w) hu
  · -- the tangent comparison
    have hred (v : Fin d → K) : familyTangent G 0 v φ.symm hΨ ∈ lieKernel G K := by
      show Lie.reduction G _ = 1
      rw [reduction_familyTangent, hΨ0]
    let tg : (Fin d → K) → Additive (lieKernel G K) := fun v => Additive.ofMul ⟨_, hred v⟩
    let κ : Additive (lieKernel G K) →ₗ[K] (Fin d → K) :=
      (R' : (Fin n → K) →ₗ[K] (Fin d → K)) ∘ₗ kernelCoordinateMap G c
    have hΨd := hasStrictFDerivAt_chart_comp G φ c hR hφ hΨ hΨ0
      (hΨc.preimage_mem_nhds (by rw [hΨ0]; exact hsrc))
    have hΨid := hΨd.hasFDerivAt.unique
      ((hasFDerivAt_id (0 : Fin d → K)).congr_of_eventuallyEq (φ.eventually_right_inverse h0t))
    have hκtg (v : Fin d → K) : κ (tg v) = v := by
      have e1 : κ (tg v) = R' (fun j => fderiv K (familyValue G φ.symm (c j)) 0 v) := by
        show R' (kernelCoordinateMap G c (tg v)) = _
        congr 1
        funext j
        rw [kernelCoordinateMap_apply]
        show (G.affinePointEvaluation (CommAlgCat.of F (DualNumber K))
          (familyTangent G 0 v φ.symm hΨ) (c j)).snd = _
        rw [affinePointEvaluation_familyTangent]
        simp
      rw [e1]
      exact congrArg (fun M : (Fin d → K) →L[K] (Fin d → K) => M v) hΨid
    -- conjugation by `g`
    let fg : (Fin d → K) → Lie.AffinePoints G K := fun z => g * φ.symm z * g⁻¹
    have hfg : IsRegularFamily G (strictDiffSubalgebra F K (0 : Fin d → K)) fg :=
      ((hconst g).mul hΨ).mul (hconst g⁻¹)
    have hfg1 : fg 0 = 1 := by simp only [fg, hΨ0, mul_one, mul_inv_cancel]
    have hfgc : ContinuousAt fg 0 := (continuousAt_const.mul hΨc).mul continuousAt_const
    have hfgs : ∀ᶠ z in 𝓝 (0 : Fin d → K), fg z ∈ φ.source :=
      hfgc.preimage_mem_nhds (by rw [hfg1]; exact hsrc)
    have hψ := hasStrictFDerivAt_chart_comp G φ c hR hφ hfg hfg1 hfgs
    set A' := R'.comp (ContinuousLinearMap.pi fun j => fderiv K (familyValue G fg (c j)) 0)
      with hA'
    have hψ0 : φ (fg 0) = 0 := by rw [hfg1, h0]
    have hcongr : fg =ᶠ[𝓝 0] φ.symm ∘ (fun z => φ (fg z)) := by
      filter_upwards [hfgs] with z hz
      exact (φ.left_inv hz).symm
    have hAd (v : Fin d → K) : adjoint G K g (tg v) = tg (A' v) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [adjoint_val]
      show Lie.constant G g * familyTangent G 0 v φ.symm hΨ * (Lie.constant G g)⁻¹ =
        familyTangent G 0 (A' v) φ.symm hΨ
      calc Lie.constant G g * familyTangent G 0 v φ.symm hΨ * (Lie.constant G g)⁻¹
          = familyTangent G 0 v (fun _ => g) (hconst g) * familyTangent G 0 v φ.symm hΨ *
              familyTangent G 0 v (fun _ => g⁻¹) (hconst g⁻¹) := by
            rw [familyTangent_const, familyTangent_const, map_inv]
        _ = familyTangent G 0 v fg hfg := by
            rw [← familyTangent_mul, ← familyTangent_mul]
        _ = familyTangent G 0 v (φ.symm ∘ fun z => φ (fg z))
              (hΨ.comp_hasStrictFDerivAt G hψ hψ0) :=
            familyTangent_congr G 0 v _ _ hcongr
        _ = familyTangent G 0 (A' v) φ.symm hΨ := familyTangent_comp G hΨ hψ hψ0 v
    have hκinj : Function.Injective κ :=
      injective_kernelCoordinateMap G c (R' : (Fin n → K) →ₗ[K] (Fin d → K)) hinj
    let eκ := LinearEquiv.ofBijective κ ⟨hκinj, fun v => ⟨tg v, hκtg v⟩⟩
    have heκ (v : Fin d → K) : eκ.symm v = tg v := by
      rw [LinearEquiv.symm_apply_eq]
      exact (hκtg v).symm
    let adE : Additive (lieKernel G K) ≃ₗ[K] Additive (lieKernel G K) :=
      LinearEquiv.ofLinearMap (adjoint G K g) (adjoint G K g⁻¹)
        (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_eq_id])
        (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_eq_id])
    let Aeq : (Fin d → K) ≃ₗ[K] (Fin d → K) := (eκ.symm.trans adE).trans eκ
    have hAeq (v : Fin d → K) : Aeq v = A' v := by
      show eκ (adjoint G K g (eκ.symm v)) = A' v
      rw [heκ, hAd]
      exact hκtg (A' v)
    let A : (Fin d → K) ≃L[K] (Fin d → K) :=
      { Aeq with
        continuous_toFun := LinearMap.continuous_on_pi (Aeq : (Fin d → K) →ₗ[K] (Fin d → K))
        continuous_invFun :=
          LinearMap.continuous_on_pi (Aeq.symm : (Fin d → K) →ₗ[K] (Fin d → K)) }
    have hA : (A : (Fin d → K) →L[K] (Fin d → K)) = A' := ContinuousLinearMap.ext hAeq
    refine ⟨A, by rw [hA]; exact hψ, ?_⟩
    have hdet : (A.toLinearEquiv : (Fin d → K) →ₗ[K] (Fin d → K)) =
        (eκ : Additive (lieKernel G K) →ₗ[K] (Fin d → K)) ∘ₗ adjoint G K g ∘ₗ
          (eκ.symm : (Fin d → K) →ₗ[K] Additive (lieKernel G K)) := rfl
    rw [hdet, LinearMap.det_conj]

end Chart


end Langlands.Global.LocalModularCharacter
