import Langlands.GroupScheme.Lie.AdjointDominance
import Langlands.AlgebraicGeometry.TangentSmoothnessExtension

/-! # Dominance of slice maps from tangent vectors over a field extension -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

open GeneralLinear.DualNumber MatrixRepresentation Langlands.AlgebraicGeometry.Picard
  Langlands.AlgebraicGeometry.TangentSmoothness

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n e : Type} [Fintype n] [DecidableEq n] [Fintype e]

/-- The `K`-valued point `(1, t₀)` of `G × 𝔸^e`, for a field extension `K` of `k`. -/
def sliceExtensionPoint (t₀ : e → K) :
    (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) K)) ⟶
      G.X ⊗ coefficientSpace e (CommRingCat.of k) :=
  lift 1 (coefficientPoint _ fun j => (Scheme.ΓSpecIso (CommRingCat.of K)).inv (t₀ j))

variable (k K) in
/-- The reduction `Spec K ⟶ Spec K[ε]`, `ε ↦ 0`, as a morphism of affine test schemes
over `k`. -/
abbrev dualNumberReduction :
    (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) K)) ⟶
      (algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (DualNumber K))) :=
  (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (TrivSqZeroExt.fstHom (CommRingCat.of k) K K)).op

theorem dualNumberReduction_left :
    (dualNumberReduction k K).left = dualNumberAugmentation K := rfl

/-- Pulling back a section of `Spec A` along `Spec φ`. -/
private theorem appTop_SpecMap_ΓSpecIso_inv {A B : CommRingCat.{u}} (φ : A ⟶ B) (z : A) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv z) = (Scheme.ΓSpecIso B).inv (φ z) :=
  (CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) z).symm

/-- The reduction `Spec K ⟶ Spec K[ε]` on global sections is the constant part. -/
private theorem dualNumberReduction_appTop (z : DualNumber K) :
    (dualNumberReduction k K).left.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv z) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv z.fst := by
  change (dualNumberAugmentation K).appTop _ = _
  rw [dualNumberAugmentation, appTop_SpecMap_ΓSpecIso_inv]
  rfl

omit [Fintype n] [DecidableEq n] in
private theorem mulVec_algebraMap_inl_add_inr {m : Type} [Fintype m] (M : Matrix n m k)
    (a b : m → K) :
    M.map (algebraMap k (DualNumber K)) *ᵥ
        (fun j => TrivSqZeroExt.inl (a j) + TrivSqZeroExt.inr (b j)) =
      fun i => TrivSqZeroExt.inl ((M.map (algebraMap k K) *ᵥ a) i) +
        TrivSqZeroExt.inr ((M.map (algebraMap k K) *ᵥ b) i) := by
  funext i
  apply TrivSqZeroExt.ext <;>
    simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_sum,
      TrivSqZeroExt.snd_sum]

omit [DecidableEq n] in
private theorem epsilonMatrix_mulVec_inl_add_inr (M : Matrix n n K) (a b : n → K) :
    epsilonMatrix M *ᵥ (fun j => TrivSqZeroExt.inl (a j) + TrivSqZeroExt.inr (b j)) =
      fun i => TrivSqZeroExt.inr ((M *ᵥ a) i) := by
  funext i
  apply TrivSqZeroExt.ext <;>
    simp [Matrix.mulVec, dotProduct, epsilonMatrix, TrivSqZeroExt.fst_sum,
      TrivSqZeroExt.snd_sum]

/-- **Tangent surjectivity of the slice map at an extension-valued point.** Let `K` be a
field extension of `k`, `B` a matrix over `k` and `t₀` a vector over `K`. If every vector `v`
over `K` is of the form `ρ(ξ) (B t₀) + B t'` for a Lie element `ξ ∈ Lie(G)(K)` and a vector
`t'` over `K`, then every `K[ε]`-valued point of `𝔸^n` over `k` lifting the image of the
`K`-point `(1, t₀)` is the image of a `K[ε]`-valued point of `G × 𝔸^e` lifting `(1, t₀)`. -/
theorem isTangentSurjectiveAtExtension_sliceMap [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G n) (B : Matrix n e k) (t₀ : e → K)
    (h : ∀ v : n → K, ∃ (ξ : lieKernel G K) (t' : e → K),
      ρ.tangentMatrix K ξ *ᵥ (B.map (algebraMap k K) *ᵥ t₀) +
        B.map (algebraMap k K) *ᵥ t' = v) :
    IsTangentSurjectiveAtExtension (G.X ⊗ coefficientSpace e (CommRingCat.of k)).hom
      (coefficientSpace n (CommRingCat.of k)).hom (sliceMap ρ B).left
      (sliceExtensionPoint (G := G) t₀).left := by
  intro t ht₁ ht₂
  let tt : (algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) (DualNumber K))) ⟶
      coefficientSpace n (CommRingCat.of k) := Over.homMk t ht₁
  let w : n → DualNumber K := fun i =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).hom (coefficientCoordinates tt i)
  have hw : ∀ i, coefficientCoordinates tt i =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv (w i) := fun i =>
    (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))) _).symm
  -- The base of the tangent vector is `B t₀`.
  have hfst : ∀ i, (w i).fst = (B.map (algebraMap k K) *ᵥ t₀) i := by
    have hat : dualNumberReduction k K ≫ tt = sliceExtensionPoint t₀ ≫ sliceMap ρ B :=
      Over.OverMorphism.ext ht₂
    have hc := congrArg coefficientCoordinates hat
    rw [sliceExtensionPoint, coefficientCoordinates_sliceMap, map_one,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec,
      coefficientCoordinates_coefficientPoint, coefficientCoordinates_comp] at hc
    intro i
    have hi := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom (congrFun hc i)
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      ((dualNumberReduction k K).left.appTop (coefficientCoordinates tt i)) = _ at hi
    rw [hw, dualNumberReduction_appTop, Iso.inv_hom_id_apply, RingHom.map_mulVec] at hi
    rw [hi]
    congr 1
    · ext a b
      exact ΓSpecIso_hom_scalarMap (CommAlgCat.of (CommRingCat.of k) K) (B a b)
    · funext j
      exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of K)) _
  obtain ⟨ξ, t', hξ⟩ := h fun i => (w i).snd
  let y : (algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) (DualNumber K))) ⟶
      coefficientSpace e (CommRingCat.of k) :=
    coefficientPoint _ fun j => (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv
      (TrivSqZeroExt.inl (t₀ j) + TrivSqZeroExt.inr (t' j))
  let s : (algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) (DualNumber K))) ⟶
      G.X ⊗ coefficientSpace e (CommRingCat.of k) := lift ξ.val y
  have hy : ∀ j, (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).hom
      (coefficientCoordinates y j) = TrivSqZeroExt.inl (t₀ j) + TrivSqZeroExt.inr (t' j) := by
    intro j
    rw [coefficientCoordinates_coefficientPoint]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))) _
  have hs₁ : dualNumberReduction k K ≫ s = sliceExtensionPoint t₀ := by
    rw [comp_lift, sliceExtensionPoint]
    congr 1
    · exact ξ.property
    · apply coefficientCoordinates_injective
      rw [coefficientCoordinates_comp, coefficientCoordinates_coefficientPoint,
        coefficientCoordinates_coefficientPoint]
      funext j
      rw [dualNumberReduction_appTop]
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
  have hs₂ : s ≫ sliceMap ρ B = tt := by
    apply coefficientCoordinates_injective
    funext i
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).hom).1
    have hc := congrFun (affineCoordinates_sliceMap ρ B
      (CommAlgCat.of (CommRingCat.of k) (DualNumber K)) ξ.val y) i
    simp only [hy] at hc
    rw [affineMatrix_lieKernel_eq, matrixUnit_val, Matrix.add_mulVec,
      Matrix.one_mulVec, mulVec_algebraMap_inl_add_inr, epsilonMatrix_mulVec_inl_add_inr] at hc
    refine hc.trans ?_
    change _ = w i
    apply TrivSqZeroExt.ext
    · simp [hfst i]
    · have := congrFun hξ i
      simp only [Pi.add_apply] at this
      simp [← this, add_comm]
  exact ⟨s.left, Over.w s, congrArg CommaMorphism.left hs₁, congrArg CommaMorphism.left hs₂⟩

/-- **Dominance of the slice map from an extension-valued point.** Let `G` be a smooth affine
group over a field `k`, `K` a field extension of `k`, `B` a matrix over `k` and `t₀` a vector
over `K`. If every vector `v` over `K` is of the form `ρ(ξ) (B t₀) + B t'` for a Lie element
`ξ ∈ Lie(G)(K)` and a vector `t'` over `K`, then the slice map `(g, t) ↦ ρ(g) (B t)` from
`G × 𝔸^e` to `𝔸^n` has dense range. -/
theorem denseRange_sliceMap_of_extension [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (ρ : MatrixRepresentation G n) (B : Matrix n e k) (t₀ : e → K)
    (h : ∀ v : n → K, ∃ (ξ : lieKernel G K) (t' : e → K),
      ρ.tangentMatrix K ξ *ᵥ (B.map (algebraMap k K) *ᵥ t₀) +
        B.map (algebraMap k K) *ᵥ t' = v) :
    DenseRange (sliceMap ρ B).left := by
  have : Smooth (G.X ⊗ coefficientSpace e (CommRingCat.of k)).hom :=
    smooth_tensor _ _ inferInstance
      (inferInstanceAs (Smooth (𝔸(ULift.{u} e; Spec (CommRingCat.of k)) ↘ _)))
  have : GeometricallyIrreducible (coefficientSpace n (CommRingCat.of k)).hom :=
    inferInstanceAs (GeometricallyIrreducible (𝔸(ULift.{u} n; Spec (CommRingCat.of k)) ↘ _))
  have : LocallyOfFiniteType (coefficientSpace n (CommRingCat.of k)).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝔸(ULift.{u} n; Spec (CommRingCat.of k)) ↘ _))
  exact denseRange_of_isTangentSurjectiveAtExtension (K := K) _ (Over.w _)
    (Over.w (sliceExtensionPoint (G := G) t₀))
    (isTangentSurjectiveAtExtension_sliceMap ρ B t₀ h)

end Langlands.GroupScheme.Lie
