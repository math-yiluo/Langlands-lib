import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.Rational.CoordinateCotangentWeights
import Langlands.GroupScheme.Rational.TorusUnipotence.MatrixCoefficients

/-! # Lie weight multiplicities from polynomial eigen-coordinates

If the coordinate algebra of an affine group `H` is a polynomial algebra on eigenfunctions
`t j` of a split torus action, of weights `w j` and vanishing at the identity, then the
dimension of the `χ`-weight space of the torus action on the Lie algebra of `H` is the number
of indices `j` with `w j = χ`. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusUnipotence

/-- In a modular complete lattice, a spanning family `U` below an independent family `W`
coincides with `W`. -/
theorem eq_of_le_of_iSup_eq_top {α β : Type*} [CompleteLattice α] [IsModularLattice α]
    {U W : β → α} (hle : ∀ i, U i ≤ W i) (hU : ⨆ i, U i = ⊤) (hW : iSupIndep W) (i : β) :
    U i = W i := by
  apply le_antisymm (hle i)
  have h1 : W i = (U i ⊔ ⨆ (j) (_ : j ≠ i), U j) ⊓ W i := by
    rw [← iSup_split_single U i, hU, top_inf_eq]
  rw [h1, sup_inf_assoc_of_le _ (hle i)]
  refine sup_le le_rfl ?_
  have h2 : (⨆ (j) (_ : j ≠ i), U j) ⊓ W i ≤ (⨆ (j) (_ : j ≠ i), W j) ⊓ W i :=
    inf_le_inf_right _ (iSup₂_mono fun j _ => hle j)
  refine h2.trans ?_
  rw [inf_comm]
  exact (hW i).le_bot.trans bot_le

section Group

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "A" => CharacterUnits.Coord H

/-- Points of `H` are determined by the values of a generating family of coordinates. -/
theorem pointCoordinates_ext {d : ℕ} {t : Fin d → A}
    (ht : Function.Surjective (aeval t : MvPolynomial (Fin d) k →ₐ[k] A))
    {B : Type u} [CommRing B] [Algebra k B] {x y : Lie.AffinePoints H B}
    (h : ∀ j, Lie.pointCoordinates H x (t j) = Lie.pointCoordinates H y (t j)) : x = y := by
  apply (Lie.pointCoordinates H).injective
  ext a
  obtain ⟨p, rfl⟩ := ht a
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C]
    exact (AlgHom.commutes _ c).trans (AlgHom.commutes _ c).symm
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, h j]

/-- At an identity-kernel point, a coordinate vanishing at the identity takes the value
`ε · D(f)`, where `D` is the identity derivation of the point. -/
theorem pointCoordinates_kernel_of_counit {B : Type u} [CommRing B] [Algebra k B]
    (x : lieKernel H B) {f : A} (hf : coordCounit H f = 0) :
    Lie.pointCoordinates H x.val f = TrivSqZeroExt.inr (Lie.kernelDerivationEquiv H x f) := by
  have h := DFunLike.congr_fun (Lie.pointCoordinates_kernel H x) f
  apply TrivSqZeroExt.ext
  · refine h.trans ?_
    change algebraMap k B (coordCounit H f) = 0
    rw [hf, map_zero]
  · rfl

/-- Epsilon scaling multiplies the identity derivation of a kernel point. -/
theorem kernelDerivationEquiv_scale_apply {B : Type u} [CommRing B] [Algebra k B] (c : B)
    (x : lieKernel H B) (f : A) :
    Lie.kernelDerivationEquiv H (lieKernelScale H c x) f =
      c * Lie.kernelDerivationEquiv H x f :=
  DFunLike.congr_fun (Lie.kernelDerivationEquiv_scale (G := H) c x) f

variable {d : ℕ} (t : Fin d → CharacterUnits.Coord H)

/-- The derivatives `(D(t j))_j` of a tangent vector along the coordinates `t j`. -/
def tangentCoordinates : Additive (lieKernel H k) →ₗ[k] (Fin d → k) where
  toFun X j := Lie.kernelDerivationEquiv H X.toMul (t j)
  map_add' X Y := by
    ext j
    simp only [toMul_add, Lie.kernelDerivationEquiv_mul, Derivation.add_apply, Pi.add_apply]
  map_smul' c X := by
    ext j
    simp only [lieKernel_smul_toMul, Lie.kernelDerivationEquiv_scale, Derivation.smul_apply,
      Pi.smul_apply, RingHom.id_apply]

@[simp] theorem tangentCoordinates_apply (X : Additive (lieKernel H k)) (j : Fin d) :
    tangentCoordinates t X j = Lie.kernelDerivationEquiv H X.toMul (t j) := rfl

variable {t}

/-- The coordinates `t j` determine a tangent vector by its derivatives. -/
theorem tangentCoordinates_injective
    (ht : Function.Surjective (aeval t : MvPolynomial (Fin d) k →ₐ[k] A))
    (hε : ∀ j, coordCounit H (t j) = 0) : Function.Injective (tangentCoordinates t) := by
  intro X Y h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply pointCoordinates_ext ht
  intro j
  rw [pointCoordinates_kernel_of_counit _ (hε j), pointCoordinates_kernel_of_counit _ (hε j)]
  exact congrArg TrivSqZeroExt.inr (congrFun h j)

/-- Every family of derivatives along polynomial coordinates vanishing at the identity is
realized by a tangent vector. -/
theorem tangentCoordinates_surjective
    (ht : Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] A))
    (hε : ∀ j, coordCounit H (t j) = 0) : Function.Surjective (tangentCoordinates t) := by
  intro v
  let e : MvPolynomial (Fin d) k ≃ₐ[k] A := AlgEquiv.ofBijective (aeval t) ht
  have he : ∀ j, e.symm (t j) = X j := fun j => by
    rw [AlgEquiv.symm_apply_eq]
    simp [e]
  obtain ⟨φ, hφ⟩ : ∃ φ : A →ₐ[k] DualNumber k, ∀ j, φ (t j) = TrivSqZeroExt.inr (v j) :=
    ⟨(aeval fun j => (TrivSqZeroExt.inr (v j) : DualNumber k)).comp e.symm.toAlgHom,
      fun j => by
        change (aeval fun j => (TrivSqZeroExt.inr (v j) : DualNumber k)) (e.symm (t j)) = _
        rw [he, aeval_X]⟩
  obtain ⟨x, hxφ⟩ : ∃ x : Lie.AffinePoints H (DualNumber k), Lie.pointCoordinates H x = φ :=
    ⟨(Lie.pointCoordinates H).symm φ, Equiv.apply_symm_apply _ _⟩
  have hx : x ∈ lieKernel H k := by
    rw [MonoidHom.mem_ker]
    apply pointCoordinates_ext ht.2
    intro j
    rw [Lie.reduction, Lie.pointCoordinates_naturality, hxφ, Lie.pointCoordinates_one,
      AlgHom.comp_apply, hφ, AlgHom.comp_apply]
    change (0 : k) = algebraMap k k (coordCounit H (t j))
    rw [hε j, map_zero]
  refine ⟨Additive.ofMul ⟨x, hx⟩, ?_⟩
  ext j
  change (Lie.pointCoordinates H x (t j)).snd = v j
  rw [hxφ, hφ]
  rfl

/-- Tangent vectors are identified with their derivatives along polynomial coordinates. -/
def tangentCoordinatesEquiv
    (ht : Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] A))
    (hε : ∀ j, coordCounit H (t j) = 0) : Additive (lieKernel H k) ≃ₗ[k] (Fin d → k) :=
  LinearEquiv.ofBijective (tangentCoordinates t)
    ⟨tangentCoordinates_injective ht.2 hε, tangentCoordinates_surjective ht hε⟩

@[simp] theorem tangentCoordinatesEquiv_apply
    (ht : Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] A))
    (hε : ∀ j, coordCounit H (t j) = 0) (X : Additive (lieKernel H k)) :
    tangentCoordinatesEquiv ht hε X = tangentCoordinates t X := rfl

variable {w : Fin d → characterLattice S}

/-- A tangent vector whose derivatives vanish along all coordinates of weight different from
`χ` is a `χ`-eigenvector of the torus action. -/
theorem mem_actionWeightSpace_of_tangentCoordinates (b : AutomorphicAction S.toGrp H)
    (ht : Function.Surjective (aeval t : MvPolynomial (Fin d) k →ₐ[k] A))
    (htw : ∀ j, t j ∈ CoordinateWeights.weightSpace b (w j))
    (hε : ∀ j, coordCounit H (t j) = 0) (χ : characterLattice S)
    {X : Additive (lieKernel H k)} (hX : ∀ j, w j ≠ χ → tangentCoordinates t X j = 0) :
    X ∈ RelativeRoot.actionWeightSpace b χ := by
  rw [RelativeRoot.mem_actionWeightSpace_iff]
  intro B _ _ s
  apply pointCoordinates_ext ht
  intro j
  have hY := pointCoordinates_kernel_of_counit
    (lieKernelMap H (Algebra.ofId k B) X.toMul) (hε j)
  have hZ := pointCoordinates_kernel_of_counit (lieKernelScale H
    (Lie.characterValue χ s : B) (lieKernelMap H (Algebra.ofId k B) X.toMul)) (hε j)
  rw [htw j, hY, hZ, kernelDerivationEquiv_scale_apply,
    Lie.kernelDerivationEquiv_naturality, Lie.constant,
    CoordinateWeights.characterValue_affineMap, Units.coe_map]
  by_cases hj : w j = χ
  · subst hj
    exact TrivSqZeroExt.inl_mul_inr _ _
  · have h0 : Lie.kernelDerivationEquiv H X.toMul (t j) = 0 := hX j hj
    rw [h0, map_zero, mul_zero, TrivSqZeroExt.inr_zero, mul_zero]

open scoped Classical in
/-- **Lie weight multiplicities.** If the coordinate algebra of `H` is a polynomial algebra
on eigenfunctions `t j` of weights `w j` vanishing at the identity, then the `χ`-weight space of
the split torus action on the Lie algebra of `H` has dimension `#{j | w j = χ}`. -/
theorem finrank_actionWeightSpace [LocallyOfFiniteType H.X.hom] (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp H)
    (ht : Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] A))
    (htw : ∀ j, t j ∈ CoordinateWeights.weightSpace b (w j))
    (hε : ∀ j, coordCounit H (t j) = 0) (χ : characterLattice S) :
    Module.finrank k (RelativeRoot.actionWeightSpace b χ) = Nat.card {j // w j = χ} := by
  let Φ := tangentCoordinatesEquiv ht hε
  let B : Module.Basis (Fin d) k (Additive (lieKernel H k)) :=
    (Pi.basisFun k (Fin d)).map Φ.symm
  have hB : ∀ j, tangentCoordinates t (B j) = Pi.single j 1 := fun j => by
    rw [← tangentCoordinatesEquiv_apply ht hε]
    simp [B, Φ]
  let U : characterLattice S → Submodule k (Additive (lieKernel H k)) :=
    fun ψ => Submodule.span k (Set.range fun j : {j // w j = ψ} => B j.1)
  have hle : ∀ ψ, U ψ ≤ RelativeRoot.actionWeightSpace b ψ := fun ψ => by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine mem_actionWeightSpace_of_tangentCoordinates b ht.2 htw hε ψ fun i hi => ?_
    rw [hB, Pi.single_apply, ite_eq_right_iff]
    rintro rfl
    exact absurd j.2 hi
  have hU : ⨆ ψ, U ψ = ⊤ := by
    rw [eq_top_iff, ← B.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (w j) (Submodule.subset_span ⟨⟨j, rfl⟩, rfl⟩)
  have hUW := eq_of_le_of_iSup_eq_top hle hU (RelativeRoot.iSupIndep_actionWeightSpace b hS) χ
  rw [← hUW]
  change Module.finrank k
    (Submodule.span k (Set.range (B ∘ Subtype.val : {j // w j = χ} → _))) = _
  rw [finrank_span_eq_card (B.linearIndependent.comp _ Subtype.val_injective),
    Nat.card_eq_fintype_card]

end Group

end Langlands.GroupScheme.TorusUnipotence
