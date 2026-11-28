import Langlands.GroupScheme.GaloisCocycleConstruction
import Langlands.GroupScheme.GaloisCocycleTowerRecovery
import Langlands.GroupScheme.GaloisCocycleRefinement
import Langlands.GroupScheme.GaloisCocycleScalarExtension

/-! # Inflation and restriction for natural cocycles on finite Galois covers

Let `k ⊆ E ⊆ K` be a tower of finite Galois extensions and `G` an affine group scheme
over `k`. A natural cocycle of `G` on the cover `Spec K → Spec k` whose Galois values are
coboundaries on the subgroup `Gal(K/E)` is trivial as soon as every cocycle of `G` on the
cover `Spec E → Spec k` is trivial. This is the exactness at `H¹(K/k, G(K))` of the sequence
`1 → H¹(E/k, G(E)) → H¹(K/k, G(K)) → H¹(K/E, G(K))`, in the form used to show triviality.

The module also compares the values of a cocycle after a base change of the field with the
values of its refinement, which turns the inflation–restriction theorem into a descent step
along a field tower, and proves two facts about cocycles in general.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisCocycle

set_option backward.isDefEq.respectTransparency false

variable {k E K : Type u} [Field k] [Field E] [Field K]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The Galois values of the twist `(a, b) ↦ f(a)⁻¹ ξ(a, b) f(b)` of a cocycle. -/
theorem value_twist [Algebra k K] (ξ : Cocycle G (cover k K)) (f : cover k K ⟶ G.X)
    (σ : K ≃ₐ[k] K) :
    value (ξ.twist f) σ = f⁻¹ * value ξ σ * GaloisPoint.conjugate k K G σ f := by
  change (𝟙 _ ≫ f)⁻¹ * ξ.toFun (𝟙 _) (arrow k K σ) * (arrow k K σ ≫ f) = _
  rw [Category.id_comp]
  rfl

variable [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
  [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k E] [IsGalois k E]
  [IsAffine G.X.left]

/-- **Inflation–restriction.** Let `k ⊆ E ⊆ K` be finite Galois extensions and `G` an affine
group scheme over `k`. If the Galois values of a cocycle `ξ` of `G` on `Spec K → Spec k` are
the coboundary of one point `f` on the automorphisms fixing `E`, and every cocycle of `G` on
`Spec E → Spec k` is trivial, then `ξ` is trivial. -/
theorem isTrivial_of_restrict (ξ : Cocycle G (cover k K))
    (f : G.affinePoints (CommAlgCat.of k K))
    (hf : ∀ σ : K ≃ₐ[k] K, σ.restrictNormal E = 1 →
      value ξ σ = f * (GaloisPoint.conjugate k K G σ f)⁻¹)
    (hE : ∀ ζ : Cocycle G (cover k E), ζ.IsTrivial) : ξ.IsTrivial := by
  let c : (K ≃ₐ[k] K) → G.affinePoints (CommAlgCat.of k K) := value (ξ.twist f)
  have hc : ∀ σ τ, c (σ * τ) = c σ * GaloisPoint.conjugate k K G σ (c τ) :=
    fun σ τ => value_mul (ξ.twist f) σ τ
  have hcE : ∀ σ : K ≃ₐ[k] K, σ.restrictNormal E = 1 → c σ = 1 := by
    intro σ hσ
    change value (ξ.twist f) σ = 1
    rw [value_twist, hf σ hσ]
    group
  let ζ : Cocycle G (cover k E) := ofValues (GaloisCocycleTowerRecovery.value k E K G c hc hcE)
    (GaloisCocycleTowerRecovery.value_mul k E K G c hc hcE)
  obtain ⟨g, hg⟩ := (hE ζ).refine (coverMap k E K)
  apply Cocycle.IsTrivial.of_twist (f := f)
  refine ⟨g, fun a b => ?_⟩
  rw [toFun_eq_of_value_eq (ξ.twist f) (ζ.refine (coverMap k E K)) (fun σ => ?_) a b]
  · exact hg a b
  · rw [value_refine, value_ofValues]
    exact (GaloisCocycleTowerRecovery.extend_value k E K G c hc hcE σ).symm

section ScalarExtension

variable {K F F₁ M₀ M : Type u} [Field K] [Field F] [Field F₁] [Field M₀] [Field M]
  [Algebra K F] [Algebra K M₀] [Algebra K M] [Algebra F M] [Algebra M₀ M]
  [IsScalarTower K F M] [IsScalarTower K M₀ M]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- The values of the scalar extension of `ξ` to the cover `Spec M → Spec F` are the values
of the refinement of `ξ` to `Spec M → Spec K` at the same automorphisms. -/
theorem scalarExtensionPointsEquiv_value [Normal K M₀] (ξ : Cocycle G (cover K M₀))
    (τ : M ≃ₐ[F] M) :
    scalarExtensionPointsEquiv G (value (scalarExtension (K := F) (M := M) ξ) τ) =
      value (ξ.refine (coverMap K M₀ M)) (τ.restrictScalars K) := by
  rw [value_scalarExtension, value_refine]

/-- A trivial scalar extension of `ξ` to `Spec M → Spec F` makes the values of the
refinement of `ξ` to `Spec M → Spec K` a coboundary on the automorphisms fixing `F`. -/
theorem exists_value_refine_of_scalarExtension_isTrivial [Normal K M₀]
    [FiniteDimensional F M] [IsGalois F M] (ξ : Cocycle G (cover K M₀))
    (h : (scalarExtension (K := F) (M := M) ξ).IsTrivial) :
    ∃ f : G.affinePoints (CommAlgCat.of K M), ∀ τ : M ≃ₐ[F] M,
      value (ξ.refine (coverMap K M₀ M)) (τ.restrictScalars K) =
        f * (GaloisPoint.conjugate K M G (τ.restrictScalars K) f)⁻¹ := by
  obtain ⟨f, hf⟩ := (isTrivial_iff _).mp h
  refine ⟨scalarExtensionPointsEquiv G f, fun τ => ?_⟩
  rw [← scalarExtensionPointsEquiv_value, hf τ, map_mul, map_inv,
    scalarExtensionPointsEquiv_conjugate]
  rfl

/-- Triviality after base change to `F` makes the values of the refinement of `ξ` to
`Spec M → Spec K` a coboundary on the automorphisms fixing `F`. -/
theorem exists_value_refine_of_baseChangePullback_isTrivial [Normal K M₀]
    [FiniteDimensional F M] [IsGalois F M] (ξ : Cocycle G (cover K M₀))
    (h : (ξ.baseChangePullback (Spec.algebraMap K F)).IsTrivial) :
    ∃ f : G.affinePoints (CommAlgCat.of K M), ∀ τ : M ≃ₐ[F] M,
      value (ξ.refine (coverMap K M₀ M)) (τ.restrictScalars K) =
        f * (GaloisPoint.conjugate K M G (τ.restrictScalars K) f)⁻¹ :=
  exists_value_refine_of_scalarExtension_isTrivial ξ (h.refine _)

/-- If the values of the refinement of `ξ` to a finite Galois cover `Spec M → Spec K` are a
coboundary on all automorphisms, then `ξ` is trivial. -/
theorem isTrivial_of_forall_value_refine [FiniteDimensional K M] [IsGalois K M]
    (ξ : Cocycle G (cover K M₀)) (f : G.affinePoints (CommAlgCat.of K M))
    (hf : ∀ σ : M ≃ₐ[K] M, value (ξ.refine (coverMap K M₀ M)) σ =
      f * (GaloisPoint.conjugate K M G σ f)⁻¹) : ξ.IsTrivial := by
  obtain ⟨hs, hfl, hq⟩ := fieldExtension_fpqc K M
  let : Surjective (cover K M).hom := hs
  let : Flat (cover K M).hom := hfl
  let : QuasiCompact (cover K M).hom := hq
  exact Cocycle.IsTrivial.of_refine_fpqcCover (coverMap K M₀ M) ((isTrivial_iff _).mpr ⟨f, hf⟩)

/-- **One descent step.** Let `K → F → F₁ → M` be field extensions with `M/K` finite Galois
and `F₁/F` finite Galois, and suppose every cocycle of `G_F` on `Spec F₁ → Spec F` is trivial.
If the values of the refinement of `ξ` to `Spec M → Spec K` are a coboundary on the
automorphisms fixing `F₁`, then they are a coboundary on the automorphisms fixing `F`. -/
theorem exists_value_refine_of_restrict [Algebra K F₁] [Algebra F F₁] [Algebra F₁ M]
    [IsScalarTower K F F₁] [IsScalarTower F F₁ M] [IsScalarTower K F₁ M]
    [FiniteDimensional K M] [IsGalois K M] [FiniteDimensional F F₁] [IsGalois F F₁]
    [Normal K M₀] [IsAffineHom G.X.hom] (ξ : Cocycle G (cover K M₀))
    (hF : ∀ ζ : Cocycle ((GroupScheme.baseChange (Spec.algebraMap K F)).obj G) (cover F F₁),
      ζ.IsTrivial)
    (f : G.affinePoints (CommAlgCat.of K M))
    (hf : ∀ τ : M ≃ₐ[F₁] M, value (ξ.refine (coverMap K M₀ M)) (τ.restrictScalars K) =
      f * (GaloisPoint.conjugate K M G (τ.restrictScalars K) f)⁻¹) :
    ∃ f : G.affinePoints (CommAlgCat.of K M), ∀ τ : M ≃ₐ[F] M,
      value (ξ.refine (coverMap K M₀ M)) (τ.restrictScalars K) =
        f * (GaloisPoint.conjugate K M G (τ.restrictScalars K) f)⁻¹ := by
  have : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite K F M
  have : IsGalois F M := IsGalois.tower_top_of_isGalois K F M
  let GF := (GroupScheme.baseChange (Spec.algebraMap K F)).obj G
  have : IsAffineHom GF.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
    infer_instance
  have : IsAffine GF.X.left := isAffine_of_isAffineHom GF.X.hom
  apply exists_value_refine_of_scalarExtension_isTrivial
  refine isTrivial_of_restrict (E := F₁) _ ((scalarExtensionPointsEquiv G).symm f)
    (fun τ hτ => ?_) hF
  apply (scalarExtensionPointsEquiv G).injective
  rw [scalarExtensionPointsEquiv_value, map_mul, map_inv, scalarExtensionPointsEquiv_conjugate,
    MulEquiv.apply_symm_apply]
  let τ₁ : M ≃ₐ[F₁] M := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => by
    have h := τ.restrictNormal_commutes F₁ x
    rw [hτ] at h
    exact h.symm)
  have hτ₁ : τ₁.restrictScalars K = τ.restrictScalars K := AlgEquiv.ext fun _ => rfl
  rw [← hτ₁]
  exact hf τ₁

end ScalarExtension

end Langlands.GroupScheme.GaloisCocycle

namespace Langlands.GroupScheme.Cocycle

set_option backward.isDefEq.respectTransparency false

/-- A cocycle with the same values as a trivial cocycle is trivial. -/
theorem IsTrivial.congr {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}
    {ξ ζ : Cocycle G U} (h : ∀ {Z : Over S} (a b : Z ⟶ U), ξ.toFun a b = ζ.toFun a b)
    (hξ : ξ.IsTrivial) : ζ.IsTrivial := by
  obtain ⟨f, hf⟩ := hξ
  exact ⟨f, fun a b => (h a b).symm.trans (hf a b)⟩

/-- The image of a cocycle under a homomorphism stays trivial after base change when the
cocycle itself does. -/
theorem isTrivial_baseChangePullback_map {S S' : Scheme.{u}} {G H : GroupScheme S}
    {U : Over S} (ξ : Cocycle G U) (φ : G ⟶ H) (b : S' ⟶ S)
    (h : (ξ.baseChangePullback b).IsTrivial) :
    ((ξ.map φ).baseChangePullback b).IsTrivial := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g ≫ ((GroupScheme.baseChange b).map φ).hom.hom, fun {Z} x y => ?_⟩
  apply (baseChangePointsEquiv b H Z).injective
  rw [baseChangePullback, baseChange_toFun, ← Category.assoc, ← Category.assoc,
    ← GrpObj.inv_comp, ← MonObj.mul_comp, baseChangePointsEquiv_comp, ← hg]
  change ξ.toFun _ _ ≫ φ.hom.hom = _
  rw [← baseChange_toFun]
  rfl

end Langlands.GroupScheme.Cocycle
