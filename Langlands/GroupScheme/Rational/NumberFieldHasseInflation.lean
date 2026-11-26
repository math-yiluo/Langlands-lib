import Langlands.GroupScheme.GaloisCocycleScalarExtension
import Langlands.GroupScheme.GaloisCocycleTowerRecovery
import Langlands.GroupScheme.GaloisCocycleConstruction
import Langlands.GroupScheme.CocycleCohomology
import Langlands.GroupScheme.Rational.CentralMuCocycleLift

/-! # Inflation and restriction for the number-field Hasse kernel

A locally trivial cocycle on a finite Galois cover `L/F` of a number field that becomes
trivial after base change to a finite Galois extension `E/F` comes, after refinement and a
twist, from a locally trivial cocycle on the cover `E/F`. So it is trivial as soon as every
locally trivial cocycle on `E/F` is trivial.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Cocycle

section Cohomologous

variable {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}

/-- Triviality passes to every cohomologous cocycle. -/
theorem IsTrivial.of_cohomologous {ξ ζ : Cocycle G U} (h : ξ.Cohomologous ζ)
    (hξ : ξ.IsTrivial) : ζ.IsTrivial := by
  obtain ⟨f, hf⟩ := h.symm
  obtain ⟨g, hg⟩ := hξ
  exact IsTrivial.of_twist (f := f) ⟨g, fun a b => (hf a b).symm.trans (hg a b)⟩

/-- A cocycle is cohomologous to each of its twists. -/
theorem cohomologous_twist (ξ : Cocycle G U) (f : U ⟶ G.X) :
    ξ.Cohomologous (ξ.twist f) :=
  ⟨f, fun _ _ => rfl⟩

/-- Two cocycles with the same values on all pairs of points are cohomologous. -/
theorem cohomologous_of_toFun_eq {ξ ζ : Cocycle G U}
    (h : ∀ {Z : Over S} (a b : Z ⟶ U), ξ.toFun a b = ζ.toFun a b) : ξ.Cohomologous ζ := by
  refine ⟨1, fun a b => ?_⟩
  simp only [twist, MonObj.comp_one, inv_one, one_mul, mul_one]
  exact (h a b).symm

end Cohomologous

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} {U : Over (Spec (CommRingCat.of F))}

/-- Local triviality passes to every cohomologous cocycle. -/
theorem LocallyTrivial.of_cohomologous {ξ ζ : Cocycle G U} (h : ξ.Cohomologous ζ)
    (hξ : ξ.LocallyTrivial) : ζ.LocallyTrivial := fun v =>
  IsTrivial.of_cohomologous (h.baseChange _ _ _) (hξ v)

end Cocycle

open GaloisCocycle GaloisPoint

variable {F L E : Type u} [Field F] [NumberField F] [Field L] [Field E]
  [Algebra F L] [Algebra F E]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F E] [IsGalois F E]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

set_option backward.isDefEq.respectTransparency false in
/-- Inflation–restriction for the Hasse kernel. Let `ξ` be a locally trivial cocycle on the
finite Galois cover `L/F`, and let `E/F` be a finite Galois extension over which `ξ` becomes
trivial, on the full pullback cover. If every locally trivial cocycle on the cover `E/F` is
trivial, then `ξ` is trivial. The field `M` is any finite Galois extension of `F` containing
compatible copies of `L` and `E`. -/
theorem Cocycle.isTrivial_of_baseChange_isTrivial_of_kernel
    (M : Type u) [Field M] [Algebra F M] [Algebra L M] [Algebra E M]
    [IsScalarTower F L M] [IsScalarTower F E M] [FiniteDimensional F M] [IsGalois F M]
    (ξ : Cocycle G (cover F L)) (hξ : ξ.LocallyTrivial)
    (hE : (ξ.baseChangePullback (Spec.algebraMap F E)).IsTrivial)
    (hker : ∀ θ : Cocycle G (cover F E), θ.LocallyTrivial → θ.IsTrivial) :
    ξ.IsTrivial := by
  have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
  have : IsGalois L M := IsGalois.tower_top_of_isGalois F L M
  let p := coverMap F E M
  let ξM := ξ.refine (coverMap F L M)
  obtain ⟨a, ha⟩ := exists_galois_coboundary_of_baseChange_isTrivial (K := E) (M := M) ξ hE
  let ξ' := ξM.twist a
  have hval : ∀ σ : M ≃ₐ[F] M,
      value ξ' σ = a⁻¹ * value ξM σ * conjugate F M G σ a := by
    intro σ
    change (𝟙 _ ≫ a)⁻¹ * value ξM σ * (arrow F M σ ≫ a) = _
    rw [Category.id_comp]
    rfl
  have htriv : ∀ σ : M ≃ₐ[F] M, σ.restrictNormal E = 1 → value ξ' σ = 1 := by
    intro σ hσ
    have hfix : ∀ x : E, σ (algebraMap E M x) = algebraMap E M x := by
      intro x
      rw [← AlgEquiv.restrictNormal_commutes σ E x, hσ]
      rfl
    let τ : M ≃ₐ[E] M := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hfix
    have hτ : τ.restrictScalars F = σ := by
      ext x
      rfl
    have h := ha τ
    rw [hτ] at h
    rw [hval, value_refine, h]
    group
  let c : (E ≃ₐ[F] E) → G.affinePoints (CommAlgCat.of F E) :=
    GaloisCocycleTowerRecovery.value F E M G (value ξ') (value_mul ξ') htriv
  let θ : Cocycle G (cover F E) :=
    ofValues c (GaloisCocycleTowerRecovery.value_mul F E M G (value ξ') (value_mul ξ') htriv)
  have hθ : ∀ {Z : Over (Spec (CommRingCat.of F))} (x y : Z ⟶ cover F M),
      (θ.refine p).toFun x y = ξ'.toFun x y := by
    intro Z x y
    refine toFun_eq_of_value_eq (θ.refine p) ξ' (fun σ => ?_) x y
    rw [value_refine, value_ofValues]
    exact GaloisCocycleTowerRecovery.extend_value F E M G (value ξ') (value_mul ξ') htriv σ
  have hξ' : ξ'.LocallyTrivial :=
    Cocycle.LocallyTrivial.of_cohomologous (Cocycle.cohomologous_twist ξM a)
      (Cocycle.LocallyTrivial.refine hξ _)
  have hθM : (θ.refine p).LocallyTrivial :=
    Cocycle.LocallyTrivial.of_cohomologous
      (Cocycle.cohomologous_of_toFun_eq (fun x y => (hθ x y).symm)) hξ'
  have hθloc : θ.LocallyTrivial := by
    intro w
    let b := algebraBaseMap F (Global.placeCompletion F w)
    obtain ⟨f, hf⟩ := hθM w
    have h2 : ((θ.baseChange b _ ((Over.mapPullbackAdj b).counit.app (cover F E))).refine
        ((Over.pullback b).map p)).IsTrivial :=
      ⟨f, fun x y => by
        rw [← Cocycle.baseChange_pullback_refine_toFun]
        exact hf x y⟩
    obtain ⟨hs, hfl, hq⟩ := fieldExtension_fpqc F M
    let : Surjective (cover F M).hom := hs
    let : Flat (cover F M).hom := hfl
    let : QuasiCompact (cover F M).hom := hq
    let : Surjective ((Over.pullback b).obj (cover F M)).hom :=
      inferInstanceAs (Surjective (pullback.snd (cover F M).hom b))
    let : Flat ((Over.pullback b).obj (cover F M)).hom :=
      inferInstanceAs (Flat (pullback.snd (cover F M).hom b))
    let : QuasiCompact ((Over.pullback b).obj (cover F M)).hom :=
      inferInstanceAs (QuasiCompact (pullback.snd (cover F M).hom b))
    exact Cocycle.IsTrivial.of_refine_fpqcCover _ h2
  have hξ'triv : ξ'.IsTrivial :=
    Cocycle.IsTrivial.of_cohomologous (Cocycle.cohomologous_of_toFun_eq hθ)
      ((hker θ hθloc).refine p)
  exact isTrivial_of_refine F L M ξ (Cocycle.IsTrivial.of_twist hξ'triv)

end Langlands.GroupScheme
