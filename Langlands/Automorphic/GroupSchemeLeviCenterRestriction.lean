import Langlands.Algebra.EnvelopingCenterQuotients
import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Enveloping centers under restriction to a rational Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme InfiniteAdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G Q M V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {q : Q ⟶ G} (l : M ⟶ Q) (iV : V ⟶ Q)

/-- Restriction of a translated smooth function to the actual infinite Levi points. -/
def infiniteLeviRestriction (a : InfiniteAdelicGroupPoints F G) :
    InfinitePlotSmoothFunctions F G →ₗ[ℂ] InfinitePlotSmoothFunctions F M where
  toFun f := ⟨fun x => f.val (M.affinePointsTarget (l ≫ q)
    (CommAlgCat.of F (InfiniteAdeleRing F)) x * a), by
      let A := CommAlgCat.of F (InfiniteAdeleRing F)
      let c := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
      have hf : G.IsPlotSmooth A (B := mixedEmbedding.mixedSpace F) c f.val := f.property
      exact (IsPlotSmooth.rightTranslate G A (B := mixedEmbedding.mixedSpace F) c hf a).postcomp
        (l ≫ q).hom.hom⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The finite parabolic homomorphism for the actual infinite enveloping centers,
in the convention of unnormalized restriction after a fixed right translation. -/
def ParabolicLeviCenterRestrictionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G Q M V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine M.X.left]
    (q : Q ⟶ G) (iV : V ⟶ Q) (l : M ⟶ Q),
    IsConnectedReductive G → IsParabolicSubgroup q →
    LeviSubgroup.IsGeometricUnipotentRadical iV → IsRationalLeviSubgroup l →
    IsIso (subgroupMultiplication l iV) →
    ∀ {d e : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)
      (hM : SmoothOfRelativeDimension e M.X.hom)
      (hcG : AdelicDifferentialCommutator F G hG)
      (hcM : AdelicDifferentialCommutator F M hM)
      (a : InfiniteAdelicGroupPoints F G),
      ∃ p : AdelicEnvelopingCenter F G hG →ₐ[ℂ] AdelicEnvelopingCenter F M hM,
        p.Finite ∧
        ∀ (f : InfinitePlotSmoothFunctions F G),
          (∀ (v : InfiniteAdelicGroupPoints F V) (x : InfiniteAdelicGroupPoints F G),
            f.val (V.affinePointsTarget (iV ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) v * x) =
              f.val x) →
          ∀ z, infiniteLeviRestriction (q := q) l a (plotSmoothCenterAction F G hG hcG z f) =
            plotSmoothCenterAction F M hM hcM (p z) (infiniteLeviRestriction (q := q) l a f)

variable [IsAffine M.X.left] {d e : ℕ}
  {hG : SmoothOfRelativeDimension d G.X.hom} {hM : SmoothOfRelativeDimension e M.X.hom}
  (hcG : AdelicDifferentialCommutator F G hG) (hcM : AdelicDifferentialCommutator F M hM)

/-- A finite parabolic center comparison extends a cofinite annihilator to one cofinite
annihilator for all restrictions to the Levi at the designated translate. -/
theorem exists_cofinite_center_ideal_of_leviRestriction
    (a : InfiniteAdelicGroupPoints F G)
    (p : AdelicEnvelopingCenter F G hG →ₐ[ℂ] AdelicEnvelopingCenter F M hM) (hp : p.Finite)
    (hpAction : ∀ f : InfinitePlotSmoothFunctions F G,
      (∀ (v : InfiniteAdelicGroupPoints F V) (x : InfiniteAdelicGroupPoints F G),
        f.val (V.affinePointsTarget (iV ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) v * x) =
          f.val x) →
      ∀ z, infiniteLeviRestriction (q := q) l a (plotSmoothCenterAction F G hG hcG z f) =
        plotSmoothCenterAction F M hM hcM (p z) (infiniteLeviRestriction (q := q) l a f))
    (J : Ideal (AdelicEnvelopingCenter F G hG))
    (hJ : Module.Finite ℂ (AdelicEnvelopingCenter F G hG ⧸ J.restrictScalars ℂ)) :
    ∃ I : Ideal (AdelicEnvelopingCenter F M hM),
      Module.Finite ℂ (AdelicEnvelopingCenter F M hM ⧸ I.restrictScalars ℂ) ∧
      ∀ f : InfinitePlotSmoothFunctions F G,
        (∀ (v : InfiniteAdelicGroupPoints F V) (x : InfiniteAdelicGroupPoints F G),
          f.val (V.affinePointsTarget (iV ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) v * x) =
            f.val x) →
        (∀ z ∈ J, plotSmoothCenterAction F G hG hcG z f = 0) →
        ∀ z ∈ I, plotSmoothCenterAction F M hM hcM z (infiniteLeviRestriction (q := q) l a f) = 0 := by
  let I := J.map p.toRingHom
  let : Module.Finite ℂ (AdelicEnvelopingCenter F G hG ⧸ J) :=
    (Module.Finite.equiv_iff (Submodule.Quotient.restrictScalarsEquiv ℂ J)).mp hJ
  refine ⟨I, ?_, fun f hLeft hJf z hz => ?_⟩
  · have hI : Module.Finite ℂ (AdelicEnvelopingCenter F M hM ⧸ I) :=
      Langlands.Algebra.quotientFinite_map p hp J
    exact (Module.Finite.equiv_iff (Submodule.Quotient.restrictScalarsEquiv ℂ I)).mpr hI
  let S := infiniteLeviRestriction (q := q) l a f
  let R := plotSmoothCenterAction F M hM hcM
  change R z S = 0
  change z ∈ J.map p.toRingHom at hz
  rw [Ideal.map] at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    change R (p x) S = 0
    rw [← hpAction f hLeft x, hJf x hx, map_zero]
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | smul t x _ hx =>
    change R (t * x) S = 0
    rw [map_mul, Module.End.mul_apply, hx, map_zero]

end Langlands.Automorphic.GroupSchemeFunctions
