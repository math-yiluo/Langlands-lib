import Langlands.GroupScheme.UnramifiedIntegralCosetDescent

/-! # Two-factor descent using a smooth integral intersection model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.LocalGalois.Separable

namespace Langlands.GroupScheme

open GaloisPointComparison

namespace IntegralModel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {U G : GroupScheme (Spec (CommRingCat.of F))}

/-- A supplied model realizes the intersection of two coefficient-point
subgroups through the actual group-scheme morphism. -/
def IsIntersectionModel (M : IntegralModel 𝒪[F] F U) (q : U ⟶ G)
    (A B : Subgroup (G.affinePoints (CommAlgCat.of F (inertiaFixedField F)))) : Prop :=
  ∀ z : U.affinePoints (CommAlgCat.of F (inertiaFixedField F)),
    M.HasIntegralCoordinates (inertiaFixedField F) z ↔
      U.affinePointsTarget q (CommAlgCat.of F (inertiaFixedField F)) z ∈ A ⊓ B

/-- Correct the first factor inside the modeled intersection, obtaining two
actual rational factors with their original subgroup bounds. -/
theorem exists_rational_factorization_of_intersectionModel
    [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]
    (M : IntegralModel 𝒪[F] F U) (hM : M.IsSmooth)
    (hconn : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left)
    (q : U ⟶ G)
    (A B : Subgroup (G.affinePoints (CommAlgCat.of F (inertiaFixedField F))))
    (hmodel : M.IsIntersectionModel q A B)
    (hA : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (x : G.affinePoints (CommAlgCat.of F (inertiaFixedField F))),
      x ∈ A → GaloisPoint.conjugate F (inertiaFixedField F) G σ x ∈ A)
    (hB : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (x : G.affinePoints (CommAlgCat.of F (inertiaFixedField F))),
      x ∈ B → GaloisPoint.conjugate F (inertiaFixedField F) G σ x ∈ B)
    (g : rationalPoints G)
    (x : U.affinePoints (CommAlgCat.of F (inertiaFixedField F)))
    (y : G.affinePoints (CommAlgCat.of F (inertiaFixedField F)))
    (hx : U.affinePointsTarget q (CommAlgCat.of F (inertiaFixedField F)) x ∈ A)
    (hy : y ∈ B)
    (hxy : GaloisPoint.extend F (inertiaFixedField F) G
        (rationalCoeffEquiv F G g) =
      U.affinePointsTarget q (CommAlgCat.of F (inertiaFixedField F)) x * y) :
    ∃ (u : rationalPoints U) (v : rationalPoints G),
      g = rationalPoints.map q u * v ∧
      GaloisPoint.extend F (inertiaFixedField F) G
        (rationalCoeffEquiv F G (rationalPoints.map q u)) ∈ A ∧
      GaloisPoint.extend F (inertiaFixedField F) G
        (rationalCoeffEquiv F G v) ∈ B := by
  let p := U.affinePointsTarget q (CommAlgCat.of F (inertiaFixedField F))
  have hconj (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (z : U.affinePoints (CommAlgCat.of F (inertiaFixedField F))) :
      p (GaloisPoint.conjugate F (inertiaFixedField F) U σ z) =
        GaloisPoint.conjugate F (inertiaFixedField F) G σ (p z) := by
    exact (DFunLike.congr_fun
      (U.affinePointsTarget_naturality q (CommAlgCat.ofHom σ.toAlgHom)) z).symm
  have hc : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      M.HasIntegralCoordinates (inertiaFixedField F)
        (x⁻¹ * GaloisPoint.conjugate F (inertiaFixedField F) U σ x) := by
    intro σ
    apply (hmodel _).mpr
    rw [map_mul, map_inv, hconj]
    refine ⟨A.mul_mem (A.inv_mem hx) (hA σ _ hx), ?_⟩
    have hfixed :
        GaloisPoint.conjugate F (inertiaFixedField F) G σ (p x) *
            GaloisPoint.conjugate F (inertiaFixedField F) G σ y = p x * y := by
      rw [← map_mul, ← hxy, GaloisPoint.conjugate_extend, hxy]
    have heq : (p x)⁻¹ *
        GaloisPoint.conjugate F (inertiaFixedField F) G σ (p x) =
        y * (GaloisPoint.conjugate F (inertiaFixedField F) G σ y)⁻¹ := by
      calc
        _ = (p x)⁻¹ *
            (GaloisPoint.conjugate F (inertiaFixedField F) G σ (p x) *
              GaloisPoint.conjugate F (inertiaFixedField F) G σ y) *
            (GaloisPoint.conjugate F (inertiaFixedField F) G σ y)⁻¹ := by group
        _ = _ := by rw [hfixed]; group
    rw [heq]
    exact B.mul_mem hy (B.inv_mem (hB σ _ hy))
  obtain ⟨u, h, hint, hu⟩ := unramifiedIntegralCosetDescent F U M hM hconn x hc
  have hph : p h ∈ A ⊓ B := (hmodel h).mp hint
  have hqu :
      GaloisPoint.extend F (inertiaFixedField F) G
        (rationalCoeffEquiv F G (rationalPoints.map q u)) = p x * p h := by
    rw [rationalCoeffEquiv_map]
    calc
      _ = p (GaloisPoint.extend F (inertiaFixedField F) U
          (rationalCoeffEquiv F U u)) := by
        exact DFunLike.congr_fun
          (U.affinePointsTarget_naturality q
            (CommAlgCat.ofHom (Algebra.ofId F (inertiaFixedField F)))) _
      _ = p x * p h := by rw [hu, map_mul]
  let v := (rationalPoints.map q u)⁻¹ * g
  refine ⟨u, v, ?_, ?_, ?_⟩
  · dsimp [v]
    group
  · rw [hqu]
    exact A.mul_mem hx hph.1
  · change GaloisPoint.extend F (inertiaFixedField F) G
        (rationalCoeffEquiv F G ((rationalPoints.map q u)⁻¹ * g)) ∈ B
    rw [map_mul, map_inv, map_mul, map_inv, hqu, hxy]
    have heq : (p x * p h)⁻¹ * (p x * y) = (p h)⁻¹ * y := by group
    rw [heq]
    exact B.mul_mem (B.inv_mem hph.2) hy

end IntegralModel

end Langlands.GroupScheme
