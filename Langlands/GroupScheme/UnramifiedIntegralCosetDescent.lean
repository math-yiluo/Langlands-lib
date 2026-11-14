import Langlands.GroupScheme.LocalUnramifiedTwistDescent

/-! # Rational points in Galois-stable integral cosets -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

open Langlands.LocalGalois.Separable GaloisPointComparison

namespace GaloisPoint

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

/-- Every point over the maximal unramified extension has a finite Galois
unramified field of definition in the same separable closure. -/
theorem exists_finiteUnramified_definition
    (x : G.affinePoints (CommAlgCat.of F (inertiaFixedField F))) :
    ∃ (E : IntermediateField F (SeparableClosure F))
      (_ : FiniteDimensional F E) (_ : IsGalois F E)
      (hE : E ≤ inertiaFixedField F)
      (xE : G.affinePoints (CommAlgCat.of F E)),
      G.affinePointMap (CommAlgCat.ofHom (IntermediateField.inclusion hE)) xE = x := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F (AffineCoordinateRing F G.X)).out
  let c := coordinates F G (inertiaFixedField F) x
  let S : Set (SeparableClosure F) := (fun a => (c a : SeparableClosure F)) '' (s : Set _)
  let E₀ : IntermediateField F (SeparableClosure F) := IntermediateField.adjoin F S
  have : FiniteDimensional F E₀ :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsSeparable.isIntegral F y
  have hE₀ : E₀ ≤ inertiaFixedField F := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨a, -, rfl⟩
    exact (c a).property
  obtain ⟨E, hfin, hgal, hE₀E, hE⟩ :=
    GaloisCocycle.exists_finiteDimensional_isGalois_between (inertiaFixedField F) E₀ hE₀
  have hcE : ∀ a ∈ s, (c a : SeparableClosure F) ∈ E := fun a ha =>
    hE₀E (IntermediateField.subset_adjoin F S ⟨a, ha, rfl⟩)
  let incl := IntermediateField.inclusion hE
  have hincl : Function.Injective incl := incl.toRingHom.injective
  have hrange : c.range ≤ incl.range := by
    rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨c a, hcE a ha⟩, rfl⟩
  let cE : AffineCoordinateRing F G.X →ₐ[F] E :=
    (AlgEquiv.ofInjective incl hincl).symm.toAlgHom.comp
      (c.codRestrict incl.range fun a => hrange ⟨a, rfl⟩)
  let xE := (coordinates F G E).symm cE
  refine ⟨E, hfin, hgal, hE, xE, ?_⟩
  apply (coordinates F G (inertiaFixedField F)).injective
  apply AlgHom.ext
  intro a
  rw [coordinates_apply, affinePointEvaluation_map, ← coordinates_apply,
    Equiv.apply_symm_apply]
  change incl ((AlgEquiv.ofInjective incl hincl).symm ⟨c a, _⟩) = c a
  rw [← AlgEquiv.ofInjective_apply incl hincl, AlgEquiv.apply_symm_apply]

end GaloisPoint

/-- An internal consequence of KP Lemma 8.1.4: a Galois-stable right coset of
the integral points of a smooth model with connected special fibre contains an
actual rational point. The equation records its integral correction. -/
def UnramifiedIntegralCosetDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (M : IntegralModel 𝒪[F] F G), M.IsSmooth →
    ConnectedSpace ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left →
    ∀ x : G.affinePoints (CommAlgCat.of F (inertiaFixedField F)),
      (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        M.HasIntegralCoordinates (inertiaFixedField F)
          (x⁻¹ * GaloisPoint.conjugate F (inertiaFixedField F) G σ x)) →
      ∃ (g : rationalPoints G)
        (h : G.affinePoints (CommAlgCat.of F (inertiaFixedField F))),
        M.HasIntegralCoordinates (inertiaFixedField F) h ∧
        GaloisPoint.extend F (inertiaFixedField F) G (rationalCoeffEquiv F G g) = x * h

/-- Correct the finite-level cocycle of a point, then descend the corrected point. -/
theorem unramifiedIntegralCosetDescent : UnramifiedIntegralCosetDescentStatement.{u} := by
  intro F _ _ _ _ G _ _ M hM hconn x hx
  obtain ⟨E, hfin, hgal, hE, xE, hxE⟩ := GaloisPoint.exists_finiteUnramified_definition G x
  let := hfin
  let := hgal
  let : Algebra E (inertiaFixedField F) := (IntermediateField.inclusion hE).toAlgebra
  have : IsScalarTower F E (inertiaFixedField F) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxE' : GaloisPoint.relativeExtend F E (inertiaFixedField F) G xE = x := hxE
  let c : (E ≃ₐ[F] E) → G.affinePoints (CommAlgCat.of F E) :=
    fun σ => xE⁻¹ * GaloisPoint.conjugate F E G σ xE
  have hc : ∀ σ τ, c (σ * τ) = c σ * GaloisPoint.conjugate F E G σ (c τ) := by
    intro σ τ
    simp only [c, GaloisPoint.conjugate_mul, map_mul, map_inv]
    group
  have hcint : ∀ σ, M.HasIntegralCoordinates E (c σ) := by
    intro σ
    apply IntegralModel.hasIntegralCoordinates_of_relativeExtend M
      (L := inertiaFixedField F)
    rw [map_mul, map_inv, GaloisPoint.relativeExtend_conjugate_lift, hxE']
    exact hx (σ.liftNormal (inertiaFixedField F))
  obtain ⟨f, hf, hcf⟩ := localUnramifiedIntegralCocycleVanishing F G M hM hconn E hE c hc hcint
  have hfixed : xE * f ∈ GaloisPoint.fixedSubgroup F E G := by
    intro σ
    rw [map_mul]
    have h := hcf σ
    change xE⁻¹ * GaloisPoint.conjugate F E G σ xE =
      f * (GaloisPoint.conjugate F E G σ f)⁻¹ at h
    calc
      _ = xE * ((xE⁻¹ * GaloisPoint.conjugate F E G σ xE) *
          GaloisPoint.conjugate F E G σ f) := by group
      _ = xE * f := by rw [h]; group
  let y := GaloisPoint.descend F E G ⟨xE * f, hfixed⟩
  have hy : GaloisPoint.extend F E G y = xE * f := GaloisPoint.extend_descend F E G _
  let h := GaloisPoint.relativeExtend F E (inertiaFixedField F) G f
  refine ⟨(rationalCoeffEquiv F G).symm y, h, ?_, ?_⟩
  · intro a
    have hi := hf a
    rw [← GaloisPoint.coordinates_apply] at hi ⊢
    rw [GaloisPoint.coordinates_relativeExtend]
    exact hi.map ((IsScalarTower.toAlgHom F E (inertiaFixedField F)).restrictScalars 𝒪[F])
  · rw [MulEquiv.apply_symm_apply]
    calc
      _ = GaloisPoint.relativeExtend F E (inertiaFixedField F) G
          (GaloisPoint.extend F E G y) := by
        apply (GaloisPoint.coordinates F G (inertiaFixedField F)).injective
        apply AlgHom.ext
        intro a
        simp only [GaloisPoint.coordinates_extend, GaloisPoint.coordinates_relativeExtend]
        exact IsScalarTower.algebraMap_apply F E (inertiaFixedField F) _
      _ = x * h := by rw [hy, map_mul, hxE']

end Langlands.GroupScheme
