import Langlands.RingTheory.Smooth.ArtinianLifting
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Smoothness of scheme morphisms from lifting along Artinian thickenings -/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.ArtinianLiftingSmooth

/-- Lifting along elementary Artinian thickenings whose residue point is locally
of finite type. Elementary means that the kernel is annihilated by the maximal
ideal of the source. -/
def LiftsArtinian {Y Z : Scheme.{u}} (g : Y ⟶ Z) : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    [IsArtinianRing B'] [IsArtinianRing B] (φ : B' →+* B), Function.Surjective φ →
      maximalIdeal B' * RingHom.ker φ = ⊥ →
      ∀ (α : Spec (CommRingCat.of B) ⟶ Y) (β : Spec (CommRingCat.of B') ⟶ Z),
        α ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ β →
        LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (residue B)) ≫ α) →
        ∃ γ : Spec (CommRingCat.of B') ⟶ Y,
          γ ≫ g = β ∧ Spec.map (CommRingCat.ofHom φ) ≫ γ = α

/-- Lifting along elementary Artinian thickenings makes a locally finite-type
morphism to a locally noetherian scheme smooth. -/
theorem smooth_of_liftsArtinian {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsLocallyNoetherian Z]
    [LocallyOfFiniteType g] (h : LiftsArtinian g) : Smooth g := by
  rw [HasRingHomProperty.iff_appLE (P := @Smooth)]
  intro U V e
  have hU : IsAffineOpen (U : Z.Opens) := U.2
  have hV : IsAffineOpen (V : Y.Opens) := V.2
  have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian U
  have hft : (g.appLE U V e).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) g ‹_› U V e
  let := (g.appLE U V e).hom.toAlgebra
  have : Algebra.FiniteType Γ(Z, U) Γ(Y, V) := hft
  change Algebra.Smooth Γ(Z, U) Γ(Y, V)
  apply Langlands.RingTheory.ArtinianLifting.smooth
  intro B' B _ _ _ _ _ _ _ _ φ hφ hel ψ hres
  let α : Spec (CommRingCat.of B) ⟶ Y :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec
  let β : Spec (CommRingCat.of B') ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, U) B')) ≫ hU.fromSpec
  have hαβ : α ≫ g = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ β := by
    simp only [α, β, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec g hU hV e]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext x
    exact (ψ.commutes x).trans (φ.commutes x).symm
  have hlft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (residue B)) ≫ α) := by
    have : IsClosedImmersion
        (Spec.map (CommRingCat.ofHom ((residue B).comp ψ.toRingHom))) :=
      IsClosedImmersion.spec_of_surjective _ hres
    have e2 : Spec.map (CommRingCat.ofHom (residue B)) ≫ α =
        Spec.map (CommRingCat.ofHom ((residue B).comp ψ.toRingHom)) ≫ hV.fromSpec := by
      simp only [α, ← Category.assoc, ← Spec.map_comp]
      rfl
    rw [e2]
    infer_instance
  obtain ⟨γ, hγg, hγφ⟩ := h B' B φ.toRingHom hφ hel α β hαβ hlft
  have hrange : Set.range γ ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩
    have : Unique (PrimeSpectrum B') := PrimeSpectrum.unique_of_ringKrullDimLE_zero
    let c : Spec (CommRingCat.of B) := closedPoint B
    have hy : y = Spec.map (CommRingCat.ofHom φ.toRingHom) c :=
      Subsingleton.elim (α := PrimeSpectrum B') _ _
    rw [hy, ← Scheme.Hom.comp_apply, hγφ]
    exact ⟨_, rfl⟩
  let γ' := IsOpenImmersion.lift hV.fromSpec γ hrange
  have hγ' : γ' ≫ hV.fromSpec = γ := IsOpenImmersion.lift_fac _ _ _
  let ψ'' : Γ(Y, V) ⟶ CommRingCat.of B' := Spec.preimage γ'
  have hψ'' : Spec.map ψ'' = γ' := Spec.map_preimage γ'
  have hcomm : g.appLE U V e ≫ ψ'' = CommRingCat.ofHom (algebraMap Γ(Z, U) B') := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec g hU hV e, ← Category.assoc, hψ'', hγ', hγg]
  refine ⟨{ toRingHom := ψ''.hom, commutes' := fun x ↦ ?_ }, ?_⟩
  · exact congrArg (fun f ↦ f.hom x) hcomm
  · have hφψ : ψ'' ≫ CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom ψ.toRingHom := by
      apply Spec.map_injective
      rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc, hψ'', hγ', hγφ]
    ext x
    exact congrArg (fun f ↦ f.hom x) hφψ

end Langlands.AlgebraicGeometry.ArtinianLiftingSmooth
