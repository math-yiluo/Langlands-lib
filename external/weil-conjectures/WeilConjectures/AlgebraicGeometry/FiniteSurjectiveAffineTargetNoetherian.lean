/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.FiniteAffinePushforwardIdealDevissage
import WeilConjectures.AlgebraicGeometry.CoherentPropertyDevissageIntegralSubschemes
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveCoherentGenericSupport
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.SerreCriterionAffineness
import WeilConjectures.AlgebraicGeometry.PQFCohomology

/-!
# Affineness of a Noetherian finite surjective image

Source: Stacks Project, Cohomology of Schemes, Lemma 01YQ
(blueprint: lem-weil-pbc-finite-surjective-affine-target-noetherian).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A Noetherian (locally Noetherian and quasi-compact) scheme receiving a finite surjective
morphism from an affine scheme is affine. Source: Stacks Project, Lemma 01YQ.
(blueprint: lem-weil-pbc-finite-surjective-affine-target-noetherian).

Proof:
1. Set P(F) to H¹(X,F) = 0. The recorded cohomological delta-functor makes
   degree-one cohomology additive and exact in the middle of a short exact sequence.
   Hence P holds for zero and is stable under extensions [pqf-def-cohomology].
2. Inclusion and projection of the zeroth summand of a positive finite biproduct
   give a retraction. Applying cohomology shows that P of the biproduct implies P(F).
3. For an integral closed subscheme with generic point ξ, choose coherent F on Y
   with the required pushforward support and generic annihilator
   [lem-weil-pbc-finite-surjective-coherent-generic-support]. Finite pushforward
   coherence makes G = f_*F coherent [lem-weil-pbc-finite-pushforward-coherent].
   The ideal-product lemma supplies the coherent, generically full, acyclic subobject
   [lem-weil-pbc-finite-affine-pushforward-ideal-devissage].
4. Apply coherent devissage to obtain P for every coherent module
   [lem-weil-pbc-coherent-property-devissage-integral-subschemes].
5. A finite-type ideal module is quasi-coherent: it is the kernel of the map from
   the structure module to the closed-subscheme structure-module pushforward
   [lem-pc-closed-immersion-coherent-cohomology,
   lem-weil-pbc-quasi-coherent-module-kernel]. It is therefore coherent on locally
   Noetherian X [pqf-lem-coherent-ft-locnoeth]. Noetherian X is compact and
   quasi-separated [lem-weil-pbc-locally-noetherian-quasi-separated], so its ideal
   H¹ vanishing implies affineness [pqf-lem-serre-criterion]. -/
theorem isAffine_of_isFinite_surjective_of_isNoetherian
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsAffine Y]
    [IsNoetherian X] : IsAffine X :=
  open CategoryTheory.Limits ZeroObject in by
  classical
  let : Zero X.Modules := HasZeroObject.zero' X.Modules
  let H := RingedSpace.moduleCohomology X.toRingedSpace 1
  let P : X.Modules → Prop := fun F ↦ IsZero (H.obj F)
  obtain ⟨D, hD⟩ := (sheafCohomologyAndHigherDirectImages.{u, u, u} X).1
  have hadd : H.Additive := by
    simpa only [H, hD] using D.additive 1
  let := hadd
  have hzero : P (0 : X.Modules) := H.map_isZero (isZero_zero _)
  have hext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      P S.X₁ → P S.X₃ → P S.X₂ := by
    intro S hS _ _ _ h₁ h₃
    obtain ⟨w, hw⟩ := D.exact_middle S hS 1
    have hz := hw.isZero_of_both_isZero
    dsimp only [ShortComplex.mk, ShortComplex.X₁, ShortComplex.X₂, ShortComplex.X₃] at hz
    rw [hD] at hz
    exact hz h₁ h₃
  have hsum : ∀ (F : X.Modules) (r : ℕ),
      RingedSpace.IsCoherent X.toRingedSpace F → 1 ≤ r →
      P (@biproduct (Fin r) X.Modules _ _ (fun _ : Fin r ↦ F)
        (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ F))) → P F := by
    intro F r _ hr hF
    let : HasBiproduct (fun _ : Fin r ↦ F) := HasBiproduct.of_hasProduct _
    let j : Fin r := ⟨0, hr⟩
    apply (IsZero.iff_id_eq_zero _).mpr
    calc
      𝟙 (H.obj F) = H.map (biproduct.ι (fun _ : Fin r ↦ F) j) ≫
          H.map (biproduct.π (fun _ : Fin r ↦ F) j) := by
        rw [← H.map_comp, biproduct.ι_π_self, H.map_id]
      _ = 0 := by rw [hF.eq_of_tgt (H.map (biproduct.ι (fun _ : Fin r ↦ F) j)) 0,
        zero_comp]
  have hintegral : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z] (ξ : X)
      (hclosure : closure ({ξ} : Set X) = Set.range i.base),
      ∃ G : X.Modules,
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        ({x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base) ∧
        (∀ g : X.presheaf.stalk ξ, ∀ m : (RingedSpace.moduleStalkFunctor
          X.toRingedSpace ξ).obj G, g ∈ IsLocalRing.maximalIdeal _ → g • m = 0) ∧
        ∀ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
          [Mono ι] [J.IsQuasicoherent],
          Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom →
          ∃ G' : Subobject G,
            RingedSpace.IsCoherent X.toRingedSpace (G' : X.Modules) ∧
            (∃ h : (G' : X.Modules) ⟶ Scheme.idealModuleProduct ι G,
              G'.arrow = h ≫ Scheme.idealModuleProductι ι G) ∧
            Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map
              G'.arrow).hom ∧ P (G' : X.Modules) := by
    intro Z i _ _ ξ hclosure
    obtain ⟨F, hF, hsupp, hann⟩ := Scheme.exists_coherent_pushforward_support_eq_range
      f i ξ hclosure
    refine ⟨(Scheme.Modules.pushforward f).obj F,
      (Scheme.Modules.isCoherent_pushforward_of_isFinite f F hF).1,
      hsupp, fun g m hg ↦ hann g hg m, ?_⟩
    intro J ι _ _ hι
    exact Scheme.Modules.finite_affine_pushforward_ideal_devissage f F hF ξ ι hι
  have hall := Scheme.Modules.coherent_property_devissage_integral_subschemes
    X P hzero hext hsum hintegral
  apply Scheme.isAffine_of_finiteType_ideal_h1_zero X
  intro I hI
  have hq : I.toModules.IsQuasicoherent := by
    have := SheafOfModules.isQuasicoherent_unit (R := I.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    have hp := Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion I.subschemeι
      (SheafOfModules.unit I.subscheme.ringCatSheaf)
    have : ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)).IsQuasicoherent := hp
    exact Scheme.Modules.isQuasicoherent_kernel I.toPushforwardSubscheme
  exact hall I.toModules
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X I.toModules).mpr
      ⟨hq, hI⟩)

end AlgebraicGeometry
