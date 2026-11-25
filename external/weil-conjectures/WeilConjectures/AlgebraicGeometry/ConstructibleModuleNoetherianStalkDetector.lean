/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbeddingNoetherian
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorizationNoetherian

/-!
# Pointwise finite pushforward detectors on a Noetherian scheme

This isolates the local detector construction in the proof of Stacks Project Tag 09Z6 (3).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Etale

/-- Every point has a finite pushforward of a finitely generated constant module
with a map from C injective on all geometric stalks above that point.
Source: Stacks Project, Tag 09Z6 (3), proof of (1) transferred to module sheaves.
(blueprint: new-lem-weil-pbc-noetherian-stalk-detector).

Proof: Restrict C to the residue field at x and choose a finite separable extension
trivializing it with a finitely generated module M. Normalize the reduced closure of x
in this extension. The resulting integral morphism nu : Y -> U has normal integral
source. The constant sheaf on Y is the pushforward of its generic restriction (09Z5).
Adjoint the trivialization first along the generic inclusion and then along nu to get
C -> nu_* M. Every algebraically closed geometric point above x lifts to that generic
extension. The triangle identities and the inverse-image stalk comparison identify
the composite of its stalk map with projection to the chosen lifted stalk with the
trivialization; hence the stalk map is injective. Express nu as a cofiltered limit
of finite U-schemes and nu_* M as the corresponding filtered colimit (09Z1).
Constructibility over a Noetherian coefficient ring makes C finitely presentable
(09Z4), so the map factors through one finite stage. Its stalk map stays injective
because its composite with the transition map is injective. Choose this finite
stage and M for each x. On the empty scheme the point-indexed family is empty;
for the zero sheaf the zero module and zero maps suffice. No finite carrier for Λ
or M is required. -/
theorem exists_noetherian_stalk_detector
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    {U : Scheme.{u}} [IsNoetherian U]
    (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf C] :
    ∃ (Y : U → Scheme.{u}) (f : ∀ x, Y x ⟶ U), (∀ x, IsFinite (f x)) ∧
      ∃ (M : U → ModuleCat.{u + 1} Λ), (∀ x, Module.Finite Λ (M x)) ∧
        ∃ (ψ : ∀ x, C ⟶ (lowerStar (ModuleCat.{u + 1} Λ) (f x)).obj
          ((constantSheaf (Y x).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M x))),
          ∀ (x : U) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (s : Spec (.of Ω) ⟶ U),
            ((Scheme.SpecToEquivOfField Ω U) s).1 = x →
              Function.Injective
                (((Scheme.pointSmallEtale s).sheafFiber
                  (A := ModuleCat.{u + 1} Λ)).map (ψ x)) := by
  classical
  have hx (x : U) :
      ∃ (Y : Scheme.{u}) (f : Y ⟶ U), IsFinite f ∧
        ∃ (M : ModuleCat.{u + 1} Λ), Module.Finite Λ M ∧
          ∃ (ψ : C ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)),
            ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
              (s : Spec (.of Ω) ⟶ U),
              ((Scheme.SpecToEquivOfField Ω U) s).1 = x →
                Function.Injective
                  (((Scheme.pointSmallEtale s).sheafFiber
                    (A := ModuleCat.{u + 1} Λ)).map ψ) := by
    obtain ⟨Y, ν, hν, M, hM, φ, hφ⟩ :=
      exists_integral_lowerStar_stalk_injective_noetherian Λ C x
    let : IsIntegralHom ν := hν
    let : Module.Finite Λ M := hM
    obtain ⟨Z, f, hf, ψ, κ, hfac⟩ :=
      exists_finite_lowerStar_factorization_noetherian Λ C ν M φ
    refine ⟨Z, f, hf, M, hM, ψ, ?_⟩
    intro Ω _ _ s hs a b hab
    apply hφ Ω s hs
    let P := (Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)
    rw [← hfac, P.map_comp]
    exact congrArg (fun v ↦ (P.map κ) v) hab
  choose Y f hf M hM ψ hψ using hx
  exact ⟨Y, f, hf, M, hM, ψ, hψ⟩

end AlgebraicGeometry.Etale
