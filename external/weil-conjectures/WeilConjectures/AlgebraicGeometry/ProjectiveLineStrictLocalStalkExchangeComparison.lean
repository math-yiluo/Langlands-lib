/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange
import WeilConjectures.AlgebraicGeometry.StrictLocalTotalCohomologyExchange

/-! # Stalk exchange under compatible strict localization

Source: Stacks Project, Tags 03Q9 and 095T.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Restriction to compatible strict henselizations conjugates the stalk exchange.
Only stalks of higher direct images are compared, not closed-fibre cohomology.

Source: Stacks Project, Tag 03Q9 and the last two paragraphs of the proof of Tag 095T.
(blueprint: lem-weil-pbc-p1-strict-local-stalk-exchange-comparison).

Proof: the pullback square and the projective-line projection are qcqs by
properness. Use the inverse-image stalk formula to identify the source stalk with
the higher-direct-image stalk at σ. Extending σ and τ to Ω leaves their pointed
étale-neighbourhood categories equivalent: finite separable residue extensions
already split over k and k'. Apply the strict-henselization stalk formula at the
extended points and identify the projective-line base changes by their pullback
universal properties. Applying that formula also over the strictly henselian
bases identifies the two local closed-point stalks with the same cohomology of
the total strict-local projective lines. Compose these identifications to get a₁
and a₂. For module coefficients use an injective module-sheaf resolution and
acyclicity of its underlying abelian sheaves; do not assume that forgetting
coefficients preserves injectives. The termwise exchange is restriction of
sections along the pulled-back neighbourhood. The structural square and the
pointed residue square imply that φ commutes with every pointed-neighbourhood
projection, by the uniqueness of pointed étale lifts to a strictly henselian
local scheme. Thus the same section map occurs in both stalk formulas.
Filtered colimits are exact, so passage to homology gives the displayed equation.
For arbitrary X', transport along the unique isomorphism of pullback squares.
This argument works in degree zero and never uses a closed-fibre theorem. -/
theorem Etale.projectiveLine_strictLocal_stalkExchangeComparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictLocalizationToBase (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    let F₀ := (ProjectiveSpace.map _
      (eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)))^*[
      ModuleCat.{u + 1} Λ].obj F
    let t₀ := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    ∃ (a₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
                (t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeSourceFunctor Λ g₀
                    (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) q).obj F₀))
                (a₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
                (t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeTargetFunctor Λ (ProjectiveSpace.map _ g₀)
                    (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B)) q).obj F₀)),
                (∀ x, a₂ ((((pointSmallEtale τ).sheafFiber
                    (A := ModuleCat.{u + 1} Λ)).map
                    (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
                  ((t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).map
                    (Etale.baseChangeHomologyMap Λ
                      (ProjectiveSpace.isPullback_map _ g₀) q F₀)).hom (a₁ x)) := by
  let F₀ := (ProjectiveSpace.map _
    (eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)))^*[
    ModuleCat.{u + 1} Λ].obj F
  let g₀ := Spec.map (CommRingCat.ofHom φ)
  obtain ⟨c₁, c₂, hc⟩ :=
    Etale.projectiveLine_originalStalk_totalCohomologyExchange Λ sq σ τ ι hι ν
      eA eB φ ρA ρB hφ hρA hρB hρ F q
  obtain ⟨d₁, d₂, hd⟩ :=
    Etale.exists_addEquiv_strictLocal_totalCohomology_exchange Λ φ
      (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
      (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B))
      (ProjectiveSpace.map _ g₀) (ProjectiveSpace.isPullback_map _ g₀) F₀ q
  refine ⟨c₁.trans d₁.symm, c₂.trans d₂.symm, ?_⟩
  intro x
  apply d₂.injective
  simp only [AddEquiv.trans_apply]
  rw [hc, hd, AddEquiv.apply_symm_apply]
  simp [F₀, g₀]

end AlgebraicGeometry
