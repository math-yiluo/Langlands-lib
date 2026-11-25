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
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ModuleAbelianStalkExchange
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange

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

/-- The original geometric-stalk exchange is pullback on total strict-local spaces.
This comparison has no local higher-direct-image stalks in its conclusion.

Source: Stacks Project, Tags 03Q9 and 03FD, and the last two paragraphs of Tag 095T.
(blueprint: lem-weil-pbc-p1-original-stalk-total-cohomology-exchange).

Proof: properness makes the projective-line projection qcqs. The inverse-image
stalk formula identifies the source with the higher-direct-image stalk at sigma.
Extending the separably closed geometric fields to Omega does not change stalks:
finite separable extensions in pointed etale neighbourhoods already split. Apply
03Q9 to compute that stalk by cohomology of the projective line over A. Apply it
also to f' at the extended point of T and use the pullback universal property to
identify its total strict-local space with the projective line over B. The
coefficient sheaf there is the pullback of F0 along the projective-space map of
phi, by inverse-image composition coherence and the structural square hphi.
Use an injective module-sheaf resolution; its underlying abelian sheaves are
acyclic by 03FD at universe u+1. This compares module cohomology with the stated
abelian cohomology without assuming that forgetting coefficients preserves
injectives. On every pointed neighbourhood the termwise derived exchange pulls
sections back along its base-changed projection. The structural square and
residue square force these projections to commute with phi, by uniqueness of
pointed etale lifts from a strictly henselian local scheme. Therefore the same
section map induces both sides of the displayed equality. Exact filtered
colimits commute with homology, giving the equality in degree q. For arbitrary
X' use the unique pullback isomorphism. Degree zero is the same restriction of
sections; zero coefficients and purely inseparable field extensions cause no
change. No local closed-point stalk or closed-fibre comparison is used. -/
theorem Etale.projectiveLine_originalStalk_totalCohomologyExchange
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
    let G₀ := (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F₀
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    ∃ (c₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
        Sheaf.H G₀ q)
      (c₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ g₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q),
      ∀ x, c₂ ((((pointSmallEtale τ).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ g₀) G₀ q (c₁ x) := by
  let p := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ))
  let G := (sheafCompose _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  let g₀ := Spec.map (CommRingCat.ofHom φ)
  let h := ProjectiveSpace.map (ULift.{u} (Fin 2)) g₀
  obtain ⟨b₁, b₂, hb⟩ := Etale.exists_addEquiv_module_abelian_stalk_exchange
    Λ (ProjectiveLine S ↘ S) f' g' g sq τ F q
  obtain ⟨a₁, a₂, ha⟩ := Etale.projectiveLine_abelian_originalStalk_totalExchange
    sq σ τ ι hι ν eA eB φ ρA ρB hφ hρA hρB hρ G q
  obtain ⟨d⟩ := Etale.pullback_forget_modules_iso Λ p F
  let c₁ := ((Sheaf.functorH _ q).mapIso d.symm).addCommGroupIsoToAddEquiv
  let c₂ := ((Sheaf.functorH _ q).mapIso
    (((h)^*[AddCommGrpCat.{u + 1}]).mapIso d.symm)).addCommGroupIsoToAddEquiv
  refine ⟨(b₁.trans a₁).trans c₁, (b₂.trans a₂).trans c₂, ?_⟩
  intro x
  change c₂ (a₂ (b₂ _)) = Etale.cohomologyMap h _ q (c₁ (a₁ (b₁ x)))
  rw [hb x, ha (b₁ x)]
  exact (Etale.cohomologyMap_map h q d.inv (a₁ (b₁ x))).symm

end AlgebraicGeometry
