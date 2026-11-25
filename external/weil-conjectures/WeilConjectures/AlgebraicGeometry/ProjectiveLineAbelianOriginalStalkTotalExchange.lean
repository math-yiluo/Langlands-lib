/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization
import WeilConjectures.AlgebraicGeometry.StrictLocalAbelianTotalExchange

/-! # Original abelian stalk exchange on total strict-local projective lines

Source: Stacks Project, Tag 03Q9 and the stalk calculation in Tag 095T.
-/

@[expose] public section

universe u
set_option autoImplicit false

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

/-- The geometric part of the original-stalk calculation, with abelian coefficients.
No module resolution, comparison of coefficient categories, or closed fibre is involved.

Source: Stacks Project, Tag 03Q9 and the final stalk calculation of Tag 095T.
(blueprint: lem-weil-pbc-p1-abelian-original-stalk-total-exchange).

Proof:
1. The projective-line projection is qcqs by properness. Its base change to Spec A
is the projective line over A, by ProjectiveSpace.isPullback_map; the same theorem
gives the local square over the local homomorphism φ.
2. Apply exists_addEquiv_strictHenselization_abelian_stalkExchange to these squares.
It identifies the two original stalks with the two closed-B-point stalks of the local
exchange, and carries the original exchange map to that local exchange map.
This is the restriction-complex portion of Tags 03Q9 and 095T.
3. Apply exists_addEquiv_strictLocal_abelian_total_exchange to the local square and G₀.
It identifies these local stalks with the two Ext cohomology groups and the local
exchange with cohomologyMap. Compose the source and target additive equivalences.
For each x, rewrite using the localization equation, then apply the strict-local
cohomology equation at the localized source element. No torsion or closed-fibre
comparison enters this proof, and all original hypotheses remain unchanged.
-/
theorem Etale.projectiveLine_abelian_originalStalk_totalExchange
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
    (G : Sheaf (ProjectiveLine S).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let G₀ := (ProjectiveSpace.map _
      (eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)))^*[
      AddCommGrpCat.{u + 1}].obj G
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let C₁ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((ProjectiveLine S ↘ S)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let C₂ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    ∃ (a₁ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₁ ≃+ Sheaf.H G₀ q)
      (a₂ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₂ ≃+
        Sheaf.H ((ProjectiveSpace.map _ g₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q),
      ∀ x, a₂ ((((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).map e).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ g₀) G₀ q (a₁ x) := by
  let jA := eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)
  let g₀ := Spec.map (CommRingCat.ofHom φ)
  let G₀ := (ProjectiveSpace.map _ jA)^*[AddCommGrpCat.{u + 1}].obj G
  obtain ⟨c₁, c₂, hc⟩ :=
    Etale.exists_addEquiv_strictHenselization_abelian_stalkExchange
      sq σ τ ι hι ν eA eB φ ρA ρB hφ hρA hρB hρ
      (ProjectiveSpace.map _ jA)
      (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
      (ProjectiveSpace.isPullback_map _ jA)
      (ProjectiveSpace.map _ g₀)
      (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B))
      (ProjectiveSpace.isPullback_map _ g₀) G q
  obtain ⟨b₁, b₂, hb⟩ :=
    Etale.exists_addEquiv_strictLocal_abelian_total_exchange φ
      (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
      (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B))
      (ProjectiveSpace.map _ g₀) (ProjectiveSpace.isPullback_map _ g₀) G₀ q
  refine ⟨c₁.trans b₁, c₂.trans b₂, ?_⟩
  intro x
  change b₂ (c₂ _) = Etale.cohomologyMap (ProjectiveSpace.map _ g₀) G₀ q (b₁ (c₁ x))
  rw [hc]
  exact hb (c₁ x)


end AlgebraicGeometry
