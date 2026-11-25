/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.AlgebraicGeometry.AbelianExchangeCubeComparisons
import WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExchangeCubeSourceStalkIso
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso

/-! # Invertibility of the canonical strict-local stalk comparisons

Source: Stacks Project, Tags 03Q9 and 03QO.
(blueprint: lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos).
-/

@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme Etale

/-- The two fixed cube restriction maps are invertible on the indicated closed-point
stalks. This says nothing about either exchange map or compatibility with exchange.
Source: Stacks Project, Tag 03Q9, theorem-higher-direct-images, and Tag 03QO,
lemma-cohomology-strictly-henselian.
(blueprint: lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos).

Proof:
1. Extend the point fields along ν and ν followed by ι. Precomposition is bijective
on pointed étale lifts because the fibres over separably closed fields are disjoint
unions of copies of the base field. These induce natural stalk isomorphisms.
2. Commute homology with the exact pullbacks g and g₀ and use the inverse-image
stalk isomorphisms. The source comparison then becomes the strict-local restriction
for f at νισ, followed by the pullback-single-complex identification. Apply unrestricted
03Q9, transporting its chosen pullback across sq₀ and eA.
3. Apply the same unrestricted theorem to f' at ντ and the coefficient g'^*G.
Cartesianness implies f' is qcqs. Transport the chosen pullback across sqB and eB;
hb and inverse-image composition identify its coefficients with p₁^*p₀^*G.
4. On either strict local base, global sections coincide naturally with the closed
point stalk, and are exact by 03QO. Hence the Leray homology comparisons in 03Q9
identify total-space cohomology with the local higher-direct-image stalks. Locality of
φ, hρ, hρA, and hρB identify the closed points and their reparametrizations. The two
morphisms in the conclusion are precisely these composites: this follows by the germ
formula for inverse-image stalks and the section-restriction formula in 03Q9. Thus
each is a composite of isomorphisms. This handles q = 0, empty total spaces, zero
sheaves, inseparable point-field extensions and nonstandard pullback models. -/
theorem Etale.isIso_strictHenselization_exchangeCube_stalkComparisons
    {S T X X' : Scheme.{u}} {g : T ⟶ S} {f : X ⟶ S}
    [QuasiCompact f] [QuasiSeparated f] {f' : X' ⟶ T} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
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
    {X₀ X₁ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f
      (eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)))
    (p₁ : X₁ ⟶ X₀) (f₁ : X₁ ⟶ Spec (.of B))
    (sq₁ : IsPullback p₁ f₁ f₀ (Spec.map (CommRingCat.ofHom φ)))
    (b : X₁ ⟶ X')
    (sqB : IsPullback b f₁ f'
      (eB.hom ≫ strictLocalizationToBase (ν ≫ τ)))
    (hb : b ≫ g' = p₁ ≫ p₀)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let jA := eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)
    let jB := eB.hom ≫ strictLocalizationToBase (ν ≫ τ)
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let t := ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
    let ht : t ≫ jB = τ := by simpa only [t, jB, Category.assoc] using hρB
    let h : jB ≫ g = g₀ ≫ jA := by simpa only [jB, g₀, jA, Category.assoc] using hφ.symm
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    let M₁ := (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g)^*[AddCommGrpCat.{u + 1}])).obj K
    let M₂ := (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f')_*[AddCommGrpCat.{u + 1}])).obj K
    let N₁ := (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀
    let N₂ := (D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀
    IsIso (derivedStalkComparison jB t τ ht M₁ N₁
      (exchangeCubeSourceComparison sq₀.toCommSq h G) (q : ℤ)) ∧
    IsIso (derivedStalkComparison jB t τ ht M₂ N₂
      (exchangeCubeTargetComparison sqB.toCommSq hb G) (q : ℤ)) := by
  constructor
  · exact Etale.isIso_strictHenselization_exchangeCube_source_stalkComparison
      sq σ τ ι hι ν eA eB φ ρA ρB hφ hρA hρB hρ p₀ f₀ sq₀ p₁ f₁ sq₁ b sqB hb G q
  · exact Etale.isIso_strictHenselization_exchangeCube_target_stalkComparison
      sq σ τ ι hι ν eA eB φ ρA ρB hφ hρA hρB hρ p₀ f₀ sq₀ p₁ f₁ sq₁ b sqB hb G q

end AlgebraicGeometry
