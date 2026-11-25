/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.AlgebraicGeometry.AbelianExchangeCubeComparisons
import WeilConjectures.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk

/-! # Invertibility of the canonical strict-local stalk comparisons

Source: Stacks Project, Tags 03Q9 and 03QO.
(blueprint: lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-source).
-/

@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme Etale

private theorem isIso_stalk_homology_derivedUpperStar
    {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    {k : Type u} [Field k] [IsSepClosed k] (t : Spec (.of k) ⟶ Z)
    {K L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (m : K ⟶ L) (q : ℤ)
    (hm : IsIso ((pointSmallEtale (t ≫ a)).sheafFiber.map
      ((DerivedCategory.Plus.homologyFunctor _ q).map m))) :
    IsIso ((pointSmallEtale t).sheafFiber.map
      ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((D+((a)^*[AddCommGrpCat.{u + 1}])).map m))) := by
  have h := (NatIso.isIso_map_iff
    (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} a t)
    ((DerivedCategory.Plus.homologyFunctor _ q).map m)).mpr hm
  exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryPlusHomologyFunctorIso
      ((a)^*[AddCommGrpCat.{u + 1}]) q) (pointSmallEtale t).sheafFiber) m).mp h

private theorem isIso_derivedStalkComparison_of_map
    {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    {k : Type u} [Field k] [IsSepClosed k]
    (t : Spec (.of k) ⟶ Z) (s : Spec (.of k) ⟶ Y) (h : t ≫ a = s)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (m : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ L) (q : ℤ)
    (hm : IsIso ((pointSmallEtale t).sheafFiber.map
      ((DerivedCategory.Plus.homologyFunctor _ q).map m))) :
    IsIso (derivedStalkComparison a t s h K L m q) := by
  subst s
  let := hm
  simp only [derivedStalkComparison, Functor.map_comp]
  infer_instance

set_option linter.unusedVariables false in
/-- The fixed source cube restriction map is invertible on the indicated closed-point
stalk. This says nothing about either exchange map or compatibility with exchange.
Source: Stacks Project, Tag 03Q9, theorem-higher-direct-images, and Tag 03QO,
lemma-cohomology-strictly-henselian.
(blueprint: lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-source).

Proof:
1. Enlarge the point fields along ν and ν followed by ι. Étale stalks are unchanged
under extensions of separably closed fields, by the bijection on pointed étale lifts.
2. Exact inverse image commutes with homology. The inverse-image stalk comparisons
for g and g₀ and the equation hρ identify the two outer stalks with those at σ and
at ρA followed by the residue closed point of Spec A, respectively.
3. Apply unrestricted 03Q9 to f at νισ. Transport its chosen cartesian model to X₀
along sq₀ and eA; the inverse-image/single-complex isomorphism identifies its coefficient
with p₀^*G. No target comparison or invertibility of an exchange map for g is used.
4. Use exact global sections on the strict local base and the sections-to-closed-point
stalk isomorphism (03QO) to express this restriction on higher-direct-image stalks.
The residue equations identify the specified geometric points. The inverse-image germ
formula and the section-restriction components of 03Q9 identify the composite with the
fixed derivedStalkComparison in the conclusion; all remaining factors are images of
composition, single-complex, or exact-pullback isomorphisms. Hence it is invertible.
For q = 0 this is the usual section restriction; the argument also handles zero sheaves,
empty total spaces, and arbitrary chosen cartesian models. -/
theorem Etale.isIso_strictHenselization_exchangeCube_stalkComparisons_source
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
      (exchangeCubeSourceComparison sq₀.toCommSq h G) (q : ℤ)) := by
  dsimp only
  apply isIso_derivedStalkComparison_of_map
  let t := ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
  let g₀ := Spec.map (CommRingCat.ofHom φ)
  have ht : t ≫ g₀ =
      (ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ))) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
    dsimp only [t, g₀]
    rw [Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
  have hm := isIso_strictHenselization_baseChange_closedStalk f (ν ≫ ι ≫ σ)
    eA p₀ f₀ sq₀
    (ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ))) G q
  rw [← ht] at hm
  have hm' := isIso_stalk_homology_derivedUpperStar g₀ t
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) (q : ℤ) hm
  let := hm'
  simp only [exchangeCubeSourceComparison, Functor.map_comp]
  infer_instance

end AlgebraicGeometry
