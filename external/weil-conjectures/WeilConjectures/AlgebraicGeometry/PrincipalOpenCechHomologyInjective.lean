/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechInjectiveComparison
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechInjectiveTerms

/-! # injective on cohomology for the principal-open Čech augmentation

Source: Stacks Project, Cohomology, Tag 08C1, finite augmented Čech argument.
(blueprint: lem-sc-principal-open-cech-homology-injective).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The principal-open section-to-total augmentation is injective on cohomology.
The source and target are specified by degree isomorphisms and the actual differential
and augmentation formulas; no choice of unspecified Čech data occurs.

Source: Stacks Project, Cohomology, Tag 08C1 (lemma-alternating-cech-complex-complex).
(blueprint: lem-sc-principal-open-cech-homology-injective).

Proof: Take a functorial K-injective resolution I of J with injective terms.
The comparison J → I is a homotopy equivalence, since both complexes are K-injective.
Sections carry its homotopies to homotopies, so the section comparison is a
quasi-isomorphism. The coefficient comparison also gives a chain map on the
displayed subset total: restriction naturality and the signed differential
verify its chain-map equation. The augmentation commutes with these comparisons
by its singleton restriction formula and its zero formula on larger subsets.
For I, each augmented section row is exact: the sheaf axiom gives exactness and
injectivity at the section term, and injective Čech acyclicity gives positive-degree
exactness. Restriction to increasing tuples identifies these rows with the subset
rows, since each subset has a unique increasing enumeration and the deletion signs
are the corresponding positions. Only columns -1 through r-1 can occur.
Suppose a closed section maps to the differential of a total cochain. At the
highest Čech-degree component of that cochain, the equation says its horizontal
differential vanishes. Row exactness supplies a horizontal preimage. Subtract the
total differential of that preimage from the cochain without changing its total
differential. Repeat down through the finitely many columns. At degree zero, row
exactness identifies the resulting cochain with an augmented section. The original
closed section is its vertical differential because the row augmentation is
injective. Hence a section class whose image vanishes was already zero.
Apply homology to the comparison square. The section comparison is invertible
on homology, so its composite with the injective-term augmentation is monic.
The other composite is the original augmentation followed by the total comparison;
monicity of this composite implies monicity of the original augmentation.
For r=0 the union is empty; sections and the total are zero, so the assertion holds.
Repeated or empty principal opens do not affect row exactness or the argument. -/
theorem principalOpenCech_homology_injective
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) [J.IsKInjective] :
    let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (K T : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ : ∀ n : ℤ, K.X n ≅ (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V))
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (α : K ⟶ T)
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ)),
      (∀ (n : ℤ) (s : K.X n),
        (σ (n + 1)).hom (K.d n (n + 1) s) =
          (modulesSpecToSheaf.map (J.d n (n + 1))).hom.app (op V) ((σ n).hom s)) →
      (∀ (n : ℤ) (s : T.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ (n + 1)).hom (T.d n (n + 1) s) S =
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (J.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) ((τ n).hom s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) ((τ n).hom s ⟨S.val.erase j.val, h⟩))
          else 0) →
      (∀ (n : ℤ) (s : K.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ n).hom (α.f n s) S = if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
              (op V) ((σ n).hom s)) else 0) →
      ∀ n : ℤ, Mono (HomologicalComplex.homologyMap α n) := by
  dsimp only
  intro K T σ τ α hle hls he hes hK hT hα n
  obtain ⟨I, K₁, T₁, σ₁, τ₁, α₁, a, b, hI, hK₁, hT₁, hα₁, ha, hsquare⟩ :=
    principalOpenCech_injective_comparison A r f J K T σ τ α hle hls he hes hK hT hα
  let : QuasiIso a := ha
  let : Mono (HomologicalComplex.homologyMap α₁ n) :=
    principalOpenCech_homology_mono_of_injective_terms A r f I hI K₁ T₁ σ₁ τ₁ α₁
      hle hls he hes hK₁ hT₁ hα₁ n
  have hH : HomologicalComplex.homologyMap α n ≫ HomologicalComplex.homologyMap b n =
      HomologicalComplex.homologyMap a n ≫ HomologicalComplex.homologyMap α₁ n := by
    rw [← HomologicalComplex.homologyMap_comp, hsquare, HomologicalComplex.homologyMap_comp]
  exact mono_of_mono_fac hH

end AlgebraicGeometry
