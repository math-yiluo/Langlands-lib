/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetComparison
import WeilConjectures.AlgebraicGeometry.KInjectiveAlternatingCechAugmentationQuasiIso
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # surjective on cohomology for the principal-open Čech augmentation

Source: Stacks Project, Cohomology, Tag 08C1, finite augmented Čech argument.
(blueprint: lem-sc-principal-open-cech-homology-surjective).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The principal-open section-to-total augmentation is surjective on cohomology.
The source and target are specified by degree isomorphisms and the actual differential
and augmentation formulas; no choice of unspecified Čech data occurs.

Source: Stacks Project, Cohomology, Tag 08C1 (lemma-alternating-cech-complex-complex).
(blueprint: lem-sc-principal-open-cech-homology-surjective).

Proof: Restrict J to the open union V. Open restriction preserves K-injectivity,
and the equivalence from modules on the over-site to modules on the open scheme
preserves it as well. The pulled-back principal opens cover V. The existing
K-injective alternating Čech augmentation theorem therefore applies on V.
The subset comparison identifies the displayed alpha, after forgetting its A-action,
with that augmentation after forgetting its O(V)-action. The comparison is an arrow
isomorphism: its source identifies sections over V, and its target groups subset
coordinates by cardinality and uses their unique increasing enumerations.
Forgetting module scalar actions preserves and reflects quasi-isomorphisms.
Transport the quasi-isomorphism through the arrow isomorphism and reflect it back
to A-modules. Its homology maps are isomorphisms, hence epimorphisms.
No boundedness, quasi-coherence, or termwise injectivity is imposed on J.
For the empty family, V is empty; the same open-cover theorem and comparison apply. -/
theorem principalOpenCech_homology_surjective
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
      ∀ n : ℤ, Epi (HomologicalComplex.homologyMap α n) := by
  intro V D K T σ τ α hle hls he hes hK hT hα n
  let X := Spec (.of A)
  let Y := V.toScheme
  let R₀ := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
  let E := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (D := SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (Scheme.Modules.overEquiv V)
  have : R₀.Additive := Functor.additive_of_preserves_binary_products R₀
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  let R := R₀ ⋙ E
  let Jr := (R₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  let J' := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  have : CochainComplex.IsKInjective Jr := kInjective_of_restrict_open X.toRingedSpace V J
  have : CochainComplex.IsKInjective J' := by
    change CochainComplex.IsKInjective
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Jr)
    infer_instance
  let U : Fin r → Y.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
  have hU : iSup U = ⊤ := by
    rw [show iSup U = V.ι ⁻¹ᵁ V from (V.ι.preimage_iSup _).symm]
    exact V.ι_preimage_self
  have hβ : QuasiIso ((alternatingCechAugmentation U).app J') :=
    kInjective_alternatingCech_augmentation_quasiIso Y r U hU J'
  let F := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let G := forget₂
    (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  obtain ⟨e⟩ := principalOpenCech_subset_comparison A r f J
    K T σ τ α hle hls he hes hK hT hα
  have hFα : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) := by
    apply (quasiIso_iff_of_arrow_mk_iso _ _ e).mpr
    change QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((alternatingCechAugmentation U).app J'))
    infer_instance
  have : QuasiIso α :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology α F).mp hFα
  infer_instance

end AlgebraicGeometry
