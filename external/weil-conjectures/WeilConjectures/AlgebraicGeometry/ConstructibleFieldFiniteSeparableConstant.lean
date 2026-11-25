/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstantDatum
import WeilConjectures.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstantCore

/-!
# Constructible sheaves over a field become constant after finite separable extension

Source: Stacks Project, proof of Lemma 09Z6, lines 12969--12971, and
Definition 03RU (blueprint: lem-weil-pbc-constructible-field-finite-separable-constant).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry

/-- A constructible sheaf of modules on the spectrum of a field becomes constant after
finite separable extension.

Source: Stacks Project, proof of Lemma 09Z6 (lemma-constructible-maps-into-constant),
Definition 03RU (definition-finite-locally-constant), and Morphisms Lemma 02GL
(lemma-etale-over-field)
(blueprint: lem-weil-pbc-constructible-field-finite-separable-constant).

Proof, following the node's seven steps:
1. Choose the constructible stratification from `def-weil-pbc-etale-constructible-sheaf`
   and `definition-constructible-sheaves--2`. The spectrum of a field has one point
   (`def-weil-affine-spectrum`), so exactly one stratum is nonempty. Its immersion
   has full image; its pullback admits an etale cover with finite constant module values.
2. The stratum immersion is a closed immersion by
   `lem-weil-pbc-immersion-closed-image-closed-immersion`. By `def-weil-closed-immersion`
   its source is Spec(k/I); nonemptiness excludes I = k, so I = 0 and it is an isomorphism.
3. Choose a point of a nonempty covering member and an affine neighborhood Spec(B)
   (`lem-weil-pbc-affine-open-spec-points`). Its composite to Spec(k) is etale by
   `definition-torsion-sheaves--3`. The point's residue field K is finite
   separable over the residue field of Spec(k)
   (`lem-weil-pbc-etale-algebra-residue-field-separable`), identified with k by
   `lem-weil-pbc-spec-field-point-residue-field`.
4. The canonical map Spec(K) to Spec(B), followed by the affine neighborhood immersion,
   gives a map j to the covering member. Functoriality of Spec
   (`def-weil-affine-spectrum`) identifies its composite to Spec(k) with pi.
5. Identify restriction on the covering member with inverse image by
   `lem-weil-pbc-etale-inverse-image-restriction`. This identification is Lambda-linear:
   its adjoint is the linear restriction map, using
   `situation-conventions` and
   `situation-conventions`. Compose with the chosen trivialization.
6. Compose inverse images along the stratum immersion, cover map and j using
   `lem-weil-pbc-inverse-image-composition`. The comparison maps are Lambda-linear
   by their adjoint characterization and `situation-conventions`;
   inverse image preserves linear maps by `situation-conventions`.
7. Pull back the trivialization along j. The inverse image of its constant sheaf is
   constant by `lemma-constructible-pullback-constant` and uniqueness of left adjoints
   (`situation-conventions`). With M the finite module of step 1,
   compose this isomorphism with the inverse of step 6's comparison to obtain the claimed
   isomorphism to the constant sheaf (`def-weil-pbc-constant-sheaf`). -/
theorem constructible_field_finite_separable_constant
    (k : Type u) [Field k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (G : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (hG : Scheme.IsConstructibleEtaleModuleSheaf G) :
    ∃ (K : Type u), ∃ (_ : Field K), ∃ (_ : Algebra k K),
      FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ (M : ModuleCat.{u + 1} Λ), Finite M ∧
        Nonempty
          ((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
            (constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj M) := by
  obtain ⟨d, hd⟩ := constructible_field_finite_separable_constant_datum k Λ G hG
  exact constructible_field_finite_separable_constant_of_datum k Λ G d hd

end AlgebraicGeometry
