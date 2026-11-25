/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality

/-! # Raw derived Hom equals restricted single-complex cohomology

Source: Stacks Project, Tag 03Q8 and its cited restriction lemmas.
(blueprint: lem-sbc-raw-restricted-cohomology-natural-iso).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Raw derived Hom is naturally isomorphic to cohomology on the restricted etale
scheme, for every structure morphism and coefficient sheaf.
Source: Stacks Project, Tag 03Q8; Cohomology on Sites, the restriction arguments
in Tags 072W and 0BKV (Lemmas 21.7.4 and 21.20.3).
(blueprint: lem-sbc-raw-restricted-cohomology-natural-iso).

Proof: For each h and U, the inverse image of the free abelian represented sheaf
is the free sheaf of the etale Y-scheme U times_S Y. The free-sheaf sections
adjunction followed by the exact extension-by-zero/restriction adjunction
identifies Hom from this sheaf with sections of the restriction to that scheme.
Restriction preserves injectives since extension by zero is exact: on geometric
stalks it is a direct sum of abelian groups. Apply the adjunction to a bounded-below
injective resolution of F. Hom from a degree-zero free sheaf to the shifted
resolution computes its restricted cohomology. The fully faithful inclusion of
D+ into D identifies this with cohomology of Q of the single complex. All steps
are additive and give e. For a triangle a followed by h equals h', identify its
restriction map by the two pullback projections. Inverse-image composition gives
exactly rawAffineRestrictedCoefficient. Naturality of the adjunction unit, the
single-functor comparison, and the shift comparison identifies the raw pullback
with homology of the derived adjunction unit followed by the coefficient map,
which is rawAffineRestrictedCohomologyMap. The triangle identities cancel the
adjunction counits, proving the displayed equation. No qcqs, affinity, limit or
continuity hypothesis is used. -/
theorem exists_raw_restricted_cohomology_natural_iso (S : Scheme.{v}) (p : ℕ)
    (U : S.Etale) :
    ∃ e : ∀ {Y : Scheme.{v}} (h : Y ⟶ S)
      (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}),
      (abelianHigherDirectImageRawPresheaf h p F).obj (op U) ≅
        rawAffineRestrictedCohomology h p F U,
      ∀ {Y Y' : Scheme.{v}} (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S)
        (w : a ≫ h = h')
        (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
        (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
        (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F')
        (t : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)),
        rawAffineRestrictedCohomologyMap a h h' w p F F' φ U ((e h F).hom t) =
          (e h' F').hom (abelianHigherDirectImageRawPullback a h h' w p F F' φ U t) := by
  have hi {Y : Scheme.{v}} (h : Y ⟶ S)
      (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
      IsIso (rawRestrictedCohomologyComparison h p F U) :=
    isIso_rawRestrictedCohomologyComparison h p F U
  refine ⟨fun h F ↦ asIso (rawRestrictedCohomologyComparison h p F U), ?_⟩
  intro Y Y' a h h' w F F' φ t
  exact rawRestrictedCohomologyComparison_naturality a h h' w p F F' φ U t

end AlgebraicGeometry.Etale
