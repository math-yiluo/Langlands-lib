import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismSplittingGeometry
import Langlands.GroupScheme.Reductive.AffinePinnedFixedExistence
import Langlands.GroupScheme.Reductive.AffinePinnedLocalAlignment

/-! # Full character-lattice labels for pinned comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.AffinePinnedModel

/-- A label remembers the whole character-lattice map. The based root-datum
and standard-pairing witnesses are propositions and do not affect equality. -/
def ComparisonLabel (M N : AffinePinnedModel.{u}) : Type u :=
  { w : (N.coordinates → ℤ) ≃ₗ[ℤ] (M.coordinates → ℤ) //
    ∃ θ : RootPairing.Equiv N.rootDatum M.rootDatum,
      θ.weightEquiv = w ∧
      (∀ s, s ∈ N.basis.support ↔ θ.indexEquiv s ∈ M.basis.support) ∧
      (∀ m n, M.rootDatum.toLinearMap m n = ∑ i, m i * n i) ∧
      (∀ m n, N.rootDatum.toLinearMap m n = ∑ i, m i * n i) }

namespace ComparisonLabel

variable {M N : AffinePinnedModel.{u}} (d : ComparisonLabel M N)

/-- Choose a based full root-datum witness for a label. -/
def rootEquiv : RootPairing.Equiv N.rootDatum M.rootDatum := d.property.choose

theorem rootEquiv_weightEquiv : d.rootEquiv.weightEquiv = d.val :=
  d.property.choose_spec.1

theorem simple_iff (s : N.rootIndex) :
    s ∈ N.basis.support ↔ d.rootEquiv.indexEquiv s ∈ M.basis.support :=
  d.property.choose_spec.2.1 s

include d in
theorem sourcePairing (m n : M.coordinates → ℤ) :
    M.rootDatum.toLinearMap m n = ∑ i, m i * n i :=
  d.property.choose_spec.2.2.1 m n

include d in
theorem targetPairing (m n : N.coordinates → ℤ) :
    N.rootDatum.toLinearMap m n = ∑ i, m i * n i :=
  d.property.choose_spec.2.2.2 m n

variable {T W : Scheme.{u}}

/-- The canonical actual pinned comparison selected by the full lattice label. -/
def representative (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) : Comparison f g :=
  (fixedComparison d.rootEquiv d.simple_iff hAffine f g).val

theorem representative_fixedTorus
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) :
    PreservesFixedTorus d.rootEquiv (d.representative hAffine f g) :=
  (fixedComparison d.rootEquiv d.simple_iff hAffine f g).property.1

theorem representative_fixedPinning
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) :
    PreservesFixedPinning d.rootEquiv d.simple_iff (d.representative hAffine f g) :=
  (fixedComparison d.rootEquiv d.simple_iff hAffine f g).property.2

/-- Canonical representatives have the concrete local pinning predicate. -/
theorem representative_isLocallyPinned
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) :
    IsLocallyPinned (d.representative hAffine f g) := by
  let a : BasedCoordinateIso (M.inclusionOver f) (N.inclusionOver g)
      M.rootDatum N.rootDatum M.basis N.basis := {
    groupIso := d.representative hAffine f g
    torusIso := fixedTorusIso d.rootEquiv T
    rootEquiv := d.rootEquiv
    sourcePairing := d.sourcePairing
    targetPairing := d.targetPairing
    simple_iff := d.simple_iff
    square := d.representative_fixedTorus hAffine f g
    characters := fixedTorusIso_characters d.rootEquiv T
  }
  exact ⟨(d.representative_fixedTorus hAffine f g).preservesTorus d.rootEquiv,
    a.cocharacter_comp,
    (d.representative_fixedPinning hAffine f g).preservesLocalPinning
      d.rootEquiv d.simple_iff⟩

/-- Representatives commute with arbitrary common-base pullback. -/
theorem representative_pull
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (q : W ⟶ T) :
    pullComparison (d.representative hAffine f g) q =
      d.representative hAffine (q ≫ f) (q ≫ g) :=
  fixedComparison_pull d.rootEquiv d.simple_iff hAffine f g q

end ComparisonLabel

variable {M N : AffinePinnedModel.{u}} {T : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- Two full weight maps giving the same monomial on every test over a field
are equal, including on the central character directions. -/
theorem weightEquiv_eq_of_field_characters (k : Type u) [Field k]
    (w v : (N.coordinates → ℤ) ≃ₗ[ℤ] (M.coordinates → ℤ))
    (h : ∀ (U : Over (Spec (CommRingCat.of k)))
      (x : U ⟶ (splitTorus (Spec (CommRingCat.of k)) M.coordinates).X)
      (m : N.coordinates → ℤ),
      ∏ i, splitTorus.pointsEquiv M.coordinates U x i ^ w m i =
        ∏ i, splitTorus.pointsEquiv M.coordinates U x i ^ v m i) : w = v := by
  apply LinearEquiv.ext
  intro m
  apply (splitTorus.characterLatticeEquiv k M.coordinates).symm.injective
  rw [← splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
    ← splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
  apply Additive.toMul.injective
  apply hom_ext_points
  intro U x
  apply (Gm.pointsEquiv (Spec (CommRingCat.of k)) U).injective
  change Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom
      (splitTorus.exponentCharacter _ M.coordinates (w m))).hom.hom) =
    Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom
      (splitTorus.exponentCharacter _ M.coordinates (v m))).hom.hom)
  simpa only [splitTorus.pointsEquiv_exponentCharacter] using h U x m

namespace ComparisonLabel

/-- At every point of the common base, equality of representatives forces
equality of the entire lattice labels. No global connectedness is required. -/
theorem eq_of_representative_eq (d c : ComparisonLabel M N)
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (x : T)
    (h : d.representative hAffine f g = c.representative hAffine f g) : d = c := by
  let q := T.fromSpecResidueField x
  have he : d.representative hAffine (q ≫ f) (q ≫ g) =
      c.representative hAffine (q ≫ f) (q ≫ g) := by
    rw [← d.representative_pull hAffine f g q,
      ← c.representative_pull hAffine f g q, h]
  have hd := d.representative_fixedTorus hAffine (q ≫ f) (q ≫ g)
  have hc := c.representative_fixedTorus hAffine (q ≫ f) (q ≫ g)
  rw [he] at hd
  have hs := hd.symm.trans hc
  let : Mono (N.inclusionOver (q ≫ g)).hom.hom := N.inclusionOver_mono (q ≫ g)
  have ht : (fixedTorusIso d.rootEquiv (Spec (T.residueField x))).hom.hom.hom =
      (fixedTorusIso c.rootEquiv (Spec (T.residueField x))).hom.hom.hom := by
    apply (cancel_mono (N.inclusionOver (q ≫ g)).hom.hom).mp
    exact congrArg (fun a => a.hom.hom) hs
  change (fixedTorusIso d.rootEquiv
      (Spec (CommRingCat.of (T.residueField x)))).hom.hom.hom =
    (fixedTorusIso c.rootEquiv
      (Spec (CommRingCat.of (T.residueField x)))).hom.hom.hom at ht
  apply Subtype.ext
  apply weightEquiv_eq_of_field_characters (T.residueField x)
  intro U t m
  have hd' := fixedTorusIso_characters d.rootEquiv _ U t m
  have hc' := fixedTorusIso_characters c.rootEquiv _ U t m
  rw [ht] at hd'
  have hdw := d.rootEquiv_weightEquiv
  have hcw := c.rootEquiv_weightEquiv
  simpa only [← RootPairing.Equiv.weightEquiv_apply, hdw, hcw] using hd'.symm.trans hc'

end ComparisonLabel

end Langlands.GroupScheme.AffinePinnedModel
