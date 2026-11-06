import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteDomainIdealDescent
import Langlands.Geometry.Analytic.StrictTestDomain.FiniteIndexRationalGluing
import Langlands.Geometry.Analytic.StrictTestDomain.QuotientTests
import Langlands.Geometry.Analytic.StrictTestDomain.ScalarCoverDescent

/-! # Closed ideals on actual strict rational covering families -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P Q : PresentedStrictAffinoidAlgebra K}

/-- Compatibility of ideals in the two actual rational intersection algebras. -/
def CompatibleIdealSections {ι : Type v} (D : ι → RationalData K P)
    (I : ∀ i, Ideal (D i).algebra) : Prop :=
  ∀ i j, (interLeft (D i) (D j)).restriction.closedIdealMap (I i) =
    (interRight (D i) (D j)).restriction.closedIdealMap (I j)

/-- The explicit ideal of base elements lying in every prescribed local ideal. -/
def idealSectionContraction {ι : Type v} (D : ι → RationalData K P)
    (I : ∀ i, Ideal (D i).algebra) : Ideal P :=
  ⨅ i, Ideal.comap (D i).baseMap.toAlgHom.toRingHom (I i)

@[simp]
theorem mem_idealSectionContraction {ι : Type v} (D : ι → RationalData K P)
    (I : ∀ i, Ideal (D i).algebra) (a : P) :
    a ∈ idealSectionContraction D I ↔ ∀ i, (D i).baseMap a ∈ I i :=
  Ideal.mem_iInf

/-- A rational family detects membership in each closedly extended global ideal. -/
def IdealCoverSeparated {ι : Type v} (D : ι → RationalData K P) : Prop :=
  ∀ (J : Ideal P) (a : P),
    (∀ i, (D i).baseMap a ∈ (D i).baseMap.closedIdealMap J) → a ∈ J

/-- Every compatible local ideal family is recovered by closed extension of
its explicit global contraction. -/
def IdealCoverDescent {ι : Type v} (D : ι → RationalData K P) : Prop :=
  ∀ I : ∀ i, Ideal (D i).algebra, CompatibleIdealSections D I →
    ∀ i, (D i).baseMap.closedIdealMap (idealSectionContraction D I) = I i

/-- Compatibility persists after any common bounded affinoid test over the
base, by factorization through the actual rational intersection. -/
theorem compatible_ideals_apply {d e : RationalData K P}
    (I : Ideal d.algebra) (J : Ideal e.algebra)
    (hIJ : (interLeft d e).restriction.closedIdealMap I =
      (interRight d e).restriction.closedIdealMap J)
    (a : BoundedAlgHom K d.algebra Q) (b : BoundedAlgHom K e.algebra Q)
    (hab : a.comp d.baseMap = b.comp e.baseMap) :
    a.closedIdealMap I = b.closedIdealMap J := by
  have hi : HasImageIn K (a.comp d.baseMap) (d.inter e).locus := by
    intro x
    rw [locus_inter]
    refine ⟨hasImageIn_comp_rational_baseMap d a x, ?_⟩
    rw [hab]
    exact hasImageIn_comp_rational_baseMap e b x
  obtain ⟨c, hc, _⟩ := (rationalRepresentation K P (d.inter e)).2.2 Q
    (a.comp d.baseMap) hi
  have ha : c.comp (interLeft d e).restriction = a := by
    apply d.hom_ext
    rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap, hc]
  have hb : c.comp (interRight d e).restriction = b := by
    apply e.hom_ext
    rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap, hc, hab]
  rw [← ha, ← hb, ← BoundedAlgHom.closedIdealMap_comp,
    ← BoundedAlgHom.closedIdealMap_comp, hIJ]

namespace CompatibleIdealSections

/-- The closed extensions of any global ideal satisfy pairwise compatibility. -/
theorem of_base {ι : Type v} (D : ι → RationalData K P) (J : Ideal P) :
    CompatibleIdealSections D (fun i => (D i).baseMap.closedIdealMap J) := by
  intro i j
  rw [BoundedAlgHom.closedIdealMap_comp, BoundedAlgHom.closedIdealMap_comp,
    (interLeft (D i) (D j)).restriction_comp_baseMap,
    (interRight (D i) (D j)).restriction_comp_baseMap]

/-- Closed ideal extension along the actual coefficient comparisons preserves
all actual ordered-pair compatibility equations. -/
theorem comparison {ι : Type v} {D : ι → RationalData K P}
    {I : ∀ i, Ideal (D i).algebra} (hI : CompatibleIdealSections D I)
    (φ : BoundedAlgHom K P Q) :
    CompatibleIdealSections (fun i => (D i).pullback φ)
      (fun i => ((D i).comparison φ).closedIdealMap (I i)) := by
  intro i j
  rw [BoundedAlgHom.closedIdealMap_comp, BoundedAlgHom.closedIdealMap_comp,
    ← intersectionComparison_comp_left, ← intersectionComparison_comp_right,
    ← BoundedAlgHom.closedIdealMap_comp, ← BoundedAlgHom.closedIdealMap_comp, hI i j]

end CompatibleIdealSections

/-- Scalar separation on an actual closed quotient proves ideal membership
locality for every finite rational point cover. -/
theorem idealCoverSeparated_of_covers (hK : ∃ c : K, 1 < ‖c‖)
    {ι : Type v} [Finite ι] (D : ι → RationalData K P)
    (hD : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus) :
    IdealCoverSeparated D := by
  intro J a ha
  have hJ := PresentedStrictAffinoidAlgebra.isClosed_ideal hK P J
  let q := PresentedStrictAffinoidAlgebra.quotientMap K P J hJ
  have hcov : ∀ x : BanachSpectrum (P.quotient K J hJ),
      ∃ i, x ∈ ((D i).pullback q).locus :=
    fun x => hD (BanachSpectrum.comap q.toBoundedRingHom x)
  have hscalar : ScalarCoverDescent (fun i => (D i).pullback q) :=
    fun s hs => wholeSpectrumRationalGluing_finiteIndex K (P.quotient K J hJ) ι
      (fun i => (D i).pullback q) hcov s hs
  apply (PresentedStrictAffinoidAlgebra.quotientMap_eq_zero_iff P J hJ a).mp
  apply hscalar.separated
  intro i
  let g := (D i).comparison q
  have hgclosed : IsClosed (RingHom.ker g.toAlgHom.toRingHom : Set (D i).algebra) :=
    isClosed_eq g.continuous continuous_const
  have hkill : (D i).baseMap.closedIdealMap J ≤ RingHom.ker g.toAlgHom.toRingHom := by
    apply ((D i).baseMap.closedIdealMap_le_iff _ _ hgclosed).mpr
    intro b hb
    change g ((D i).baseMap b) = 0
    have h := congrArg (fun f : BoundedAlgHom K P ((D i).pullback q).algebra => f b)
      ((D i).comparison_comp_baseMap q)
    exact h.trans (by
      change ((D i).pullback q).baseMap (q b) = 0
      rw [(PresentedStrictAffinoidAlgebra.quotientMap_eq_zero_iff P J hJ b).mpr hb,
        map_zero])
  have h := congrArg (fun f : BoundedAlgHom K P ((D i).pullback q).algebra => f a)
    ((D i).comparison_comp_baseMap q)
  rw [map_zero]
  exact h.symm.trans (hkill (ha i))

namespace IdealCoverSeparated

/-- Equality of all closed extensions detects equality of two global ideals. -/
theorem eq_of_extensions {ι : Type v} {D : ι → RationalData K P}
    (hD : IdealCoverSeparated D) {J H : Ideal P}
    (h : ∀ i, (D i).baseMap.closedIdealMap J = (D i).baseMap.closedIdealMap H) : J = H := by
  apply le_antisymm
  · intro a ha
    apply hD H a
    intro i
    rw [← h i]
    exact (D i).baseMap.mem_closedIdealMap ha
  · intro a ha
    apply hD J a
    intro i
    rw [h i]
    exact (D i).baseMap.mem_closedIdealMap ha

end IdealCoverSeparated

end Langlands.Analytic.StrictTestDomain
