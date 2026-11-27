import Langlands.Global.AdelicEisensteinDoubleCosetsProof
import Langlands.Group.RelativeWeylSolomonProof

/-! # Indexing the Bruhat terms of Arthur's constant-term calculation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme AdelicGroupPoints Langlands.GroupScheme.GaloisPointComparison
  Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing
  Langlands.Automorphic.GroupSchemeFunctions

/-- One choice of lift for each Weyl element supplies compatible double-coset
representatives for all pairs of standard parabolics. -/
theorem isDoubleCosetRepresentatives_of_minimal
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {M : CoxeterMatrix (SimpleRoot i ν)} (cs : CoxeterSystem M (relativeWeylGroup i))
    (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (P Q : Finset (SimpleRoot i ν)) (n : relativeWeylGroup i → normalizerPoints i)
    (hn : ∀ w, (QuotientGroup.mk (n w) : relativeWeylGroup i) = w) :
    IsDoubleCosetRepresentatives F (Standard.parabolicHom i ν (rootSet i ν Q))
      (Standard.parabolicHom i ν (rootSet i ν P))
      (fun w : {w : relativeWeylGroup i // IsMinimal cs Q P w} => (n w.val).val) := by
  classical
  obtain ⟨e, he⟩ := (standardParabolicPointsStatement_proof F G hG T i hi ν hν).2.2.2
    (rootSet i ν Q) (rootSet i ν P) (rootSet_subset i ν Q) (rootSet_subset i ν P)
  let I := {w : relativeWeylGroup i // IsMinimal cs Q P w}
  have := hG.finite_relativeWeylGroup i hi
  let WP := standardRelativeWeylGroup i ν (rootSet i ν P)
  let WQ := standardRelativeWeylGroup i ν (rootSet i ν Q)
  let PP := standardParabolicPoints i ν (rootSet i ν P)
  let PQ := standardParabolicPoints i ν (rootSet i ν Q)
  have he' (j : I) :
      e (DoubleCoset.mk WQ WP j.val) = DoubleCoset.mk PQ PP (n j.val).val := by
    conv_lhs => rw [← hn j.val]
    exact he (n j.val)
  have hclass (w v : relativeWeylGroup i) :
      DoubleCoset.mk WQ WP w = DoubleCoset.mk WQ WP v ↔ v ∈ doubleCoset cs Q P w := by
    rw [DoubleCoset.eq]
    change (∃ a ∈ WQ, ∃ b ∈ WP, v = a * w * b) ↔ _
    rw [show WQ = standardSubgroup cs Q from (hcs.2.2.2.2 Q).symm,
      show WP = standardSubgroup cs P from (hcs.2.2.2.2 P).symm]
    rfl
  intro z hz
  obtain ⟨q, rfl⟩ := hz
  obtain ⟨y, rfl⟩ := (rationalCoeffEquiv F G).surjective q
  change ∃! j : I, ∃ x ∈ rationalImage F (Standard.parabolicHom i ν (rootSet i ν Q)),
    ∃ t ∈ rationalImage F (Standard.parabolicHom i ν (rootSet i ν P)),
      principalPoint F G y = x * innerAdelicPoint F G (n j.val).val * t
  have hrep (j : I) :
      (∃ x ∈ rationalImage F (Standard.parabolicHom i ν (rootSet i ν Q)),
        ∃ t ∈ rationalImage F (Standard.parabolicHom i ν (rootSet i ν P)),
          principalPoint F G y = x * innerAdelicPoint F G (n j.val).val * t) ↔
        DoubleCoset.mk PQ PP (n j.val).val = DoubleCoset.mk PQ PP y := by
    rw [DoubleCoset.eq, rationalImage_eq_map_range, rationalImage_eq_map_range,
      (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν Q)).2,
      (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν P)).2,
      ← principalPoint_eq_innerAdelicPoint]
    let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    have hinj : Function.Injective (principalPoint F G) :=
      (rational_injective F G).comp (rationalCoeffEquiv F G).injective
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨t, ht, rfl⟩, hz⟩
      exact ⟨x, hx, t, ht, hinj (by simpa only [map_mul] using hz)⟩
    · rintro ⟨x, hx, t, ht, hz⟩
      refine ⟨_, ⟨x, hx, rfl⟩, _, ⟨t, ht, rfl⟩, ?_⟩
      simp only [hz, map_mul]
  let w := (e.symm (DoubleCoset.mk PQ PP y)).out
  have hw : e (DoubleCoset.mk WQ WP w) = DoubleCoset.mk PQ PP y := by
    rw [DoubleCoset.out_eq', e.apply_symm_apply]
  obtain ⟨v, hv, hvmin⟩ := exists_minimal_in_doubleCoset_unrestricted cs Q P w
  let j : I := ⟨v, hvmin⟩
  refine ⟨j, (hrep j).mpr ?_, ?_⟩
  · rw [← he', ← hw]
    exact congrArg e ((hclass w v).mpr hv).symm
  · intro k hk
    apply Subtype.ext
    have hkClass : DoubleCoset.mk WQ WP w = DoubleCoset.mk WQ WP k.val :=
      e.injective (hw.trans ((he' k).trans ((hrep k).mp hk)).symm)
    exact minimalRepresentativeUnique_proof cs Q P w k.val v
      ((hclass _ _).mp hkClass) hv k.property hvmin

section Coxeter

variable {B W : Type*} [Fintype B] [DecidableEq B] [Group W] {M : CoxeterMatrix B}
  (cs : CoxeterSystem M W)

/-- Holding the left parabolic fixed, the admissible right indices are all
subsets of the positive simple roots at a left-minimal Weyl element. -/
theorem isMinimal_iff_leftMinimal_and_subset {Q P : Finset B} {w : W} :
    IsMinimal cs Q P w ↔ IsMinimal cs Q ∅ w ∧ P ⊆ positiveSimpleSet cs w := by
  rw [minimalityLengthCriterion_proof cs Q P w, minimalityLengthCriterion_proof cs Q ∅ w]
  simp only [Finset.notMem_empty, false_implies, implies_true, and_true]
  exact and_congr_right fun _ => forall₂_congr fun a _ => (mem_positiveSimpleSet cs w a).symm

/-- On the source side, the smaller Levi is the intersection with the
simple reflections conjugated from the fixed parabolic. -/
theorem intersectionSubset_eq_neutral_inter {Q P : Finset B} {w : W}
    (hw : IsMinimal cs Q P w) :
    intersectionSubset cs Q P w =
      P ∩ (positiveSimpleSet cs w ∩ simpleImage cs w⁻¹ Q) := by
  rw [intersectionSubset_eq_simpleImage_inter cs hw]
  have hP := ((isMinimal_iff_leftMinimal_and_subset cs).mp hw).2
  ext a
  simp only [Finset.mem_inter]
  exact ⟨fun h => ⟨h.2, hP h.2, h.1⟩, fun h => ⟨h.2.2, h.1⟩⟩

/-- The second intersection index is determined by the first one and the Weyl element. -/
theorem intersectionSubset_inv_eq_of_image {Q P : Finset B} {w : W}
    (hw : IsMinimal cs Q P w) :
    intersectionSubset cs P Q w⁻¹ = simpleImage cs w (intersectionSubset cs Q P w) ∩ Q := by
  classical
  rw [intersectionSubset_eq_simpleImage_inter cs (isMinimal_inv cs hw), inv_inv,
    intersectionSubset_eq_simpleImage_inter cs hw]
  ext b
  simp only [Finset.mem_inter, simpleImage, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, ha, he⟩, hb⟩
    refine ⟨⟨a, ⟨⟨b, hb, ?_⟩, ha⟩, he⟩, hb⟩
    rw [← he]
    group
  · rintro ⟨⟨a, ⟨_, ha⟩, he⟩, hb⟩
    exact ⟨⟨a, ha, he⟩, hb⟩

end Coxeter

end Langlands.Global.ArthurTruncation.Idempotence
