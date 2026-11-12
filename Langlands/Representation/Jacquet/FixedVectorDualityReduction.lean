import Langlands.Representation.Jacquet.FixedVectorSmallProgenerator
import Langlands.Representation.Category.ContragredientAdjunction
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof

/-! # Fixed-vector generation and smooth duality from a splitting -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe uG uV uW

namespace Langlands.Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : OpenSubgroup G)

/-- Every smooth representation is the sum of a fixed-vector-generated subrepresentation
and a subrepresentation with no fixed vectors. This is an input, not an existence theorem. -/
def fixedVectorSplitting : Prop :=
  ∀ A : SmoothRep.{0,uG,uV} ℂ G,
    ∃ S T : Subrepresentation A.representation,
      fixedVectorGenerated K.toSubgroup (SmoothRep.subrepresentation A S) ∧
      fixedVectors (SmoothRep.subrepresentation A T).representation K.toSubgroup = ⊥ ∧
      S ⊔ T = ⊤

/-- Compact-open fixed duality carries vanishing of fixed vectors to the smooth dual. -/
theorem fixedVectors_contragredient_eq_bot (hK : IsCompact (K : Set G))
    (A : SmoothRep.{0,uG,uV} ℂ G)
    (hA : fixedVectors A.representation K.toSubgroup = ⊥) :
    fixedVectors A.contragredient.representation K.toSubgroup = ⊥ := by
  apply le_antisymm _ bot_le
  intro ℓ hℓ
  change ℓ = 0
  let l : fixedVectors A.contragredient.representation K.toSubgroup := ⟨ℓ, hℓ⟩
  have hl : l = 0 := by
    apply (smoothDualFixedRestriction_bijective A.representation A.isSmooth K hK).1
    ext v
    have hv : v.val = 0 := by
      exact hA.le v.property
    change ℓ.val v.val = 0
    rw [hv, map_zero]
  exact congrArg Subtype.val hl

/-- There are no nonzero maps from an object without fixed vectors to the smooth dual
of a fixed-vector-generated representation. The source and target carrier universes are independent. -/
theorem hom_contragredient_eq_zero_of_fixedVectors_eq_bot
    (hK : IsCompact (K : Set G))
    (A : SmoothRep.{0,uG,uV} ℂ G) (hA : fixedVectorGenerated K.toSubgroup A)
    (B : SmoothRep.{0,uG,uW} ℂ G)
    (hB : fixedVectors B.representation K.toSubgroup = ⊥)
    (f : B.representation.IntertwiningMap A.contragredient.representation) : f = 0 := by
  let t : A.representation.IntertwiningMap B.contragredient.representation :=
    (contragredientMap f).comp (smoothBidual A.isSmooth)
  have ht : t = 0 := by
    apply fixedVectorGenerated_hom_ext K hA
    intro v hv
    have hm := map_mem_fixedVectors t hv
    rw [fixedVectors_contragredient_eq_bot K hK B hB] at hm
    exact hm
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  have h := congrArg (fun q : A.representation.IntertwiningMap
    B.contragredient.representation => (q v).val b) ht
  exact h

/-- The zero-fixed-vector summand in a smooth dual vanishes, so a supplied splitting
makes its other summand the entire smooth dual. -/
theorem fixedVectorGenerated_contragredient_of_splitting
    (hK : IsCompact (K : Set G)) (hsplit : fixedVectorSplitting.{uG,uV} K)
    (A : SmoothRep.{0,uG,uV} ℂ G) (hA : fixedVectorGenerated K.toSubgroup A) :
    fixedVectorGenerated K.toSubgroup A.contragredient := by
  obtain ⟨S, T, hS, hT, hsum⟩ := hsplit A.contragredient
  have hi := hom_contragredient_eq_zero_of_fixedVectors_eq_bot K hK A hA
    (SmoothRep.subrepresentation A.contragredient T) hT
    (SmoothRep.hom (SmoothRep.subtype A.contragredient T))
  have hT0 : T = ⊥ := by
    apply le_antisymm _ bot_le
    intro ℓ hℓ
    change ℓ = 0
    exact congrArg (fun f => f ⟨ℓ, hℓ⟩) hi
  have hStop : S = ⊤ := by simpa only [hT0, sup_bot_eq] using hsum
  apply fixedVectorGenerated_of_surjective K.toSubgroup hS
    (SmoothRep.hom (SmoothRep.subtype A.contragredient S))
  intro ℓ
  refine ⟨⟨ℓ, ?_⟩, rfl⟩
  rw [hStop]
  trivial

/-- The converse follows from the injective evaluation into the smooth bidual and
closure of fixed-vector generation under subobjects. -/
theorem fixedVectorGenerated_iff_contragredient_of_splitting
    (hK : IsCompact (K : Set G)) (hcofinal : CompactOpenCofinal G)
    (hsplit : fixedVectorSplitting.{uG,uV} K)
    [(fixedVectorGenerated.{uG,uV} K.toSubgroup).IsClosedUnderSubobjects]
    (A : SmoothRep.{0,uG,uV} ℂ G) :
    fixedVectorGenerated K.toSubgroup A ↔
      fixedVectorGenerated K.toSubgroup A.contragredient := by
  constructor
  · exact fixedVectorGenerated_contragredient_of_splitting K hK hsplit A
  · intro hA
    have hAA := fixedVectorGenerated_contragredient_of_splitting K hK hsplit
      A.contragredient hA
    have : Mono (SmoothRep.bidualHom A) := SmoothRep.mono_bidualHom hcofinal A
    exact (fixedVectorGenerated K.toSubgroup).prop_of_mono (SmoothRep.bidualHom A) hAA

end Langlands.Jacquet
