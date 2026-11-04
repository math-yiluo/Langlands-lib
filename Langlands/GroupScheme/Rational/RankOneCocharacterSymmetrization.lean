import Langlands.GroupScheme.Rational.RankOneWeylQuotient
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Rational.WeylPositiveCocharacter

/-! # Integral cocharacter symmetrization in semisimple rank at most one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Subtract the actual normalizer translate of an integral cocharacter. -/
def normalizerSymmetrizedCocharacter (i : T.toGrp ⟶ G)
    (n : normalizerPoints i) (ν : cocharacterLattice T) : cocharacterLattice T :=
  ν - cocharacterAut (normalizingAut i n) ν

/-- Every element of the actual rank-one Weyl quotient squares to the identity. -/
theorem IsConnectedReductive.relativeWeylGroup_sq_eq_one_of_rankOne
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (w : relativeWeylGroup i) : w ^ 2 = 1 := by
  let : Finite (relativeWeylGroup i) :=
    Finite.of_injective
      (hG.rankOneRelativeWeylQuotientSignEmbedding_of_isMaximalTorus i hi hT hdep)
      (hG.rankOneRelativeWeylQuotientSignEmbedding_of_isMaximalTorus i hi hT hdep).injective
  apply isSelfInv_iff_sq_eq_one.mp
  apply isSelfInv_iff_isOfFinOrder_and_orderOf_le_two.mpr
  exact ⟨isOfFinOrder_of_finite w,
    orderOf_le_card.trans
      (hG.card_relativeWeylGroup_le_two_of_rankOne_of_isMaximalTorus i hi hT hdep)⟩

/-- The action of any normalizing rational point is an involution on the entire
integral cocharacter lattice, including its central directions. -/
theorem IsConnectedReductive.cocharacterAut_normalizingAut_sq_eq_one_of_rankOne
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints i) :
    cocharacterAut (normalizingAut i n) ^ 2 = 1 := by
  let := hi.2.1.mono
  have h := congrArg (relativeWeylCocharacterAction i)
    (hG.relativeWeylGroup_sq_eq_one_of_rankOne i hi hT hdep (QuotientGroup.mk n))
  simpa only [map_pow, map_one, relativeWeylCocharacterAction_mk] using h

/-- A rank-one normalizer action negates the symmetrized cocharacter exactly,
without dividing by two or passing to the Lie algebra. -/
theorem IsConnectedReductive.cocharacterAut_normalizerSymmetrizedCocharacter
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints i) (ν : cocharacterLattice T) :
    cocharacterAut (normalizingAut i n) (normalizerSymmetrizedCocharacter i n ν) =
      -normalizerSymmetrizedCocharacter i n ν := by
  have hinv := congrArg
    (fun e : cocharacterLattice T ≃ₗ[ℤ] cocharacterLattice T => e ν)
    (hG.cocharacterAut_normalizingAut_sq_eq_one_of_rankOne i hi hT hdep n)
  change cocharacterAut (normalizingAut i n)
    (cocharacterAut (normalizingAut i n) ν) = ν at hinv
  dsimp only [normalizerSymmetrizedCocharacter]
  rw [map_sub, hinv]
  abel

/-- Every nonidentity actual Weyl class negates every actual root in rank one.
This assertion does not assert existence of such a class. -/
theorem IsConnectedReductive.weylAction_eq_neg_of_rankOne
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints i) (hn : (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1)
    (α : characterLattice T) :
    haveI := hG.isAffineHom
    haveI := hi.2.1.mono
    α ∈ roots i → weylAction i n α = -α := by
  let := hG.isAffineHom
  let := hG.smooth
  let := hi.2.1.mono
  intro hα
  have hneg : relativeWeylAction i (QuotientGroup.mk n) = LinearEquiv.neg ℚ := by
    apply (hT.relativeWeylAction_eq_one_or_neg_of_rankOne i hdep
      (QuotientGroup.mk n)).resolve_left
    intro h
    apply hn
    apply hG.relativeWeylAction_injective_of_isMaximalTorus i hi hT
    simpa only [map_one] using h
  apply hT.character_toRat_injective
  have h := congrArg
    (fun e : relativeRootSpan i ≃ₗ[ℚ] relativeRootSpan i =>
      (e ⟨toRat α, toRat_mem_ratSpan hα⟩ : ℚ ⊗[ℤ] characterLattice T)) hneg
  rw [coe_relativeWeylAction_mk_apply, ratAut_toRat] at h
  exact h.trans (map_neg toRat α).symm

/-- Subtracting a normalizer translate doubles the pairing with any character
that the normalizer negates. -/
theorem latticePairing_normalizerSymmetrizedCocharacter_of_neg
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (n : normalizerPoints i) (α : characterLattice T) (ν : cocharacterLattice T)
    (hα : weylAction i n α = -α) :
    latticePairing T α (normalizerSymmetrizedCocharacter i n ν) =
      2 * latticePairing T α ν := by
  have h := latticePairing_characterAut_cocharacterAut (normalizingAut i n) α ν
  change latticePairing T (weylAction i n α)
    (cocharacterAut (normalizingAut i n) ν) = latticePairing T α ν at h
  rw [hα, map_neg, LinearMap.neg_apply] at h
  rw [normalizerSymmetrizedCocharacter, map_sub]
  omega

/-- A nonidentity actual rank-one Weyl class doubles every root pairing after
integral symmetrization. -/
theorem IsConnectedReductive.latticePairing_normalizerSymmetrizedCocharacter
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints i) (hn : (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1)
    (α : characterLattice T) (ν : cocharacterLattice T) :
    haveI := hG.isAffineHom
    α ∈ roots i →
      latticePairing T α (normalizerSymmetrizedCocharacter i n ν) =
        2 * latticePairing T α ν := by
  let := hG.isAffineHom
  let := hi.2.1.mono
  intro hα
  exact latticePairing_normalizerSymmetrizedCocharacter_of_neg i n α ν
    (hG.weylAction_eq_neg_of_rankOne i hi hT hdep n hn α hα)

/-- Conjugation sends the actual symmetrized cocharacter to its negative as an
equality of group-scheme homomorphisms. -/
theorem IsConnectedReductive.groupHom_normalizerSymmetrizedCocharacter_comp_innerIso
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints i) (ν : cocharacterLattice T) :
    (CommGroupScheme.groupHom (normalizerSymmetrizedCocharacter i n ν) ≫ i) ≫
        (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom =
      CommGroupScheme.groupHom (-normalizerSymmetrizedCocharacter i n ν) ≫ i := by
  rw [← groupHom_cocharacterAut_comp,
    hG.cocharacterAut_normalizerSymmetrizedCocharacter i hi hT hdep n ν]

/-- Conjugation carries the entire dynamic unipotent subgroup of the
symmetrized cocharacter to that of its negative on every test scheme. -/
theorem IsConnectedReductive.unipotent_normalizerSymmetrizedCocharacter_conj
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints i) (ν : cocharacterLattice T) :
    Dynamic.unipotent (CommGroupScheme.groupHom
        (normalizerSymmetrizedCocharacter i n ν) ≫ i) =
      (Dynamic.unipotent (CommGroupScheme.groupHom
        (-normalizerSymmetrizedCocharacter i n ν) ≫ i)).comap
          (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom := by
  rw [Dynamic.unipotent_eq_comap_of_iso _ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)),
    hG.groupHom_normalizerSymmetrizedCocharacter_comp_innerIso i hi hT hdep n ν]

end Langlands.GroupScheme
