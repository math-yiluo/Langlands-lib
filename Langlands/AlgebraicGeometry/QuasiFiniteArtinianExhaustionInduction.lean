import Langlands.AlgebraicGeometry.ImmersionExhaustionFamilies
import Langlands.AlgebraicGeometry.LocalArtinianExhaustionProof
import Langlands.AlgebraicGeometry.QuasiFiniteArtinianExhaustionStatement
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreReduction
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepReduction

/-! # Local dimension induction for Artinian subscheme exhaustion -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.AlgebraicGeometry.ImmersionExhaustion

open UnramifiedFunctor

/-- The stalk-to-open locality input, kept explicit until its separate
localization-spreading implementation is imported. -/
def StalkLocalityStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsNoetherian S]
    (I : Type v) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Family S I),
    LocallyOfFiniteType D.ambient.hom → QuasiCompact D.ambient.hom →
    (∀ s : S, (D.baseChange (S.fromSpecStalk s)).Full) → D.Full

/-- Exhaustion on noetherian bases with a uniform strict bound on local
dimensions. The dimension bound is only an induction parameter. -/
def DimensionBound (n : ℕ) : Prop :=
  ∀ (S : Scheme.{u}) [IsNoetherian S],
    (∀ s : S, ringKrullDim (S.presheaf.stalk s) < n) →
    ∀ (I : Type v) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : Family S I),
      LocallyOfFiniteType D.ambient.hom → LocallyQuasiFinite D.ambient.hom →
      QuasiCompact D.ambient.hom → D.ArtinianTests → D.Full

/-- Strong induction applies the local geometric step to a stalk ring and
the induction hypothesis to its punctured spectrum. -/
theorem dimensionBound_of_stalkLocality (hLG : StalkLocalityStatement.{u, v}) :
    ∀ n : ℕ, DimensionBound.{u, v} n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S _ hd I _ _ _ D hft hqf hqc htests
    apply hLG S I D hft hqc
    intro s
    obtain ⟨m, hm⟩ := exists_nat_eq_ringKrullDim (S.presheaf.stalk s)
    have hmn : m < n := by
      have hs := hd s
      rw [hm] at hs
      exact_mod_cast hs
    let R := CommRingCat.of (S.presheaf.stalk s)
    let E := D.baseChange (S.fromSpecStalk s)
    have hftE : LocallyOfFiniteType E.ambient.hom := by
      change LocallyOfFiniteType (pullback.snd D.ambient.hom (S.fromSpecStalk s))
      let := hft
      infer_instance
    have hqfE : LocallyQuasiFinite E.ambient.hom := by
      change LocallyQuasiFinite (pullback.snd D.ambient.hom (S.fromSpecStalk s))
      let := hqf
      infer_instance
    have hqcE : QuasiCompact E.ambient.hom := by
      change QuasiCompact (pullback.snd D.ambient.hom (S.fromSpecStalk s))
      let := hqc
      infer_instance
    have htE : E.ArtinianTests := htests.baseChange (S.fromSpecStalk s)
    apply E.full_iff.mpr
    apply LocalArtinianExhaustion.localArtinianExhaustion R E.ambient.left E.ambient.hom
      hftE hqfE hqcE I (fun i => (E.member i).left) (fun i => (E.inclusion i).left)
      E.immersion
    · intro i k hik
      obtain ⟨a, ha⟩ := E.increasing i k hik
      exact ⟨a.left, congrArg (fun f => f.left) ha⟩
    · let U := puncturedSpectrum R
      have : NoetherianSpace U.toScheme :=
        U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
      have : IsNoetherian U.toScheme :=
        { toIsLocallyNoetherian := inferInstance
          toCompactSpace := inferInstance }
      have hdU (t : U.toScheme) :
          ringKrullDim (U.toScheme.presheaf.stalk t) < m := by
        have ht := ringKrullDim_stalk_puncturedSpectrum_lt R t
        change ringKrullDim (U.toScheme.presheaf.stalk t) <
          ringKrullDim (S.presheaf.stalk s) at ht
        rwa [hm] at ht
      let F := E.baseChange U.ι
      have hftF : LocallyOfFiniteType F.ambient.hom := by
        change LocallyOfFiniteType (pullback.snd E.ambient.hom U.ι)
        let := hftE
        infer_instance
      have hqfF : LocallyQuasiFinite F.ambient.hom := by
        change LocallyQuasiFinite (pullback.snd E.ambient.hom U.ι)
        let := hqfE
        infer_instance
      have hqcF : QuasiCompact F.ambient.hom := by
        change QuasiCompact (pullback.snd E.ambient.hom U.ι)
        let := hqcE
        infer_instance
      obtain ⟨i, hi⟩ := ih m hmn U.toScheme hdU I F hftF hqfF hqcF
        (htE.baseChange U.ι)
      exact ⟨i, (isIso_over_map_iff (E.inclusion i) U.ι).mp hi⟩
    · intro k
      have : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) :=
        isArtinianRing_quotient_maximalIdeal_pow R k
      have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_of_lt
          ((Ideal.pow_le_self (Nat.succ_ne_zero k)).trans_lt
            (IsLocalRing.maximalIdeal.isMaximal R).lt_top))
      have : IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) :=
        IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
      obtain ⟨i, hi⟩ := htE (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))
        (maximalIdealPowQuotientMap R k)
      exact ⟨i, (isIso_over_map_iff (E.inclusion i)
        (maximalIdealPowQuotientMap R k)).mp hi⟩

/-- No global dimension bound on the original base is needed: each stalk
ring has its own finite bound, applied after that scalar extension. -/
theorem full_of_artinianTests_of_stalkLocality (hLG : StalkLocalityStatement.{u, v})
    (S : Scheme.{u}) [IsNoetherian S]
    (I : Type v) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Family S I) (hft : LocallyOfFiniteType D.ambient.hom)
    (hqf : LocallyQuasiFinite D.ambient.hom) (hqc : QuasiCompact D.ambient.hom)
    (htests : D.ArtinianTests) : D.Full := by
  apply hLG S I D hft hqc
  intro s
  obtain ⟨m, hm⟩ := exists_nat_eq_ringKrullDim (S.presheaf.stalk s)
  let R := CommRingCat.of (S.presheaf.stalk s)
  let E := D.baseChange (S.fromSpecStalk s)
  have hdim (t : Spec R) : ringKrullDim ((Spec R).presheaf.stalk t) < m + 1 := by
    have ht : ringKrullDim ((Spec R).presheaf.stalk t) ≤ ringKrullDim R := by
      rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight]
      have : t.asIdeal.IsPrime := t.isPrime
      exact_mod_cast Ideal.height_le_ringKrullDim_of_isPrime (I := t.asIdeal)
    change ringKrullDim ((Spec R).presheaf.stalk t) ≤
      ringKrullDim (S.presheaf.stalk s) at ht
    rw [hm] at ht
    exact ht.trans_lt (by exact_mod_cast Nat.lt_succ_self m)
  have hftE : LocallyOfFiniteType E.ambient.hom := by
    change LocallyOfFiniteType (pullback.snd D.ambient.hom (S.fromSpecStalk s))
    let := hft
    infer_instance
  have hqfE : LocallyQuasiFinite E.ambient.hom := by
    change LocallyQuasiFinite (pullback.snd D.ambient.hom (S.fromSpecStalk s))
    let := hqf
    infer_instance
  have hqcE : QuasiCompact E.ambient.hom := by
    change QuasiCompact (pullback.snd D.ambient.hom (S.fromSpecStalk s))
    let := hqc
    infer_instance
  exact dimensionBound_of_stalkLocality hLG (m + 1) (Spec R) hdim I E
    hftE hqfE hqcE (htests.baseChange (S.fromSpecStalk s))

/-- The standalone geometric exhaustion target follows from the separate
stalk-locality theorem and the already proved local geometric step. -/
theorem exhaustion_of_stalkLocality (hLG : StalkLocalityStatement.{u, v}) :
    Langlands.AlgebraicGeometry.QuasiFiniteArtinianExhaustionStatement.{u, v} := by
  intro S X _ f hft hqf hqc I _ _ _ Y j hj hinc ht
  let D := Family.ofSchemes f Y j hj hinc
  have htests : D.ArtinianTests := by
    intro R _ _ _ b
    obtain ⟨i, hi⟩ := ht R b
    exact ⟨i, (isIso_over_map_iff (D.inclusion i) b).mpr hi⟩
  exact D.full_iff.mp
    (full_of_artinianTests_of_stalkLocality hLG S I D hft hqf hqc htests)

end Langlands.AlgebraicGeometry.ImmersionExhaustion
