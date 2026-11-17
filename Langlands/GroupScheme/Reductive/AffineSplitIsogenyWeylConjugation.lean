import Langlands.GroupScheme.Reductive.AffineSplitIsogenyWeylLaws
import Langlands.GroupScheme.Reductive.LocalSplitRootPairRescaling
import Langlands.GroupScheme.Reductive.PoweredNegativeConjugation

/-! # Assembly of powered Weyl-conjugation laws -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [DecidableEq I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  {H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom H.X.hom]
  (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
  {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
  {b : P.Base} {b' : Q.Base}
  (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
  (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
  (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u')

include hd

/-- Arbitrary-unit negative conjugation transfers through the common power of a root orbit. -/
theorem conj_neg_poweredWeylFamily (hi' : IsClosedSubgroup i')
    (hpos : ∀ a, b.IsPos a ↔ b'.IsPos (f.indexEquiv.symm a))
    {c : J} (hc : c ∈ b.support) {a : J}
    (ha : b.IsPos a) (hca : b.IsPos (P.reflectionPerm c a)) (κ : Rˣ)
    (h : wordConj P (poweredRootFamily f hchar u') [c]
        (weylFamily P W (poweredRootFamily f hchar u') a) =
      scaleHom (κ : R) ≫
        weylFamily P W (poweredRootFamily f hchar u') (P.reflectionPerm c a)) :
    wordConj P (poweredRootFamily f hchar u') [c]
        (weylFamily P W (poweredRootFamily f hchar u') (P.reflectionPerm a a)) =
      scaleHom ((κ⁻¹ : Rˣ) : R) ≫
        weylFamily P W (poweredRootFamily f hchar u')
          (P.reflectionPerm c (P.reflectionPerm a a)) := by
  have hpow (x y : J) :
      rootPower f hchar (f.indexEquiv.symm (P.reflectionPerm x y)) =
        rootPower f hchar (f.indexEquiv.symm y) := by
    apply rootPower_eq_of_factor_eq
    rw [f.indexEquiv_symm_reflectionPerm, f.rootFactor_reflectionPerm]
  rw [wordConj_powered_reindex] at h ⊢
  simp only [weylFamily_powered_eq f hchar hb W u', rootMap,
    List.map_cons, List.map_nil] at h ⊢
  simp only [hpow] at h ⊢
  simp only [f.indexEquiv_symm_reflectionPerm] at h ⊢
  apply hd.conj_neg_precompose_power (rootPoint_rootPower f hchar (f.indexEquiv.symm a))
    hi' (hb c hc) ((hpos a).mp ha) ?_ κ h
  simpa only [f.indexEquiv_symm_reflectionPerm] using
    (hpos (P.reflectionPerm c a)).mp hca

/-- All target fields except the separately supplied negative-unit step are now
discharged from the genuine target geometry and the isogeny characteristic condition. -/
theorem targetWeylRelations_powered_of_negative
    (hi' : IsClosedSubgroup i')
    (hPpair : ∀ m n, P.toLinearMap m n = ∑ j, m j * n j)
    (hN : ∀ c ∈ b.support, ∀ a, b.IsPos a → b.IsPos (P.reflectionPerm c a) →
      ∀ κ : Rˣ,
      wordConj P (poweredRootFamily f hchar u') [c]
          (weylFamily P W (poweredRootFamily f hchar u') a) =
        scaleHom (κ : R) ≫
          weylFamily P W (poweredRootFamily f hchar u') (P.reflectionPerm c a) →
      wordConj P (poweredRootFamily f hchar u') [c]
          (weylFamily P W (poweredRootFamily f hchar u') (P.reflectionPerm a a)) =
        scaleHom ((κ⁻¹ : Rˣ) : R) ≫
          weylFamily P W (poweredRootFamily f hchar u')
            (P.reflectionPerm c (P.reflectionPerm a a))) :
    TargetWeylRelations P b W (poweredRootFamily f hchar u') := by
  have hQpair := hd.rootDatum.pairing (IsLocalRing.ResidueField R)
  have hL c (hc : c ∈ b.support) :
      RankOneLaws i' (Q.coroot (f.indexEquiv.symm c)) (u' (f.indexEquiv.symm c))
        (u' (Q.reflectionPerm (f.indexEquiv.symm c) (f.indexEquiv.symm c))) := by
    apply localSplitRootPairLaws R H hd.reductive I' i' hi' hd.maximal J' Q hd.rootDatum
      (f.indexEquiv.symm c) _ _ (hd.param _ (hb c hc)).1
    · simpa only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
        using (hd.param _ (hb c hc)).2
    · exact hd.weyl _ (hb c hc)
  obtain ⟨hB, hA, hD, hS⟩ := poweredWeylTransportRelations f hchar hb W u' hd hi'
  obtain ⟨hSq, hFix⟩ :=
    poweredWeylActionRelations f hchar hb W u' hd hi' hPpair hQpair hL
  refine ⟨hB, ?_, ?_, hA, hD, hS, hN⟩
  · intro c hc a
    simpa only [signUnit_val] using hSq c hc a
  · intro c hc a hnp hcone hnm hconem
    apply hFix c hc a
    · intro h
      exact hnp (by simpa only [neg_neg] using (congrArg Neg.neg h).symm)
    · intro d s t hs ht h
      exact hcone d t s ht hs (by simpa only [add_comm] using h)
    · intro h
      exact hnm (by simpa only [neg_neg] using (congrArg Neg.neg h).symm)
    · intro d s t hs ht h
      exact hconem d t s ht hs (by simpa only [add_comm] using h)

/-- All target conjugation fields are actual powered-family identities. -/
theorem targetWeylRelations_powered
    (hi' : IsClosedSubgroup i')
    (hPpair : ∀ m n, P.toLinearMap m n = ∑ j, m j * n j)
    (hpos : ∀ a, b.IsPos a ↔ b'.IsPos (f.indexEquiv.symm a)) :
    TargetWeylRelations P b W (poweredRootFamily f hchar u') := by
  apply targetWeylRelations_powered_of_negative f hchar hb W u' hd hi' hPpair
  intro c hc a ha hca κ h
  exact conj_neg_poweredWeylFamily f hchar hb W u' hd hi' hpos hc ha hca κ h

/-- Genuine source and target normalized data give common Weyl units for the actual
powered family, without any additional target action-law hypothesis. -/
theorem weylConjugationRelations_powered [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {u : J → (Ga R ⟶ G)} (hdG : IsNormalSimpleData i P b W u)
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (hpos : ∀ a, b.IsPos a ↔ b'.IsPos (f.indexEquiv.symm a)) :
    WeylConjugationRelations P b W u (poweredRootFamily f hchar u') := by
  have hPU : PartnerUnique P G i := by
    intro a xp xm xm' hp hm hm' hn hn'
    exact rootPartner_unique hdG.reductive hi hdG.maximal hdG.rootDatum a hp hm hm' hn hn'
  have hSC : PartnerRescales P G i := by
    intro a xp xm hp hm hn κ
    exact isWeylPoint_rescale hdG.reductive hi hdG.maximal hdG.rootDatum a hp hm hn κ
  exact TargetWeylProofs.weylConjugationRelations_of_targetLaws hdG
    (targetWeylRelations_powered f hchar hb W u' hd hi'
      (hdG.rootDatum.pairing (IsLocalRing.ResidueField R)) hpos) hPU hSC

end Langlands.GroupScheme.AffineRootDatumIsogeny

namespace Langlands.GroupScheme

open LocalSplitCell AffineRootDatumIsogeny

/-- Common Weyl units for actual powered maps under the original characteristic condition. -/
def PoweredWeylConjugationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (I I' J J' : Type u) [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
    [Finite J] [Finite J']
    (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    [P.IsReduced] [Q.IsReduced] (p : ℕ)
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H),
    IsClosedSubgroup i → IsClosedSubgroup i' →
    ∀ (b : P.Base) (b' : Q.Base)
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support),
    (∀ a, b.IsPos a ↔ b'.IsPos (f.indexEquiv.symm a)) →
    ∀ (W : ∀ α, SimpleWord P b α)
    (u : J → (Ga R ⟶ G)) (u' : J' → (Ga R ⟶ H)),
    IsNormalSimpleData i P b W u →
    IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u' →
      WeylConjugationRelations P b W u (poweredRootFamily f hchar u')

/-- Every target action field is proved before applying the common-unit induction. -/
theorem poweredWeylConjugation : PoweredWeylConjugationStatement.{u} := by
  intro R _ _ I I' J J' _ _ _ _ _ _ P Q _ _ p f hchar G H _ _ i i' hi hi' b b' hb
    hpos W u u' hdG hdH
  exact weylConjugationRelations_powered f hchar hb W u' hdH hdG hi hi' hpos

end Langlands.GroupScheme
