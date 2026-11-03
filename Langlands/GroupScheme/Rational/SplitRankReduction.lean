import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.SubgroupConjugacy
import Langlands.GroupScheme.Rational.ConjugacyStatement

/-! # Split rank from maximal extension and source isomorphisms -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
local notation "S" => Spec (CommRingCat.of k)

/-- The intrinsic finite rank of a split torus, obtained from a chosen splitting.
The following lemma proves independence of the splitting. -/
def IsSplitTorus.rank {T : GroupScheme S} (hT : IsSplitTorus T) : ℕ :=
  Nat.card hT.choose

theorem IsSplitTorus.rank_eq_card {T : GroupScheme S} (hT : IsSplitTorus T)
    (I : Type u) [Finite I] (e : T ≅ splitTorus S I) :
    hT.rank = Nat.card I := by
  obtain ⟨hJ, ⟨e'⟩⟩ := hT.choose_spec
  let := hJ
  exact splitTorus.card_eq_card_of_iso hT.choose I (e'.symm ≪≫ e)

theorem splitRank_splitTorus (I : Type u) [Finite I] :
    splitRank (splitTorus S I) = (Nat.card I : ℕ∞) := by
  apply le_antisymm
  · refine iSup_le fun J => iSup_le fun _ => iSup_le fun j => iSup_le fun hj => ?_
    exact_mod_cast splitTorus.card_le_card_of_isClosedSubgroup J I j hj
  · exact card_le_splitRank I (𝟙 _) (IsClosedSubgroup.of_iso (Iso.refl _))

theorem splitRank_eq_of_splitIso {T : GroupScheme S}
    (I : Type u) [Finite I] (e : T ≅ splitTorus S I) :
    splitRank T = (Nat.card I : ℕ∞) := by
  rw [splitRank_eq_of_iso e, splitRank_splitTorus]

theorem IsSplitTorus.rank_eq_splitRank {T : GroupScheme S} (hT : IsSplitTorus T) :
    (hT.rank : ℕ∞) = splitRank T := by
  obtain ⟨hI, ⟨e⟩⟩ := hT.choose_spec
  let := hI
  rw [hT.rank_eq_card hT.choose e, splitRank_eq_of_splitIso hT.choose e]

/-- A factorization of a closed split torus through a split group bounds its rank. -/
theorem card_le_card_of_split_factorization {T G : GroupScheme S}
    (I J : Type u) [Finite I] [Finite J] (e : T ≅ splitTorus S I)
    (j : splitTorus S J ⟶ G) (hj : IsClosedSubgroup j)
    (i : T ⟶ G) (f : splitTorus S J ⟶ T) (hf : f ≫ i = j) :
    Nat.card J ≤ Nat.card I := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Mono f.hom.hom := mono_of_mono_fac
    (by simpa only [Grp.comp_hom_hom] using congrArg (fun a => a.hom.hom) hf)
  let : Mono (f ≫ e.hom).hom.hom := by
    change Mono (f.hom.hom ≫ e.hom.hom.hom)
    infer_instance
  exact splitTorus.card_le_card_of_mono J I (f ≫ e.hom)

/-- The supremum equals the rank of a fixed maximal torus once every split torus extends
maximally and every maximal torus is isomorphic to the fixed one. -/
theorem IsMaximalSplitTorus.card_eq_splitRank_of_extension
    {G : GroupScheme S} {T : CommGroupScheme S} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i)
    (hExtension : ∀ (J : Type u) [Finite J] (j : splitTorus S J ⟶ G),
      IsClosedSubgroup j →
        ∃ (T' : CommGroupScheme S) (i' : T'.toGrp ⟶ G),
          IsMaximalSplitTorus i' ∧ ∃ f : splitTorus S J ⟶ T'.toGrp, f ≫ i' = j)
    (hIso : ∀ (T' : CommGroupScheme S) (i' : T'.toGrp ⟶ G),
      IsMaximalSplitTorus i' → Nonempty (T'.toGrp ≅ T.toGrp))
    (I : Type u) [Finite I] (e : T.toGrp ≅ splitTorus S I) :
    (Nat.card I : ℕ∞) = splitRank G := by
  apply le_antisymm (hi.1.card_le_splitRank I e)
  refine iSup_le fun J => iSup_le fun _ => iSup_le fun j => iSup_le fun hj => ?_
  obtain ⟨T', i', hi', f, hf⟩ := hExtension J j hj
  obtain ⟨e'⟩ := hIso T' i' hi'
  exact_mod_cast card_le_card_of_split_factorization I J (e' ≪≫ e) j hj i' f hf

/-- Rational conjugacy supplies precisely the source isomorphisms needed by the rank reduction. -/
theorem IsMaximalSplitTorus.card_eq_splitRank_of_extension_conjugacy
    {G : GroupScheme S} {T : CommGroupScheme S} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i)
    (hExtension : ∀ (J : Type u) [Finite J] (j : splitTorus S J ⟶ G),
      IsClosedSubgroup j →
        ∃ (T' : CommGroupScheme S) (i' : T'.toGrp ⟶ G),
          IsMaximalSplitTorus i' ∧ ∃ f : splitTorus S J ⟶ T'.toGrp, f ≫ i' = j)
    (hConjugacy : ∀ (T' : CommGroupScheme S) (i' : T'.toGrp ⟶ G),
      IsMaximalSplitTorus i' → SubgroupConjugate i' i)
    (I : Type u) [Finite I] (e : T.toGrp ≅ splitTorus S I) :
    (Nat.card I : ℕ∞) = splitRank G :=
  hi.card_eq_splitRank_of_extension hExtension
    (fun T' i' hi' => by obtain ⟨_, e', _⟩ := hConjugacy T' i' hi'; exact ⟨e'⟩) I e

/-- Conditional assembly only: the geometric hypotheses are explicit proof obligations. -/
theorem maximalSplitTorusConjugacyStatement_of_extension_conjugacy
    (hExtension : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G →
      ∀ (J : Type u) [Finite J] (j : splitTorus (Spec (CommRingCat.of k)) J ⟶ G),
        IsClosedSubgroup j →
          ∃ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G),
            IsMaximalSplitTorus i' ∧
              ∃ f : splitTorus (Spec (CommRingCat.of k)) J ⟶ T'.toGrp, f ≫ i' = j)
    (hConjugacy : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G →
      ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
        (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G),
        IsMaximalSplitTorus i → IsMaximalSplitTorus i' → SubgroupConjugate i i') :
    MaximalSplitTorusConjugacyStatement.{u} := by
  intro k _ G hG
  refine ⟨hConjugacy k G hG, ?_⟩
  intro T i hi I _ e
  exact hi.card_eq_splitRank_of_extension_conjugacy (hExtension k G hG)
    (fun T' i' hi' => hConjugacy k G hG T' T i' i hi' hi) I e

end Langlands.GroupScheme
