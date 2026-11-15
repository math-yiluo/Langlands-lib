import Langlands.GroupScheme.Rational.SplitTorusMonomorphism

/-! # Split subtori of full split rank are maximal split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

/-- A split subtorus whose number of factors is at least the split rank of the ambient group
is a maximal split torus. -/
theorem IsSplitSubtorus.isMaximalSplitTorus_of_splitRank_le (hi : IsSplitSubtorus i)
    (J : Type u) [Finite J] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) J)
    (hJ : splitRank G ≤ Nat.card J) : IsMaximalSplitTorus i := by
  refine ⟨hi, fun T' i' hi' f hf => ?_⟩
  obtain ⟨J', _, ⟨e'⟩⟩ := hi'.1
  have : IsClosedImmersion i.hom.hom.left := hi.2
  have hmi : Mono i.hom.hom := Over.mono_of_mono_left _
  have hfm : Mono f.hom.hom := by
    have hcomp : Mono (f.hom.hom ≫ i'.hom.hom) := by
      have h : (f ≫ i').hom.hom = f.hom.hom ≫ i'.hom.hom := rfl
      rw [← h, hf]
      exact hmi
    exact mono_of_mono f.hom.hom i'.hom.hom
  have : IsIso e.inv.hom.hom := inferInstanceAs (IsIso ((Grp.forget _).mapIso e).inv)
  have : IsIso e'.hom.hom.hom := inferInstanceAs (IsIso ((Grp.forget _).mapIso e').hom)
  let g : splitTorus (Spec (CommRingCat.of k)) J ⟶ splitTorus (Spec (CommRingCat.of k)) J' :=
    e.inv ≫ f ≫ e'.hom
  have : Mono g.hom.hom := by
    change Mono (e.inv.hom.hom ≫ f.hom.hom ≫ e'.hom.hom.hom)
    infer_instance
  have hle := splitTorus.card_le_card_of_mono J J' g
  have hle' : (Nat.card J' : ℕ∞) ≤ splitRank G := hi'.card_le_splitRank J' e'
  have heq : Nat.card J = Nat.card J' :=
    le_antisymm hle (by exact_mod_cast hle'.trans hJ)
  have : IsIso g := splitTorus.isIso_of_mono_of_card_eq J J' g heq
  have hfeq : f = e.hom ≫ g ≫ e'.inv := by simp [g]
  rw [hfeq]
  infer_instance

/-- A split subtorus with at least as many factors as some maximal split torus is a maximal
split torus, provided all maximal split tori have the split rank as their number of factors. -/
theorem IsSplitSubtorus.isMaximalSplitTorus_of_card_le
    (hrank : ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
      IsMaximalSplitTorus a → ∀ (I : Type u) [Finite I],
        (A.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) → (Nat.card I : ℕ∞) = splitRank G)
    (hi : IsSplitSubtorus i) {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ G} (ha : IsMaximalSplitTorus a) (I J : Type u) [Finite I] [Finite J]
    (eA : A.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) J) (hIJ : Nat.card I ≤ Nat.card J) :
    IsMaximalSplitTorus i :=
  hi.isMaximalSplitTorus_of_splitRank_le J e (by
    rw [← hrank A a ha I eA]
    exact_mod_cast hIJ)

end Langlands.GroupScheme
