import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.Reductive.Basic

/-! # Split subtori, maximal split tori, the split rank and anisotropy over a field -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-! ### Split subtori and maximal split tori -/

section SplitSubtori

variable {T : CommGroupScheme (Spec (CommRingCat.of k))} {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A homomorphism `i : T ⟶ G` from a commutative group scheme is a split subtorus of `G` when
`T` is a split torus and `i` is a closed immersion. -/
def IsSplitSubtorus (i : T.toGrp ⟶ G) : Prop :=
  IsSplitTorus T.toGrp ∧ IsClosedSubgroup i

/-- A split subtorus `i : T ⟶ G` is maximal when every factorization `f ≫ i' = i` through a
split subtorus `i' : T' ⟶ G` has `f` an isomorphism. -/
def IsMaximalSplitTorus (i : T.toGrp ⟶ G) : Prop :=
  IsSplitSubtorus i ∧
    ∀ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G),
      IsSplitSubtorus i' → ∀ f : T.toGrp ⟶ T'.toGrp, f ≫ i' = i → IsIso f

theorem IsMaximalSplitTorus.isSplitSubtorus {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) :
    IsSplitSubtorus i :=
  hi.1

end SplitSubtori

/-- An isomorphism of group schemes is a closed subgroup. -/
theorem IsClosedSubgroup.of_iso {S : Scheme.{u}} {H G : GroupScheme S} (e : H ≅ G) :
    IsClosedSubgroup e.hom := by
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget S).mapIso ((Grp.forget _).mapIso e)).hom)
  change IsClosedImmersion e.hom.hom.hom.left
  infer_instance

/-- Precomposing a closed subgroup with an isomorphism of group schemes gives a closed
subgroup. -/
theorem IsClosedSubgroup.iso_comp {S : Scheme.{u}} {H H' G : GroupScheme S} (e : H' ≅ H)
    {i : H ⟶ G} (hi : IsClosedSubgroup i) : IsClosedSubgroup (e.hom ≫ i) := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion e.hom.hom.hom.left := IsClosedSubgroup.of_iso e
  change IsClosedImmersion (e.hom.hom.hom.left ≫ i.hom.hom.left)
  infer_instance

/-! ### The split rank -/

/-- The split rank (`k`-rank) of `G`: the supremum, in `ℕ∞`, of `Nat.card I` over finite
`I : Type u` admitting a closed-subgroup homomorphism `splitTorus S I ⟶ G`. -/
def splitRank (G : GroupScheme (Spec (CommRingCat.of k))) : ℕ∞ :=
  ⨆ (I : Type u) (_ : Finite I) (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (_ : IsClosedSubgroup i), (Nat.card I : ℕ∞)

/-- `G` is anisotropic when its split rank is zero (the convention of Borel–Tits 4.23). -/
def IsAnisotropic (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  splitRank G = 0

section Rank

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Every closed split torus `splitTorus S I ⟶ G` has `Nat.card I` at most the split rank. -/
theorem card_le_splitRank (I : Type u) [Finite I]
    (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G) (hi : IsClosedSubgroup i) :
    (Nat.card I : ℕ∞) ≤ splitRank G :=
  le_iSup_of_le I <| le_iSup_of_le inferInstance <| le_iSup_of_le i <| le_iSup_of_le hi le_rfl

/-- The dimension of a split subtorus is at most the split rank. -/
theorem IsSplitSubtorus.card_le_splitRank {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} (hi : IsSplitSubtorus i) (I : Type u) [Finite I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) :
    (Nat.card I : ℕ∞) ≤ splitRank G :=
  Langlands.GroupScheme.card_le_splitRank I (e.inv ≫ i) (hi.2.iso_comp e.symm)

/-- The split rank is zero exactly when every closed split torus in `G` has empty index type. -/
theorem isAnisotropic_iff :
    IsAnisotropic G ↔ ∀ (I : Type u) [Finite I]
      (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G), IsClosedSubgroup i → IsEmpty I := by
  constructor
  · intro hG I _ i hi
    have h := Langlands.GroupScheme.card_le_splitRank I i hi
    rw [show splitRank G = 0 from hG, nonpos_iff_eq_zero, Nat.cast_eq_zero,
      Nat.card_eq_zero] at h
    exact h.resolve_right (not_infinite_iff_finite.mpr inferInstance)
  · intro h
    refine le_antisymm (iSup_le fun I => iSup_le fun _ => iSup_le fun i => iSup_le fun hi => ?_)
      bot_le
    have := h I i hi
    simp

/-- In an anisotropic group every split subtorus has empty index type. -/
theorem IsAnisotropic.isEmpty_of_isSplitSubtorus (hG : IsAnisotropic G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsSplitSubtorus i) (I : Type u) [Finite I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) : IsEmpty I :=
  isAnisotropic_iff.mp hG I (e.inv ≫ i) (hi.2.iso_comp e.symm)

end Rank

/-- The multiplicative group has split rank at least one. -/
theorem one_le_splitRank_gm : 1 ≤ splitRank (Gm (Spec (CommRingCat.of k))).toGrp := by
  simpa using card_le_splitRank PUnit (splitTorus.gmIso _).inv
    (IsClosedSubgroup.of_iso (splitTorus.gmIso _).symm)

/-- With the convention of Borel–Tits 4.23, the multiplicative group is not anisotropic. -/
theorem not_isAnisotropic_gm : ¬ IsAnisotropic (Gm (Spec (CommRingCat.of k))).toGrp := by
  intro h
  have h1 := one_le_splitRank_gm (k := k)
  rw [show splitRank (Gm (Spec (CommRingCat.of k))).toGrp = 0 from h] at h1
  exact absurd h1 (by simp)

/-! ### Homomorphisms out of the trivial split torus -/

/-- The split torus on an empty index type has a single point over every test scheme, so there is
at most one homomorphism out of it. -/
theorem splitTorus.subsingleton_hom_of_isEmpty {S : Scheme.{u}} (I : Type u) [Finite I]
    [IsEmpty I] (H : GroupScheme S) : Subsingleton (splitTorus S I ⟶ H) := by
  have hpt : ∀ (U : Over S) (x : U ⟶ (splitTorus S I).X), x = 1 := fun U x =>
    (splitTorus.pointsEquiv I U).injective (Subsingleton.elim _ _)
  have key : ∀ f : splitTorus S I ⟶ H, f.hom.hom = 1 := fun f => by
    rw [← Category.id_comp f.hom.hom, hpt _ (𝟙 _), MonObj.one_comp]
  exact ⟨fun f g => Grp.hom_ext f g ((key f).trans (key g).symm)⟩

/-- In an anisotropic group every split subtorus `T` admits at most one homomorphism to any group
scheme; in particular its characters `T ⟶ 𝔾ₘ` are trivial. -/
theorem IsAnisotropic.subsingleton_hom_of_isSplitSubtorus
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsAnisotropic G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G} (hi : IsSplitSubtorus i)
    (H : GroupScheme (Spec (CommRingCat.of k))) : Subsingleton (T.toGrp ⟶ H) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hi.1
  have := hG.isEmpty_of_isSplitSubtorus hi I e
  have := splitTorus.subsingleton_hom_of_isEmpty (S := Spec (CommRingCat.of k)) I H
  exact ⟨fun f g => by
    rw [← e.hom_inv_id_assoc f, ← e.hom_inv_id_assoc g,
      Subsingleton.elim (e.inv ≫ f) (e.inv ≫ g)]⟩

/-- In an anisotropic group every split subtorus has trivial character group: there is at most
one homomorphism `T ⟶ 𝔾ₘ` of commutative group schemes. -/
theorem IsAnisotropic.subsingleton_character
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsAnisotropic G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G} (hi : IsSplitSubtorus i) :
    Subsingleton (T ⟶ Gm (Spec (CommRingCat.of k))) :=
  have := hG.subsingleton_hom_of_isSplitSubtorus hi (Gm (Spec (CommRingCat.of k))).toGrp
  ⟨fun f g => congrArg Additive.ofMul (Subsingleton.elim f.toMul g.toMul)⟩

end Langlands.GroupScheme
