import Langlands.Covering.Dual.CharacterExactSequence

/-! # Pullback of the dual extension for the second L-group twist -/

universe u v w z

namespace Langlands.Covering.Dual

variable {B : Type u} {E : Type v} {D : Type w} {A : Type z}
variable [CommGroup B] [CommGroup E] [CommGroup D] [Group A]

/-- Pairs `(a, χ)` such that the restriction of `χ` along `i` is `κ a`. -/
def characterPullback (i : B →* E) (κ : A →* Character B) :
    Subgroup (A × Character E) :=
  ((precompose i).comp (MonoidHom.snd A (Character E))).eqLocus
    (κ.comp (MonoidHom.fst A (Character E)))

@[simp] theorem mem_characterPullback (i : B →* E) (κ : A →* Character B)
    (x : A × Character E) :
    x ∈ characterPullback i κ ↔ x.2.comp i = κ x.1 :=
  Iff.rfl

/-- The first coordinate of a pair in the pullback. -/
def pullbackFst (i : B →* E) (κ : A →* Character B) : characterPullback i κ →* A :=
  (MonoidHom.fst A (Character E)).comp (characterPullback i κ).subtype

/-- The character coordinate of a pair in the pullback. -/
def pullbackSnd (i : B →* E) (κ : A →* Character B) :
    characterPullback i κ →* Character E :=
  (MonoidHom.snd A (Character E)).comp (characterPullback i κ).subtype

@[simp] theorem pullbackFst_apply (i : B →* E) (κ : A →* Character B)
    (x : characterPullback i κ) :
    pullbackFst i κ x = x.val.1 := rfl

@[simp] theorem pullbackSnd_apply (i : B →* E) (κ : A →* Character B)
    (x : characterPullback i κ) :
    pullbackSnd i κ x = x.val.2 := rfl

theorem pullback_restriction (i : B →* E) (κ : A →* Character B)
    (x : characterPullback i κ) :
    (pullbackSnd i κ x).comp i = κ (pullbackFst i κ x) :=
  (mem_characterPullback i κ x.val).mp x.property

/-- Pull back the dual character sequence along `κ` to get the second twist. -/
def secondTwist (S : GroupExtension B E D) (κ : A →* Character B) :
    GroupExtension (Character D) (characterPullback S.inl κ) A where
  inl := ((1 : Character D →* A).prod (dualExtension S).inl).codRestrict
    (characterPullback S.inl κ) fun ψ ↦ by
      change (dualExtension S).rightHom ((dualExtension S).inl ψ) = κ 1
      rw [GroupExtension.rightHom_inl, map_one]
  rightHom := pullbackFst S.inl κ
  inl_injective := by
    intro ψ φ h
    exact (dualExtension S).inl_injective (congrArg (pullbackSnd S.inl κ) h)
  range_inl_eq_ker_rightHom := by
    apply SetLike.ext
    intro x
    constructor
    · rintro ⟨ψ, rfl⟩
      exact MonoidHom.mem_ker.mpr rfl
    · intro hx
      have ha : x.val.1 = 1 := MonoidHom.mem_ker.mp hx
      have hχ : x.val.2 ∈ (dualExtension S).rightHom.ker := by
        change x.val.2.comp S.inl = 1
        have h := (mem_characterPullback S.inl κ x.val).mp x.property
        simpa only [ha, map_one] using h
      rw [← (dualExtension S).range_inl_eq_ker_rightHom] at hχ
      obtain ⟨ψ, hψ⟩ := hχ
      exact ⟨ψ, Subtype.ext (Prod.ext ha.symm hψ)⟩
  rightHom_surjective := by
    intro a
    obtain ⟨χ, hχ⟩ := (dualExtension S).rightHom_surjective (κ a)
    exact ⟨⟨(a, χ), hχ⟩, rfl⟩

@[simp] theorem secondTwist_inl_val (S : GroupExtension B E D) (κ : A →* Character B)
    (ψ : Character D) :
    ((secondTwist S κ).inl ψ).val = (1, ψ.comp S.rightHom) := rfl

@[simp] theorem secondTwist_rightHom_apply (S : GroupExtension B E D) (κ : A →* Character B)
    (x : characterPullback S.inl κ) :
    (secondTwist S κ).rightHom x = x.val.1 := rfl

/-- Turn a bimultiplicative pairing into the map to the characters of its first variable. -/
def pairingCharacter (h : B →* A →* ℂˣ) : A →* Character B :=
  h.flip

@[simp] theorem pairingCharacter_apply (h : B →* A →* ℂˣ) (a : A) (b : B) :
    pairingCharacter h a b = h b a := rfl

theorem mem_characterPullback_pairing (i : B →* E) (h : B →* A →* ℂˣ)
    (a : A) (χ : Character E) :
    (a, χ) ∈ characterPullback i (pairingCharacter h) ↔ ∀ b, χ (i b) = h b a := by
  rw [mem_characterPullback]
  exact ⟨fun heq b ↦ DFunLike.congr_fun heq b, fun hχ ↦ MonoidHom.ext hχ⟩

/-- The second twist for a supplied bimultiplicative pairing. -/
abbrev secondTwistOfPairing (S : GroupExtension B E D) (h : B →* A →* ℂˣ) :
    GroupExtension (Character D) (characterPullback S.inl (pairingCharacter h)) A :=
  secondTwist S (pairingCharacter h)

end Langlands.Covering.Dual
