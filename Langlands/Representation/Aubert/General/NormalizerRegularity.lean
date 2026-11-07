import Langlands.Representation.Aubert.General.Parabolic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.RepresentationTheory.Irreducible

/-! # Regularity under the literal normalizer of a subgroup -/

noncomputable section

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Subgroup G}

/-- Inverse conjugation on the literal subgroup by an element of its normalizer. -/
def normalizerConjugation (g : Subgroup.normalizer (M : Set G)) : M ≃ₜ* M :=
  conjugationEquiv (g : G) (Subgroup.mem_normalizer_iff''.mp g.property)

/-- The original smooth representation, with its action pulled back by inverse
conjugation. The carrier and its universe are unchanged. -/
def normalizerConjugate (g : Subgroup.normalizer (M : Set G))
    (σ : SmoothRep.{0, uG, uV} ℂ M) : SmoothRep.{0, uG, uV} ℂ M :=
  SmoothRep.pullback (normalizerConjugation g) σ

/-- No normalizer element outside the subgroup fixes the representation's
isomorphism class. This uses actual conjugation on the literal subgroup. -/
def IsNormalizerRegular (σ : SmoothRep.{0, uG, uV} ℂ M) : Prop :=
  ∀ g : Subgroup.normalizer (M : Set G), (g : G) ∉ M →
    ¬ Nonempty ((normalizerConjugate g σ).representation.Equiv σ.representation)

/-- An element of the subgroup gives its original inner-action equivalence. -/
def normalizerConjugateInnerEquiv (σ : SmoothRep.{0, uG, uV} ℂ M)
    (g : Subgroup.normalizer (M : Set G)) (hg : (g : G) ∈ M) :
    (normalizerConjugate g σ).representation.Equiv σ.representation where
  toFun := σ.representation ⟨(g : G), hg⟩
  invFun := σ.representation (⟨(g : G), hg⟩ : M)⁻¹
  left_inv v := σ.representation.inv_self_apply ⟨(g : G), hg⟩ (v : σ)
  right_inv v := σ.representation.self_inv_apply ⟨(g : G), hg⟩ v
  map_add' := map_add _
  map_smul' := map_smul _
  isIntertwining' m := by
    change σ.representation ⟨(g : G), hg⟩ *
        σ.representation (normalizerConjugation g m) =
      σ.representation m * σ.representation ⟨(g : G), hg⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (g : G) * ((g : G)⁻¹ * (m : G) * (g : G)) = (m : G) * (g : G)
    group

/-- Regularity says that precisely the inner normalizer elements fix the class. -/
theorem isNormalizerRegular_iff (σ : SmoothRep.{0, uG, uV} ℂ M) :
    IsNormalizerRegular σ ↔
      ∀ g : Subgroup.normalizer (M : Set G),
        Nonempty ((normalizerConjugate g σ).representation.Equiv σ.representation) ↔
          (g : G) ∈ M := by
  constructor
  · intro h g
    exact ⟨fun he => by_contra fun hg => h g hg he,
      fun hg => ⟨normalizerConjugateInnerEquiv σ g hg⟩⟩
  · intro h g hg he
    exact hg ((h g).mp he)

/-- Conjugation by an actual normalizer preserves and reflects irreducibility. -/
theorem normalizerConjugate_isIrreducible_iff
    (σ : SmoothRep.{0, uG, uV} ℂ M) (g : Subgroup.normalizer (M : Set G)) :
    (normalizerConjugate g σ).IsIrreducible ↔ σ.IsIrreducible :=
  isIrreducible_comp_continuousMulEquiv_iff σ.representation (normalizerConjugation g)

/-- For a regular irreducible representation, the nonidentity normalizer
conjugates contribute no intertwiners into the original representation. -/
theorem normalizerConjugate_hom_eq_zero
    (σ : SmoothRep.{0, uG, uV} ℂ M) (hσ : σ.IsIrreducible)
    (hreg : IsNormalizerRegular σ)
    (g : Subgroup.normalizer (M : Set G)) (hg : (g : G) ∉ M)
    (f : (normalizerConjugate g σ).representation.IntertwiningMap σ.representation) :
    f = 0 := by
  let := hσ
  let := (normalizerConjugate_isIrreducible_iff σ g).mpr hσ
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hf | hf
  · exact (hreg g hg ⟨f.ofBijective hf⟩).elim
  · exact hf

/-- The central character of the actual normalizer conjugate. -/
def normalizerConjugateCentralCharacter (g : Subgroup.normalizer (M : Set G))
    (ω : Subgroup.center M →* ℂˣ) : Subgroup.center M →* ℂˣ :=
  ω.comp (Subgroup.centerCongr (normalizerConjugation g).toMulEquiv).toMonoidHom

theorem normalizerConjugate_hasCentralCharacter
    (σ : SmoothRep.{0, uG, uV} ℂ M) (ω : Subgroup.center M →* ℂˣ)
    (hω : σ.HasCentralCharacter ω) (g : Subgroup.normalizer (M : Set G)) :
    (normalizerConjugate g σ).HasCentralCharacter
      (normalizerConjugateCentralCharacter g ω) := by
  intro z v
  exact hω (Subgroup.centerCongr (normalizerConjugation g).toMulEquiv z) v

/-- Separation of central characters is a sufficient condition for actual
normalizer regularity. No irreducibility or admissibility is needed here. -/
theorem isNormalizerRegular_of_centralCharacter
    (σ : SmoothRep.{0, uG, uV} ℂ M) [Nontrivial σ]
    (ω : Subgroup.center M →* ℂˣ) (hω : σ.HasCentralCharacter ω)
    (hsep : ∀ g : Subgroup.normalizer (M : Set G), (g : G) ∉ M →
      normalizerConjugateCentralCharacter g ω ≠ ω) :
    IsNormalizerRegular σ := by
  intro g hg ⟨e⟩
  apply hsep g hg
  ext z
  obtain ⟨v, hv⟩ := exists_ne (0 : σ)
  have hev : e v ≠ 0 := fun h => hv (e.injective (h.trans (map_zero e).symm))
  apply smul_left_injective ℂ hev
  calc
    _ = e ((normalizerConjugateCentralCharacter g ω z : ℂ) •
        (v : normalizerConjugate g σ)) := (e.map_smul _ _).symm
    _ = e ((normalizerConjugate g σ).representation (z : M) v) :=
      congrArg e (normalizerConjugate_hasCentralCharacter σ ω hω g z v).symm
    _ = σ.representation (z : M) (e v) :=
      Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (z : M) v
    _ = _ := hω z (e v)

end Langlands.Aubert.General
