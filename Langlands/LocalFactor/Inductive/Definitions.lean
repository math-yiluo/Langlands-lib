import Langlands.VirtualRepresentation.ExactInduction
import Langlands.VirtualRepresentation.ExactRestriction
import Langlands.Weil.Local.ExtensionWeilRange
import Langlands.Weil.Representation.CharacterLine
import Langlands.Weil.Representation.InductionContinuity

/-!
# Inductive functions of Weil representations (Tate 1979, section 2.3.2)

A finite extension of a p-adic field `F` is a p-adic field `E` with an embedding
`F → E` over `ℚ_p`. Its Weil group `W_E` maps to `W_F` by the Library's actual Weil
map, an open embedding with finite-index range. Representations are continuous
finite-dimensional complex representations, `R(W_E)` is the published
exact-relation virtual group, and `Ind_{E'/E}` is the published induction along
the Weil map. The predicates are Tate's additivity, inductivity, and inductivity
in degree zero.
-/

noncomputable section

namespace Langlands.LocalFactor.Inductive

universe u v

open FiniteRepresentation VirtualRepresentation Weil.Local

section Weil

variable {p : ℕ} [Fact p.Prime]

/-- Tate's representations of `W_E`: continuous, on finite-dimensional complex
spaces in the universe of `E`. -/
abbrev IsRepresentation (E : PadicField.{u} p)
    (A : FiniteRepresentation.{0, u, u} ℂ (localWeilGroup E)) : Prop :=
  A.IsContinuous

/-- Tate's `M(W_E)`: isomorphism classes of representations of `W_E`. -/
abbrev Classes (E : PadicField.{u} p) := IsomorphismClassesWith (IsRepresentation E)

/-- Tate's `R(W_E)`: the exact-relation virtual group of representations of `W_E`. -/
abbrev Virtual (E : PadicField.{u} p) := ExactGrothendieckGroup (IsRepresentation E)

/-- Tate's `R⁰(W_E)`: virtual representations of degree zero. -/
abbrev VirtualDegreeZero (E : PadicField.{u} p) : Submodule ℤ (Virtual E) :=
  ExactGrothendieckGroup.degreeZero (IsRepresentation E)

/-- The class of a representation of `W_E` in `R(W_E)`, Tate's `[V]`. -/
abbrev virtualClass (E : PadicField.{u} p) : Classes E → Virtual E :=
  ExactGrothendieckGroup.ofClass (IsRepresentation E)

/-- The class of the one-dimensional representation given by a quasi-character
`χ` of `W_E`, on the Library's character line. -/
def characterClass (E : PadicField.{u} p) (χ : localWeilGroup E →ₜ* ℂˣ) : Classes E :=
  Quotient.mk _ (continuousCharacterLine χ)

/-- The class `[1_E]` of the trivial one-dimensional representation. -/
abbrev trivialClass (E : PadicField.{u} p) : Classes E := characterClass E 1

theorem rank_characterClass (E : PadicField.{u} p) (χ : localWeilGroup E →ₜ* ℂˣ) :
    classRank (forgetPropertyClass (IsRepresentation E) (characterClass E χ)) = 1 :=
  characterLine_rank χ.toMonoidHom

variable (E E' : PadicField.{u} p) (g : E.Carrier →ₐ[Padic p] E'.Carrier)

/-- Induction `Ind_{E'/E}` on isomorphism classes, along the actual Weil map
`W_{E'} → W_E` of the embedding `g`. -/
def induceClass : Classes E' → Classes E :=
  continuousInduceAlongClass (extensionWeilMap E E' g).toMonoidHom
    (extensionWeilMap_isOpenEmbedding E E' g)

theorem induceClass_isExactAdditive :
    ExactGrothendieckGroup.IsExactAdditive (IsRepresentation E')
      (fun c => ExactGrothendieckGroup.ofClass (IsRepresentation E) (induceClass E E' g c)) := by
  intro A B C f k hfk
  exact ExactGrothendieckGroup.ofRepresentation_shortExact (IsRepresentation E)
    (isShortExact_induce _ ((isShortExact_restrict_iff _ f k).mpr hfk))

/-- Tate's `Ind_{E'/E} : R(W_{E'}) → R(W_E)`. -/
def virtualInduce : Virtual E' →ₗ[ℤ] Virtual E :=
  ExactGrothendieckGroup.lift (IsRepresentation E')
    (fun c => ExactGrothendieckGroup.ofClass (IsRepresentation E) (induceClass E E' g c))
    (induceClass_isExactAdditive E E' g)

theorem virtualInduce_virtualClass (c : Classes E') :
    virtualInduce E E' g (virtualClass E' c) = virtualClass E (induceClass E E' g c) :=
  ExactGrothendieckGroup.lift_ofClass _ _ _ _

/-- Induction of the class of an actual representation. -/
theorem virtualInduce_ofRepresentation
    (A : {A : FiniteRepresentation.{0, u, u} ℂ (localWeilGroup E') // A.IsContinuous}) :
    virtualInduce E E' g (ExactGrothendieckGroup.ofRepresentation (IsRepresentation E') A) =
      ExactGrothendieckGroup.ofRepresentation (IsRepresentation E)
        ⟨induceAlong (extensionWeilMap E E' g).toMonoidHom (extensionWeilMap_injective E E' g)
            A.val,
          isContinuous_induceAlong _ (extensionWeilMap_isOpenEmbedding E E' g) A.property⟩ :=
  ExactGrothendieckGroup.lift_ofClass _ _ _ _

/-- Induction multiplies the virtual degree by `[E' : E]`. -/
theorem degree_virtualInduce (x : Virtual E') :
    ExactGrothendieckGroup.degree (IsRepresentation E) (virtualInduce E E' g x) =
      (extensionDegree E E' g : ℤ) * ExactGrothendieckGroup.degree (IsRepresentation E') x := by
  have hc : (ExactGrothendieckGroup.degree (IsRepresentation E)).comp (virtualInduce E E' g) =
      (extensionDegree E E' g : ℤ) • ExactGrothendieckGroup.degree (IsRepresentation E') := by
    apply ExactGrothendieckGroup.hom_ext
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change ExactGrothendieckGroup.degree (IsRepresentation E)
          (virtualInduce E E' g (ExactGrothendieckGroup.ofRepresentation _ A)) =
        (extensionDegree E E' g : ℤ) *
          ExactGrothendieckGroup.degree (IsRepresentation E')
            (ExactGrothendieckGroup.ofRepresentation _ A)
      rw [virtualInduce_ofRepresentation, ExactGrothendieckGroup.degree_ofRepresentation,
        ExactGrothendieckGroup.degree_ofRepresentation]
      rw [rank_induceAlong, extensionWeilMap_range_index, Nat.cast_mul]
  exact LinearMap.congr_fun hc x

variable (F : PadicField.{u} p)

/-- A finite extension of `F`: a p-adic field with an embedding of `F` over `ℚ_p`. -/
structure Extension where
  /-- The extension field. -/
  field : PadicField.{u} p
  /-- The embedding of `F`. -/
  embedding : F.Carrier →ₐ[Padic p] field.Carrier

variable {F}

/-- An embedding `E → E'` of extensions of `F` over `F`: the tower `E'/E/F`. -/
def IsTower (E E' : Extension F) (g : E.field.Carrier →ₐ[Padic p] E'.field.Carrier) : Prop :=
  g.comp E.embedding = E'.embedding

variable (F) (X : Type v) [AddCommGroup X]

/-- Tate's data `λ`: an element of `X` for every finite extension `E` of `F` and every
class `V ∈ M(W_E)`. Multiplicative targets such as `ℂˣ` are used through `Additive`. -/
abbrev ClassFunction := ∀ E : Extension F, Classes E.field → X

/-- Tate 2.3.2: additivity on every actual short exact sequence over every `E`. -/
def IsAdditive (a : ClassFunction F X) : Prop :=
  ∀ E : Extension F, ExactGrothendieckGroup.IsExactAdditive (IsRepresentation E.field) (a E)

/-- The extension of an additive function to the homomorphism `R(W_E) → X`. -/
def virtualExtension (a : ClassFunction F X) (ha : IsAdditive F X a) (E : Extension F) :
    Virtual E.field →ₗ[ℤ] X :=
  ExactGrothendieckGroup.lift (IsRepresentation E.field) (a E) (ha E)

/-- Tate 2.3.2: `λ` is inductive if it is additive and `λ_E ∘ Ind_{E'/E} = λ_{E'}` on
`R(W_{E'})` for every tower `E'/E/F`. -/
def IsInductive (a : ClassFunction F X) : Prop :=
  ∃ ha : IsAdditive F X a, ∀ (E E' : Extension F) (g : E.field.Carrier →ₐ[Padic p] E'.field.Carrier),
    IsTower E E' g →
      (virtualExtension F X a ha E).comp (virtualInduce E.field E'.field g) =
        virtualExtension F X a ha E'

/-- Tate 2.3.2: `λ` is inductive in degree zero if it is additive and
`λ_E ∘ Ind_{E'/E} = λ_{E'}` on `R⁰(W_{E'})` for every tower `E'/E/F`. -/
def IsInductiveInDegreeZero (a : ClassFunction F X) : Prop :=
  ∃ ha : IsAdditive F X a, ∀ (E E' : Extension F) (g : E.field.Carrier →ₐ[Padic p] E'.field.Carrier),
    IsTower E E' g → ∀ x ∈ VirtualDegreeZero E'.field,
      virtualExtension F X a ha E (virtualInduce E.field E'.field g x) =
        virtualExtension F X a ha E' x

end Weil

end Langlands.LocalFactor.Inductive
