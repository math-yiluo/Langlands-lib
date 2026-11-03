import Langlands.GroupScheme.Torus.Grouplike

/-! # Twisting characters by grouplike families, and conjugation of character points

A homomorphism `s : Multiplicative M →* B[M]ˣ` with grouplike values twists the characters
`t : Multiplicative M →* Dˣ` over every `B`-algebra `x : B ⟶ D` into the characters
`m ↦ evaluate x t (s m)`. This is the action of an endomorphism of the diagonalizable group
`D(M)` over `B` on its points. Grouplike families lift uniquely along nilpotent ideals.

A point `g` of a group functor normalizing an embedded diagonalizable group induces such a
twist: conjugation by `g` on the embedded characters is the twist by the grouplike family
`conjUniversal`.
-/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]

section Twist

variable {B : CommAlgCat.{u} R}

/-- Twisting a character `t` over a `B`-algebra `x : B ⟶ D` by a family `s` of elements of
`B[M]`: the character `m ↦ evaluate x t (s m)`. -/
def twist (s : Multiplicative M →* (algebra (M := M) B)ˣ) {D : CommAlgCat.{u} R} (x : B ⟶ D)
    (t : Multiplicative M →* Dˣ) : Multiplicative M →* Dˣ :=
  mapCharacter (evaluate x t) s

theorem twist_apply (s : Multiplicative M →* (algebra (M := M) B)ˣ) {D : CommAlgCat.{u} R}
    (x : B ⟶ D) (t : Multiplicative M →* Dˣ) (m : Multiplicative M) :
    ((twist s x t m : Dˣ) : D) = (evaluate x t).hom (s m : AddMonoidAlgebra B M) :=
  rfl

/-- A family with grouplike values. -/
def IsGrouplikeHom (s : Multiplicative M →* (algebra (M := M) B)ˣ) : Prop :=
  ∀ m, IsGrouplike (M := M) (B := B) (s m)

variable {s : Multiplicative M →* (algebra (M := M) B)ˣ}

theorem twist_mul (hs : IsGrouplikeHom s) {D : CommAlgCat.{u} R} (x : B ⟶ D)
    (t t' : Multiplicative M →* Dˣ) : twist s x (t * t') = twist s x t * twist s x t' :=
  MonoidHom.ext fun m => Units.ext ((hs m).evaluate_mul x t t')

theorem twist_one (hs : IsGrouplikeHom s) {D : CommAlgCat.{u} R} (x : B ⟶ D) :
    twist s x 1 = 1 :=
  MonoidHom.ext fun m => Units.ext ((hs m).evaluate_one x)

theorem mapCharacter_twist {D D' : CommAlgCat.{u} R} (x : B ⟶ D) (t : Multiplicative M →* Dˣ)
    (f : D ⟶ D') : mapCharacter f (twist s x t) = twist s (x ≫ f) (mapCharacter f t) := by
  rw [twist, twist, mapCharacter_mapCharacter, evaluate_comp]

theorem twist_coefficientMap {B' D : CommAlgCat.{u} R} (π : B ⟶ B') (x : B' ⟶ D)
    (t : Multiplicative M →* Dˣ) :
    twist (mapCharacter (coefficientMap (M := M) π) s) x t = twist s (π ≫ x) t := by
  rw [twist, twist, mapCharacter_mapCharacter, coefficientMap_evaluate]

theorem mapCharacter_id {D : CommAlgCat.{u} R} (t : Multiplicative M →* Dˣ) :
    mapCharacter (𝟙 D) t = t := by
  ext m
  rfl

theorem twist_constant_universal : twist s (constant B) (universal B) = s := by
  rw [twist, evaluate_constant_universal, mapCharacter_id]

/-- Twisting by the universal monomials is the identity. -/
theorem twist_universal {D : CommAlgCat.{u} R} (x : B ⟶ D) (t : Multiplicative M →* Dˣ) :
    twist (universal (M := M) B) x t = t :=
  mapCharacter_evaluate_universal x t

theorem evaluate_mul_of_twist_mul {D : CommAlgCat.{u} R} {x : B ⟶ D}
    {t t' : Multiplicative M →* Dˣ} (h : twist s x (t * t') = twist s x t * twist s x t')
    (m : Multiplicative M) :
    (evaluate x (t * t')).hom (s m : AddMonoidAlgebra B M) =
      (evaluate x t).hom (s m : AddMonoidAlgebra B M) *
        (evaluate x t').hom (s m : AddMonoidAlgebra B M) := by
  have e := congrArg (fun χ : Multiplicative M →* Dˣ => ((χ m : Dˣ) : D)) h
  rw [MonoidHom.mul_apply, Units.val_mul] at e
  exact e

/-- **Converse grouplike criterion**: a family whose twists are multiplicative and unital
in the character has grouplike values. -/
theorem isGrouplikeHom_of_twist
    (h_mul : ∀ (D : CommAlgCat.{u} R) (x : B ⟶ D) (t t' : Multiplicative M →* Dˣ),
      twist s x (t * t') = twist s x t * twist s x t')
    (h_one : ∀ (D : CommAlgCat.{u} R) (x : B ⟶ D), twist s x 1 = 1) :
    IsGrouplikeHom s := by
  intro m
  refine ⟨?_, ?_⟩
  · have h := evaluate_mul_of_twist_mul
      (h_mul (algebra (M := M) (algebra (M := M) B))
        (constant (M := M) B ≫ constant (M := M) (algebra (M := M) B))
        (universal (M := M) (algebra (M := M) B))
        (mapCharacter (constant (M := M) (algebra (M := M) B)) (universal (M := M) B))) m
    have e₁ : evaluate (constant (M := M) B ≫ constant (M := M) (algebra (M := M) B))
        (mapCharacter (constant (M := M) (algebra (M := M) B)) (universal (M := M) B)) =
          constant (M := M) (algebra (M := M) B) := by
      rw [← evaluate_comp, evaluate_constant_universal, Category.id_comp]
    have e₂ : evaluate (constant (M := M) B ≫ constant (M := M) (algebra (M := M) B))
        (universal (M := M) (algebra (M := M) B)) = coefficientMap (constant (M := M) B) := rfl
    rw [e₁, e₂] at h
    rw [diagonalMap, h, mul_comm]
  · have e := congrArg (fun χ : Multiplicative M →* Bˣ => ((χ m : Bˣ) : B)) (h_one B (𝟙 B))
    exact e

/-- Composite of twists. -/
theorem twist_twist {s' : Multiplicative M →* (algebra (M := M) B)ˣ} {D : CommAlgCat.{u} R}
    (x : B ⟶ D) (t : Multiplicative M →* Dˣ) :
    twist s x (twist s' x t) = twist (twist s (constant B) s') x t := by
  ext m
  change (evaluate x (twist s' x t)).hom (s m) =
    (evaluate x t).hom ((evaluate (constant B) s').hom (s m))
  rw [← CommAlgCat.comp_apply, evaluate_comp, constant_evaluate]
  rfl

theorem IsGrouplikeHom.twist (hs : IsGrouplikeHom s) {s' : Multiplicative M →* (algebra (M := M) B)ˣ}
    (hs' : IsGrouplikeHom s') : IsGrouplikeHom (twist s (constant B) s') :=
  isGrouplikeHom_of_twist
    (fun D x t t' => by
      rw [← twist_twist, ← twist_twist, ← twist_twist, twist_mul hs' x, twist_mul hs x])
    (fun D x => by rw [← twist_twist, twist_one hs', twist_one hs])

theorem isGrouplikeHom_universal : IsGrouplikeHom (universal (M := M) B) :=
  isGrouplikeHom_of_twist (fun D x t t' => by rw [twist_universal, twist_universal,
    twist_universal]) (fun D x => twist_universal x 1)

end Twist

section Lift

variable {C D : CommAlgCat.{u} R} (π : C ⟶ D) (hker : ∀ x, π.hom x = 0 → IsNilpotent x)
include hker

/-- Grouplike families are determined by their reduction along a nilpotent kernel. -/
theorem isGrouplikeHom_lift_unique {s s' : Multiplicative M →* (algebra (M := M) C)ˣ}
    (hs : IsGrouplikeHom s) (hs' : IsGrouplikeHom s')
    (h : mapCharacter (coefficientMap (M := M) π) s = mapCharacter (coefficientMap π) s') :
    s = s' :=
  MonoidHom.ext fun m => Units.ext (isGrouplike_lift_unique π hker (hs m) (hs' m)
    (congrArg (fun χ : Multiplicative M →* (algebra (M := M) D)ˣ =>
      ((χ m : (algebra (M := M) D)ˣ) : AddMonoidAlgebra D M)) h))

/-- **Grouplike families lift** along a surjection with nilpotent kernel. -/
theorem exists_isGrouplikeHom_lift (hπ : Function.Surjective π.hom)
    {s : Multiplicative M →* (algebra (M := M) D)ˣ} (hs : IsGrouplikeHom s) :
    ∃ s' : Multiplicative M →* (algebra (M := M) C)ˣ, IsGrouplikeHom s' ∧
      mapCharacter (coefficientMap (M := M) π) s' = s := by
  choose v hv hvπ using fun m => exists_isGrouplike_lift (M := M) π hπ hker (hs m)
  let s' : Multiplicative M →* (algebra (M := M) C)ˣ :=
    { toFun := fun m => (hv m).isUnit.unit
      map_one' := Units.ext <| isGrouplike_lift_unique π hker (hv 1) IsGrouplike.one (by
        show (coefficientMap (M := M) π).hom (v 1) = (coefficientMap (M := M) π).hom 1
        rw [hvπ, map_one, Units.val_one, map_one])
      map_mul' := fun a b => Units.ext <| isGrouplike_lift_unique π hker (hv (a * b))
        ((hv a).mul (hv b)) (by
          show (coefficientMap (M := M) π).hom (v (a * b)) =
            (coefficientMap (M := M) π).hom (v a * v b)
          rw [hvπ, map_mul, map_mul, hvπ, hvπ, Units.val_mul]) }
  exact ⟨s', fun m => hv m, MonoidHom.ext fun m => Units.ext (hvπ m)⟩

end Lift

section Conjugation

/-- A natural injective embedding of the characters `Multiplicative M →* Dˣ` into the points
`F D` of a group functor: the points of an embedded diagonalizable group. -/
structure CharacterEmbedding (F : CommAlgCat.{u} R ⥤ GrpCat.{u}) (M : Type u)
    [AddCommGroup M] where
  /-- The embedding on points over each algebra. -/
  hom : ∀ D : CommAlgCat.{u} R, (Multiplicative M →* Dˣ) →* F.obj D
  /-- Naturality in the algebra. -/
  naturality : ∀ {D D' : CommAlgCat.{u} R} (f : D ⟶ D') (t : Multiplicative M →* Dˣ),
    F.map f (hom D t) = hom D' (mapCharacter f t)
  /-- Injectivity on points over each algebra. -/
  injective : ∀ D : CommAlgCat.{u} R, Function.Injective (hom D)

variable {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} (ι : CharacterEmbedding F M)

/-- The subgroups of embedded characters. -/
def CharacterEmbedding.range (D : CommAlgCat.{u} R) : Subgroup (F.obj D) :=
  (ι.hom D).range

variable {A : CommAlgCat.{u} R} {g : F.obj A}
  (hg : ∀ (D : CommAlgCat.{u} R) (f : A ⟶ D) (t : Multiplicative M →* Dˣ),
    ∃ t', ι.hom D t' = F.map f g * ι.hom D t * (F.map f g)⁻¹)

/-- Conjugation by a point `g` normalizing the embedded characters, as a map on characters. -/
def conjChar {D : CommAlgCat.{u} R} (f : A ⟶ D) (t : Multiplicative M →* Dˣ) :
    Multiplicative M →* Dˣ :=
  Classical.choose (hg D f t)

theorem hom_conjChar {D : CommAlgCat.{u} R} (f : A ⟶ D) (t : Multiplicative M →* Dˣ) :
    ι.hom D (conjChar ι hg f t) = F.map f g * ι.hom D t * (F.map f g)⁻¹ :=
  Classical.choose_spec (hg D f t)

theorem conjChar_mul {D : CommAlgCat.{u} R} (f : A ⟶ D) (t t' : Multiplicative M →* Dˣ) :
    conjChar ι hg f (t * t') = conjChar ι hg f t * conjChar ι hg f t' := by
  apply ι.injective D
  rw [map_mul, hom_conjChar, hom_conjChar, hom_conjChar, map_mul]
  group

theorem conjChar_one {D : CommAlgCat.{u} R} (f : A ⟶ D) : conjChar ι hg f 1 = 1 := by
  apply ι.injective D
  rw [hom_conjChar, map_one, mul_one, mul_inv_cancel]

theorem mapCharacter_conjChar {D D' : CommAlgCat.{u} R} (f : A ⟶ D) (f' : D ⟶ D')
    (t : Multiplicative M →* Dˣ) :
    mapCharacter f' (conjChar ι hg f t) = conjChar ι hg (f ≫ f') (mapCharacter f' t) := by
  apply ι.injective D'
  rw [← ι.naturality, hom_conjChar, hom_conjChar, map_mul, map_mul, map_inv, ι.naturality,
    F.map_comp, ConcreteCategory.comp_apply]

/-- The universal conjugated character, over the group algebra `A[M]`. -/
def conjUniversal : Multiplicative M →* (algebra (M := M) A)ˣ :=
  conjChar ι hg (constant A) (universal A)

/-- Conjugation of characters is the twist by the universal conjugated character. -/
theorem conjChar_eq_twist {D : CommAlgCat.{u} R} (f : A ⟶ D) (t : Multiplicative M →* Dˣ) :
    conjChar ι hg f t = twist (conjUniversal ι hg) f t := by
  have h := mapCharacter_conjChar ι hg (constant A) (evaluate f t) (universal A)
  rw [constant_evaluate, mapCharacter_evaluate_universal] at h
  rw [← h]
  rfl

/-- The universal conjugated character has grouplike values. -/
theorem isGrouplikeHom_conjUniversal : IsGrouplikeHom (conjUniversal ι hg) :=
  isGrouplikeHom_of_twist
    (fun D x t t' => by
      rw [← conjChar_eq_twist, ← conjChar_eq_twist, ← conjChar_eq_twist, conjChar_mul])
    (fun D x => by rw [← conjChar_eq_twist, conjChar_one])

end Conjugation

end Langlands.GroupScheme.CharacterAction
