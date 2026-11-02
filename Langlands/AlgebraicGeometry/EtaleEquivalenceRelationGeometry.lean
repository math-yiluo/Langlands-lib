import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Structural morphisms of étale equivalence relations

The existential scheme-valued relation axioms determine unique unit, inverse, and
composition morphisms. These constructions provide the scheme-level interface used for
the stratification in Stacks Tags 0BBN and 07ST, without choosing a quotient space.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u})

/-- A map to the relation scheme is determined by its two endpoints. -/
lemma hom_ext {T : Scheme.{u}} {a b : T ⟶ E.R}
    (ht : a ≫ E.t = b ≫ E.t) (hs : a ≫ E.s = b ≫ E.s) : a = b := by
  let := E.mono_lift
  apply (cancel_mono (prod.lift E.t E.s)).mp
  apply prod.hom_ext
  · simpa using ht
  · simpa using hs

/-- The identity arrow of the relation. -/
noncomputable def unit : E.U ⟶ E.R :=
  (E.refl E.U (𝟙 E.U)).choose

@[reassoc (attr := simp)]
lemma unit_t : E.unit ≫ E.t = 𝟙 E.U :=
  (E.refl E.U (𝟙 E.U)).choose_spec.1

@[reassoc (attr := simp)]
lemma unit_s : E.unit ≫ E.s = 𝟙 E.U :=
  (E.refl E.U (𝟙 E.U)).choose_spec.2

/-- Reversal of arrows in the relation. -/
noncomputable def inverse : E.R ⟶ E.R :=
  (E.symm E.R (𝟙 E.R)).choose

@[reassoc (attr := simp)]
lemma inverse_t : E.inverse ≫ E.t = E.s := by
  simpa only [inverse, Category.id_comp] using (E.symm E.R (𝟙 E.R)).choose_spec.1

@[reassoc (attr := simp)]
lemma inverse_s : E.inverse ≫ E.s = E.t := by
  simpa only [inverse, Category.id_comp] using (E.symm E.R (𝟙 E.R)).choose_spec.2

@[reassoc (attr := simp)]
lemma inverse_inverse : E.inverse ≫ E.inverse = 𝟙 E.R := by
  apply E.hom_ext <;> simp

/-- Reversal is an involutive isomorphism of the relation scheme. -/
noncomputable def inverseIso : E.R ≅ E.R where
  hom := E.inverse
  inv := E.inverse
  hom_inv_id := E.inverse_inverse
  inv_hom_id := E.inverse_inverse

/-- Composition of arrows `(x,y)` and `(y,z)`, with the first arrow written first. -/
noncomputable def composition : pullback E.s E.t ⟶ E.R :=
  (E.trans (pullback E.s E.t) (pullback.fst E.s E.t) (pullback.snd E.s E.t)
    pullback.condition).choose

@[reassoc (attr := simp)]
lemma composition_t : E.composition ≫ E.t = pullback.fst E.s E.t ≫ E.t :=
  (E.trans (pullback E.s E.t) (pullback.fst E.s E.t) (pullback.snd E.s E.t)
    pullback.condition).choose_spec.1

@[reassoc (attr := simp)]
lemma composition_s : E.composition ≫ E.s = pullback.snd E.s E.t ≫ E.s :=
  (E.trans (pullback E.s E.t) (pullback.fst E.s E.t) (pullback.snd E.s E.t)
    pullback.condition).choose_spec.2

/-- The composite of two composable maps to the relation. -/
noncomputable def compose {T : Scheme.{u}} (a b : T ⟶ E.R)
    (h : a ≫ E.s = b ≫ E.t) : T ⟶ E.R :=
  pullback.lift a b h ≫ E.composition

@[reassoc (attr := simp)]
lemma compose_t {T : Scheme.{u}} (a b : T ⟶ E.R)
    (h : a ≫ E.s = b ≫ E.t) : E.compose a b h ≫ E.t = a ≫ E.t := by
  simp only [compose, Category.assoc, composition_t]
  rw [← Category.assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma compose_s {T : Scheme.{u}} (a b : T ⟶ E.R)
    (h : a ≫ E.s = b ≫ E.t) : E.compose a b h ≫ E.s = b ≫ E.s := by
  simp only [compose, Category.assoc, composition_s]
  rw [← Category.assoc, pullback.lift_snd]

lemma compose_unit_left {T : Scheme.{u}} (a : T ⟶ E.R) :
    E.compose (a ≫ E.t ≫ E.unit) a (by simp) = a := by
  apply E.hom_ext <;> simp

lemma compose_unit_right {T : Scheme.{u}} (a : T ⟶ E.R) :
    E.compose a (a ≫ E.s ≫ E.unit) (by simp) = a := by
  apply E.hom_ext <;> simp

lemma compose_assoc {T : Scheme.{u}} (a b c : T ⟶ E.R)
    (hab : a ≫ E.s = b ≫ E.t) (hbc : b ≫ E.s = c ≫ E.t) :
    E.compose (E.compose a b hab) c (by simpa using hbc) =
      E.compose a (E.compose b c hbc) (by simpa using hab) := by
  apply E.hom_ext <;> simp

lemma compose_inverse_right {T : Scheme.{u}} (a : T ⟶ E.R) :
    E.compose a (a ≫ E.inverse) (by simp) = a ≫ E.t ≫ E.unit := by
  apply E.hom_ext <;> simp

lemma compose_inverse_left {T : Scheme.{u}} (a : T ⟶ E.R) :
    E.compose (a ≫ E.inverse) a (by simp) = a ≫ E.s ≫ E.unit := by
  apply E.hom_ext <;> simp

/-- A map commuting with the endpoints also commutes with reversal. -/
lemma inverse_naturality {F : EtaleEquivalenceRelation.{u}}
    (f : E.U ⟶ F.U) (g : E.R ⟶ F.R)
    (ht : g ≫ F.t = E.t ≫ f) (hs : g ≫ F.s = E.s ≫ f) :
    E.inverse ≫ g = g ≫ F.inverse := by
  apply F.hom_ext <;> simp [ht, hs]

/-- The identity morphism is cartesian. -/
lemma isCartesianHom_id :
    IsCartesianHom E E (𝟙 E.U) (𝟙 E.R) :=
  ⟨by simp, IsPullback.of_id_fst⟩

/-- Cartesian relation morphisms compose. -/
lemma IsCartesianHom.comp {E₁ E₂ E₃ : EtaleEquivalenceRelation.{u}}
    {f₁ : E₁.U ⟶ E₂.U} {g₁ : E₁.R ⟶ E₂.R}
    {f₂ : E₂.U ⟶ E₃.U} {g₂ : E₂.R ⟶ E₃.R}
    (h₁ : IsCartesianHom E₁ E₂ f₁ g₁) (h₂ : IsCartesianHom E₂ E₃ f₂ g₂) :
    IsCartesianHom E₁ E₃ (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  refine ⟨?_, h₁.2.paste_horiz h₂.2⟩
  rw [Category.assoc, h₂.1, ← Category.assoc, h₁.1, Category.assoc]

/-- The target square of a cartesian relation morphism is also cartesian. -/
lemma IsCartesianHom.isPullback_t {F : EtaleEquivalenceRelation.{u}}
    {f : E.U ⟶ F.U} {g : E.R ⟶ F.R} (h : IsCartesianHom E F f g) :
    IsPullback g E.t F.t f := by
  apply h.2.of_iso E.inverseIso F.inverseIso (Iso.refl _) (Iso.refl _)
  · exact (E.inverse_naturality f g h.1 h.2.w).symm
  · simp [inverseIso]
  · simp [inverseIso]
  · simp

/-- The relation scheme is affine whenever the object scheme is affine and the
relation is a closed subscheme of its absolute square. -/
lemma isAffine_relation [IsAffine E.U] [IsClosedImmersion (prod.lift E.t E.s)] :
    IsAffine E.R := by
  let : IsAffine (E.U ⨯ E.U) :=
    .of_isPullback (IsPullback.of_hasBinaryProduct' E.U E.U)
  exact
  isAffine_of_isAffineHom (prod.lift E.t E.s)

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
