import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RepresentationTheory.Rep.Basic

/-! # Galois coverings on a site -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w'

variable {C : Type u} [Category.{v} C]

namespace GaloisCovering

/-- The sieve of arrows `h` into `U` along which `g` becomes a deck translate of `f`. -/
def transitivitySieve {Γ : Type w} {V' : C} (deck : Γ → (V' ⟶ V')) {U : C}
    (f g : U ⟶ V') : Sieve U where
  arrows _ h := ∃ γ : Γ, h ≫ g = h ≫ f ≫ deck γ
  downward_closed := by
    rintro W W' h ⟨γ, hγ⟩ k
    exact ⟨γ, by rw [Category.assoc, hγ, Category.assoc]⟩

end GaloisCovering

/-- A Galois covering `p : V' ⟶ V` with group `Γ` acting on `V'` over `V`. The arrow
`p` covers `V`. Any two arrows to `V'` with the same composite to `V` agree up to a
deck transformation locally. A deck transformation other than the identity fixes an
arrow `U ⟶ V'` only when the empty sieve covers `U`. -/
structure GaloisCovering (J : GrothendieckTopology C)
    (Γ : Type w) [Group Γ] (V' V : C) where
  p : V' ⟶ V
  covering : Sieve.ofArrows (fun _ : Unit => V') (fun _ => p) ∈ J V
  deck : Γ → (V' ⟶ V')
  deck_one : deck 1 = 𝟙 V'
  deck_mul : ∀ γ δ : Γ, deck (γ * δ) = deck δ ≫ deck γ
  deck_comp : ∀ γ : Γ, deck γ ≫ p = p
  locally_transitive : ∀ {U : C} (f g : U ⟶ V'), f ≫ p = g ≫ p →
    GaloisCovering.transitivitySieve deck f g ∈ J U
  locally_free : ∀ {U : C} (f : U ⟶ V') (γ : Γ), f ≫ deck γ = f → γ = 1 ∨ ⊥ ∈ J U

namespace GaloisCovering

variable {J : GrothendieckTopology C} {Γ : Type w} [Group Γ] {V' V : C}
variable (G : GaloisCovering J Γ V' V)
variable {R : Type w'} [CommRing R]

/-- Sections of a module sheaf as morphisms from `R`. -/
abbrev sectionHom {M : ModuleCat.{w'} R} (x : M) : ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

theorem map_map_apply (F : Cᵒᵖ ⥤ ModuleCat.{w'} R) {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y)
    (x : F.obj (op X)) : F.map g.op (F.map f.op x) = F.map (g ≫ f).op x := by
  rw [op_comp, F.map_comp, ConcreteCategory.comp_apply]

theorem sectionHom_apply_one {M : ModuleCat.{w'} R} (x : M) : sectionHom x (1 : R) = x := by
  simp [sectionHom]

theorem sectionHom_comp {M N : ModuleCat.{w'} R} (x : M) (g : M ⟶ N) :
    sectionHom x ≫ g = sectionHom (g x) := by
  ext
  simp [sectionHom]

/-- Separatedness of a module sheaf along a covering sieve, stated for elements. -/
theorem eq_of_sieve {F : Sheaf J (ModuleCat.{w'} R)} {U : C} (S : Sieve U) (hS : S ∈ J U)
    (s t : F.obj.obj (op U))
    (h : ∀ ⦃W : C⦄ (k : W ⟶ U), S k → F.obj.map k.op s = F.obj.map k.op t) : s = t := by
  have he : sectionHom s = sectionHom t := by
    apply F.property.hom_ext ⟨S, hS⟩
    intro I
    rw [sectionHom_comp, sectionHom_comp, h I.f I.hf]
  simpa [sectionHom_apply_one] using congrArg (fun e => e (1 : R)) he

/-- Restrictions of an invariant section along two arrows with the same composite to
`V` agree. -/
theorem map_eq_map_of_invariant (F : Sheaf J (ModuleCat.{w'} R)) (x : F.obj.obj (op V'))
    (hx : ∀ γ : Γ, F.obj.map (G.deck γ).op x = x) {W : C} (a b : W ⟶ V')
    (hab : a ≫ G.p = b ≫ G.p) : F.obj.map a.op x = F.obj.map b.op x := by
  apply eq_of_sieve _ (G.locally_transitive a b hab)
  rintro Z k ⟨γ, hγ⟩
  rw [map_map_apply, map_map_apply, hγ, ← Category.assoc]
  conv_rhs => rw [← map_map_apply, hx γ]

/-- Restriction along a Galois covering is injective. -/
theorem map_p_injective (F : Sheaf J (ModuleCat.{w'} R)) :
    Function.Injective (F.obj.map G.p.op) := by
  intro s t hst
  have he : sectionHom s = sectionHom t := by
    apply F.property.hom_ext_ofArrows (fun _ : Unit => G.p) G.covering
    intro _
    rw [sectionHom_comp, sectionHom_comp, hst]
  simpa [sectionHom_apply_one] using congrArg (fun e => e (1 : R)) he

/-- Galois descent: a deck-invariant section over `V'` comes from a section over `V`. -/
theorem exists_map_p_eq (F : Sheaf J (ModuleCat.{w'} R)) (x : F.obj.obj (op V'))
    (hx : ∀ γ : Γ, F.obj.map (G.deck γ).op x = x) :
    ∃ s : F.obj.obj (op V), F.obj.map G.p.op s = x := by
  let e := F.property.amalgamateOfArrows (fun _ : Unit => G.p) G.covering
    (fun _ => sectionHom x) (by
      intro W i j a b hab
      rw [sectionHom_comp, sectionHom_comp, G.map_eq_map_of_invariant F x hx a b hab])
  refine ⟨e (1 : R), ?_⟩
  have h := F.property.amalgamateOfArrows_map (fun _ : Unit => G.p) G.covering
    (fun _ => sectionHom x) (by
      intro W i j a b hab
      rw [sectionHom_comp, sectionHom_comp, G.map_eq_map_of_invariant F x hx a b hab]) ()
  have h1 := congrArg (fun g => g (1 : R)) h
  simpa [sectionHom_apply_one] using h1

section Representation

variable {R : Type w} [CommRing R]

/-- The left action of `Γ` on sections over `V'`: `γ` acts by restriction along the deck
transformation of `γ⁻¹`. -/
def representation (F : Sheaf J (ModuleCat.{w} R)) : Representation R Γ (F.obj.obj (op V')) where
  toFun γ := (F.obj.map (G.deck γ⁻¹).op).hom
  map_one' := by
    rw [inv_one, G.deck_one, op_id, F.obj.map_id]
    rfl
  map_mul' γ δ := by
    rw [mul_inv_rev, G.deck_mul, op_comp, F.obj.map_comp]
    rfl

@[simp]
theorem representation_apply (F : Sheaf J (ModuleCat.{w} R)) (γ : Γ) (x : F.obj.obj (op V')) :
    G.representation F γ x = F.obj.map (G.deck γ⁻¹).op x := rfl

/-- Sections over `V'` as a representation of `Γ`. -/
abbrev rep (F : Sheaf J (ModuleCat.{w} R)) : Rep.{w} R Γ := Rep.of (G.representation F)

/-- Invariance under the representation is invariance under all deck restrictions. -/
theorem representation_invariant_iff (F : Sheaf J (ModuleCat.{w} R)) (x : F.obj.obj (op V')) :
    (∀ γ : Γ, G.representation F γ x = x) ↔ ∀ γ : Γ, F.obj.map (G.deck γ).op x = x := by
  constructor
  · intro h γ
    simpa using h γ⁻¹
  · intro h γ
    exact h γ⁻¹

end Representation

end GaloisCovering

end Langlands.Cohomology
