import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Comparison of actual homogeneous quotient models

Two effective scheme epimorphisms from the same relative scheme, with the same
fibers on every relative test, have a unique compatible comparison isomorphism.
In particular the construction applies to fpqc quotient projections.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HomogeneousQuotientComparison

variable {S : Scheme.{u}} {X Q R : Over S} (q : X ⟶ Q) (r : X ⟶ R)

/-- Equality on the fibers of a relative morphism also gives equality for
arbitrary underlying scheme maps. -/
theorem scheme_comp_eq_of_fiber_eq
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q → a ≫ r = b ≫ r)
    {T : Scheme.{u}} (a b : T ⟶ X.left)
    (hab : a ≫ q.left = b ≫ q.left) :
    a ≫ r.left = b ≫ r.left := by
  have hb : b ≫ X.hom = a ≫ X.hom := by
    rw [← Over.w q, ← Category.assoc, ← hab, Category.assoc]
  let a₀ : Over.mk (a ≫ X.hom) ⟶ X := Over.homMk a rfl
  let b₀ : Over.mk (a ≫ X.hom) ⟶ X := Over.homMk b hb
  exact congrArg (fun f => f.left) (h _ a₀ b₀ (Over.OverMorphism.ext hab))

variable [EffectiveEpi q.left]

/-- Descend an actual scheme map that is constant on the relative fibers. -/
def descSchemeHom
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q → a ≫ r = b ≫ r) :
    Q.left ⟶ R.left :=
  EffectiveEpi.desc q.left r.left
    (fun a b hab => scheme_comp_eq_of_fiber_eq q r h a b hab)

@[reassoc]
theorem fac_descSchemeHom
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q → a ≫ r = b ≫ r) :
    q.left ≫ descSchemeHom q r h = r.left :=
  EffectiveEpi.fac _ _ _

/-- The descended map is over the original base scheme. -/
def desc
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q → a ≫ r = b ≫ r) :
    Q ⟶ R :=
  Over.homMk (descSchemeHom q r h) (by
    apply (cancel_epi q.left).mp
    rw [fac_descSchemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_desc
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q → a ≫ r = b ≫ r) :
    q ≫ desc q r h = r :=
  Over.OverMorphism.ext (fac_descSchemeHom q r h)

/-- Compatibility with the quotient projection uniquely determines the map. -/
theorem desc_unique
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q → a ≫ r = b ≫ r)
    (f : Q ⟶ R) (hf : q ≫ f = r) : f = desc q r h := by
  let : Epi q := Over.epi_of_epi_left q
  apply (cancel_epi q).mp
  exact hf.trans (fac_desc q r h).symm

variable [EffectiveEpi r.left]

/-- The unique compatible isomorphism between two actual quotient models whose
fibers agree on every relative scheme test. -/
def iso
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q ↔ a ≫ r = b ≫ r) :
    Q ≅ R where
  hom := desc q r (fun T a b hab => (h T a b).mp hab)
  inv := desc r q (fun T a b hab => (h T a b).mpr hab)
  hom_inv_id := by
    let : Epi q := Over.epi_of_epi_left q
    apply (cancel_epi q).mp
    rw [← Category.assoc, fac_desc, fac_desc, Category.comp_id]
  inv_hom_id := by
    let : Epi r := Over.epi_of_epi_left r
    apply (cancel_epi r).mp
    rw [← Category.assoc, fac_desc, fac_desc, Category.comp_id]

@[reassoc]
theorem comp_iso_hom
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q ↔ a ≫ r = b ≫ r) :
    q ≫ (iso q r h).hom = r :=
  fac_desc q r _

@[reassoc]
theorem comp_iso_inv
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q ↔ a ≫ r = b ≫ r) :
    r ≫ (iso q r h).inv = q :=
  fac_desc r q _

/-- The comparison is the only isomorphism compatible with both projections. -/
theorem iso_unique
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q ↔ a ≫ r = b ≫ r)
    (e : Q ≅ R) (he : q ≫ e.hom = r) : e = iso q r h := by
  apply Iso.ext
  exact desc_unique q r _ e.hom he

/-- Existence of lifts on any fixed test scheme is independent of the supplied
quotient model. The source of every lift remains the same actual scheme. -/
theorem forall_lifts_iff
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q ↔ a ≫ r = b ≫ r)
    (T : Over S) :
    (∀ p : T ⟶ Q, ∃ g : T ⟶ X, g ≫ q = p) ↔
      (∀ p : T ⟶ R, ∃ g : T ⟶ X, g ≫ r = p) := by
  constructor
  · intro hlift p
    obtain ⟨g, hg⟩ := hlift (p ≫ (iso q r h).inv)
    refine ⟨g, ?_⟩
    rw [← comp_iso_hom q r h, ← Category.assoc, hg, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · intro hlift p
    obtain ⟨g, hg⟩ := hlift (p ≫ (iso q r h).hom)
    refine ⟨g, ?_⟩
    rw [← comp_iso_inv q r h, ← Category.assoc, hg, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

end Langlands.GroupScheme.HomogeneousQuotientComparison
