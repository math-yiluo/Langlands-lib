import Langlands.GroupScheme.Dynamic.FlagQuotientSections
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Rational translations of an actual scheme quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable (k : Type u) [Field k]
variable (G : GroupScheme (Spec (CommRingCat.of k)))
variable (H : SubgroupFunctor G) {Q : Over (Spec (CommRingCat.of k))}
variable (π : G.X ⟶ Q)
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
  g ≫ π = h ≫ π ↔ g⁻¹ * h ∈ H.carrier T)

include hfib

/-- Left multiplication preserves the exact right-coset fibers on every test scheme. -/
theorem rationalLeftTranslation_preserves_fibers (a : RationalPoint k G.X)
    {T : Over (Spec (CommRingCat.of k))} (g h : T ⟶ G.X)
    (he : g ≫ π = h ≫ π) :
    g ≫ (rationalLeftTranslation k G a).hom ≫ π =
      h ≫ (rationalLeftTranslation k G a).hom ≫ π := by
  rw [← Category.assoc, ← Category.assoc]
  apply (hfib T _ _).mpr
  simpa only [comp_rationalLeftTranslation, mul_inv_rev, mul_assoc,
    inv_mul_cancel_left] using (hfib T g h).mp he

/-- Fiber preservation also holds for arbitrary maps of the underlying schemes. -/
theorem rationalLeftTranslation_preserves_scheme_fibers (a : RationalPoint k G.X)
    {Z : Scheme.{u}} (g h : Z ⟶ G.X.left)
    (he : g ≫ π.left = h ≫ π.left) :
    g ≫ ((rationalLeftTranslation k G a).hom ≫ π).left =
      h ≫ ((rationalLeftTranslation k G a).hom ≫ π).left := by
  have hb : h ≫ G.X.hom = g ≫ G.X.hom := by
    rw [← Over.w π, ← Category.assoc, ← he, Category.assoc]
  let g₀ : Over.mk (g ≫ G.X.hom) ⟶ G.X := Over.homMk g rfl
  let h₀ : Over.mk (g ≫ G.X.hom) ⟶ G.X := Over.homMk h hb
  exact congrArg (fun f => f.left)
    (rationalLeftTranslation_preserves_fibers k G H π hfib a g₀ h₀
      (Over.OverMorphism.ext he))

variable [EffectiveEpi π.left]

/-- The underlying scheme map obtained by descending actual left translation. -/
def flagQuotientTranslationSchemeHom (a : RationalPoint k G.X) : Q.left ⟶ Q.left :=
  EffectiveEpi.desc π.left ((rationalLeftTranslation k G a).hom ≫ π).left
    (fun g h he =>
      rationalLeftTranslation_preserves_scheme_fibers k G H π hfib a g h he)

@[reassoc]
theorem fac_flagQuotientTranslationSchemeHom (a : RationalPoint k G.X) :
    π.left ≫ flagQuotientTranslationSchemeHom k G H π hfib a =
      ((rationalLeftTranslation k G a).hom ≫ π).left :=
  EffectiveEpi.fac _ _ _

/-- The descended translation is a morphism over the original field. -/
def flagQuotientTranslationHom (a : RationalPoint k G.X) : Q ⟶ Q :=
  Over.homMk (flagQuotientTranslationSchemeHom k G H π hfib a) (by
    apply (cancel_epi π.left).mp
    rw [fac_flagQuotientTranslationSchemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_flagQuotientTranslationHom (a : RationalPoint k G.X) :
    π ≫ flagQuotientTranslationHom k G H π hfib a =
      (rationalLeftTranslation k G a).hom ≫ π :=
  Over.OverMorphism.ext (fac_flagQuotientTranslationSchemeHom k G H π hfib a)

/-- Actual quotient translation by a rational group point. Its inverse is the
descended left translation by the inverse point. -/
def flagQuotientTranslation (a : RationalPoint k G.X) : Q ≅ Q where
  hom := flagQuotientTranslationHom k G H π hfib a
  inv := flagQuotientTranslationHom k G H π hfib a⁻¹
  hom_inv_id := by
    have : Epi π := Over.epi_of_epi_left π
    apply (cancel_epi π).mp
    rw [← Category.assoc, fac_flagQuotientTranslationHom, Category.assoc,
      fac_flagQuotientTranslationHom, Category.comp_id]
    change (rationalLeftTranslation k G a).hom ≫
      (rationalLeftTranslation k G a).inv ≫ π = π
    simp
  inv_hom_id := by
    have : Epi π := Over.epi_of_epi_left π
    apply (cancel_epi π).mp
    rw [← Category.assoc, fac_flagQuotientTranslationHom, Category.assoc,
      fac_flagQuotientTranslationHom, Category.comp_id]
    change (rationalLeftTranslation k G a).inv ≫
      (rationalLeftTranslation k G a).hom ≫ π = π
    simp

@[reassoc]
theorem fac_flagQuotientTranslation (a : RationalPoint k G.X) :
    π ≫ (flagQuotientTranslation k G H π hfib a).hom =
      (rationalLeftTranslation k G a).hom ≫ π :=
  fac_flagQuotientTranslationHom k G H π hfib a

/-- Rational-point lifting and one actual section near the identity coset give
actual algebraic sections near every rational point of the same quotient. -/
theorem localSections_of_rational_lifts
    (hlift : ∀ p : RingPoint k Q k, ∃ g : RingPoint k G.X k, g ≫ π = p)
    (U : Q.left.Opens) (s : openOver k Q U ⟶ G.X)
    (hq : Set.range
      (rationalPointEquiv k Q ((1 : RationalPoint k G.X) ≫ π)).left ⊆ U)
    (hs : s ≫ π = openOverι k Q U) :
    ∀ p : RingPoint k Q k,
      ∃ (V : Q.left.Opens) (t : openOver k Q V ⟶ G.X),
        Set.range p.left ⊆ V ∧ t ≫ π = openOverι k Q V := by
  apply localSections_of_transitive_lifts k π
    (rationalPointEquiv k Q ((1 : RationalPoint k G.X) ≫ π)) U s hq hs
  intro p
  obtain ⟨b, hb⟩ := hlift p
  let a : RationalPoint k G.X := (rationalPointEquiv k G.X).symm b
  refine ⟨(rationalLeftTranslation k G a).hom,
    flagQuotientTranslation k G H π hfib a,
    (fac_flagQuotientTranslation k G H π hfib a).symm, ?_⟩
  rw [← rationalPointEquiv_natural, Category.assoc, fac_flagQuotientTranslation,
    ← Category.assoc]
  have ha : (1 : RationalPoint k G.X) ≫ (rationalLeftTranslation k G a).hom = a := by
    rw [comp_rationalLeftTranslation, mul_one]
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ a.left = a.left
    exact Category.id_comp _
  rw [ha, rationalPointEquiv_natural]
  change rationalPointEquiv k G.X ((rationalPointEquiv k G.X).symm b) ≫ π = p
  rw [Equiv.apply_symm_apply]
  exact hb

end Langlands.GroupScheme.Dynamic
