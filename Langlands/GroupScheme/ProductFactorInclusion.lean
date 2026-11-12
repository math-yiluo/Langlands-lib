import Langlands.GroupScheme.Products
import Langlands.GroupScheme.ImageGenerationSubgroup
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectOfSection

/-!
# Factor inclusions into finite products of group schemes

For a finite family `A` of group schemes, `piSingle A x` is the homomorphism
`A x ⟶ pi A` which is the identity in coordinate `x` and trivial in every other
coordinate. It is a closed subgroup with normal image, and every homomorphism
into `pi A` that is trivial outside the coordinate `x` factors through it. Two
closed split tori in two different factors give a closed split torus of the
product whose rank is the sum of their ranks.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {I : Type u} [Finite I] (A : I → GroupScheme S) [DecidableEq I]

/-- The inclusion of the factor `x` into a finite product: the identity in
coordinate `x` and the trivial homomorphism in every other coordinate. -/
def piSingle (x : I) : A x ⟶ pi A :=
  Pi.lift (Function.update (fun y => (0 : A x ⟶ A y)) x (𝟙 (A x)))

@[reassoc (attr := simp)]
theorem piSingle_π_self (x : I) : piSingle A x ≫ Pi.π A x = 𝟙 (A x) := by
  rw [piSingle, Pi.lift_comp_π, Function.update_self]

@[reassoc]
theorem piSingle_π_of_ne {x y : I} (h : y ≠ x) : piSingle A x ≫ Pi.π A y = 0 := by
  rw [piSingle, Pi.lift_comp_π, Function.update_of_ne h]

/-- The coordinate `x` of the image of a point under `piSingle A x` is that point. -/
theorem piSingle_points_self (x : I) {T : Over S} (t : T ⟶ (A x).X) :
    (t ≫ (piSingle A x).hom.hom) ≫ (Pi.π A x).hom.hom = t := by
  rw [Category.assoc, ← Grp.comp_hom_hom, piSingle_π_self]
  exact Category.comp_id t

/-- The other coordinates of the image of a point under `piSingle A x` are trivial. -/
theorem piSingle_points_of_ne {x y : I} (h : y ≠ x) {T : Over S} (t : T ⟶ (A x).X) :
    (t ≫ (piSingle A x).hom.hom) ≫ (Pi.π A y).hom.hom = 1 := by
  rw [Category.assoc, ← Grp.comp_hom_hom, piSingle_π_of_ne A h]
  exact MonObj.comp_one t

/-- A homomorphism into the product that is trivial outside the coordinate `x`
factors through the inclusion of that factor. -/
theorem eq_comp_piSingle {B : GroupScheme S} (f : B ⟶ pi A) (x : I)
    (h : ∀ y, y ≠ x → f ≫ Pi.π A y = 0) : f = (f ≫ Pi.π A x) ≫ piSingle A x := by
  apply Pi.hom_ext
  intro y
  by_cases hy : y = x
  · subst hy
    rw [Category.assoc, piSingle_π_self, Category.comp_id]
  · rw [Category.assoc, piSingle_π_of_ne A hy, comp_zero, h y hy]

/-- The image of a factor inclusion is normal on every test scheme. -/
theorem isNormal_range_piSingle (x : I) : (SubgroupFunctor.range (piSingle A x)).IsNormal := by
  intro T g z _ hz
  obtain ⟨w, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  let gx : T ⟶ (A x).X := g ≫ (Pi.π A x).hom.hom
  refine SubgroupFunctor.mem_range.mpr ⟨gx * w * gx⁻¹, ?_⟩
  apply (piPointsEquiv A T).injective
  funext y
  simp only [piPointsEquiv_apply, MonObj.mul_comp, GrpObj.inv_comp]
  by_cases hy : y = x
  · subst hy
    rw [piSingle_points_self]
  · simp only [piSingle_points_of_ne A hy, mul_one, inv_one, mul_inv_cancel]

end Base

section Field

variable {k : Type u} [Field k] {I : Type u} [Finite I]
  (A : I → GroupScheme (Spec (CommRingCat.of k))) [DecidableEq I]

/-- A factor inclusion into a separated finite product is a closed subgroup. -/
theorem isClosedSubgroup_piSingle [IsSeparated (pi A).X.hom] (x : I) :
    IsClosedSubgroup (piSingle A x) :=
  IsClosedSubgroup.of_comp_eq_id _ (Pi.π A x) (piSingle_π_self A x)

/-- Closed split tori in two different factors of a separated finite product give a
closed split torus of the product, of rank the sum of their ranks. -/
theorem card_add_card_le_splitRank_pi [IsSeparated (pi A).X.hom] {x y : I} (hxy : x ≠ y)
    {J₁ J₂ : Type u} [Finite J₁] [Finite J₂]
    (t₁ : splitTorus (Spec (CommRingCat.of k)) J₁ ⟶ A x)
    (t₂ : splitTorus (Spec (CommRingCat.of k)) J₂ ⟶ A y)
    (h₁ : IsClosedSubgroup t₁) (h₂ : IsClosedSubgroup t₂) :
    ((Nat.card J₁ + Nat.card J₂ : ℕ) : ℕ∞) ≤ splitRank (pi A) := by
  let P₁ := splitTorus (Spec (CommRingCat.of k)) J₁
  let P₂ := splitTorus (Spec (CommRingCat.of k)) J₂
  let Ψ : P₁ ⊗ P₂ ⟶ pi A :=
    Pi.lift (Function.update (Function.update (fun z => (0 : P₁ ⊗ P₂ ⟶ A z)) x
      (fst P₁ P₂ ≫ t₁)) y (snd P₁ P₂ ≫ t₂))
  have hΨx : Ψ ≫ Pi.π A x = fst P₁ P₂ ≫ t₁ := by
    rw [Pi.lift_comp_π, Function.update_of_ne hxy, Function.update_self]
  have hΨy : Ψ ≫ Pi.π A y = snd P₁ P₂ ≫ t₂ := by
    rw [Pi.lift_comp_π, Function.update_self]
  let q : (pi A).X ⟶ (A x).X ⊗ (A y).X := lift (Pi.π A x).hom.hom (Pi.π A y).hom.hom
  have hq : Ψ.hom.hom ≫ q = t₁.hom.hom ⊗ₘ t₂.hom.hom := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, ← Grp.comp_hom_hom, hΨx, tensorHom_fst]
      rfl
    · rw [Category.assoc, lift_snd, ← Grp.comp_hom_hom, hΨy, tensorHom_snd]
      rfl
  have : IsClosedImmersion t₁.hom.hom.left := h₁
  have : IsClosedImmersion t₂.hom.hom.left := h₂
  have hclosed : IsClosedImmersion (Ψ.hom.hom.left ≫ q.left) := by
    rw [← Over.comp_left, hq]
    exact ImageGeneration.isClosedImmersion_tensorHom_left _ _
  have : IsSeparated q.left := by
    have : IsSeparated (q.left ≫ ((A x).X ⊗ (A y).X).hom) := by
      rw [Over.w]
      infer_instance
    exact IsSeparated.of_comp _ (((A x).X ⊗ (A y).X).hom)
  have hΨ : IsClosedSubgroup Ψ := IsClosedImmersion.of_comp Ψ.hom.hom.left q.left
  have hcard := card_le_splitRank (J₁ ⊕ J₂) ((splitTorus.prodIso J₁ J₂).inv ≫ Ψ)
    (hΨ.iso_comp (splitTorus.prodIso J₁ J₂).symm)
  rwa [Nat.card_sum] at hcard

end Field

end Langlands.GroupScheme
