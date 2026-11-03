import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.Dynamic.OppositeCellContraction
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Separation of a dynamic parabolic normalizer from opposite directions -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section General

variable {S : Scheme.{u}} {G : GroupScheme S}
  (χ : (Gm S).toGrp ⟶ G) (A : SubgroupFunctor G)
  (hA : A.IsNormalizedBy (SubgroupFunctor.range χ))
  (hdisj : ∀ (T : Over S) (g : T ⟶ G.X),
    g ∈ A.carrier T → g ∈ (parabolic χ).carrier T → g = 1)

include hA hdisj in
/-- A subgroup normalized by the cocharacter and disjoint from its dynamic
parabolic also meets the all-test normalizer of that parabolic trivially. -/
theorem eq_one_of_mem_normalizer_of_disjoint
    {T : Over S} {g : T ⟶ G.X} (hgA : g ∈ A.carrier T)
    (hgN : g ∈ (parabolic χ).normalizer.carrier T) : g = 1 := by
  let V := T ⊗ (Gm S).X
  let n : V ⟶ G.X := fst T (Gm S).X ≫ g
  let x : V ⟶ G.X := snd T (Gm S).X ≫ χ.hom.hom
  have hnA : n ∈ A.carrier V := A.comp_mem _ hgA
  have hxRange : x ∈ (SubgroupFunctor.range χ).carrier V :=
    SubgroupFunctor.mem_range.mpr ⟨snd T (Gm S).X, rfl⟩
  have hxP : x ∈ (parabolic χ).carrier V := by
    apply centralizer_le_parabolic χ V
    have hr := range_comp_le_centralizer_comp χ (𝟙 _) (𝟙 _)
    simpa only [Category.id_comp] using hr V hxRange
  have hcP : n⁻¹ * x * n * x⁻¹ ∈ (parabolic χ).carrier V :=
    ((parabolic χ).carrier V).mul_mem
      (hgN V (fst T (Gm S).X) x hxP).2
      (((parabolic χ).carrier V).inv_mem hxP)
  have hcA : n⁻¹ * x * n * x⁻¹ ∈ A.carrier V := by
    have h := (A.carrier V).mul_mem ((A.carrier V).inv_mem hnA)
      (hA V x n hxRange hnA)
    simpa only [mul_assoc] using h
  have hc : n⁻¹ * x * n * x⁻¹ = 1 := hdisj V _ hcA hcP
  have hz : g ∈ (centralizer χ).carrier T := by
    change x * n * x⁻¹ = n
    calc
      x * n * x⁻¹ = n * (n⁻¹ * x * n * x⁻¹) := by group
      _ = n := by rw [hc, mul_one]
  exact hdisj T g hgA (centralizer_le_parabolic χ T hz)

end General

section Affine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (χ : (Gm (Spec R)).toGrp ⟶ G)

/-- The opposite dynamic unipotent meets the all-test normalizer of the
dynamic parabolic only in the identity. -/
theorem eq_one_of_mem_opposite_unipotent_of_mem_normalizer
    {T : Over (Spec R)} {g : T ⟶ G.X}
    (hgU : g ∈ (unipotent (oppositeCocharacter χ)).carrier T)
    (hgN : g ∈ (parabolic χ).normalizer.carrier T) : g = 1 := by
  apply eq_one_of_mem_normalizer_of_disjoint χ
    (unipotent (oppositeCocharacter χ)) ?_ ?_ hgU hgN
  · have h := unipotent_isNormalizedBy_range_of_common_commutativeGroup χ
      (𝟙 (Gm (Spec R)).toGrp)
      (CommGroupScheme.groupHom (Gm.powerHom (Spec R) (-1)))
    simpa only [Category.id_comp, oppositeCocharacter] using h
  · exact fun T g hu hp =>
      eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hu hp

/-- The all-test intersection of the opposite dynamic unipotent and the
normalizer of the dynamic parabolic is trivial. -/
theorem opposite_unipotent_inf_normalizer_parabolic :
    unipotent (oppositeCocharacter χ) ⊓ (parabolic χ).normalizer = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  change (g ∈ (unipotent (oppositeCocharacter χ)).carrier T ∧
    g ∈ (parabolic χ).normalizer.carrier T) ↔ g = 1
  constructor
  · exact fun h => eq_one_of_mem_opposite_unipotent_of_mem_normalizer χ h.1 h.2
  · rintro rfl
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

/-- The multiplicative equivalence, on every test scheme, from the intersection
of the opposite unipotent and the parabolic normalizer to the trivial subgroup. -/
def oppositeUnipotentNormalizerEquivBot (T : Over (Spec R)) :
    (unipotent (oppositeCocharacter χ) ⊓ (parabolic χ).normalizer).carrier T ≃*
      (⊥ : SubgroupFunctor G).carrier T :=
  MulEquiv.subgroupCongr
    (congrArg (fun H : SubgroupFunctor G => H.carrier T)
      (opposite_unipotent_inf_normalizer_parabolic χ))

/-- A point normalizing a dynamic parabolic belongs to it whenever it has
an opposite-unipotent times parabolic factorization over the test scheme. -/
theorem mem_parabolic_of_mem_normalizer_of_opposite_factorization
    {T : Over (Spec R)} {g u p : T ⟶ G.X}
    (hgN : g ∈ (parabolic χ).normalizer.carrier T)
    (hu : u ∈ (unipotent (oppositeCocharacter χ)).carrier T)
    (hp : p ∈ (parabolic χ).carrier T) (hgp : g = u * p) :
    g ∈ (parabolic χ).carrier T := by
  have hpN := SubgroupFunctor.le_normalizer (parabolic χ) T hp
  have huN : u ∈ (parabolic χ).normalizer.carrier T := by
    have h := ((parabolic χ).normalizer.carrier T).mul_mem hgN
      (((parabolic χ).normalizer.carrier T).inv_mem hpN)
    simpa only [hgp, mul_inv_cancel_right] using h
  have hu1 := eq_one_of_mem_opposite_unipotent_of_mem_normalizer χ hu huN
  simpa only [hgp, hu1, one_mul] using hp

end Affine

end Langlands.GroupScheme.Dynamic
