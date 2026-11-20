import Langlands.Global.AdelicEisensteinConstantTermStatement

/-! # Rational and adelic points of subgroups in the constant-term formula

Group-theoretic facts on points used in the proof of Bernstein–Lapid (6.17):

* rational images `H(F)` of subgroups lie in `G(F)` and are functorial;
* the principal subgroup of the adelic points of `range j` is the rational image of `j`;
* a geometric unipotent radical `V` of `Q` is normalized by `Q(𝔸)` on adelic points and by
  `Q(F)` on rational points;
* for a rational Levi subgroup `M` of `P` and a geometric unipotent radical `U` of `P`,
  `P(F) ⊆ U(𝔸) M(F)`, from the Levi decomposition `M × U₀ ≅ P` of `IsRationalLeviSubgroup` and
  the uniqueness of the unipotent radical (`IsUnipotentRadical.range_eq`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
variable {G H H' : GroupScheme (Spec (CommRingCat.of F))}

/-- The principal map commutes with group-scheme morphisms: `j(rational y) = rational(j y)`. -/
theorem map_rational (j : H ⟶ G) (y : RationalGroupPoints F H) :
    map F H G j (rational F H y) = rational F G (H.affinePointsTarget j _ y) :=
  (congrArg (fun φ : RationalGroupPoints F H →* AdelicGroupPoints F G => φ y)
    (rational_naturality F H j)).symm

/-- `j(rational (k y)) = (k ≫ j)(rational y)`. -/
theorem map_rational_affinePointsTarget (k : H' ⟶ H) (j : H ⟶ G)
    (y : RationalGroupPoints F H') :
    map F H G j (rational F H (H'.affinePointsTarget k _ y)) =
      map F H' G (k ≫ j) (rational F H' y) := by
  rw [← map_rational, map_comp_apply_of_hom]

theorem mem_rationalImage_iff (j : H ⟶ G) (x : AdelicGroupPoints F G) :
    x ∈ rationalImage F j ↔ ∃ y : RationalGroupPoints F H, map F H G j (rational F H y) = x :=
  Iff.rfl

/-- `H(F) ⊆ G(F)`. -/
theorem rationalImage_le_rationalSubgroup (j : H ⟶ G) :
    rationalImage F j ≤ rationalSubgroup F G := by
  rintro _ ⟨y, rfl⟩
  exact ⟨_, (map_rational j y).symm⟩

/-- `(k ≫ j)(F) ⊆ j(F)`. -/
theorem rationalImage_comp_le (k : H' ⟶ H) (j : H ⟶ G) :
    rationalImage F (k ≫ j) ≤ rationalImage F j := by
  rintro _ ⟨y, rfl⟩
  exact ⟨H'.affinePointsTarget k _ y, map_rational_affinePointsTarget k j y⟩

/-- The rational image is the image of the principal subgroup. -/
theorem rationalImage_eq_map (j : H ⟶ G) :
    rationalImage F j = (rationalSubgroup F H).map (map F H G j).toMonoidHom := by
  rw [rationalImage, rationalSubgroup, MonoidHom.range_comp]

/-- The principal subgroup of the adelic points of `range j` is the rational image of `j`. -/
theorem mem_rationalSubgroup_range_iff (j : H ⟶ G)
    (v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
    v ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j) ↔
      (v : AdelicGroupPoints F G) ∈ rationalImage F j := by
  constructor
  · rintro ⟨⟨q, hq⟩, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : RationalGroupPoints F H, H.affinePointsTarget j _ y = q := hq
    refine ⟨y, ?_⟩
    show map F H G j (rational F H y) = AdelicGroupPoints.rational F G q
    rw [map_rational, hy]
  · rintro ⟨y, hy⟩
    refine ⟨⟨H.affinePointsTarget j _ y, ⟨y, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show rational F G (H.affinePointsTarget j _ y) = (v : AdelicGroupPoints F G)
    rw [← map_rational]
    exact hy

/-- The rational image lies in the adelic points of the range. -/
theorem rationalImage_le_adelicPoints (j : H ⟶ G) :
    rationalImage F j ≤ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) := by
  rintro _ ⟨y, rfl⟩
  exact ⟨rational F H y, rfl⟩

section Normal

variable {Q V : GroupScheme (Spec (CommRingCat.of F))} (q : Q ⟶ G) (iV : V ⟶ Q)

/-- Points of `Q(𝔸)` normalize the adelic points of a normal subgroup `V` of `Q`. -/
theorem conj_mem_adelicPoints_range (hN : (SubgroupFunctor.range iV).IsNormal)
    (x : AdelicGroupPoints F Q) {v : AdelicGroupPoints F G}
    (hv : v ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :
    map F Q G q x * v * (map F Q G q x)⁻¹ ∈
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) := by
  obtain ⟨y, hy⟩ : ∃ y : AdelicGroupPoints F V, y ≫ (iV ≫ q).hom.hom = v := hv
  subst hy
  obtain ⟨y', hy'⟩ : ∃ y' : AdelicGroupPoints F V,
      y' ≫ iV.hom.hom = x * (y ≫ iV.hom.hom) * x⁻¹ :=
    hN _ x (y ≫ iV.hom.hom) trivial ⟨y, rfl⟩
  refine ⟨y', ?_⟩
  show y' ≫ (iV ≫ q).hom.hom =
    Q.affinePointsTarget q _ x * (y ≫ (iV ≫ q).hom.hom) * (Q.affinePointsTarget q _ x)⁻¹
  rw [Grp.comp_hom_hom, ← Category.assoc, hy', ← Category.assoc]
  show Q.affinePointsTarget q _ (x * (y ≫ iV.hom.hom) * x⁻¹) =
    Q.affinePointsTarget q _ x * Q.affinePointsTarget q _ (y ≫ iV.hom.hom) *
      (Q.affinePointsTarget q _ x)⁻¹
  rw [map_mul, map_mul, map_inv]

/-- Points of `Q(F)` normalize the rational points of a normal subgroup `V` of `Q`. -/
theorem conj_mem_rationalImage (hN : (SubgroupFunctor.range iV).IsNormal)
    {x v : AdelicGroupPoints F G} (hx : x ∈ rationalImage F q)
    (hv : v ∈ rationalImage F (iV ≫ q)) : x * v * x⁻¹ ∈ rationalImage F (iV ≫ q) := by
  obtain ⟨x₀, rfl⟩ := hx
  obtain ⟨y₀, rfl⟩ := hv
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : RationalGroupPoints F V,
      V.affinePointsTarget iV _ y₁ = x₀ * V.affinePointsTarget iV _ y₀ * x₀⁻¹ :=
    hN _ x₀ (y₀ ≫ iV.hom.hom) trivial ⟨y₀, rfl⟩
  refine ⟨y₁, ?_⟩
  show map F V G (iV ≫ q) (rational F V y₁) =
    map F Q G q (rational F Q x₀) * map F V G (iV ≫ q) (rational F V y₀) *
      (map F Q G q (rational F Q x₀))⁻¹
  rw [← map_rational_affinePointsTarget iV q, ← map_rational_affinePointsTarget iV q, hy₁,
    map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]

/-- The rational points of `V` lie in those of `Q`. -/
theorem rationalImage_comp_le_of_radical :
    rationalImage F (iV ≫ q) ≤ rationalImage F q :=
  rationalImage_comp_le iV q

end Normal

section Levi

variable {P U M : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P)

/-- Levi decomposition on rational points: `P(F) ⊆ U(𝔸) M(F)`. -/
theorem rationalImage_le_parabolicQuotientSubgroup (hl : IsRationalLeviSubgroup l)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) :
    rationalImage F p ≤ parabolicQuotientSubgroup F p iU l := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨U₀, r₀, hr₀, hiso⟩ := hl.exists_unipotentRadical
  have hrange : SubgroupFunctor.range r₀ = SubgroupFunctor.range iU := hr₀.1.range_eq hU.1
  have key : y = lift (y ≫ inv (subgroupMultiplication l r₀) ≫ fst M.X U₀.X)
      (y ≫ inv (subgroupMultiplication l r₀) ≫ snd M.X U₀.X) ≫ subgroupMultiplication l r₀ := by
    rw [← Category.assoc y _ (fst M.X U₀.X), ← Category.assoc y _ (snd M.X U₀.X),
      lift_comp_fst_snd, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [comp_subgroupMultiplication] at key
  have hu : (y ≫ inv (subgroupMultiplication l r₀) ≫ snd M.X U₀.X) ≫ r₀.hom.hom ∈
      (SubgroupFunctor.range iU).carrier _ := by
    rw [← hrange]
    exact ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u' : RationalGroupPoints F U, U.affinePointsTarget iU _ u' =
      (y ≫ inv (subgroupMultiplication l r₀) ≫ snd M.X U₀.X) ≫ r₀.hom.hom := hu
  have hy : y = M.affinePointsTarget l _ (y ≫ inv (subgroupMultiplication l r₀) ≫ fst M.X U₀.X) *
      U.affinePointsTarget iU _ u' := by
    rw [hu']
    exact key
  change map F P G p (rational F P y) ∈ _
  rw [hy, map_mul, map_mul, map_rational_affinePointsTarget, map_rational_affinePointsTarget]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨_, rfl⟩)
    (Subgroup.mem_sup_left ⟨rational F U u', rfl⟩)

end Levi

end Langlands.Global.AdelicGroupPoints
