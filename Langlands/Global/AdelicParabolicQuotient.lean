import Langlands.Global.LeftCosetSpace
import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Dynamic.Decomposition

/-! # The parabolic quotient `X_P = U(𝔸_F) M(F) \ G(𝔸_F)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.Global

section ProductSubgroup

variable {H : Type*} [Group H]

/-- If `Γ` normalizes `N`, the join `N ⊔ Γ` consists of the products `n γ` with `n ∈ N` and
`γ ∈ Γ`. -/
theorem mem_sup_iff_exists_mul_of_le_normalizer {N Γ : Subgroup H}
    (hΓ : Γ ≤ Subgroup.normalizer (N : Set H)) {x : H} :
    x ∈ N ⊔ Γ ↔ ∃ n ∈ N, ∃ γ ∈ Γ, n * γ = x := by
  let S : Subgroup H :=
    { carrier := {x | ∃ n ∈ N, ∃ γ ∈ Γ, n * γ = x}
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, γ₁, hγ₁, rfl⟩ ⟨n₂, hn₂, γ₂, hγ₂, rfl⟩
        refine ⟨n₁ * (γ₁ * n₂ * γ₁⁻¹), N.mul_mem hn₁ ((Subgroup.mem_normalizer_iff.mp
          (hΓ hγ₁) n₂).mp hn₂), γ₁ * γ₂, Γ.mul_mem hγ₁ hγ₂, by group⟩
      one_mem' := ⟨1, N.one_mem, 1, Γ.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨n, hn, γ, hγ, rfl⟩
        refine ⟨γ⁻¹ * n⁻¹ * γ, ?_, γ⁻¹, Γ.inv_mem hγ, by group⟩
        have h := (Subgroup.mem_normalizer_iff.mp (hΓ (Γ.inv_mem hγ)) n⁻¹).mp (N.inv_mem hn)
        simpa only [inv_inv] using h }
  constructor
  · intro hx
    have hle : N ⊔ Γ ≤ S :=
      sup_le (fun n hn => ⟨n, hn, 1, Γ.one_mem, mul_one n⟩)
        (fun γ hγ => ⟨1, N.one_mem, γ, hγ, one_mul γ⟩)
    exact hle hx
  · rintro ⟨n, hn, γ, hγ, rfl⟩
    exact (N ⊔ Γ).mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hγ)

end ProductSubgroup

namespace AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
variable {G P U M : GroupScheme (Spec (CommRingCat.of F))}
variable (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P)

/-- The image `U(𝔸_F)` of the adelic points of `U` in `G(𝔸_F)`, through `iU ≫ p`. -/
def parabolicUnipotentImage : Subgroup (AdelicGroupPoints F G) :=
  (map F U G (iU ≫ p)).toMonoidHom.range

/-- The image `M(F)` of the rational points of `M` in `G(𝔸_F)`, through `l ≫ p`. -/
def parabolicLeviRationalImage : Subgroup (AdelicGroupPoints F G) :=
  ((map F M G (l ≫ p)).toMonoidHom.comp (rational F M)).range

/-- The subgroup `U(𝔸_F) M(F)` of `G(𝔸_F)`, as the join of the two images. -/
def parabolicQuotientSubgroup : Subgroup (AdelicGroupPoints F G) :=
  parabolicUnipotentImage F p iU ⊔ parabolicLeviRationalImage F p l

/-- The parabolic quotient `X_P = U(𝔸_F) M(F) \ G(𝔸_F)` of Mœglin–Waldspurger I.2.17, as the
left coset space of `G(𝔸_F)` by `U(𝔸_F) M(F)`, with its quotient topology and the right
translation action of `G(𝔸_F)`. -/
abbrev ParabolicQuotient :=
  LeftCosetSpace (parabolicQuotientSubgroup F p iU l)

namespace ParabolicQuotient

/-- The projection `G(𝔸_F) → X_P`. -/
def mk (g : AdelicGroupPoints F G) : ParabolicQuotient F p iU l :=
  LeftCosetSpace.mk _ g

theorem mk_surjective : Function.Surjective (mk F p iU l) :=
  LeftCosetSpace.mk_surjective _

/-- Left translation by `U(𝔸_F)` does not change the class. -/
@[simp] theorem mk_unipotent_mul (n : AdelicGroupPoints F U) (g : AdelicGroupPoints F G) :
    mk F p iU l (map F U G (iU ≫ p) n * g) = mk F p iU l g :=
  LeftCosetSpace.mk_subgroup_mul _ ⟨_, Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨n, rfl⟩)⟩ g

/-- Left translation by `M(F)` does not change the class. -/
@[simp] theorem mk_leviRational_mul (γ : RationalGroupPoints F M) (g : AdelicGroupPoints F G) :
    mk F p iU l (map F M G (l ≫ p) (rational F M γ) * g) = mk F p iU l g :=
  LeftCosetSpace.mk_subgroup_mul _ ⟨_, Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)⟩ g

/-- Right translation by `G(𝔸_F)` on `X_P`. -/
@[simp] theorem rightTranslate_mk (g x : AdelicGroupPoints F G) :
    LeftCosetSpace.rightTranslate _ g (mk F p iU l x) = mk F p iU l (x * g) := rfl

theorem continuous_mk : Continuous (mk F p iU l) :=
  LeftCosetSpace.continuous_mk _

end ParabolicQuotient

variable {F p iU l}

/-- If the image of `M(F)` normalizes the image of `U(𝔸_F)`, the subgroup `U(𝔸_F) M(F)` consists
exactly of the products `n γ`. -/
theorem mem_parabolicQuotientSubgroup_iff
    (hN : parabolicLeviRationalImage F p l ≤ Subgroup.normalizer (parabolicUnipotentImage F p iU : Set (AdelicGroupPoints F G)))
    (x : AdelicGroupPoints F G) :
    x ∈ parabolicQuotientSubgroup F p iU l ↔
      ∃ n : AdelicGroupPoints F U, ∃ γ : RationalGroupPoints F M,
        map F U G (iU ≫ p) n * map F M G (l ≫ p) (rational F M γ) = x := by
  rw [parabolicQuotientSubgroup, mem_sup_iff_exists_mul_of_le_normalizer hN]
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, _, ⟨γ, rfl⟩, rfl⟩
    exact ⟨n, γ, rfl⟩
  · rintro ⟨n, γ, rfl⟩
    exact ⟨_, ⟨n, rfl⟩, _, ⟨γ, rfl⟩, rfl⟩

/-- If the image of `P(𝔸_F)` normalizes the image of `U(𝔸_F)`, so does the image of `M(F)`. -/
theorem parabolicLeviRationalImage_le_normalizer
    (hP : (map F P G p).toMonoidHom.range ≤ Subgroup.normalizer (parabolicUnipotentImage F p iU : Set (AdelicGroupPoints F G))) :
    parabolicLeviRationalImage F p l ≤ Subgroup.normalizer (parabolicUnipotentImage F p iU : Set (AdelicGroupPoints F G)) := by
  rintro _ ⟨γ, rfl⟩
  apply hP
  refine ⟨map F M P l (rational F M γ), ?_⟩
  change map F P G p (map F M P l (rational F M γ)) = map F M G (l ≫ p) (rational F M γ)
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]

/-- Two points have the same class in `X_P` exactly when they differ on the left by a product
`n γ` with `n ∈ U(𝔸_F)` and `γ ∈ M(F)`. -/
theorem ParabolicQuotient.mk_eq_mk_iff
    (hN : parabolicLeviRationalImage F p l ≤ Subgroup.normalizer (parabolicUnipotentImage F p iU : Set (AdelicGroupPoints F G)))
    (x y : AdelicGroupPoints F G) :
    ParabolicQuotient.mk F p iU l x = ParabolicQuotient.mk F p iU l y ↔
      ∃ n : AdelicGroupPoints F U, ∃ γ : RationalGroupPoints F M,
        map F U G (iU ≫ p) n * map F M G (l ≫ p) (rational F M γ) * x = y := by
  rw [ParabolicQuotient.mk, ParabolicQuotient.mk, LeftCosetSpace.mk_eq_mk_iff,
    mem_parabolicQuotientSubgroup_iff hN]
  constructor
  · rintro ⟨n, γ, h⟩
    exact ⟨n, γ, by rw [h]; group⟩
  · rintro ⟨n, γ, rfl⟩
    exact ⟨n, γ, by group⟩

section Standard

open Langlands.GroupScheme

variable (F) {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T) (J : Set (characterLattice T))

/-- The adelic image of the published representative `Standard.parabolicScheme i ν J` is the
standard intersection functor `standardParabolic i ν J` evaluated on the adeles. No geometric
parabolicity is asserted: for an empty standard-cocharacter family the functor is all of `G`. -/
theorem standardParabolic_range_eq :
    (map F (Standard.parabolicScheme i ν J) G (Standard.parabolicHom i ν J)).toMonoidHom.range =
      (standardParabolic i ν J).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) :=
  congrArg (fun H : SubgroupFunctor G => H.carrier
    ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))))
    (Standard.isRepresentedBy_parabolicHom i ν J).2

/-- The adelic image of the published representative `Standard.unipotentScheme i ν J`, through the
standard parabolic representative, is the standard intersection functor `standardUnipotent i ν J`
evaluated on the adeles. It is identified with a unipotent radical only under separate
hypotheses; for an empty standard-cocharacter family it is all of `G`. -/
theorem standardUnipotentImage_eq :
    parabolicUnipotentImage F (Standard.parabolicHom i ν J) (Standard.unipotentToParabolic i ν J) =
      (standardUnipotent i ν J).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) := by
  rw [parabolicUnipotentImage, Standard.unipotentToParabolic_comp]
  exact congrArg (fun H : SubgroupFunctor G => H.carrier
    ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))))
    (Standard.isRepresentedBy_unipotentHom i ν J).2

/-- The adelic points of the standard parabolic representative normalize those of the standard
unipotent representative, for all `i`, `ν` and `J`. -/
theorem standardParabolic_range_le_normalizer :
    (map F (Standard.parabolicScheme i ν J) G (Standard.parabolicHom i ν J)).toMonoidHom.range ≤
      Subgroup.normalizer (parabolicUnipotentImage F (Standard.parabolicHom i ν J)
        (Standard.unipotentToParabolic i ν J) : Set (AdelicGroupPoints F G)) := by
  have key : ∀ g ∈ (map F (Standard.parabolicScheme i ν J) G
      (Standard.parabolicHom i ν J)).toMonoidHom.range,
      ∀ u ∈ parabolicUnipotentImage F (Standard.parabolicHom i ν J)
        (Standard.unipotentToParabolic i ν J),
      g * u * g⁻¹ ∈ parabolicUnipotentImage F (Standard.parabolicHom i ν J)
        (Standard.unipotentToParabolic i ν J) := by
    intro g hg u hu
    rw [standardParabolic_range_eq] at hg
    rw [standardUnipotentImage_eq] at hu ⊢
    rw [mem_standardUnipotent] at hu ⊢
    intro ζ hζ
    exact Dynamic.conj_mem_unipotent _ ((mem_standardParabolic i ν).1 hg ζ hζ) (hu ζ hζ)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact key g hg n
  · intro hn
    have h := key g⁻¹ (inv_mem hg) _ hn
    simpa [mul_assoc] using h

/-- For the published standard representatives with index set `J`, the join of the unipotent
adelic image and the rational Levi image is exactly the set of products. This is a statement about
the standard intersection functors; it does not assert that they are a parabolic, its unipotent
radical and a Levi subgroup. -/
theorem mem_standardParabolicQuotientSubgroup_iff (x : AdelicGroupPoints F G) :
    x ∈ parabolicQuotientSubgroup F (Standard.parabolicHom i ν J)
        (Standard.unipotentToParabolic i ν J) (Standard.leviToParabolic i ν J) ↔
      ∃ n : AdelicGroupPoints F (Standard.unipotentScheme i ν J),
        ∃ γ : RationalGroupPoints F (Standard.leviScheme i ν J),
          map F _ G (Standard.unipotentToParabolic i ν J ≫ Standard.parabolicHom i ν J) n *
            map F _ G (Standard.leviToParabolic i ν J ≫ Standard.parabolicHom i ν J)
              (rational F _ γ) = x :=
  mem_parabolicQuotientSubgroup_iff
    (parabolicLeviRationalImage_le_normalizer (standardParabolic_range_le_normalizer F i ν J)) x

end Standard

end AdelicGroupPoints

end Langlands.Global
