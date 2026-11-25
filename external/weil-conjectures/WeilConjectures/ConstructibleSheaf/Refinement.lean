/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism

/-!
# Refinement of stratifications

Finite local constancy of the pullback of a sheaf `F` to an immersed subscheme depends only on
the image of the immersion: for immersions `a : Z ⟶ X` and `b : Z' ⟶ X` with
`range a ⊆ range b`, the projection `Z ×_X Z' ⟶ Z` is a surjective closed immersion, along
which finite local constancy descends
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset`,
`isFiniteLocallyConstantSheaf_upperStar_iff_of_range_eq`).

Consequently constructibility passes from a stratification to any refinement
(`AlgebraicGeometry.Scheme.Stratification.Refines`,
`Stratification.Refines.isFiniteLocallyConstantSheaf_upperStar`), and two stratifications have
a common refinement by intersecting the strata (`Stratification.inter`).
(blueprint: `lemma-constructible-immersion-independence`, `def:constructible-refines`,
`lemma:constructible-common-refinement`, `lemma:constructible-of-refines`)

-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

/-- A surjective immersion is a closed immersion. -/
lemma IsClosedImmersion.of_isImmersion_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] [Surjective f] : IsClosedImmersion f :=
  IsClosedImmersion.iff_isPreimmersion.mpr
    ⟨inferInstance, by rw [Set.range_eq_univ.mpr f.surjective]; exact isClosed_univ⟩

namespace Scheme

variable {X : Scheme.{u}}

section Independence

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
variable {Z Z' : Scheme.{u}} (a : Z ⟶ X) (b : Z' ⟶ X)

/-- The first projection `Z ×_X Z' ⟶ Z` is surjective when `range a ⊆ range b`. -/
lemma surjective_pullback_fst_of_range_subset (h : Set.range a ⊆ Set.range b) :
    Surjective (pullback.fst a b) where
  surj := by
    rw [← Set.range_eq_univ, Pullback.range_fst, Set.preimage_eq_univ_iff]
    exact h

variable [IsImmersion b]

/-- **Finite local constancy of a pullback along an immersion depends only on the image**: if
`b : Z' ⟶ X` is an immersion, `a : Z ⟶ X` is any morphism with `range a ⊆ range b` and
`b^* F` is finite locally constant, so is `a^* F`. The projection `p : Z ×_X Z' ⟶ Z` is a
surjective closed immersion, `p^* a^* F ≅ q^* b^* F` is finite locally constant, and finite
local constancy descends along `p`. (blueprint: `lemma-constructible-immersion-independence`) -/
theorem IsFiniteLocallyConstantSheaf.upperStar_of_range_subset (h : Set.range a ⊆ Set.range b)
    (F : Sheaf X.smallEtaleTopology A)
    [IsFiniteLocallyConstantSheaf ((Etale.upperStar A b).obj F)] :
    IsFiniteLocallyConstantSheaf ((Etale.upperStar A a).obj F) := by
  have := surjective_pullback_fst_of_range_subset a b h
  have := IsClosedImmersion.of_isImmersion_of_surjective (pullback.fst a b)
  have : IsFiniteLocallyConstantSheaf ((Etale.upperStar A (pullback.snd a b)).obj
      ((Etale.upperStar A b).obj F)) :=
    IsFiniteLocallyConstantSheaf.upperStar _ _
  have : IsFiniteLocallyConstantSheaf ((Etale.upperStar A (pullback.fst a b)).obj
      ((Etale.upperStar A a).obj F)) :=
    IsFiniteLocallyConstantSheaf.of_iso (F := (Etale.upperStar A (pullback.snd a b)).obj
      ((Etale.upperStar A b).obj F))
      (((Etale.upperStarComp A (pullback.snd a b) b).app F).symm ≪≫
        eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj F) pullback.condition.symm) ≪≫
        (Etale.upperStarComp A (pullback.fst a b) a).app F)
  exact IsFiniteLocallyConstantSheaf.of_upperStar (pullback.fst a b) _

/-- **Independence of the scheme structure**: for immersions `a`, `b` with the same image,
`a^* F` is finite locally constant if and only if `b^* F` is.
(blueprint: `lemma-constructible-immersion-independence`) -/
theorem isFiniteLocallyConstantSheaf_upperStar_iff_of_range_eq [IsImmersion a]
    (h : Set.range a = Set.range b)
    (F : Sheaf X.smallEtaleTopology A) :
    IsFiniteLocallyConstantSheaf ((Etale.upperStar A a).obj F) ↔
      IsFiniteLocallyConstantSheaf ((Etale.upperStar A b).obj F) :=
  ⟨fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar_of_range_subset b a h.ge F,
    fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar_of_range_subset a b h.le F⟩

end Independence

section Refines

/-- A stratification `T` *refines* a stratification `S` if every stratum of `T` is contained
in a stratum of `S`. (blueprint: `def:constructible-refines`) -/
def Stratification.Refines (T S : Stratification X) : Prop :=
  ∀ l, ∃ k, T.stratum l ⊆ S.stratum k

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- **Constructibility passes to refinements**: if the pullbacks of `F` to the strata of `S`
are finite locally constant and `T` refines `S`, the pullbacks of `F` to the strata of `T` are
finite locally constant. (blueprint: `lemma:constructible-of-refines`) -/
theorem Stratification.Refines.isFiniteLocallyConstantSheaf_upperStar {T S : Stratification X}
    (hTS : T.Refines S) (F : Sheaf X.smallEtaleTopology A)
    (hS : ∀ k, IsFiniteLocallyConstantSheaf ((Etale.upperStar A (S.immersion k)).obj F)) (l) :
    IsFiniteLocallyConstantSheaf ((Etale.upperStar A (T.immersion l)).obj F) := by
  obtain ⟨k, hk⟩ := hTS l
  have := hS k
  refine IsFiniteLocallyConstantSheaf.upperStar_of_range_subset (T.immersion l) (S.immersion k)
    ?_ F
  rw [T.range_immersion, S.range_immersion]
  exact hk

/-- A sheaf is constructible with respect to a refinement of a witnessing stratification. -/
theorem IsConstructibleSheaf.of_refines {T S : Stratification X} (hTS : T.Refines S)
    (F : Sheaf X.smallEtaleTopology A)
    (hS : ∀ k, IsFiniteLocallyConstantSheaf ((Etale.upperStar A (S.immersion k)).obj F)) :
    IsConstructibleSheaf F :=
  ⟨T, hTS.isFiniteLocallyConstantSheaf_upperStar F hS⟩

end Refines

section Inter

variable (S T : Stratification X)

/-- **The common refinement of two stratifications**: the strata are the intersections
`S.stratum k ∩ T.stratum l`, with the fibre products `S.domain k ×_X T.domain l` as schemes.
(blueprint: `lemma:constructible-common-refinement`) -/
@[simps n stratum domain immersion]
def Stratification.inter : Stratification X where
  n := S.n * T.n
  stratum k := S.stratum (finProdFinEquiv.symm k).1 ∩ T.stratum (finProdFinEquiv.symm k).2
  isLocallyClosed_stratum k :=
    (S.isLocallyClosed_stratum _).inter (T.isLocallyClosed_stratum _)
  isConstructible_stratum k :=
    (S.isConstructible_stratum _).inter (T.isConstructible_stratum _)
  iUnion_stratum_eq_univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (T.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨finProdFinEquiv (k, l), by simpa using ⟨hk, hl⟩⟩
  pairwise_disjoint_stratum k k' hkk' := by
    have hne : finProdFinEquiv.symm k ≠ finProdFinEquiv.symm k' :=
      fun h ↦ hkk' (finProdFinEquiv.symm.injective h)
    by_cases h₁ : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm k').1
    · have h₂ : (finProdFinEquiv.symm k).2 ≠ (finProdFinEquiv.symm k').2 :=
        fun h ↦ hne (Prod.ext h₁ h)
      exact (T.pairwise_disjoint_stratum h₂).mono Set.inter_subset_right Set.inter_subset_right
    · exact (S.pairwise_disjoint_stratum h₁).mono Set.inter_subset_left Set.inter_subset_left
  domain k := Limits.pullback (S.immersion (finProdFinEquiv.symm k).1)
    (T.immersion (finProdFinEquiv.symm k).2)
  immersion k := pullback.fst _ _ ≫ S.immersion (finProdFinEquiv.symm k).1
  range_immersion k := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Pullback.range_fst,
      Set.image_preimage_eq_inter_range, S.range_immersion, T.range_immersion, Set.inter_comm]

/-- The common refinement refines the first stratification. -/
lemma Stratification.inter_refines_left : (S.inter T).Refines S :=
  fun k ↦ ⟨(finProdFinEquiv.symm k).1, Set.inter_subset_left⟩

/-- The common refinement refines the second stratification. -/
lemma Stratification.inter_refines_right : (S.inter T).Refines T :=
  fun k ↦ ⟨(finProdFinEquiv.symm k).2, Set.inter_subset_right⟩

/-- **Two stratifications have a common refinement.**
(blueprint: `lemma:constructible-common-refinement`) -/
lemma Stratification.exists_refines : ∃ R : Stratification X, R.Refines S ∧ R.Refines T :=
  ⟨S.inter T, S.inter_refines_left T, S.inter_refines_right T⟩

end Inter

end Scheme

end AlgebraicGeometry

end
