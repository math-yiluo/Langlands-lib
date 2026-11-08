import Langlands.GroupScheme.SimplyConnected.LocalKneserTitsStatement
import Langlands.GroupScheme.SimplyConnected.LocalRankOneKneserTitsStatement

/-!
# Reduction of local Kneser–Tits to groups of split rank one

This module states the reduction of the local Kneser–Tits theorem to
simply connected `F`-simple groups of split rank one, in the normal-subgroup
formulation of `Langlands.GroupScheme.LocalKneserTitsStatement`. It proves
that this reduction and the rank-one statement together give the general
statement. It does not prove the reduction or the rank-one statement.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over any nonarchimedean local field, let `N` be a normal subgroup of the
rational points of an isotropic almost-simple simply connected group which
contains the rational unipotent radicals of all rational parabolic
subgroups. If `N` contains the image of the rational points of every
almost-simple simply connected group of split rank one mapping to the group
whose own parabolic radicals have images in `N`, then `N` is the whole
group. -/
def LocalKneserTitsRankOneReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsSimplyConnected G → IsAlmostSimple G → ¬ IsAnisotropic G →
    ∀ (N : Subgroup (rationalPoints G)), N.Normal →
      (∀ (P U : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G) (r : U ⟶ P),
        IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p)).range ≤ N) →
      (∀ (A : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom A.X.hom]
        (a : A ⟶ G),
        IsSimplyConnected A → IsAlmostSimple A → splitRank A = 1 →
        (∀ (P U : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ A) (r : U ⟶ P),
          IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
          (rationalPoints.map (r ≫ p ≫ a)).range ≤ N) →
        (rationalPoints.map a).range ≤ N) →
      N = ⊤

/-- The rank-one statement transfers along any group-scheme homomorphism
whose parabolic-radical images lie in the given ambient normal subgroup. -/
theorem rationalPoints_range_le_of_localRankOneKneserTits
    (hKT : LocalRankOneKneserTitsStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {A G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom A.X.hom]
    (hA_sc : IsSimplyConnected A) (hA : IsAlmostSimple A)
    (hA1 : splitRank A = 1) (a : A ⟶ G)
    (K : Subgroup (rationalPoints G)) [K.Normal]
    (hrad : ∀ (P U : GroupScheme (Spec (CommRingCat.of F)))
      (p : P ⟶ A) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p ≫ a)).range ≤ K) :
    (rationalPoints.map a).range ≤ K := by
  let N := K.comap (rationalPoints.map a)
  have hN : N.Normal := inferInstance
  have hNtop : N = ⊤ := hKT F A hA_sc hA hA1 N hN (by
    intro P U p r hp hr
    rintro _ ⟨x, rfl⟩
    change rationalPoints.map a (rationalPoints.map (r ≫ p) x) ∈ K
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
      using hrad P U p r hp hr ⟨x, rfl⟩)
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ N := by rw [hNtop]; trivial
  exact hx

/-- The rank-one statement and the reduction to rank one give the local
Kneser–Tits statement. -/
theorem localKneserTits_of_rankOne_of_reduction
    (h1 : LocalRankOneKneserTitsStatement.{u})
    (hred : LocalKneserTitsRankOneReductionStatement.{u}) :
    LocalKneserTitsStatement.{u} := by
  intro F _ _ _ _ G _ hsc hG hiso N hN hrad
  refine hred F G hsc hG hiso N hN hrad ?_
  intro A _ a hA_sc hA hA1 hArad
  have : N.Normal := hN
  exact rationalPoints_range_le_of_localRankOneKneserTits h1 hA_sc hA hA1 a N hArad

end Langlands.GroupScheme
