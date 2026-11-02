import Langlands.AbelianScheme.Tate.TwoPowerTorsionLevelComparisonStatement
import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureGroupGeometry

/-! # Comparison of actual two-power torsion levels through a closed immersion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

/-- The existing two-power torsion level maps are bijective for a closed
abelian subscheme containing the actual torsion locus. -/
theorem twoPowerTorsionLevelComparison :
    TwoPowerTorsionLevelComparisonStatement.{u} := by
  intro K _ A B f hi hcontains n
  let T := Over.mk (𝟙 (Spec (CommRingCat.of K)))
  have : Subsingleton T.left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  have : IsReduced T.left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  let f' : B.X ⟶ A.X := (groupHom f).hom.hom
  have : IsClosedImmersion (hom f) := hi
  have : Mono f' := Over.mono_of_mono_left f'
  constructor
  · intro x y h
    apply GroupScheme.Tate.toSection_injective B.toGrp T (2 ^ n)
    change (Additive.toMul x).val = (Additive.toMul y).val
    apply (cancel_mono f').mp
    exact congrArg (fun z =>
      (GroupScheme.Tate.toSection A.toGrp T (2 ^ n) z).toMul) h
  · intro x
    let s : T ⟶ A.X := (Additive.toMul x).val
    have hs : s ^ (2 ^ n) = 1 :=
      (GroupScheme.Tate.mem_levelGroup A.toGrp T (2 ^ n) s).mp
        (Additive.toMul x).property
    have hrange : Set.range s.left ⊆ Set.range (hom f) := by
      rintro _ ⟨a, rfl⟩
      apply hcontains
      exact ⟨n, s, hs, congrArg s.left (Subsingleton.elim _ _)⟩
    obtain ⟨t, ht⟩ :=
      exists_factor_closedImmersion_of_reduced (hom f) s.left hrange
    have hbase : t ≫ B.X.hom = 𝟙 (Spec (CommRingCat.of K)) := by
      rw [← Over.w f', ← Category.assoc, ht]
      exact Over.w s
    let t' : T ⟶ B.X := Over.homMk t hbase
    have ht' : t' ≫ f' = s := Over.OverMorphism.ext ht
    have htpow : t' ^ (2 ^ n) = 1 := by
      apply (cancel_mono f').mp
      rw [MonObj.pow_comp, ht', hs, MonObj.one_comp]
    let y : GroupScheme.Tate.Level B.toGrp T (2 ^ n) :=
      Additive.ofMul ⟨t',
        (GroupScheme.Tate.mem_levelGroup B.toGrp T (2 ^ n) t').mpr htpow⟩
    refine ⟨y, ?_⟩
    apply GroupScheme.Tate.toSection_injective A.toGrp T (2 ^ n)
    change t' ≫ f' = s
    exact ht'

end Langlands.AbelianScheme.Tate
