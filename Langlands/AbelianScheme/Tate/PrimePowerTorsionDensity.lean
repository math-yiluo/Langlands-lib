import Langlands.AbelianScheme.Tate.PrimePowerTorsionGeometry
import Langlands.AbelianScheme.Tate.TwoPowerTorsionDensityReduction
import Langlands.AbelianScheme.FieldCubePullbackProof
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof

/-! # Density and homomorphism detection for actual prime-power torsion -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.Tate.PrimePowerTorsion

universe u

/-- The existing prime-power torsion level maps are bijective for a closed
abelian subscheme containing the actual torsion locus. -/
theorem levelComparison
    {K : Type u} [Field K] (A B : AbelianScheme (Spec (CommRingCat.of K)))
    (p : ℕ) (f : B ⟶ A) (hi : IsClosedImmersion (hom f))
    (hcontains : locus A p ⊆ Set.range (hom f)) (n : ℕ) :
    Function.Bijective (GroupScheme.Tate.levelMap
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (groupHom f) (p ^ n)) := by
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
    apply GroupScheme.Tate.toSection_injective B.toGrp T (p ^ n)
    change (Additive.toMul x).val = (Additive.toMul y).val
    apply (cancel_mono f').mp
    exact congrArg (fun z =>
      (GroupScheme.Tate.toSection A.toGrp T (p ^ n) z).toMul) h
  · intro x
    let s : T ⟶ A.X := (Additive.toMul x).val
    have hs : s ^ (p ^ n) = 1 :=
      (GroupScheme.Tate.mem_levelGroup A.toGrp T (p ^ n) s).mp
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
    have htpow : t' ^ (p ^ n) = 1 := by
      apply (cancel_mono f').mp
      rw [MonObj.pow_comp, ht', hs, MonObj.one_comp]
    let y : GroupScheme.Tate.Level B.toGrp T (p ^ n) :=
      Additive.ofMul ⟨t',
        (GroupScheme.Tate.mem_levelGroup B.toGrp T (p ^ n) t').mpr htpow⟩
    refine ⟨y, ?_⟩
    apply GroupScheme.Tate.toSection_injective A.toGrp T (p ^ n)
    change t' ≫ f' = s
    exact ht'


/-- Actual p-power torsion is Zariski dense over every geometric characteristic-zero field. -/
theorem dense_locus {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (p : ℕ) [Fact p.Prime] :
    Dense (locus A p) := by
  obtain ⟨B, f, hi, hrange⟩ := closureAbelianScheme_exists A p
  have hp : ((p ^ 1 : ℕ) : K) ≠ 0 := by
    rw [pow_one]
    exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨gA, hgA⟩ := exists_hasRelativeDimension A
  obtain ⟨gB, hgB⟩ := exists_hasRelativeDimension B
  have hA := natCard_level_eq_of_cubePullback_of_ample
    GroupScheme.fieldCubePullback.{u} GroupScheme.algebraicallyClosedFieldAmpleExistence.{u}
    A gA hgA (p ^ 1) hp
  have hB := natCard_level_eq_of_cubePullback_of_ample
    GroupScheme.fieldCubePullback.{u} GroupScheme.algebraicallyClosedFieldAmpleExistence.{u}
    B gB hgB (p ^ 1) hp
  have hbij := levelComparison A B p f hi (hrange ▸ subset_closure) 1
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [hA, hB, pow_one] at hcard
  have hg : gB = gA := by
    have := Nat.pow_right_injective (Fact.out : p.Prime).two_le hcard
    omega
  subst hg
  have : IsIso (hom f) := fieldEqualDimensionClosedImmersion K B A gB hgB hgA f hi
  rw [dense_iff_closure_eq, ← hrange]
  exact Set.range_eq_univ.mpr (hom f).surjective


/-- Density of the actual prime-power torsion detects vanishing of an actual
homomorphism through its existing torsion-level maps. -/
theorem hom_eq_zero_of_dense_locus
    {K : Type u} [Field K] (p : ℕ)
    {A B : AbelianScheme (Spec (CommRingCat.of K))}
    (hA : Dense (locus A p)) (f : A ⟶ B)
    (hf : ∀ n : ℕ, GroupScheme.Tate.levelMap
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (AbelianScheme.groupHom f) (p ^ n) = 0) :
    f = 0 := by
  let T : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  let f' : A.X ⟶ B.X := (AbelianScheme.groupHom f).hom.hom
  let z' : A.X ⟶ B.X := (AbelianScheme.groupHom (0 : A ⟶ B)).hom.hom
  have hsection (n : ℕ) (s : T ⟶ A.X) (hs : s ^ (p ^ n) = 1) :
      s ≫ f' = s ≫ z' := by
    let t : GroupScheme.Tate.Level A.toGrp T (p ^ n) :=
      Additive.ofMul ⟨s, (GroupScheme.Tate.mem_levelGroup A.toGrp T (p ^ n) s).mpr hs⟩
    have h := congrArg (fun F =>
      (GroupScheme.Tate.toSection B.toGrp T (p ^ n) (F t)).toMul) (hf n)
    change s ≫ f' = 1 at h
    simpa [z', MonObj.comp_one] using h
  have : IsReduced A.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K A.X.left A.X.hom
  have : IsDominant (equalizer.ι f' z').left := by
    constructor
    apply hA.mono
    rintro x ⟨n, s, hs, rfl⟩
    refine ⟨(equalizer.lift s (hsection n s hs)).left
      (default : Spec (CommRingCat.of K)), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
  have hhom : AbelianScheme.hom f = AbelianScheme.hom (0 : A ⟶ B) := by
    apply ext_of_isDominant_of_isSeparated B.X.hom
      (by exact f'.w.trans z'.w.symm) (equalizer.ι f' z').left
    exact congrArg (fun k => k.left) (equalizer.condition f' z')
  apply (Additive.toMul.injective)
  apply Grp.hom_ext
  exact Over.OverMorphism.ext hhom

end Langlands.AbelianScheme.Tate.PrimePowerTorsion
