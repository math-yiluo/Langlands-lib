import Langlands.Geometry.Building.StandardLeviStrictQuotientPartitionStatement
import Langlands.Geometry.Building.CocharacterUniformizerConeQuotientStatement
import Langlands.GroupScheme.Rational.CocharacterConeFaces
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof
import Langlands.Geometry.Building.StandardLeviStrictUniformizerProof
import Langlands.Geometry.Building.CocharacterUniformizerConeQuotientProof

/-! # The partition of the nonnegative quotient by actual standard-Levi pieces: proof

The first two declarations reduce the partition to the strict-image and
nonnegative cone-comparison statements. The final theorem discharges both by
their published proofs. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

section Image

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The strict-image target and the published existence of actual standard-Levi
split components identify each actual quotient piece with its lattice image. -/
theorem standardLeviStrictQuotientFace_eq_uniformizerImage_of_strictImage
    (hstrict : StandardLeviStrictImageStatement.{u})
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν)
    (A₀ : CommGroupScheme (Spec (CommRingCat.of F))) (f₀ : A₀ ⟶ T)
    (J : Set (characterLattice T)) :
    standardLeviStrictQuotientFace F i ν A₀ f₀ J =
      (QuotientGroup.mk'
        ((CA F A₀).map (rationalPoints.map (CommGroupScheme.groupHom f₀)))) ''
          ((fun ξ : cocharacterLattice T =>
            latticeSection F T (Multiplicative.ofAdd ξ)) ''
              {ξ | IsStandardCocharacter i ν J ξ}) := by
  have := hi.isSplitSubtorus.mono
  apply Set.Subset.antisymm
  · rintro x ⟨hJ, L, j, hjc, hj, B, b, hb, g, hg, z, hz, hzx⟩
    rw [hstrict F G hG T i hi ν hν J hJ L j hjc hj B b hb g hg] at hz
    exact ⟨z, hz, hzx⟩
  · rintro x ⟨z, ⟨ξ, hξ, hξz⟩, hzx⟩
    obtain ⟨_, B, b, g, hb, hg⟩ :=
      standardLeviSplitComponentStatement F G hG T i hi ν hν J hξ.1
    let g' : B ⟶ T := Additive.ofMul g
    have hg' : CommGroupScheme.groupHom g' ≫ i =
        b ≫ Standard.leviHom i ν J := hg
    refine ⟨hξ.1, Standard.leviScheme i ν J, Standard.leviHom i ν J,
      Standard.isClosedSubgroup_leviHom i ν J,
      Standard.isRepresentedBy_leviHom i ν J, B, b, hb, g', hg', z, ?_, hzx⟩
    rw [hstrict F G hG T i hi ν hν J hξ.1
      (Standard.leviScheme i ν J) (Standard.leviHom i ν J)
      (Standard.isClosedSubgroup_leviHom i ν J)
      (Standard.isRepresentedBy_leviHom i ν J) B b hb g' hg']
    exact ⟨ξ, hξ, hξz⟩

end Image

/-- This conditional reduction retains the two exact comparison targets as
hypotheses; it does not supply unconditional proofs of them. -/
theorem standardLeviStrictQuotientPartition_of_comparisons
    (hstrict : StandardLeviStrictImageStatement.{u})
    (hcone : ConeQuotientComparisonStatement.{u}) :
    StandardLeviStrictQuotientPartitionStatement.{u} := by
  intro F _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  intro ν hν A₀ a₀ ha₀ f₀ hf₀
  let R := simpleRelativeRoots i ν
  let P := RealTorusSpace.rootAnnihilatorInt T R
  let N := (CA F A₀).map (rationalPoints.map (CommGroupScheme.groupHom f₀))
  let q := QuotientGroup.mk' N
  obtain ⟨e, he⟩ := hcone F G hG T i hi ν hν A₀ a₀ ha₀ f₀ hf₀
  have hforward : ∀ (J : Set (characterLattice T))
      (x : rationalPoints T.toGrp ⧸ N),
      x ∈ standardLeviStrictQuotientFace F i ν A₀ f₀ J →
        ∃ y : CocharacterCone.quotient T R,
          y.val ∈ CocharacterCone.strictFace i ν J ∧
            (e (Multiplicative.ofAdd y)).val = x := by
    intro J x hx
    rw [standardLeviStrictQuotientFace_eq_uniformizerImage_of_strictImage
      hstrict hG i hi ν hν A₀ f₀ J] at hx
    obtain ⟨_, ⟨ξ, hξ, rfl⟩, hξx⟩ := hx
    have hc : ξ ∈ CocharacterCone.nonnegative T R :=
      fun α hα => hξ.nonneg i ν hα
    refine ⟨⟨P.mkQ ξ, ⟨ξ, hc, rfl⟩⟩, ⟨ξ, hξ, rfl⟩, ?_⟩
    exact (he ξ hc).trans hξx
  have hbackward : ∀ (J : Set (characterLattice T))
      (y : CocharacterCone.quotient T R),
      y.val ∈ CocharacterCone.strictFace i ν J →
        (e (Multiplicative.ofAdd y)).val ∈
          standardLeviStrictQuotientFace F i ν A₀ f₀ J := by
    intro J y hy
    obtain ⟨ξ, hξ, hξy⟩ := hy
    have hc : ξ ∈ CocharacterCone.nonnegative T R :=
      fun α hα => hξ.nonneg i ν hα
    have hy : (⟨P.mkQ ξ, ⟨ξ, hc, rfl⟩⟩ : CocharacterCone.quotient T R) = y :=
      Subtype.ext hξy
    rw [standardLeviStrictQuotientFace_eq_uniformizerImage_of_strictImage
      hstrict hG i hi ν hν A₀ f₀ J]
    refine ⟨_, ⟨ξ, hξ, rfl⟩, ?_⟩
    exact (he ξ hc).symm.trans
      (congrArg (fun z => (e (Multiplicative.ofAdd z)).val) hy)
  constructor
  · intro J x hx
    obtain ⟨y, _, hyx⟩ := hforward J x hx
    exact hyx ▸ (e (Multiplicative.ofAdd y)).property
  · intro x
    let y := (e.symm x).toAdd
    obtain ⟨J, hJ, hunique⟩ := CocharacterCone.existsUnique_strictFace i ν y
    have hy : e (Multiplicative.ofAdd y) = x := e.apply_symm_apply x
    refine ⟨J, ?_, ?_⟩
    · rw [← hy]
      exact hbackward J y hJ
    · intro K hK
      obtain ⟨z, hz, hzx⟩ := hforward K x.val hK
      have hzy : z = y := by
        apply Multiplicative.ofAdd.injective
        apply e.injective
        exact (Subtype.ext hzx).trans hy.symm
      exact hunique K (hzy ▸ hz)

/-- The actual strict standard-Levi pieces lie in the nonnegative
common-uniformizer quotient and partition it. -/
theorem standardLeviStrictQuotientPartition :
    StandardLeviStrictQuotientPartitionStatement.{u} :=
  standardLeviStrictQuotientPartition_of_comparisons
    standardLeviStrictImage coneQuotientComparison

end Langlands.GroupScheme.CocharacterUniformizer
