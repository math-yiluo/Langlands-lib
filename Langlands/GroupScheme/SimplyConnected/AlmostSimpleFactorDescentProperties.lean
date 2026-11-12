import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorStabilizerDescent
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple

/-! # Almost-simplicity reflected to the actual descended factor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Almost-simplicity reflects along every field extension. -/
theorem IsAlmostSimple.of_fieldExtension
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsAlmostSimple ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    IsAlmostSimple G := by
  let b := algebraBaseMap k K
  have hsemi := IsSemisimple.of_fieldExtension hG.isSemisimple
  let : IsAffineHom G.X.hom := hsemi.isConnectedReductive.isAffineHom
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  refine ⟨hsemi, ?_, ?_⟩
  · intro hc
    apply hG.noncommutative
    intro T x y
    apply (commute_iff_eq _ _).mpr
    apply (baseChangePointsEquiv b G T).injective
    simpa only [map_mul] using
      (hc _ (baseChangePointsEquiv b G T x) (baseChangePointsEquiv b G T y)).eq
  · intro H i hi hs hc hn
    let : IsAffineHom H.X.hom := hi.isAffineHom
    let : Smooth H.X.hom := hs
    let : ConnectedSpace H.X.left := hc
    let : IsClosedImmersion i.hom.hom.left := hi
    let : Mono i.hom.hom := Over.mono_of_mono_left _
    have hsK : Smooth ((GroupScheme.baseChange b).obj H).X.hom :=
      inferInstanceAs (Smooth (pullback.snd H.X.hom b))
    have hcK : ConnectedSpace ((GroupScheme.baseChange b).obj H).X.left :=
      H.connectedSpace_baseChange_of_smooth_affine b
    have hnK : (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).IsNormal := by
      rw [SubgroupFunctor.range_baseChangeHom]
      exact hn.baseChange b
    rcases hG.normalSubgroup_trivial_or_full ((GroupScheme.baseChange b).obj H)
      ((GroupScheme.baseChange b).map i) (hi.baseChange b) hsK hcK hnK with hb | ht
    · left
      rw [SubgroupFunctor.range_baseChangeHom] at hb
      exact SubgroupFunctor.eq_bot_of_baseChange_eq_bot b hb
    · right
      apply le_antisymm (fun _ _ _ => Subgroup.mem_top _)
      apply SubgroupFunctor.le_range_of_baseChange_le b i
      rw [SubgroupFunctor.top_baseChange, ← SubgroupFunctor.range_baseChangeHom, ht]

/-- Absolute almost-simplicity reflects along every field extension. -/
theorem IsAbsolutelyAlmostSimple.of_fieldExtension
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsAbsolutelyAlmostSimple
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    IsAbsolutelyAlmostSimple G := by
  refine ⟨IsAlmostSimple.of_fieldExtension hG.1, ?_⟩
  let : Algebra k (AlgebraicClosure K) :=
    ((algebraMap K (AlgebraicClosure K)).comp (algebraMap k K)).toAlgebra
  let closureEmbedding : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) := closureEmbedding.toRingHom.toAlgebra
  let b := algebraBaseMap k K
  let a := toAlgebraicClosure k
  let c := toAlgebraicClosure K
  let d := algebraBaseMap (AlgebraicClosure k) (AlgebraicClosure K)
  have hcomp : c ≫ b = d ≫ a := by
    dsimp [a, b, c, d, toAlgebraicClosure, algebraBaseMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    exact RingHom.ext fun x => (closureEmbedding.commutes x).symm
  have htotal : IsAlmostSimple ((GroupScheme.baseChange (c ≫ b)).obj G) :=
    (hG.2).of_iso (baseChangeCompIso b c G)
  rw [hcomp] at htotal
  have hiter : IsAlmostSimple
      ((GroupScheme.baseChange d).obj ((GroupScheme.baseChange a).obj G)) :=
    htotal.of_iso (baseChangeCompIso a d G).symm
  exact IsAlmostSimple.of_fieldExtension hiter

/-- Absolute almost-simplicity is unchanged by an actual group isomorphism. -/
theorem IsAbsolutelyAlmostSimple.of_iso
    {G H : GroupScheme (Spec (CommRingCat.of k))} (e : G ≅ H)
    (hH : IsAbsolutelyAlmostSimple H) : IsAbsolutelyAlmostSimple G :=
  ⟨hH.1.of_iso e,
    hH.2.of_iso ((GroupScheme.baseChange (toAlgebraicClosure k)).mapIso e)⟩

namespace SimplyConnectedAlmostSimpleProduct

variable {L : Type u} [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    [IsGalois k L] [IsAffineHom G.X.hom]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom]

/-- The actual selected factor's stabilizer-field model is almost-simple. -/
theorem isAlmostSimple_factorStabilizerDescent (i : D.Index) :
    IsAlmostSimple (D.factorStabilizerDescent i).1 := by
  apply IsAlmostSimple.of_fieldExtension (K := L)
  exact (D.isAlmostSimple i).of_iso (D.factorStabilizerDescent i).2.2.1

/-- Absolute almost-simplicity reflects to the actual stabilizer-field model
as soon as it is known for the recovered factor. -/
theorem isAbsolutelyAlmostSimple_factorStabilizerDescent (i : D.Index)
    (hi : IsAbsolutelyAlmostSimple (D.factor i)) :
    IsAbsolutelyAlmostSimple (D.factorStabilizerDescent i).1 := by
  apply IsAbsolutelyAlmostSimple.of_fieldExtension (K := L)
  exact hi.of_iso (D.factorStabilizerDescent i).2.2.1

/-- The actual selected factor over its stabilizer field, with simple
connectedness, almost-simplicity, normality and exact inclusion recovery. -/
def almostSimpleFactorStabilizerDescent (i : D.Index) :
    Σ H : GroupScheme (Spec (CommRingCat.of (D.factorStabilizerField i))),
      Σ j : H ⟶ (GroupScheme.baseChange
          (algebraBaseMap k (D.factorStabilizerField i))).obj G,
        {r : (GroupScheme.baseChange
            (algebraBaseMap (D.factorStabilizerField i) L)).obj H ≅ D.factor i //
          IsAffine H.X.left ∧ IsClosedSubgroup j ∧ IsSimplyConnected H ∧
            IsAlmostSimple H ∧ (SubgroupFunctor.range j).IsNormal ∧
            (GroupScheme.baseChange (algebraBaseMap (D.factorStabilizerField i) L)).map j =
              r.hom ≫ (D.inclusion i ≫
                (GaloisPointComparison.towerBaseChangeIso k (D.factorStabilizerField i) L G).inv)} := by
  let d := D.factorStabilizerDescent i
  exact ⟨d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1,
    D.isSimplyConnected_factorStabilizerDescent i,
    D.isAlmostSimple_factorStabilizerDescent i,
    D.isNormal_factorStabilizerDescent i, d.2.2.2.2.2⟩

end SimplyConnectedAlmostSimpleProduct

end Langlands.GroupScheme
