import Langlands.AbelianScheme.Isogeny
import Langlands.GroupScheme.SubgroupRangeTransport
import Langlands.GroupScheme.Torus.NoTorusBaseChangeReduction
import Langlands.GroupScheme.Torus.NoTorusBasicReductionStatement
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.RootSubgroupVectorTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Unipotent.FieldReflectionProof

/-! # Absence of nontrivial closed tori and elementary transport -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Every closed torus inclusion into the group has trivial all-test range. -/
def HasNoNontrivialClosedTorus (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
    ∀ (i : T.toGrp ⟶ G), IsClosedSubgroup i → SubgroupFunctor.range i = ⊥

namespace HasNoNontrivialClosedTorus

variable {G H G' : GroupScheme (Spec (CommRingCat.of k))}

/-- Triviality of every homomorphism from a torus implies the closed-torus condition. -/
theorem of_forall_hom
    (hG : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ i : T.toGrp ⟶ G, SubgroupFunctor.range i = ⊥) :
    HasNoNontrivialClosedTorus G :=
  fun T hT i _ => hG T hT i

/-- A closed subgroup inherits the absence of nontrivial closed tori. -/
theorem of_closedSubgroup (hG : HasNoNontrivialClosedTorus G)
    (j : H ⟶ G) (hj : IsClosedSubgroup j) : HasNoNontrivialClosedTorus H := by
  intro T hT i hi
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  exact (SubgroupFunctor.range_comp_eq_bot_iff i j).mp
    (hG T hT (i ≫ j) (hi.comp hj))

/-- The closed-torus condition passes to a target when every target torus lifts
up to an isogeny of tori. -/
theorem of_torus_lifting (hG : HasNoNontrivialClosedTorus G) (φ : G ⟶ G')
    (hlift : ∀ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G'),
      IsTorus T'.toGrp → IsClosedSubgroup i' →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
          (f : T.toGrp ⟶ T'.toGrp),
          IsTorus T.toGrp ∧ IsClosedSubgroup i ∧ IsIsogeny f ∧ i ≫ φ = f ≫ i') :
    HasNoNontrivialClosedTorus G' := by
  intro T' hT' i' hi'
  obtain ⟨T, i, f, hT, hi, hf, hcomm⟩ := hlift T' i' hT' hi'
  have hi0 : i = 0 := SubgroupFunctor.eq_zero_of_range_eq_bot (hG T hT i hi)
  let : Flat f.hom.hom.left := hf.2.1
  let : Surjective f.hom.hom.left := hf.2.2
  let : Epi f.hom.hom.left := Flat.epi_of_flat_of_surjective _
  let : Epi f.hom.hom := Over.epi_of_epi_left _
  let : Epi f := (Grp.forget _).epi_of_epi_map (inferInstanceAs (Epi f.hom.hom))
  have hzero : f ≫ i' = f ≫ 0 := by
    rw [← hcomm, hi0, zero_comp, comp_zero]
  rw [(cancel_epi f).mp hzero, SubgroupFunctor.range_zero]

/-- The nilpotent case follows from the explicit central-torus structure statement. -/
theorem isUnipotent_of_nilpotent (hstructure : NilpotentCentralTorusStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : HasNoNontrivialClosedTorus G) (hnil : IsNilpotentGroupScheme G) :
    IsUnipotent G := by
  obtain ⟨T, i, Q, q, hmax, _, _, hQ, hq⟩ := hstructure k G hnil
  have hbot : RelativeRoot.IsFppfQuotient ⊥ q := by
    simpa only [hG T hmax.1 i hmax.2.1] using hq
  exact IsUnipotent.of_iso hbot.isoOfBot hQ

/-- The finite-field case follows from geometric maximal-torus existence and
the algebraically closed trivial-maximal-torus statement. -/
theorem isUnipotent_of_finiteField
    (hfinite : FiniteFieldGeometricMaximalTorusStatement.{u})
    (halgclosed : AlgClosedTrivialMaximalTorusUnipotentStatement.{u})
    [Finite k] [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : HasNoNontrivialClosedTorus G) : IsUnipotent G := by
  obtain ⟨T, i, hmax, hgeom⟩ := hfinite k G
  have hconn := G.connectedSpace_baseChange_of_smooth_affine (toAlgebraicClosure k)
  have : Smooth ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have hbot : SubgroupFunctor.range
      ((GroupScheme.baseChange (toAlgebraicClosure k)).map i) = ⊥ := by
    rw [SubgroupFunctor.range_baseChangeHom, hG T hmax.1 i hmax.2.1,
      SubgroupFunctor.bot_baseChange]
  exact IsUnipotent.of_baseChange
    (halgclosed (AlgebraicClosure k) _
      ((CommGroupScheme.baseChange (toAlgebraicClosure k)).obj T) _ hgeom hbot)

end HasNoNontrivialClosedTorus

end Langlands.GroupScheme
