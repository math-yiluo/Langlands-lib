import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Category.SmoothCoproducts
import Langlands.Representation.Induction.CompactQuotientProof
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Coproduct comparison for normalized induction

The natural comparison from the sum of induced representations to induction of
the sum is an isomorphism when the left quotient is compact.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe uG uI uV

namespace Langlands.Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} {ι : Type uI} [DecidableEq ι]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : ι → SmoothRep.{0, uG, max uI uV} ℂ M)

/-- The summand inclusions induce the canonical coproduct comparison. -/
def inductionDirectSumMap :
    SmoothRep.directSum.{uG, uI, max uG uV} (fun i => (normalizedInductionFunctor h hU).obj (A i)) ⟶
      (normalizedInductionFunctor h hU).obj (SmoothRep.directSum.{uG, uI, uV} A) :=
  (SmoothRep.directSumIsColimit.{uG, uI, max uG uV}
    (fun i => (normalizedInductionFunctor h hU).obj (A i))).desc
    (Cofan.mk _ (fun i => (normalizedInductionFunctor h hU).map (SmoothRep.directSumι.{uG, uI, uV} A i)))

@[simp]
theorem inductionDirectSumMap_lof (i : ι)
    (f : (normalizedInductionFunctor h hU).obj (A i)) :
    SmoothRep.hom (inductionDirectSumMap h hU A)
      (DirectSum.lof ℂ ι (fun i => (normalizedInductionFunctor h hU).obj (A i)) i f) =
      SmoothRep.hom ((normalizedInductionFunctor h hU).map (SmoothRep.directSumι.{uG, uI, uV} A i)) f := by
  change (DirectSum.toModule ℂ ι ((normalizedInductionFunctor h hU).obj (SmoothRep.directSum.{uG, uI, uV} A))
    (fun i => (SmoothRep.hom
      ((normalizedInductionFunctor h hU).map (SmoothRep.directSumι.{uG, uI, uV} A i))).toLinearMap))
    (DirectSum.lof ℂ ι (fun i => (normalizedInductionFunctor h hU).obj (A i)) i f) = _
  apply DirectSum.toModule_lof

/-- Applying an induced summand projection recovers the corresponding component. -/
theorem inductionDirectSumMap_component
    (x : SmoothRep.directSum.{uG, uI, max uG uV} (fun i => (normalizedInductionFunctor h hU).obj (A i))) (i : ι) :
    SmoothRep.hom ((normalizedInductionFunctor h hU).map (SmoothRep.directSumπ.{uG, uI, uV} A i))
      (SmoothRep.hom (inductionDirectSumMap h hU A) x) = DirectSum.component ℂ ι
      (fun i => (normalizedInductionFunctor h hU).obj (A i)) i x := by
  have he :
      (SmoothRep.hom ((normalizedInductionFunctor h hU).map (SmoothRep.directSumπ.{uG, uI, uV} A i))).toLinearMap.comp
        (SmoothRep.hom (inductionDirectSumMap h hU A)).toLinearMap =
      DirectSum.component ℂ ι
        (fun i => (normalizedInductionFunctor h hU).obj (A i)) i := by
    apply DirectSum.linearMap_ext
    intro j
    ext f
    change SmoothRep.hom ((normalizedInductionFunctor h hU).map (SmoothRep.directSumπ.{uG, uI, uV} A i))
      (SmoothRep.hom (inductionDirectSumMap h hU A)
        (DirectSum.lof ℂ ι (fun i => (normalizedInductionFunctor h hU).obj (A i)) j f)) = _
    rw [inductionDirectSumMap_lof]
    dsimp only [LinearMap.comp_apply]
    by_cases hji : j = i
    · subst j
      rw [DirectSum.component.lof_self]
      apply Subtype.ext
      apply Subtype.ext
      funext g
      change (DirectSum.lof ℂ ι (fun i => A i) i
        (Induction.eval P (inducingRepresentation h hU (A i)) f g)) i = _
      exact DirectSum.lof_apply ℂ i _
    · rw [DirectSum.component.of, dite_eq_right hji]
      apply Subtype.ext
      apply Subtype.ext
      funext g
      change (DirectSum.lof ℂ ι (fun i => A i) j
        (Induction.eval P (inducingRepresentation h hU (A j)) f g)) i = 0
      change DirectSum.component ℂ ι (fun i => A i) i
        (DirectSum.lof ℂ ι (fun i => A i) j
          (Induction.eval P (inducingRepresentation h hU (A j)) f g)) = 0
      rw [DirectSum.component.of, dite_eq_right hji]
  exact DFunLike.congr_fun he x

/-- The canonical induction coproduct comparison is injective. -/
theorem inductionDirectSumMap_injective :
    Function.Injective (SmoothRep.hom (inductionDirectSumMap h hU A)) := by
  intro x y hxy
  apply DFinsupp.ext
  intro i
  have hi := congrArg
    (SmoothRep.hom ((normalizedInductionFunctor h hU).map (SmoothRep.directSumπ.{uG, uI, uV} A i))) hxy
  simpa only [inductionDirectSumMap_component, DirectSum.component] using! hi

/-- Compactness of the left quotient bounds the nonzero induced components of
each smooth function by one finite set. -/
theorem inductionDirectSumMap_surjective [CompactSpace (Induction.LeftQuotient P)] :
    Function.Surjective (SmoothRep.hom (inductionDirectSumMap h hU A)) := by
  classical
  intro f
  let I := normalizedInductionFunctor.{uG, max uI uV} h hU
  let v (g : G) : DirectSum ι (fun i => A i) :=
    Induction.eval P (inducingRepresentation h hU (SmoothRep.directSum.{uG, uI, uV} A)) f g
  let c (i : ι) : I.obj (A i) := SmoothRep.hom (I.map (SmoothRep.directSumπ A i)) f
  obtain ⟨K, hK⟩ := f.property
  obtain ⟨t, ht⟩ := Induction.exists_finset_doubleCoset_cover P K
  let S : Finset ι := t.biUnion (fun g => (v g).support)
  have hright (i : ι) (k : K) (g : G) :
      Induction.eval P (inducingRepresentation h hU (A i)) (c i) (g * (k : G)) =
        Induction.eval P (inducingRepresentation h hU (A i)) (c i) g := by
    exact congrArg
      (fun z : Induction.EquivariantFunctions P
          (inducingRepresentation h hU (SmoothRep.directSum.{uG, uI, uV} A)) =>
        DirectSum.component ℂ ι (fun i => A i) i (z.val g)) (hK k)
  have hzrep (i : ι) (hi : i ∉ S) (g : G) (hg : g ∈ t) :
      Induction.eval P (inducingRepresentation h hU (A i)) (c i) g = 0 := by
    change (v g) i = 0
    apply DFinsupp.notMem_support_iff.mp
    intro hig
    exact hi (Finset.mem_biUnion.mpr ⟨g, hg, hig⟩)
  have hz (i : ι) (hi : i ∉ S) : c i = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change Induction.eval P (inducingRepresentation h hU (A i)) (c i) x = 0
    obtain ⟨g, hg, p, hp, k, hk, rfl⟩ := ht x
    rw [hright i ⟨k, hk⟩ (p * g)]
    calc
      Induction.eval P (inducingRepresentation h hU (A i)) (c i) (p * g) =
          inducingRepresentation h hU (A i) ⟨p, hp⟩
            (Induction.eval P (inducingRepresentation h hU (A i)) (c i) g) :=
        Induction.eval_covariant P (inducingRepresentation h hU (A i)) (c i) ⟨p, hp⟩ g
      _ = 0 := by rw [hzrep i hi g hg, map_zero]
  let x : DirectSum ι (fun i => I.obj (A i)) := DFinsupp.mk S (fun i => c i)
  have hx (i : ι) : DirectSum.component ℂ ι (fun i => I.obj (A i)) i x = c i := by
    change (DFinsupp.mk (β := fun i => I.obj (A i)) S (fun i => c i)) i = c i
    by_cases hi : i ∈ S
    · exact DFinsupp.mk_of_mem hi
    · rw [DFinsupp.mk_of_notMem hi, hz i hi]
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply DFinsupp.ext
  intro i
  have he := inductionDirectSumMap_component h hU A x i
  rw [hx i] at he
  exact congrArg (fun z => Induction.eval P (inducingRepresentation h hU (A i)) z g) he

/-- For a compact quotient, the image of the concrete coproduct cofan is colimiting. -/
def inductionDirectSumIsColimit [CompactSpace (Induction.LeftQuotient P)] :
    IsColimit ((normalizedInductionFunctor h hU).mapCocone
      (SmoothRep.directSumCofan.{uG, uI, uV} A)) := by
  let e := SmoothRep.mkIso ((SmoothRep.hom (inductionDirectSumMap h hU A)).ofBijective
    ⟨inductionDirectSumMap_injective h hU A, inductionDirectSumMap_surjective h hU A⟩)
  refine (isColimitMapCoconeCofanMkEquiv (normalizedInductionFunctor h hU) A
    (SmoothRep.directSumι.{uG, uI, uV} A)).symm ?_
  refine IsColimit.ofIsoColimit
    (SmoothRep.directSumIsColimit.{uG, uI, max uG uV}
      (fun i => (normalizedInductionFunctor h hU).obj (A i))) (Cocone.ext e ?_)
  rintro ⟨i⟩
  apply ObjectProperty.hom_ext
  ext f
  exact inductionDirectSumMap_lof h hU A i f

instance normalizedInductionFunctor_preservesCoproduct [CompactSpace (Induction.LeftQuotient P)] :
    PreservesColimit (Discrete.functor A) (normalizedInductionFunctor h hU) :=
  preservesColimit_of_preserves_colimit_cocone (SmoothRep.directSumIsColimit A)
    (inductionDirectSumIsColimit h hU A)

instance normalizedInductionFunctor_preservesCoproducts [CompactSpace (Induction.LeftQuotient P)] :
    PreservesColimitsOfShape (Discrete ι)
      (normalizedInductionFunctor.{uG, max uI uV} h hU) := by
  classical
  exact preservesColimitsOfShape_of_discrete _

end Langlands.Aubert.General
