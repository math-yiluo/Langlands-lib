import Langlands.Representation.LanglandsClassification.ComaximalQuotientRetraction
import Langlands.Representation.LanglandsClassification.OneDimensionalHomHead
import Langlands.Representation.LanglandsClassification.LeviInductionQuotient
import Langlands.Representation.LanglandsClassification.PQRegularIntertwiningDimension
import Langlands.Representation.Aubert.General.InductionCarrierTransport
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Strong heads from regular opposite Jacquet modules

The geometric identity piece, regularity, finite-length preservation and
second adjunction are inputs. The actual quotient, Jacquet and induction
maps retain independent field and inducing-carrier universes.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M N Q U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance oppositeHeadAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

/-- Equivalent inducing representations in independent carrier universes
give equivalent actual represented-parabolic inductions. -/
def leviInductionEquivOfEquiv
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (τ : letI := leviPointTopology l hl; SmoothRep.{0, u, w} ℂ (rationalPoints M))
    (e : letI := leviPointTopology l hl; σ.representation.Equiv τ.representation) :
    letI := leviPointTopology l hl
    ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.Equiv
      ((leviInductionFunctor p l r hp hr hl hmul).obj τ).representation := by
  letI := leviPointTopology l hl
  exact normalizedInductionEquivOfEquiv
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (SmoothRep.pullbackEquiv (leviPointsEquiv p l hp hl).symm e)

/-- The actual represented-parabolic Jacquet functor preserves surjective maps. -/
theorem leviJacquet_map_surjective
    {A B : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    (f : A ⟶ B) (hf : Function.Surjective (SmoothRep.hom f)) :
    letI := leviPointTopology l hl
    Function.Surjective
      (SmoothRep.hom ((leviJacquetFunctor p l r hp hr hl hmul).map f)) := by
  let := leviPointTopology l hl
  exact Jacquet.Localization.map_surjective _ 1 _ (pointImage_le_normalizer p l r hr)
    (Jacquet.Localization.isInvariant_one _ _ (pointImage_le_normalizer p l r hr))
    (SmoothRep.hom f) hf

variable
  (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
  (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))

/-- A supplied second adjunction gives a nonzero map from the inducing
representation into the opposite Jacquet module, without identifying `v` and `u`.
The induction comparison first raises the inducing carrier to `max u v`. -/
theorem exists_nonzero_oppositeJacquetMap
    (adj : letI := leviPointTopology l hl
      leviInductionFunctor.{u, max u v} p l r hp hr hl hmul ⊣
        leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G))
    (t : letI := leviPointTopology l hl
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IntertwiningMap
        π.representation)
    (ht : t ≠ 0) :
    letI := leviPointTopology l hl
    ∃ j : σ.representation.IntertwiningMap
      ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj π).representation, j ≠ 0 := by
  let := leviPointTopology l hl
  let σ' := SmoothRep.universeLift.{u} σ
  let e := leviInductionEquivOfEquiv p l r hp hl hr hmul σ σ'
    (SmoothRep.universeLiftEquiv σ)
  let t' := t.comp e.symm.toIntertwiningMap
  have ht' : t' ≠ 0 := by
    intro hz
    apply ht
    ext x
    change t x = 0
    have hx := congrArg (fun f => f (e x)) hz
    change t (e.symm (e x)) = 0 at hx
    simpa only [e.symm_apply_apply] using hx
  let : (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).Additive :=
    { map_add := by
        intro A B f g
        apply ObjectProperty.hom_ext
        ext x
        rfl }
  let j' := adj.homEquiv σ' π (SmoothRep.ofHom t')
  have hj' : j' ≠ 0 := by
    intro hz
    have hz' : SmoothRep.ofHom t' = 0 := (adj.homEquiv σ' π).injective (by
      simpa only [Adjunction.homAddEquiv_zero] using hz)
    exact ht' (congrArg SmoothRep.hom hz')
  refine ⟨(SmoothRep.hom j').comp (SmoothRep.universeLiftEquiv σ).toIntertwiningMap, ?_⟩
  intro hz
  apply hj'
  apply ObjectProperty.hom_ext
  ext x
  obtain ⟨x, rfl⟩ := (SmoothRep.universeLiftEquiv σ).surjective x
  exact congrArg (fun f => f x) hz

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (hG : IsConnectedReductive G)
  {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M)
  (ha : IsSplitComponent a)

include hG ha in
/-- A regular identity piece and a supplied second adjunction embed every
irreducible quotient of the induced representation into induction from `Q`.
The source and target are the published actual induction objects. -/
theorem exists_regularOppositeQuotientEmbedding
    (adj : letI := leviPointTopology l hl
      leviInductionFunctor.{u, max u v} p l r hp hr hl hmul ⊣
        leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hirr : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hreg : IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ)
    (eS : letI := leviPointTopology l hl
      ((boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).obj σ).toRepresentation.Equiv σ.representation)
    (π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G))
    (hπ : letI := leviPointTopology l hl
      Classification.IsIrreducibleQuotient
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation π.representation) :
    letI := leviPointTopology l hl
    ∃ j : π.representation.IntertwiningMap
      ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj σ).representation,
      Function.Injective j := by
  let := leviPointTopology l hl
  obtain ⟨hπirr, t, ht⟩ := hπ
  let : Nontrivial π :=
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible π.representation hπirr
  have ht0 : t ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    obtain ⟨y, hy⟩ := ht x
    apply hx
    simpa only [hz, Representation.IntertwiningMap.coe_zero, Pi.zero_apply] using hy.symm
  obtain ⟨j, hj⟩ := exists_nonzero_oppositeJacquetMap p l r hp hl hr hmul
    q lQ rQ hq hlQ hrQ hmulQ adj σ π t ht0
  let J := leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ
  let S := (boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (identityParabolicDoubleCoset p q)).obj σ
  have hJt : Function.Surjective (SmoothRep.hom (J.map (SmoothRep.ofHom t))) :=
    leviJacquet_map_surjective q lQ rQ hq hlQ hrQ hmulQ (SmoothRep.ofHom t) ht
  obtain ⟨ret, hret⟩ := Classification.quotient_retraction_of_comaximal hirr S eS
    (rationalPoints.map a)
    (fun b g => (Subgroup.mem_center_iff.mp
      (ha.isCentralSplitTorus.isCentral.map_mem_center b) g).symm)
    hreg (SmoothRep.hom (J.map (SmoothRep.ofHom t))) hJt j hj
  let : Nontrivial σ :=
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible σ.representation hirr
  have hret0 : ret ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : σ)
    have h := congrArg (fun f : σ.representation.IntertwiningMap σ.representation => f x) hret
    change ret (j x) = x at h
    exact hx (by simpa only [hz, Representation.IntertwiningMap.coe_zero, Pi.zero_apply]
      using h.symm)
  let F := (leviFrobeniusReciprocity k G hG Q M U q lQ rQ hq hlQ hrQ hmulQ π σ).choose
  have hemb0 : F.symm ret ≠ 0 := by
    intro hz
    apply hret0
    have h := congrArg F hz
    simpa only [F.apply_symm_apply, map_zero] using h
  let := hπirr
  exact ⟨F.symm ret,
    (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right hemb0⟩

include hG ha in
/-- Finite-length preservation, regularity, an identity-piece equivalence and
the second adjunction give a strong irreducible head of actual induction. -/
theorem exists_regularOppositeLeviHead
    (adj : letI := leviPointTopology l hl
      leviInductionFunctor.{u, max u v} p l r hp hr hl hmul ⊣
        leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ)
    (hfinite : letI := leviPointTopology l hl
      SmoothRep.PreservesFiniteLength (leviInductionFunctor.{u, v} p l r hp hr hl hmul))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hirr : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hadm : letI := leviPointTopology l hl; σ.IsAdmissible)
    (hreg : IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ)
    (eS : letI := leviPointTopology l hl
      ((boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).obj σ).toRepresentation.Equiv σ.representation) :
    letI := leviPointTopology l hl
    ∃ π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
      Classification.IsIrreducibleHead
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation π.representation := by
  let := leviPointTopology l hl
  obtain ⟨π, hπ⟩ := exists_irreducibleLeviInductionQuotient p l r hp hl hr hmul hfinite σ hirr
  refine ⟨π, Classification.smooth_isIrreducibleHead_of_finrank_one _
    ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj σ) ?_ ?_ π hπ⟩
  · exact pqRegular_intertwining_finrank_eq_one hG p l r hp hl hr hmul
      q lQ rQ hq hlQ hrQ hmulQ a ha σ hreg eS hadm hirr
  · intro π' hπ'
    exact exists_regularOppositeQuotientEmbedding p l r hp hl hr hmul
      q lQ rQ hq hlQ hrQ hmulQ hG a ha adj σ hirr hreg eS π' hπ'

/-- Choose the actual strong head and its certificate from the stated inputs. -/
def regularOppositeLeviHead
    (adj : letI := leviPointTopology l hl
      leviInductionFunctor.{u, max u v} p l r hp hr hl hmul ⊣
        leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ)
    (hfinite : letI := leviPointTopology l hl
      SmoothRep.PreservesFiniteLength (leviInductionFunctor.{u, v} p l r hp hr hl hmul))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hirr : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hadm : letI := leviPointTopology l hl; σ.IsAdmissible)
    (hreg : IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ)
    (eS : letI := leviPointTopology l hl
      ((boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).obj σ).toRepresentation.Equiv σ.representation) :
    letI := leviPointTopology l hl
    {π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G) //
      Classification.IsIrreducibleHead
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation π.representation} :=
  ⟨(exists_regularOppositeLeviHead p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
      hG a ha adj hfinite σ hirr hadm hreg eS).choose,
    (exists_regularOppositeLeviHead p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
      hG a ha adj hfinite σ hirr hadm hreg eS).choose_spec⟩

end Langlands.Aubert.General.RepresentedParabolic
