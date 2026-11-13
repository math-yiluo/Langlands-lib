import Langlands.Representation.CuspidalSupport.CenterFiniteHoweStatement
import Langlands.Representation.CuspidalSupport.FiniteTypeCenterAdmissibleStatement
import Langlands.Representation.CuspidalSupport.FiniteTypeComponentCharacterizationStatement
import Langlands.Representation.CuspidalSupport.BernsteinCentralIdempotentStatements
import Langlands.Representation.CuspidalSupport.CentralProjectorSupport
import Langlands.Representation.Smooth.Admissibility.HoweStatement
import Langlands.Representation.Category.UniverseLiftFunctor
import Langlands.Representation.Category.UniverseLiftFinitenessProof
import Langlands.Representation.Jacquet.StandardBernsteinFixedVectorReduction
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.Representation.CuspidalSupport.RationalSummandEndCenterReduction

/-! # Renard VI.10.8 from VI.6.3, VI.7.4 and VI.10.7

A conditional reduction of the centre form of Howe's theorem (Renard VI.10.8):
the three implications and the finite-length conclusion follow from Howe's
theorem VI.6.3, the Theorem and Proposition of VI.10.7 and the central
idempotents of VI.7.4, which are explicit hypotheses of
`centerFiniteHowe_of_inputs`. The elementary centre lemmas in
`Langlands.SmoothRep` carry no hypotheses.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u v uR uG uV uX uI

namespace Langlands.SmoothRep

section Idempotents

variable {R : Type uR} [Field R] [CharZero R] {V : Type uV} [AddCommGroup V] [Module R V]
  {I : Type uI}

/-- A family of commuting idempotent endomorphisms which sums to the identity,
with finitely many nonzero terms at each vector, is pairwise orthogonal. -/
theorem orthogonal_of_pointwise_complete
    (p : I → Module.End R V) (hidem : ∀ i, p i * p i = p i)
    (hcomm : ∀ i j, p i * p j = p j * p i)
    (hfin : ∀ x, (Function.support fun i => p i x).Finite)
    (hsum : ∀ x, ∑ᶠ i, p i x = x) {s t : I} (hst : s ≠ t) :
    p s * p t = 0 := by
  classical
  have hcomm' : ∀ i j x, p i (p j x) = p j (p i x) := fun i j x => by
    simpa using congrArg (fun f : Module.End R V => f x) (hcomm i j)
  have hidem' : ∀ i x, p i (p i x) = p i x := fun i x => by
    simpa using congrArg (fun f : Module.End R V => f x) (hidem i)
  -- Main claim, by induction on the number of support indices outside `A`.
  have key : ∀ (n : ℕ) (A : Finset I) (w : V), 2 ≤ A.card → (∀ a ∈ A, p a w = w) →
      ((hfin w).toFinset \ A).card ≤ n → w = 0 := by
    intro n
    induction n with
    | zero =>
      intro A w hA hAw hcard
      have hsub : (Function.support fun i => p i w) ⊆ (A : Set I) := by
        intro i hi
        have hi' : i ∈ (hfin w).toFinset := (hfin w).mem_toFinset.mpr hi
        by_contra hiA
        have : i ∈ (hfin w).toFinset \ A := Finset.mem_sdiff.mpr ⟨hi', hiA⟩
        have hpos := Finset.card_pos.mpr ⟨i, this⟩
        omega
      have h1 : ∑ᶠ i, p i w = ∑ i ∈ A, p i w := finsum_eq_sum_of_support_subset _ hsub
      have h2 : ∑ i ∈ A, p i w = A.card • w := by
        rw [Finset.sum_congr rfl hAw, Finset.sum_const]
      have h3 : (A.card : R) • w = w := by
        rw [Nat.cast_smul_eq_nsmul, ← h2, ← h1, hsum w]
      have h4 : ((A.card : R) - 1) • w = 0 := by
        rw [sub_smul, h3, one_smul, sub_self]
      have hne : ((A.card : R) - 1) ≠ 0 := by
        intro h
        have : (A.card : R) = ((1 : ℕ) : R) := by rw [Nat.cast_one]; exact sub_eq_zero.mp h
        have := Nat.cast_injective (R := R) this
        omega
      exact (smul_eq_zero.mp h4).resolve_left hne
    | succ n ih =>
      intro A w hA hAw hcard
      by_cases hempty : ((hfin w).toFinset \ A).Nonempty
      · obtain ⟨q, hq⟩ := hempty
        have hqA : q ∉ A := (Finset.mem_sdiff.mp hq).2
        -- The two pieces `p q w` and `w - p q w`.
        have hsupp1 : ∀ i, p i w = 0 → p i (p q w) = 0 := fun i hi => by
          rw [hcomm' i q, hi, map_zero]
        have hsupp2 : ∀ i, p i w = 0 → p i (w - p q w) = 0 := fun i hi => by
          rw [map_sub, hcomm' i q, hi, map_zero, sub_zero]
        have hcard' : ((hfin w).toFinset \ A).card - 1 ≤ n := by omega
        have hw1 : p q w = 0 := by
          apply ih (insert q A) (p q w)
          · exact hA.trans (Finset.card_le_card (Finset.subset_insert q A))
          · intro a ha
            rcases Finset.mem_insert.mp ha with rfl | ha
            · exact hidem' a w
            · rw [hcomm' a q, hAw a ha]
          · refine le_trans (Finset.card_le_card ?_) ((Finset.card_erase_of_mem hq).symm ▸ hcard')
            intro i hi
            obtain ⟨hi1, hi2⟩ := Finset.mem_sdiff.mp hi
            have hi1' : p i (p q w) ≠ 0 := (hfin _).mem_toFinset.mp hi1
            refine Finset.mem_erase.mpr ⟨fun h => hi2 (h ▸ Finset.mem_insert_self _ _), ?_⟩
            refine Finset.mem_sdiff.mpr ⟨(hfin w).mem_toFinset.mpr ?_,
              fun h => hi2 (Finset.mem_insert_of_mem h)⟩
            exact fun h => hi1' (hsupp1 i h)
        have hw2 : w - p q w = 0 := by
          apply ih A (w - p q w) hA
          · intro a ha
            rw [map_sub, hcomm' a q, hAw a ha]
          · refine le_trans (Finset.card_le_card ?_) ((Finset.card_erase_of_mem hq).symm ▸ hcard')
            intro i hi
            obtain ⟨hi1, hi2⟩ := Finset.mem_sdiff.mp hi
            have hi1' : p i (w - p q w) ≠ 0 := (hfin _).mem_toFinset.mp hi1
            refine Finset.mem_erase.mpr ⟨?_, ?_⟩
            · rintro rfl
              apply hi1'
              rw [map_sub, hidem', sub_self]
            · refine Finset.mem_sdiff.mpr ⟨(hfin w).mem_toFinset.mpr ?_, hi2⟩
              exact fun h => hi1' (hsupp2 i h)
        rw [hw1, sub_zero] at hw2
        exact hw2
      · rw [Finset.not_nonempty_iff_eq_empty] at hempty
        exact ih A w hA hAw (by rw [hempty]; simp)
  ext x
  let w := p s (p t x)
  have hs : p s w = w := hidem' s _
  have ht : p t w = w := by
    change p t (p s (p t x)) = p s (p t x)
    rw [hcomm' t s, hidem']
  have hA : 2 ≤ ({s, t} : Finset I).card := by
    rw [Finset.card_pair hst]
  have := key _ {s, t} w hA (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hs
    · rw [Finset.mem_singleton.mp ha]; exact ht) le_rfl
  simpa [w] using this

end Idempotents

section UniverseCenter

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- Restrict a central transformation of the lifted category along the fully
faithful carrier lift. -/
def catCenterUniverseRestrict
    (z : CatCenter (SmoothRep.{0, uG, max uV uX} ℂ G)) :
    CatCenter (SmoothRep.{0, uG, uV} ℂ G) where
  app X := (universeLiftFunctor.{uX, uG, uV} G).preimage
    (z.app ((universeLiftFunctor.{uX, uG, uV} G).obj X))
  naturality X Y f := by
    apply (universeLiftFunctor.{uX, uG, uV} G).map_injective
    simp only [Functor.id_obj, Functor.id_map, Functor.map_comp, Functor.map_preimage]
    exact (z.naturality ((universeLiftFunctor.{uX, uG, uV} G).map f))

variable {G}

/-- A central transformation acts on a carrier lift through its restriction. -/
theorem hom_app_universeLift
    (z : CatCenter (SmoothRep.{0, uG, max uV uX} ℂ G))
    (A : SmoothRep.{0, uG, uV} ℂ G) (x : universeLift.{uX} A) :
    hom (z.app (universeLift.{uX} A)) x =
      ULift.up (hom ((catCenterUniverseRestrict.{uG, uV, uX} G z).app A) x.down) := by
  have h := (universeLiftFunctor.{uX, uG, uV} G).map_preimage
    (z.app ((universeLiftFunctor.{uX, uG, uV} G).obj A))
  rw [← universeLiftFunctor_map_apply]
  exact congrArg (fun f => hom f x) h.symm

/-- The centre operator span on a carrier lift is finite-dimensional when it is
on the original representation. -/
theorem finiteDimensional_centerOperatorSpan_universeLift
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : FiniteDimensional ℂ (centerOperatorSpan A)) :
    FiniteDimensional ℂ (centerOperatorSpan (universeLift.{uX} A)) := by
  let e : A ≃ₗ[ℂ] universeLift.{uX} A := (universeLiftEquiv.{uX} A).toLinearEquiv
  have hle : centerOperatorSpan (universeLift.{uX} A) ≤
      (centerOperatorSpan A).map e.conj.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    refine ⟨(hom ((catCenterUniverseRestrict.{uG, uV, uX} G z).app A)).toLinearMap,
      Submodule.subset_span ⟨_, rfl⟩, ?_⟩
    ext x
    change e (hom ((catCenterUniverseRestrict.{uG, uV, uX} G z).app A) (e.symm x)) =
      hom (z.app (universeLift.{uX} A)) x
    rw [hom_app_universeLift]
    rfl
  exact Submodule.finiteDimensional_of_le hle

end UniverseCenter

section CenterOperators

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- On one object, the action of the categorical centre is multiplicative. -/
theorem centerOperator_mul (A : SmoothRep.{0, uG, uV} ℂ G)
    (x y : CatCenter (SmoothRep.{0, uG, uV} ℂ G)) :
    (hom ((x * y).app A)).toLinearMap =
      (hom (x.app A)).toLinearMap * (hom (y.app A)).toLinearMap := by
  rw [CatCenter.mul_app']
  rfl

/-- Central idempotents with pointwise finite sum to the identity act on each
object by pairwise orthogonal projections. -/
theorem centerOperator_orthogonal {I : Type uI} (A : SmoothRep.{0, uG, uV} ℂ G)
    (e : I → CatCenter (SmoothRep.{0, uG, uV} ℂ G)) (hidem : ∀ s, IsIdempotentElem (e s))
    (hfin : ∀ v : A, (Function.support fun s => hom ((e s).app A) v).Finite)
    (hsum : ∀ v : A, ∑ᶠ s, hom ((e s).app A) v = v) {s t : I} (hst : s ≠ t) :
    ((hom ((e s).app A)).toLinearMap).comp (hom ((e t).app A)).toLinearMap = 0 := by
  have h := orthogonal_of_pointwise_complete
    (fun s => (hom ((e s).app A)).toLinearMap)
    (fun s => by rw [← centerOperator_mul, (hidem s).eq])
    (fun s t => by
      rw [← centerOperator_mul, ← centerOperator_mul,
        show e s * e t = e t * e s from Std.Commutative.comm _ _])
    hfin hsum hst
  exact h

end CenterOperators

end Langlands.SmoothRep

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.CuspidalSupport Langlands.SmoothRep
open Langlands.AlgebraicGeometry.PointTopology Langlands.Aubert.General.RationalPointFamily

/-- Renard VI.10.8, proof of `(2) ∧ (3) ⇒ (1)` from the Proposition of VI.10.7 and the
central idempotents of VI.7.4: an admissible `ℨ(G)`-finite representation is of finite type.
The argument runs on the carrier lift to `Type (max u v)`. -/
theorem finiteType_of_admissible_centerFinite
    (hChar : FiniteTypeComponentCharacterizationStatement.{u, v})
    (hIdem : BernsteinCentralIdempotentStatement.{u, max u v})
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      π.IsAdmissible → FiniteDimensional ℂ (centerOperatorSpan π) →
        Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π hadm hcf
  have : LocallyOfFiniteType G.X.hom := by
    have := hG.smooth
    infer_instance
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  let family := Jacquet.standardBernsteinFamily i ν hG hi hν
  obtain ⟨e, hidem, hid, -, hsupp⟩ := hIdem k G T i ν family
  let L : SmoothRep.{0, u, max u v} ℂ (rationalPoints G) := universeLift.{u} π
  have hcfL : FiniteDimensional ℂ (centerOperatorSpan L) :=
    finiteDimensional_centerOperatorSpan_universeLift π hcf
  have hadmL : L.IsAdmissible := (Langlands.SmoothRep.isAdmissible_universeLift_iff π).mpr hadm
  have hfinite : (centralOperatorSupport L e).Finite := by
    apply finite_centralOperatorSupport L e hcfL
    · intro s
      exact (centerOperator_mul L (e s) (e s)).symm.trans (by rw [(hidem s).eq])
    · intro s t hst
      exact centerOperator_orthogonal L e hidem (fun v => (hsupp L v).1)
        (fun v => (hsupp L v).2) hst
  have hsub : {s : BernsteinInertialClass.{u, max u v} i ν family |
      ∃ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
        SmoothRep.IsSubquotient σ L ∧ IsBernsteinInertialSupport i ν family s σ} ⊆
      centralOperatorSupport L e := by
    rintro s ⟨σ, hσL, hσs⟩
    obtain ⟨a, -, hσirr, -⟩ := id hσs
    have hblock : bernsteinBlockProperty i ν family s σ := by
      rw [bernsteinBlockProperty_iff_saturated]
      intro ρ hρ hρσ
      obtain ⟨f⟩ := NormalHecke.nonempty_iso_of_isSubquotient hσirr hρ hρσ
      exact hσs.of_iso f.symm
    have : σ.representation.IsIrreducible := hσirr
    have hnt : Nontrivial σ.representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) _
    have : Nontrivial σ := hnt
    exact mem_centralOperatorSupport_of_subquotient e s hσL (hid s σ hblock)
  have hL : Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) L.representation.asModule :=
    (hChar k G T i ν family L).mpr
      ⟨IsAdmissible.isCenterAdmissible L hadmL, hfinite.subset hsub⟩
  exact (moduleFinite_universeLift_iff π).mp hL

/-- Renard VI.10.8 (finite type, admissibility and `ℨ(G)`-finiteness: any two imply the
third, and then finite length), from Howe's theorem VI.6.3, the Theorem and Proposition of
VI.10.7 and the central idempotents of VI.7.4. -/
theorem centerFiniteHowe_of_inputs
    (hHowe : SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement.{u, v})
    (hTheorem : FiniteTypeCenterAdmissibleStatement.{u, v})
    (hChar : FiniteTypeComponentCharacterizationStatement.{u, v})
    (hIdem : BernsteinCentralIdempotentStatement.{u, max u v}) :
    CenterFiniteHoweStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π
  dsimp only
  intro h
  have hTA : Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule →
      π.IsAdmissible → FiniteDimensional ℂ (centerOperatorSpan π) ∧ π.HasFiniteLength :=
    fun hfin hadm => ⟨finite_centerOperatorSpan_of_finiteType_admissible π hfin hadm,
      hHowe k G hG π hfin hadm⟩
  rcases h with ⟨hfin, hadm⟩ | ⟨hfin, hcf⟩ | ⟨hadm, hcf⟩
  · exact ⟨hfin, hadm, hTA hfin hadm⟩
  · have hadm : π.IsAdmissible :=
      isAdmissible_of_centerAdmissible_centerFinite π (hTheorem k G hG π hfin) hcf
    exact ⟨hfin, hadm, hTA hfin hadm⟩
  · have hfin := finiteType_of_admissible_centerFinite hChar hIdem k G hG π hadm hcf
    exact ⟨hfin, hadm, hTA hfin hadm⟩

/-- Renard VI.10.8 as a consequence of Howe's theorem VI.6.3, the Theorem and Proposition
of VI.10.7 and the central idempotents of VI.7.4: the implication from these four
published statements (at the displayed universes) to `CenterFiniteHoweStatement`. -/
def CenterFiniteHoweReductionStatement : Prop :=
  SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement.{u, v} →
  FiniteTypeCenterAdmissibleStatement.{u, v} →
  FiniteTypeComponentCharacterizationStatement.{u, v} →
  BernsteinCentralIdempotentStatement.{u, max u v} →
  CenterFiniteHoweStatement.{u, v}

/-- The reduction statement holds. -/
theorem centerFiniteHoweReduction : CenterFiniteHoweReductionStatement.{u, v} :=
  centerFiniteHowe_of_inputs

end Langlands.Aubert.General.RepresentedParabolic
