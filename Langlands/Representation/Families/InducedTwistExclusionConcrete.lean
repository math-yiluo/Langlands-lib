import Langlands.Representation.Families.InducedTwistExclusionAlgebra
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Geometric.FullIntersectionIrreducible
import Langlands.Representation.Geometric.SelfIntersectionLevi
import Langlands.Representation.Exponents.SupercuspidalIndexComparison
import Langlands.GroupScheme.Rational.MaximalTorusParameterExistenceProof
import Langlands.GroupScheme.Rational.ParabolicLeviIntersectionReduction
import Langlands.Representation.Filtration.GluedAtObject
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Representation.EquivalencePullback
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.CuspidalSupport.GroupTransport

/-! # Frobenius reciprocity and Jacquet maps for subquotients of an induced representation -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance exclusionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- For a nonzero invariant subspace `S` of `I = i_P(σ)`, the Frobenius map
`r_P(I) → σ` of the identity of `I` is nonzero on the image of `r_P(S) → r_P(I)`. -/
theorem exists_mem_range_jacquet_subtype_frobenius_ne_zero (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (S : Subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
    (hS : S ≠ ⊥) :
    letI := leviPointTopology l hl
    ∃ Φ : ((leviJacquetFunctor p l r hp hr hl hmul).obj
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ)).representation.IntertwiningMap
          σ.representation,
      ∃ w ∈ (SmoothRep.hom ((leviJacquetFunctor p l r hp hr hl hmul).map
          (SmoothRep.subtype _ S))).range, Φ w ≠ 0 := by
  let := leviPointTopology l hl
  obtain ⟨eS, heS⟩ := leviFrobeniusReciprocity k G hG P M U p l r hp hl hr hmul
    (SmoothRep.subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj σ) S) σ
  obtain ⟨eI, heI⟩ := leviFrobeniusReciprocity k G hG P M U p l r hp hl hr hmul ((leviInductionFunctor p l r hp hr hl hmul).obj σ) σ
  refine ⟨eI (Representation.IntertwiningMap.id _), ?_⟩
  have hF : SmoothRep.hom (SmoothRep.subtype ((leviInductionFunctor p l r hp hr hl hmul).obj σ) S) ≠ 0 := by
    intro h
    apply hS
    apply le_bot_iff.mp
    intro x hx
    have hx0 : (SmoothRep.hom (SmoothRep.subtype _ S)) ⟨x, hx⟩ = 0 := by
      rw [h]
      rfl
    exact (Submodule.mem_bot ℂ).mpr hx0
  have heF : eS (SmoothRep.hom (SmoothRep.subtype ((leviInductionFunctor p l r hp hr hl hmul).obj σ) S)) ≠ 0 := by
    intro h
    exact hF (eS.injective (h.trans (map_zero eS).symm))
  obtain ⟨y, hy⟩ : ∃ y, eS (SmoothRep.hom (SmoothRep.subtype ((leviInductionFunctor p l r hp hr hl hmul).obj σ) S)) y ≠ 0 := by
    by_contra h
    push Not at h
    exact heF (Representation.IntertwiningMap.ext (LinearMap.ext h))
  obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective
    (SmoothRep.subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj σ) S).representation (pointImage (r ≫ p)) 1 y
  refine ⟨_, ⟨Jacquet.Localization.mk _ (pointImage (r ≫ p)) 1 x, rfl⟩, ?_⟩
  rw [heS] at hy
  change eI (Representation.IntertwiningMap.id _)
    (Jacquet.Localization.mk ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation
      (pointImage (r ≫ p)) 1 x.1) ≠ 0
  rw [heI]
  exact hy

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k] [TopologicalSpace k]
  [IsAffineHom G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- A rational point of the parabolic conjugates its Levi into the parabolic. -/
theorem range_levi_le_range_comp_innerIso_of_mem (p : P ⟶ G) (l : M ⟶ P)
    {z : rationalPoints G} (hz : z ∈ pointImage p) :
    SubgroupFunctor.range (l ≫ p) ≤ SubgroupFunctor.range (p ≫ (G.innerIso z).hom) := by
  rw [SubgroupFunctor.le_def]
  intro V y hy
  rw [MaximalTorusParameterExistence.mem_range_comp_innerIso_iff]
  have hzV : G.constantPoint z V ∈ (SubgroupFunctor.range p).carrier V :=
    (SubgroupFunctor.range p).comp_mem (Over.homMk V.hom) hz
  have hyp : y ∈ (SubgroupFunctor.range p).carrier V :=
    (SubgroupFunctor.le_def.mp (RepresentedParabolicLeviIntersection.range_comp_le l p)) V hy
  exact mul_mem (mul_mem (inv_mem hzV) hyp) hzV

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k] [TopologicalSpace k]
  [IsAffineHom G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- A representative of the identity double coset `P(k) 1 P(k)` lies in `P(k)`. -/
theorem mem_pointImage_of_doubleCoset_eq_one (p : P ⟶ G) {z : rationalPoints G}
    (hz : DoubleCoset.mk (pointImage p) (pointImage p) z =
      DoubleCoset.mk (pointImage p) (pointImage p) 1) : z ∈ pointImage p := by
  obtain ⟨h, hh, k', hk', hzk⟩ := DoubleCoset.eq.mp hz.symm
  rw [hzk, mul_one]
  exact mul_mem hh hk'

/-- **Exclusion from separated geometric-lemma pieces.** Let `σ` be irreducible admissible on
`M(k)`, and let `χ` be a generalized eigencharacter of `σ` on the split component `A_M(k)`.
Suppose that, in a represented geometric lemma for `r_P ∘ i_P`, no piece outside the identity
double coset has `χ` as a generalized eigencharacter on `A_M(k)`. Then for every nonzero
invariant subspace `S` of `i_P(σ)`, the character `χ` is not a generalized eigencharacter of
`r_P(i_P(σ) / S)` on `A_M(k)`. -/
theorem not_isGeneralizedEigencharacter_jacquet_quotient_of_pieceSeparation
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσirr : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hσadm : letI := leviPointTopology l hl; σ.IsAdmissible)
    {m : ℕ}
    (c : Fin m ≃ DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
      (pointImage p : Set (rationalPoints G)))
    (z : Fin m → rationalPoints G)
    (hz : ∀ i, DoubleCoset.mk (pointImage p) (pointImage p) (z i) = c i)
    (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul (z i))
    (hglue : IsGluedFrom
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul p l r hp hr hl hmul)
      (fun i => (D i).pieceFunctor))
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : letI := leviPointTopology l hl
      IsGeneralizedEigencharacter (σ.representation.comp (rationalPoints.map a)) χ)
    (hsep : ∀ i, c i ≠ DoubleCoset.mk (pointImage p) (pointImage p) 1 →
      ¬ IsGeneralizedEigencharacter
        (((D i).pieceFunctor.obj σ).ρ.comp (rationalPoints.map a)) χ)
    (S : Subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
    (hS : S ≠ ⊥) :
    letI := leviPointTopology l hl
    ¬ IsGeneralizedEigencharacter
      (((leviJacquetFunctor p l r hp hr hl hmul).obj
        (SmoothRep.quotient _ S)).representation.comp (rationalPoints.map a)) χ := by
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have hι : ∀ t, rationalPoints.map a t ∈ Subgroup.center (rationalPoints M) :=
    fun t => ha.1.2.map_mem_center t
  -- the filtration of `r_P(i_P σ)` by the pieces
  obtain ⟨n, e, s, hs⟩ := hglue.exists_selected_filtration σ (fun _ => True)
    (fun _ h => absurd trivial h)
  let i0 : Fin m := c.symm (DoubleCoset.mk (pointImage p) (pointImage p) 1)
  let j0 : Fin n := e.symm ⟨i0, trivial⟩
  have hother : ∀ j, j ≠ j0 → ¬ IsGeneralizedEigencharacter
      ((s.gradedRepresentation j).ρ.comp (rationalPoints.map a)) χ := by
    intro j hj hjχ
    obtain ⟨E⟩ := hs j
    have hne : c (e j).val ≠ DoubleCoset.mk (pointImage p) (pointImage p) 1 := by
      intro h
      apply hj
      have hi : (e j).val = i0 := by
        change (e j).val = c.symm _
        rw [← h, Equiv.symm_apply_apply]
      change j = e.symm ⟨i0, trivial⟩
      rw [← hi]
      simp
    exact hsep _ hne ((isGeneralizedEigencharacter_iff_of_equiv
      (Cohomology.HyperextAbutment.equivComp E (rationalPoints.map a)) χ).mp hjχ)
  have hgr : (s.gradedRepresentation j0).ρ.IsIrreducible := by
    obtain ⟨E⟩ := hs j0
    have he0 : (e j0).val = i0 := by simp [j0]
    have hz0 : z (e j0).val ∈ pointImage p := by
      apply mem_pointImage_of_doubleCoset_eq_one p
      rw [hz, he0]
      exact Equiv.apply_symm_apply c _
    have : IsIso (D (e j0).val).p' :=
      (D (e j0).val).isIso_p'_of_range_le (range_levi_le_range_comp_innerIso_of_mem p l hz0)
    have : IsIso (D (e j0).val).q' := (D (e j0).val).isIso_q'_of_isIso_p'
    exact (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv E).mpr
      ((D (e j0).val).pieceFunctor_isIrreducible_of_isIso σ hσirr)
  -- admissibility of `r_P(i_P σ)`
  have hIadm : ((leviInductionFunctor p l r hp hr hl hmul).obj σ).IsAdmissible :=
    leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement
      arbitraryParabolicQuotientCompact hG p l r hp hl hr hmul σ hσadm
  have hJadm := arbitraryParabolicJacquetAdmissibility k G hG P M U p l r hp hl hr hmul
    ((leviInductionFunctor p l r hp hr hl hmul).obj σ) hIadm
  have hE : IsAdmissible ((leviJacquetFunctor p l r hp hr hl hmul).obj
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ)).representation :=
    isAdmissible_comp_continuousMulEquiv _ (leviPointsEquiv p l hp hl) hJadm
  -- the Frobenius map, nonzero on the image of `r_P(S)`
  obtain ⟨Φ, w, hw, hΦw⟩ :=
    exists_mem_range_jacquet_subtype_frobenius_ne_zero hG p l r hp hl hr hmul σ S hS
  -- the quotient map `r_P(i_P σ) → r_P(i_P σ / S)`
  let q := SmoothRep.hom ((leviJacquetFunctor p l r hp hr hl hmul).map
    (SmoothRep.mkQ ((leviInductionFunctor p l r hp hr hl hmul).obj σ) S))
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective
      (SmoothRep.quotient ((leviInductionFunctor p l r hp hr hl hmul).obj σ) S).representation
      (pointImage (r ≫ p)) 1 y
    obtain ⟨x', rfl⟩ := SmoothRep.mkQ_surjective
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ) S x
    exact ⟨Jacquet.Localization.mk _ (pointImage (r ≫ p)) 1 x', rfl⟩
  have hqW : ∀ w ∈ (SmoothRep.hom ((leviJacquetFunctor p l r hp hr hl hmul).map
      (SmoothRep.subtype _ S))).range, q w = 0 := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective
      (SmoothRep.subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj σ) S).representation
      (pointImage (r ≫ p)) 1 y
    have hx : SmoothRep.hom (SmoothRep.mkQ ((leviInductionFunctor p l r hp hr hl hmul).obj σ) S)
        x.1 = 0 := (Submodule.Quotient.mk_eq_zero _).mpr x.2
    change Jacquet.Localization.mk _ (pointImage (r ≫ p)) 1
      (SmoothRep.hom (SmoothRep.mkQ ((leviInductionFunctor p l r hp hr hl hmul).obj σ) S) x.1) = 0
    rw [hx, map_zero]
  exact InducedTwistExclusion.not_isGeneralizedEigencharacter_of_isolatedGrade
    (rationalPoints.map a) hι hE s j0 χ hother hgr σ.representation σ.isSmooth hσirr hχ Φ _
    ⟨w, hw, hΦw⟩ _ ((leviJacquetFunctor p l r hp hr hl hmul).obj
      (SmoothRep.quotient _ S)).isSmooth q hq hqW

end Langlands.Aubert.General.RepresentedParabolic
