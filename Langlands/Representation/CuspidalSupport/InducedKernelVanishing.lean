import Langlands.Representation.CuspidalSupport.SelfIntersectionPieceVanishing
import Langlands.Representation.Filtration.NaturalHomStepVanishing
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof
import Langlands.Representation.Geometric.RepresentedGeometricLemmaGeometryProof
import Langlands.Representation.Geometric.RepresentedGeometricLemmaSupportGradedStatement
import Langlands.Representation.Geometric.ClosedOrbitLast

/-! # Natural maps from `r_P ∘ i_P` vanish off the identity coset -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance inducedKernelAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
private theorem quotientMap_eq_iff' (H : Subgroup (rationalPoints G)) (x y : rationalPoints G) :
    Induction.quotientMap H x = Induction.quotientMap H y ↔ y * x⁻¹ ∈ H :=
  Quotient.eq.trans QuotientGroup.rightRel_apply

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
set_option maxHeartbeats 800000 in
/-- If the last orbit of an ordering of `P(F) \ G(F) / P(F)` is the identity coset, then the
class in `r_P(i_P σ)` of an induced function `f` with `f(1) = 0` lies in the step of the
support filtration spanned by the other orbits. -/
theorem leviJacquet_mk_mem_step_of_eval_one {n : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage p) (n + 1))
    (hlast : s.representative (Fin.last n) ∈ pointImage p)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (f : letI := leviPointTopology l hl; (leviInductionFunctor p l r hp hr hl hmul).obj σ)
    (hf : letI := leviPointTopology l hl
      Induction.eval (pointImage p)
        (inducingRepresentation
          (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
          (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
          (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f 1 = 0) :
    letI := leviPointTopology l hl
    Jacquet.Localization.mk ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation
        (pointImage (r ≫ p)) 1 f ∈
      ((leviJacquetSupportFiltration.{u, v} p l r hp hr hl hmul p l r hp hr hl hmul s).step
        ⟨n, by omega⟩).obj σ := by
  let := leviPointTopology l hl
  refine Exists.intro f (And.intro ?_ rfl)
  intro x hx
  obtain ⟨i, hix⟩ := s.covers (Induction.quotientMap (pointImage p) x)
  by_cases hi : i.val < n
  · exact ⟨i, hi, hix⟩
  · exfalso
    have hil : i = Fin.last n := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    rw [hil, Geometric.cosetOrbit_self_eq_singleton _ _ hlast] at hix
    have hxP : x ∈ pointImage p := by
      have h1 := (quotientMap_eq_iff' (pointImage p) _ _).mp hix
      rw [one_mul] at h1
      simpa using (pointImage p).inv_mem h1
    apply hx
    have hcov := f.1.2 ⟨x, hxP⟩ 1
    have hf' : f.1.1 1 = 0 := hf
    change f.1.1 x = 0
    refine Eq.trans ?_ (Eq.trans hcov ?_)
    · exact congrArg f.1.1 (mul_one x).symm
    · rw [hf', map_zero]

set_option maxHeartbeats 800000 in
/-- On the graded pieces of the support filtration at orbits whose representative is not in
`M(F)`, every map to `σ` commuting with the endomorphisms of `σ` is zero, for `σ` as in
`pieceFunctor_hom_eq_zero_of_not_mem`. -/
theorem leviJacquetSupportFiltration_graded_hom_eq_zero (hG : IsConnectedReductive G) {n : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage p) n)
    (E : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      p l r hp hr hl hmul (s.representative i)⁻¹)
    (hF : (leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
      p l r hp hr hl hmul s).HasGradedPieces (fun i => (E i).pieceFunctor))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (hsc : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsSupercuspidal σ)
    (hfix : letI := leviPointTopology l hl
      ∀ t : rationalPoints M,
      (∀ n : ℕ, 0 < n → t ^ n ∉ Plancherel.rationalCommonNormKernel M) →
        ∀ v : σ, σ.representation t v = v → v = 0)
    (i : Fin n) (hi : s.representative i ∉ pointImage (l ≫ p))
    (g : letI := leviPointTopology l hl
      ((leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
        p l r hp hr hl hmul s).graded i).obj σ ⟶ SmoothRep.toRep.obj σ)
    (hg : letI := leviPointTopology l hl
      ∀ a : σ ⟶ σ, ((leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
        p l r hp hr hl hmul s).graded i).map a ≫ g = g ≫ SmoothRep.toRep.map a) :
    g = 0 := by
  let iso := (hF i).some
  let g' := iso.inv.app σ ≫ g
  have hz : ((s.representative i)⁻¹)⁻¹ ∉ pointImage (l ≫ p) := by
    rwa [inv_inv]
  have hzero : g' = 0 := by
    apply pieceFunctor_hom_eq_zero_of_not_mem hG (E i) hz σ hsc hfix g'
    intro a
    change (E i).pieceFunctor.map a ≫ iso.inv.app σ ≫ g = (iso.inv.app σ ≫ g) ≫ _
    rw [← Category.assoc, iso.inv.naturality a, Category.assoc, hg a, Category.assoc]
  have hgg : g = iso.hom.app σ ≫ g' := by
    change g = iso.hom.app σ ≫ iso.inv.app σ ≫ g
    rw [Iso.hom_inv_id_app_assoc]
  rw [hgg, hzero, Limits.comp_zero]

set_option maxHeartbeats 1600000 in
/-- Let `σ` be a supercuspidal representation of `M(F)` in which no element `t` with
`t ^ n ∉ ⁰M(F)` for all `n > 0` fixes a nonzero vector. Let `h : r_P(i_P σ) → σ` be an
`M(F)`-map that intertwines `r_P(i_P a)` with `a` for every endomorphism `a` of `σ`. Then `h`
vanishes on the class of every induced function `f` with `f(1) = 0`. -/
theorem leviJacquetInduction_hom_apply_mk_eq_zero (hG : IsConnectedReductive G)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (hsc : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsSupercuspidal σ)
    (hfix : letI := leviPointTopology l hl
      ∀ t : rationalPoints M,
      (∀ n : ℕ, 0 < n → t ^ n ∉ Plancherel.rationalCommonNormKernel M) →
        ∀ v : σ, σ.representation t v = v → v = 0)
    (h : letI := leviPointTopology l hl
      ((leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul).obj
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ)).representation.IntertwiningMap
        σ.representation)
    (hh : letI := leviPointTopology l hl
      ∀ (a : σ ⟶ σ)
        (y : (leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul).obj
          ((leviInductionFunctor p l r hp hr hl hmul).obj σ)),
        h (SmoothRep.hom ((leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul).map
          ((leviInductionFunctor p l r hp hr hl hmul).map a)) y) = SmoothRep.hom a (h y))
    (f : letI := leviPointTopology l hl; (leviInductionFunctor p l r hp hr hl hmul).obj σ)
    (hf : letI := leviPointTopology l hl
      Induction.eval (pointImage p)
        (inducingRepresentation
          (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
          (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
          (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f 1 = 0) :
    h (Jacquet.Localization.mk ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation
      (pointImage (r ≫ p)) 1 f) = 0 := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  -- The double cosets `P(F) \ G(F) / P(F)` with their intersection data.
  obtain ⟨m, c, z, hz, ⟨D⟩⟩ :=
    representedGeometricLemmaGeometry k G hG P M N P M N p l r hp hl hr hmul
      p l r hp hl hr hmul
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hPclosed := isClosed_pointImage p hp.isClosedSubgroup
  have hfinite : Finite (DoubleCoset.Quotient
      (pointImage p : Set (rationalPoints G)) (pointImage p : Set (rationalPoints G))) :=
    Finite.of_surjective c c.surjective
  obtain ⟨n, ⟨s⟩⟩ :=
    (Geometric.closedSubgroupOrbitOrdering_of_finiteOrbitOrdering
      Langlands.Topology.finiteOrbitOrdering) (rationalPoints G) (pointImage p) (pointImage p)
        hPclosed hPclosed hfinite
  have hbij : Function.Bijective
      (fun i : Fin m => DoubleCoset.mk (pointImage p) (pointImage p) ((z i)⁻¹)⁻¹) := by
    simpa only [inv_inv, hz] using c.bijective
  obtain ⟨e, t0, ht0⟩ := s.classifiedRepresentatives (fun i : Fin m => (z i)⁻¹) hbij
  -- The orbit of the identity coset is closed.
  obtain ⟨j0, hj0⟩ := t0.covers (Induction.quotientMap (pointImage p) 1)
  have hwP : t0.representative j0 ∈ pointImage p := by
    obtain ⟨q, hq⟩ := hj0
    have h1 := (quotientMap_eq_iff' (pointImage p) _ _).mp hq
    rw [one_mul, mul_inv_rev, inv_inv] at h1
    have h2 := (pointImage p).mul_mem q.2 h1
    rwa [mul_inv_cancel_left] at h2
  have : T2Space (Induction.LeftQuotient (pointImage p)) :=
    QuotientIntegration.leftQuotient_t2Space _ hPclosed
  have hclosed : IsClosed
      (Geometric.cosetOrbit (pointImage p) (pointImage p) (t0.representative j0)) := by
    rw [Geometric.cosetOrbit_self_eq_singleton _ _ hwP]
    exact isClosed_singleton
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Fin.pos j0).ne'
  -- Put the identity orbit last.
  let s' := t0.closedOrbitLast j0 hclosed
  have hlast : s'.representative (Fin.last n') = t0.representative j0 :=
    t0.closedOrbitLast_representative_last j0 hclosed
  have hrep (i : Fin (n' + 1)) :
      s'.representative i = (z (e (Geometric.moveLastPermutation j0 i)))⁻¹ :=
    ht0 _
  let E : ∀ i : Fin (n' + 1), GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      p l r hp hr hl hmul (s'.representative i)⁻¹ := fun i => by
    rw [hrep i, inv_inv]
    exact D (e (Geometric.moveLastPermutation j0 i))
  have hF := representedGeometricLemmaSupportGraded_of_orbitComparison.{u, max u v}
      arbitraryParabolicQuotientCompact parabolicRootPresentationExistence
      representedGeometricLemmaOrbitComparison
      k G hG P M N P M N p l r hp hl hr hmul p l r hp hl hr hmul (n' + 1) s' E
  clear_value E s'
  -- The non-identity orbits do not meet `M(F)`.
  have hnot (i : Fin (n' + 1)) (hi : i.val < n') :
      s'.representative i ∉ pointImage (l ≫ p) := by
    intro hmem
    have hne : i ≠ Fin.last n' := by
      intro hil
      rw [hil, Fin.val_last] at hi
      exact lt_irrefl _ hi
    have hdisj : Disjoint
        (Geometric.cosetOrbit (pointImage p) (pointImage p) (s'.representative i))
        (Geometric.cosetOrbit (pointImage p) (pointImage p) (s'.representative (Fin.last n'))) :=
      s'.disjoint hne
    rw [Geometric.cosetOrbit_self_eq_singleton _ _ (pointImage_comp_le p l hmem), hlast,
      Geometric.cosetOrbit_self_eq_singleton _ _ hwP] at hdisj
    exact Set.disjoint_singleton.mp hdisj rfl
  -- `h` as a morphism of representations, natural in `σ`.
  let H : (leviJacquetInductionFunctor.{u, max u v} p l r hp hr hl hmul
      p l r hp hr hl hmul).obj σ ⟶ SmoothRep.toRep.obj σ := Rep.ofHom h
  have hH (a : σ ⟶ σ) :
      (leviJacquetInductionFunctor.{u, max u v} p l r hp hr hl hmul
        p l r hp hr hl hmul).map a ≫ H = H ≫ SmoothRep.toRep.map a := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    exact hh a y
  have hlastP : s'.representative (Fin.last n') ∈ pointImage p := by
    rw [hlast]
    exact hwP
  have hmem := leviJacquet_mk_mem_step_of_eval_one s' hlastP σ f hf
  have hgr := leviJacquetSupportFiltration_graded_hom_eq_zero hG s' E hF σ hsc hfix
  have key := RepFunctorFiltration.hom_apply_eq_zero_of_mem_step_of_lt
    (leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul p l r hp hr hl hmul s')
    σ H hH ⟨n', by omega⟩
  have key2 := key (by
    intro i hi g hg
    apply hgr i (hnot i hi) g
    intro a
    exact hg a)
  exact key2 _ hmem

end Langlands.Aubert.General.RepresentedParabolic
