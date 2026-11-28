import Langlands.GroupScheme.Rational.QuasiSplitRegularConjugate
import Langlands.GroupScheme.Rational.InfiniteFieldStronglyRegularPointReduction
import Langlands.GroupScheme.Absolute.StronglyRegularTorusPointProof
import Langlands.GroupScheme.LocalGroupIsoBorelRefinement
import Langlands.GroupScheme.InnerCocycleTwist
import Langlands.GroupScheme.CocycleAffineRefinement
import Langlands.GroupScheme.GaloisCocycle

/-! # A prescribed maximal torus in a pure inner twist -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1450000

/-- An actual maximal torus in a connected reductive group over an infinite
field contains a rational point with all-test centralizer equal to that torus. -/
theorem IsMaximalTorus.exists_stronglyRegularPoint {F : Type u} [Field F] [Infinite F]
    {H : GroupScheme (Spec (CommRingCat.of F))} (hH : IsConnectedReductive H)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {j : T.toGrp ⟶ H}
    (hj : IsMaximalTorus j) :
    ∃ p : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ T.X,
      ∀ {Z : Over (Spec (CommRingCat.of F))} (c : Z ⟶ H.X),
        c * (toUnit Z ≫ p ≫ j.hom.hom) = (toUnit Z ≫ p ≫ j.hom.hom) * c →
        ∃ s : Z ⟶ T.X, s ≫ j.hom.hom = c := by
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom H.X.hom := hH.isAffineHom
  obtain ⟨hbsurj, hbflat, hbqc⟩ := fieldExtension_fpqc F (AlgebraicClosure F)
  let b := toAlgebraicClosure F
  let : Flat b := hbflat
  let : Surjective b := hbsurj
  let : QuasiCompact b := hbqc
  have hjΩ := (maximalTorusBaseChange F (AlgebraicClosure F) H T j hj.1 hj.2.1).mp hj
  obtain ⟨U, hU, hUne, hUreg⟩ :=
    algClosedStronglyRegularTorusPoint (AlgebraicClosure F) _ hH.baseChange_toAlgebraicClosure _ _ hjΩ
  have hdense : HasDenseRationalPoints F T.X :=
    IsTorus.hasDenseRationalPoints_of_finiteGaloisSplitting torusFiniteGaloisSplitting hj.1
  have hgeo := hasDenseGeometricRationalPoints_of_hasDenseRationalPoints
    (K := AlgebraicClosure F) T.X hdense
  obtain ⟨y, hyU, hy⟩ := hgeo.inter_open_nonempty U hU hUne
  simp only [Set.mem_iUnion, Set.mem_range] at hy
  obtain ⟨p, a, rfl⟩ := hy
  let t := geometricRationalPoint (K := AlgebraicClosure F) T.X p
  have ht : Set.range t.left ⊆ U := by
    have : Subsingleton (Spec (CommRingCat.of (AlgebraicClosure F))) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum (AlgebraicClosure F)))
    rintro _ ⟨a', rfl⟩
    rwa [Subsingleton.elim (α := Spec (CommRingCat.of (AlgebraicClosure F))) a' a]
  refine ⟨p, ?_⟩
  intro Z c hc
  have : Mono j.hom.hom.left := hj.2.1.mono
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  let V := (Over.pullback b).obj Z
  let q : (Over.map b).obj V ⟶ Z := EnvelopeBaseChange.pullbackFst b Z
  have : EffectiveEpi q.left := inferInstanceAs (EffectiveEpi (pullback.fst Z.hom b))
  apply SubgroupFunctor.mem_range_of_comp_mem_range j q
  let c' : V ⟶ ((GroupScheme.baseChange b).obj H).X := (Over.pullback b).map c
  have hc'q : baseChangePointsEquiv b H V c' = q ≫ c :=
    EnvelopeBaseChange.baseChangePointsEquiv_pullback_map b H c
  have hx : baseChangePointsEquiv b H V
      (toUnit V ≫ t ≫ ((GroupScheme.baseChange b).map j).hom.hom) =
        q ≫ toUnit Z ≫ p ≫ j.hom.hom := by
    rw [baseChangePointsEquiv_naturality]
    have htj : t ≫ ((GroupScheme.baseChange b).map j).hom.hom =
        geometricRationalPoint (K := AlgebraicClosure F) H.X (p ≫ j.hom.hom) :=
      geometricRationalPoint_natural (K := AlgebraicClosure F) j.hom.hom p
    have hg : baseChangePointsEquiv b H (𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure F)))))
        (geometricRationalPoint (K := AlgebraicClosure F) H.X (p ≫ j.hom.hom)) =
        toUnit _ ≫ p ≫ j.hom.hom :=
      MatrixRepresentation.baseChangePointsEquiv_geometricRationalPoint (p ≫ j.hom.hom)
    rw [htj, hg]
    simp only [← Category.assoc]
    congr 2
    apply toUnit_unique
  have hc' : c' * (toUnit V ≫ t ≫ ((GroupScheme.baseChange b).map j).hom.hom) =
      (toUnit V ≫ t ≫ ((GroupScheme.baseChange b).map j).hom.hom) * c' := by
    apply (baseChangePointsEquiv b H V).injective
    rw [map_mul, map_mul, hc'q, hx, ← MonObj.comp_mul, ← MonObj.comp_mul, hc]
  obtain ⟨s, hs⟩ := hUreg t ht c' hc'
  have hmem : c' ∈ (SubgroupFunctor.range ((GroupScheme.baseChange b).map j)).carrier V :=
    SubgroupFunctor.mem_range.mpr ⟨s, hs⟩
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange, hc'q] at hmem
  exact hmem

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- A discrepancy given by an actual cocycle gives the inverse local charts
of the pure inner form. -/
def HasDiscrepancy.innerTwist {ξ : Cocycle G U} {e : LocalGroupIso G H U}
    (hξ : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ) : ξ.InnerTwist where
  obj := H
  chart := e.symm
  transition {Z} a b z := by
    have h := hξ a b ((e.toFun b).symm z)
    rw [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id,
      MulEquiv.apply_symm_apply] at h
    have he := (e.toFun a).injective (h.trans ((e.toFun a).apply_symm_apply z).symm)
    change (e.toFun b).symm z = (ξ.toFun a b)⁻¹ * (e.toFun a).symm z * ξ.toFun a b
    rw [← he]
    group

/-- When a pure inner local chart matches two rational points, the inverse
cocycle commutes with the target rational point on every test scheme. -/
theorem HasDiscrepancy.innerTwist_difference_commutes
    {ξ : Cocycle G U} {e : LocalGroupIso G H U}
    (hξ : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    (x : 𝟙_ (Over S) ⟶ G.X) (y : 𝟙_ (Over S) ⟶ H.X)
    (hxy : e.toFun (𝟙 U) (toUnit U ≫ x) = toUnit U ≫ y)
    {Z : Over S} (a b : Z ⟶ U) :
    Commute ((hξ.innerTwist.difference (Cocycle.coboundary (1 : U ⟶ G.X))).toFun a b)
      (toUnit Z ≫ y) := by
  let D := hξ.innerTwist
  have hx (a : Z ⟶ U) : D.chart.toFun a (toUnit Z ≫ y) = toUnit Z ≫ x := by
    apply (e.toFun a).injective
    change e.toFun a ((e.toFun a).symm (toUnit Z ≫ y)) = _
    rw [MulEquiv.apply_symm_apply]
    have h := (e.naturality a (𝟙 U) (toUnit U ≫ x)).trans (congrArg (fun v => a ≫ v) hxy)
    simpa only [Category.comp_id, ← Category.assoc, comp_toUnit] using h.symm
  have hc := D.chart_reverse a b (toUnit Z ≫ y)
  rw [hx a, hx b] at hc
  apply (D.chart.toFun a).injective
  rw [map_mul, map_mul, D.chart_difference, hx a]
  simp only [Cocycle.coboundary, MonObj.comp_one, inv_one, mul_one, one_mul]
  calc
    (ξ.toFun a b)⁻¹ * (toUnit Z ≫ x) =
        (ξ.toFun a b)⁻¹ * (ξ.toFun a b * (toUnit Z ≫ x) * (ξ.toFun a b)⁻¹) :=
      congrArg (fun v => (ξ.toFun a b)⁻¹ * v) hc
    _ = (toUnit Z ≫ x) * (ξ.toFun a b)⁻¹ := by group

/-- Vanishing of cocycles reduced to a prescribed maximal torus in a pure
inner form implies triviality of the original quasi-split cocycle. -/
theorem HasDiscrepancy.isTrivial_of_prescribedTwistTorus
    {F L : Type u} [Field F] [Infinite F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    {ξ : Cocycle G (GaloisCocycle.cover F L)}
    {e : LocalGroupIso G H (GaloisCocycle.cover F L)}
    (hξ : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    (hsc : IsSimplyConnected G) (hqs : IsQuasiSplit G) (hH : IsConnectedReductive H)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {j : T.toGrp ⟶ H} (hj : IsMaximalTorus j)
    (hvan : ∀ (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
        (ζ : Cocycle T.toGrp (GaloisCocycle.cover F E)), (ζ.map j).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨p, hp⟩ := hj.exists_stronglyRegularPoint hH
  let y := p ≫ j.hom.hom
  obtain ⟨x, _, _, _, _, _, E, _, _, _, _, r, g, hg⟩ :=
    quasiSplitSimplyConnectedRegularConjugate F L G G hsc hqs (𝟙 G) (isCentralIsogeny_id G)
      (AutomorphicAction.conjugation (𝟙 G))
      (fun a b => by simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id])
      ξ H e hξ y T.toGrp j hj.1 hj.2.1 (fun c hc => hp c hc)
  let V := GaloisCocycle.cover F E
  let ξ' := (ξ.refine r).twist g
  let e' := (e.refine r).twist (AutomorphicAction.conjugation (𝟙 G)) g
  have he' : e'.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ' :=
    HasDiscrepancy.twist (HasDiscrepancy.refine hξ r) g
  have hxy : e'.toFun (𝟙 V) (toUnit V ≫ x) = toUnit V ≫ y := by
    change e.toFun (𝟙 V ≫ r)
      ((AutomorphicAction.conjugation (𝟙 G)).act (𝟙 V ≫ g) (toUnit V ≫ x)) = _
    rw [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id, Category.id_comp,
      Category.id_comp]
    exact hg
  let D := he'.innerTwist
  let ζ := D.difference (Cocycle.coboundary (1 : V ⟶ G.X))
  let : IsClosedImmersion j.hom.hom.left := hj.2.1
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hval {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ V) :
      ∃ s : Z ⟶ T.X, s ≫ j.hom.hom = ζ.toFun a b :=
    hp _ (he'.innerTwist_difference_commutes x y hxy a b).eq
  let ζT := ζ.lift j (fun _ _ => hval _ _)
  have ht : ζ.IsTrivial := by
    obtain ⟨b, hb⟩ := hvan E ζT
    exact ⟨b, fun a c => (ζ.lift_toFun j _ a c).symm.trans (hb a c)⟩
  obtain ⟨f, hf⟩ := (D.cohomologous_iff_difference_isTrivial _).mpr ht
  have htriv : (ξ'.twist f).IsTrivial := by
    refine ⟨1, fun a b => ?_⟩
    exact (hf a b).symm
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc F E
  let : Surjective V.hom := hs
  let : Flat V.hom := hf
  let : QuasiCompact V.hom := hq
  have hr : (ξ.refine r).IsTrivial := Cocycle.IsTrivial.of_twist (Cocycle.IsTrivial.of_twist htriv)
  exact Cocycle.IsTrivial.of_refine_fpqcCover (V := V) r hr

end LocalGroupIso

end Langlands.GroupScheme
