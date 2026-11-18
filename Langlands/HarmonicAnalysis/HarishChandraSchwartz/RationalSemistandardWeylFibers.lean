import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceConstants
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.WeylPositiveCocharacter

/-! # Parabolic fibers over Weyl-conjugate actual Levis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hD : SemistandardSpectralDynamicCoverageStatement.{u})

/-- The actual all-test triple conjugated by a normalizer point of the fixed torus. -/
def normalizerConjugateIndex (n : normalizerPoints i) (p : SemistandardSpectralIndex i) :
    SemistandardSpectralIndex i :=
  SemistandardSpectralIndex.ofCocharacter hG
    (cocharacterAut (normalizingAut i n) (.ofCoverage hG hD hi p : CocharacterPresentation hG p).cocharacter)

theorem normalizerConjugateIndex_parabolic (n : normalizerPoints i) (p : SemistandardSpectralIndex i) :
    (normalizerConjugateIndex hG hi hD n p).parabolic =
      p.parabolic.comap (G.innerIso (n : rationalPoints G)).inv := by
  let r := CocharacterPresentation.ofCoverage hG hD hi p
  change Dynamic.parabolic
    (CommGroupScheme.groupHom (cocharacterAut (normalizingAut i n) r.cocharacter) ≫ i) = _
  rw [groupHom_cocharacterAut_comp, ← r.parabolic_eq]
  exact ((SubgroupFunctor.eq_comap_iso_iff (G.innerIso (n : rationalPoints G))).mp
    (Dynamic.parabolic_eq_comap_of_iso r.hom _)).symm

theorem normalizerConjugateIndex_levi (n : normalizerPoints i) (p : SemistandardSpectralIndex i) :
    (normalizerConjugateIndex hG hi hD n p).levi =
      p.levi.comap (G.innerIso (n : rationalPoints G)).inv := by
  let r := CocharacterPresentation.ofCoverage hG hD hi p
  change Dynamic.centralizer
    (CommGroupScheme.groupHom (cocharacterAut (normalizingAut i n) r.cocharacter) ≫ i) = _
  rw [groupHom_cocharacterAut_comp, ← r.levi_eq]
  exact ((SubgroupFunctor.eq_comap_iso_iff (G.innerIso (n : rationalPoints G))).mp
    (Dynamic.centralizer_eq_comap_of_iso r.hom _)).symm

theorem normalizerConjugateIndex_radical (n : normalizerPoints i) (p : SemistandardSpectralIndex i) :
    (normalizerConjugateIndex hG hi hD n p).radical =
      p.radical.comap (G.innerIso (n : rationalPoints G)).inv := by
  let r := CocharacterPresentation.ofCoverage hG hD hi p
  change Dynamic.unipotent
    (CommGroupScheme.groupHom (cocharacterAut (normalizingAut i n) r.cocharacter) ≫ i) = _
  rw [groupHom_cocharacterAut_comp, ← r.radical_eq]
  exact ((SubgroupFunctor.eq_comap_iso_iff (G.innerIso (n : rationalPoints G))).mp
    (Dynamic.unipotent_eq_comap_of_iso r.hom _)).symm

private theorem innerIso_inv_inv (g : rationalPoints G) :
    (G.innerIso g⁻¹).inv = (G.innerIso g).hom := by
  rw [← innerIso_inv_hom, inv_inv]

theorem normalizerConjugateIndex_inv (n : normalizerPoints i) (p : SemistandardSpectralIndex i) :
    normalizerConjugateIndex hG hi hD n⁻¹ (normalizerConjugateIndex hG hi hD n p) = p := by
  apply SemistandardSpectralIndex.ext
  · rw [normalizerConjugateIndex_parabolic, normalizerConjugateIndex_parabolic,
      Subgroup.coe_inv, innerIso_inv_inv, SubgroupFunctor.comap_iso_inv_hom]
  · rw [normalizerConjugateIndex_levi, normalizerConjugateIndex_levi,
      Subgroup.coe_inv, innerIso_inv_inv, SubgroupFunctor.comap_iso_inv_hom]
  · rw [normalizerConjugateIndex_radical, normalizerConjugateIndex_radical,
      Subgroup.coe_inv, innerIso_inv_inv, SubgroupFunctor.comap_iso_inv_hom]

/-- The whole conjugated triple is independent of the choice of normalizer lift. -/
theorem normalizerConjugateIndex_eq_of_relativeWeyl_eq (p : SemistandardSpectralIndex i)
    {n m : normalizerPoints i}
    (hnm : (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk m) :
    normalizerConjugateIndex hG hi hD n p = normalizerConjugateIndex hG hi hD m p := by
  let := hi.isSplitSubtorus.mono
  let r := CocharacterPresentation.ofCoverage hG hD hi p
  have he := congrArg (fun w => relativeWeylCocharacterAction i w r.cocharacter) hnm
  simp only [relativeWeylCocharacterAction_mk] at he
  unfold normalizerConjugateIndex
  rw [show (CocharacterPresentation.ofCoverage hG hD hi p).cocharacter = r.cocharacter from rfl, he]

/-- The image of the actual Levi functor under the Weyl quotient, with the
conjugate realized as an intrinsic semistandard Levi. -/
def weylConjugateLevi (M : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (w : relativeWeylGroup i) : SemistandardSpectralLevi i :=
  ⟨relativeWeylConjugateSubgroupFunctor i M.val hM w, by
    obtain ⟨p, hp⟩ := M.property
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
    refine ⟨normalizerConjugateIndex hG hi hD n p, ?_⟩
    rw [normalizerConjugateIndex_levi, hp, relativeWeylConjugateSubgroupFunctor_mk]⟩

theorem weylConjugateLevi_mk (M : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (n : normalizerPoints i) :
    (weylConjugateLevi hG hi hD M hM (QuotientGroup.mk n)).val =
      M.val.comap (G.innerIso (n : rationalPoints G)).inv := rfl

private def normalizerParabolicFiberEquiv (M M' : SemistandardSpectralLevi i)
    (n : normalizerPoints i) (hn : M.val.comap (G.innerIso (n : rationalPoints G)).inv = M'.val) :
    SemistandardSpectralParabolicFiber i M ≃ SemistandardSpectralParabolicFiber i M' where
  toFun p := ⟨normalizerConjugateIndex hG hi hD n p.val, by
    rw [normalizerConjugateIndex_levi, p.property, hn]⟩
  invFun q := ⟨normalizerConjugateIndex hG hi hD n⁻¹ q.val, by
    rw [normalizerConjugateIndex_levi, Subgroup.coe_inv, innerIso_inv_inv, q.property, ← hn,
      SubgroupFunctor.comap_iso_inv_hom]⟩
  left_inv p := Subtype.ext (normalizerConjugateIndex_inv hG hi hD n p.val)
  right_inv q := Subtype.ext (by
    simpa only [inv_inv] using normalizerConjugateIndex_inv hG hi hD n⁻¹ q.val)

/-- A lift of `s` bijects the actual parabolic fibers over `M` and `s.M`
by conjugating the entire triple. The target Levi is independent of the lift. -/
def weylParabolicFiberEquiv (M : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (w : relativeWeylGroup i) :
    SemistandardSpectralParabolicFiber i M ≃
      SemistandardSpectralParabolicFiber i (weylConjugateLevi hG hi hD M hM w) := by
  apply normalizerParabolicFiberEquiv hG hi hD M _ w.out
  exact (weylConjugateLevi_mk hG hi hD M hM w.out).symm.trans
    (congrArg (fun v => (weylConjugateLevi hG hi hD M hM v).val) (Quotient.out_eq w))

theorem weylParabolicFiberEquiv_mk (M : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) (n : normalizerPoints i)
    (p : SemistandardSpectralParabolicFiber i M) :
    (weylParabolicFiberEquiv hG hi hD M hM (QuotientGroup.mk n) p).val =
      normalizerConjugateIndex hG hi hD n p.val :=
  normalizerConjugateIndex_eq_of_relativeWeyl_eq hG hi hD p.val (Quotient.out_eq _)

theorem card_weylConjugateParabolicFiber (M : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) (w : relativeWeylGroup i) :
    Nat.card (SemistandardSpectralParabolicFiber i
      (weylConjugateLevi hG hi hD M hM w)) =
    Nat.card (SemistandardSpectralParabolicFiber i M) :=
  Nat.card_congr (weylParabolicFiberEquiv hG hi hD M hM w).symm

end Langlands.HarishChandraSchwartz.RationalSemistandard
