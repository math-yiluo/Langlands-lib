import Langlands.GroupScheme.Rational.ParabolicGalleryAvoidingProof
import Langlands.Representation.CuspidalSupport.InducedProgeneratorIndependenceStatement
import Langlands.Representation.Exponents.LeviInductionConjugation
import Langlands.Representation.Exponents.LeviParabolicTransitivityProof
import Langlands.Representation.Families.InducedTwistPersistenceGallery

/-! # Reduction of induced progenerator independence to a rank-one comparison -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme GroupScheme.RationalCocharacter
open Langlands.InducedTwistPersistence (pointImage_le_of_range_le pointImage_comp_eq_inf_of_range_eq_comap)

/-- The comparison of the inductions of a Levi progenerator from opposite parabolics when
one of them is maximal proper. The common Levi is given by the same embedded group scheme
on both sides. -/
def InducedProgeneratorMaximalOppositeStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    have := hG.isAffineHom
    let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N P' N' : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (p' : P' ⟶ G) (l' : M ⟶ P') (r' : N' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r')),
      l' ≫ p' = l ≫ p →
      SubgroupFunctor.range p ⊓ SubgroupFunctor.range p' = SubgroupFunctor.range (l ≫ p) →
      ¬ IsIso p →
      (∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G) (f : P ⟶ Q),
        IsParabolicSubgroup q → f ≫ q = p → IsIso f ∨ IsIso q) →
      haveI := hl.isConnectedReductive.isAffineHom
      haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
      haveI := hl.isConnectedReductive.smooth
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints M), π.IsIrreducible → IsSupercuspidal π →
      ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M), ρ₀.IsIrreducible →
      ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
        Function.Injective (SmoothRep.hom j) →
        Nonempty ((leviInductionFunctor p l r hp hr hl hmul).obj
            (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) ≅
          (leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj
            (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀))

section CommonLevi

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance independenceAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

set_option maxHeartbeats 1600000 in
/-- Transitivity transports the rank-one comparisons along a gallery with common Levi. -/
private theorem inducedProgeneratorIso_of_commonLevi (hG : IsConnectedReductive G)
    (hmax : InducedProgeneratorMaximalOppositeStatement.{u, v})
    {P M N P' N' : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (p' : P' ⟶ G) (l' : M ⟶ P') (r' : N' ⟶ P')
    (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
    (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
    (hmul' : IsIso (subgroupMultiplication l' r'))
    (hlevi : l' ≫ p' = l ≫ p) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints M), π.IsIrreducible → IsSupercuspidal π →
    ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M), ρ₀.IsIrreducible →
    ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
      Function.Injective (SmoothRep.hom j) →
      Nonempty ((leviInductionFunctor p l r hp hr hl hmul).obj
          (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) ≅
        (leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj
          (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀)) := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro π hπ hsc ρ₀ hρ₀ j hj
  let A := CuspidalSupport.rationalNormKernelSummandInduction M ρ₀
  let X := (leviInductionFunctor p l r hp hr hl hmul).obj A
  have hP : IsRationalParabolicWithLevi (l ≫ p) (SubgroupFunctor.range p) :=
    ⟨P, p, l, hp, hl, rfl, rfl⟩
  have hP' : IsRationalParabolicWithLevi (l ≫ p) (SubgroupFunctor.range p') :=
    ⟨P', p', l', hp', hl', hlevi, rfl⟩
  obtain ⟨S, a, ha⟩ := exists_isSplitComponent M
  have hcentralizer := torusCentralizer_eq_range_of_isRationalParabolicWithLevi hG ha hP
  have hintersection : SubgroupFunctor.range p ⊓ torusCentralizer (a ≫ l ≫ p) =
      SubgroupFunctor.range p' ⊓ torusCentralizer (a ≫ l ≫ p) := by
    rw [hcentralizer]
    have hle : SubgroupFunctor.range (l ≫ p) ≤ SubgroupFunctor.range p' :=
      hlevi ▸ SubgroupFunctor.range_comp_le l' p'
    apply SubgroupFunctor.ext
    intro T
    rw [SubgroupFunctor.inf_carrier, SubgroupFunctor.inf_carrier,
      inf_eq_right.mpr (SubgroupFunctor.range_comp_le l p T), inf_eq_right.mpr (hle T)]
  have hgallery := (rationalParabolicGalleryAvoiding k G hG M S (l ≫ p) a ha.1.1 ha.1.2
    _ _ hP hP' hintersection).gallery
  let Invariant (F : SubgroupFunctor G) : Prop :=
    ∃ (R V : GroupScheme (Spec (CommRingCat.of k))) (q : R ⟶ G) (m : M ⟶ R) (n : V ⟶ R)
      (hq : IsParabolicSubgroup q) (hm : IsRationalLeviSubgroup m)
      (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (hmulR : IsIso (subgroupMultiplication m n)),
      m ≫ q = l ≫ p ∧ SubgroupFunctor.range q = F ∧
        Nonempty (X ≅ (leviInductionFunctor q m n hq hn hm hmulR).obj A)
  have hstep {F F' : SubgroupFunctor G} (hd : IsRationalRankOneWall (l ≫ p) F F')
      (hF : Invariant F) : Invariant F' := by
    obtain ⟨-, hF', ⟨d⟩⟩ := hd
    obtain ⟨R, V, q, m, n, hq, hm, hn, hmulR, hMq, hqF, ⟨e⟩⟩ := hF
    obtain ⟨R', q', m', hq', hm', hMq', hq'F⟩ := hF'
    obtain ⟨V', n', hn', hmulR'⟩ := hm'.exists_unipotentRadical
    obtain ⟨U, u, hu, hmulU⟩ := d.levi.exists_unipotentRadical
    obtain ⟨W, w, hw, hmulW⟩ := d.innerLevi.exists_unipotentRadical
    obtain ⟨W', w', hw', hmulW'⟩ := d.innerLevi'.exists_unipotentRadical
    have hL := d.levi.isConnectedReductive
    have := hL.isAffineHom
    let : TopologicalSpace (rationalPoints d.M) := leviPointTopology d.m d.levi
    have := leviPoints_locallyCompactSpace d.p d.m d.parabolic d.levi
    have := leviPoints_nonarchimedeanGroup d.p d.m d.parabolic d.levi
    have hEmbedding : d.l ≫ d.q ≫ d.m ≫ d.p = m ≫ q := by
      rw [← Category.assoc d.l]
      exact d.levi_comp.trans hMq.symm
    have hEmbedding' : d.l' ≫ d.q' ≫ d.m ≫ d.p = m' ≫ q' := by
      rw [← Category.assoc d.l', d.commonLevi]
      exact d.levi_comp.trans hMq'.symm
    obtain ⟨⟨first⟩, -⟩ := leviParabolicTransitivity.{u, max u v} k G hG
      R M V d.P d.M U d.Q W q m n hq hm hn hmulR d.p d.m u d.parabolic d.levi hu hmulU
      d.q d.l w d.innerParabolic d.innerLevi hw hmulW
      (pointImage_le_of_range_le d.p q hqF d.contained) hEmbedding
      (pointImage_comp_eq_inf_of_range_eq_comap d.q (d.m ≫ d.p) q d.intersection hqF)
    obtain ⟨⟨second⟩, -⟩ := leviParabolicTransitivity.{u, max u v} k G hG
      R' M V' d.P d.M U d.Q' W' q' m' n' hq' hm' hn' hmulR' d.p d.m u d.parabolic d.levi hu hmulU
      d.q' d.l' w' d.innerParabolic' d.innerLevi' hw' hmulW'
      (pointImage_le_of_range_le d.p q' hq'F d.contained') hEmbedding'
      (pointImage_comp_eq_inf_of_range_eq_comap d.q' (d.m ≫ d.p) q' d.intersection' hq'F)
    obtain ⟨wall⟩ := hmax k d.M hL d.Q M W d.Q' W'
      d.q d.l w d.innerParabolic d.innerLevi hw hmulW
      d.q' d.l' w' d.innerParabolic' d.innerLevi' hw' hmulW'
      d.commonLevi d.opposite d.proper d.maximal π hπ hsc ρ₀ hρ₀ j hj
    exact ⟨R', V', q', m', n', hq', hm', hn', hmulR', hMq', hq'F,
      ⟨e ≪≫ first.app A ≪≫
        (leviInductionFunctor d.p d.m u d.parabolic hu d.levi hmulU).mapIso wall ≪≫
        (second.app A).symm⟩⟩
  have transport {F : SubgroupFunctor G}
      (history : Relation.ReflTransGen (IsRationalRankOneWall (l ≫ p))
        (SubgroupFunctor.range p) F) : Invariant F := by
    have hStart : Invariant (SubgroupFunctor.range p) :=
      ⟨P, N, p, l, r, hp, hl, hr, hmul, rfl, rfl, ⟨Iso.refl X⟩⟩
    induction history with
    | refl => exact hStart
    | tail _ hWall ih => exact hstep hWall ih
  obtain ⟨R, V, q, m, n, hq, hm, hn, hmulR, hMq, hqF, ⟨e⟩⟩ := transport hgallery.2.2
  exact ⟨e ≪≫ leviInductionIsoOfRangeEq q m n hq hm hn hmulR p' l' r' hp' hl' hr' hmul'
    hqF.symm (hlevi.trans hMq.symm) A⟩

end CommonLevi

set_option maxHeartbeats 900000 in
/-- The maximal opposite comparison implies independence for two arbitrary conjugate
Levi embeddings, by the rank-one gallery and conjugation of normalized induction. -/
theorem inducedProgeneratorIndependence_of_maximalOpposite
    (hmax : InducedProgeneratorMaximalOppositeStatement.{u, v}) :
    InducedProgeneratorIndependenceStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N P' M' N' p l r hp hl hr hmul p' l' r' hp' hl' hr' hmul' g φ hφ
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := hl'.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M') := leviPointTopology l' hl'
  intro e he π hπ hsc ρ₀ hρ₀ j hj
  let p₀ := p' ≫ (G.innerIso g).inv
  let l₀ := φ.hom ≫ l'
  have hp₀ : IsParabolicSubgroup p₀ := hp'.comp_iso (G.innerIso g).symm
  have hl₀ : IsRationalLeviSubgroup l₀ := hl'.iso_comp φ
  have hmul₀ : IsIso (subgroupMultiplication l₀ r') :=
    isIso_subgroupMultiplication_iso_comp φ (l := l') (r := r') hmul'
  have h₀ : l₀ ≫ p₀ = l ≫ p := by
    calc
      l₀ ≫ p₀ = (φ.hom ≫ l' ≫ p') ≫ (G.innerIso g).inv := by
        simp only [l₀, p₀, Category.assoc]
      _ = l ≫ p := by rw [hφ]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨sameLevi⟩ := inducedProgeneratorIso_of_commonLevi hG hmax p l r hp hl hr hmul
    p₀ l₀ r' hp₀ hl₀ hr' hmul₀ h₀ π hπ hsc ρ₀ hρ₀ j hj
  have hback : p₀ ≫ (G.innerIso g).hom = p' := by simp [p₀]
  have hconj : l' ≫ p' = φ.symm.hom ≫ l₀ ≫ p₀ ≫ (G.innerIso g).hom := by
    rw [hback]
    simp [l₀]
  have heq : ambientIsoPointsEquiv φ.symm = e := ContinuousMulEquiv.ext fun m => (he m).symm
  rw [← heq]
  exact ⟨sameLevi ≪≫ leviInductionIsoOfConj p₀ l₀ r' hp₀ hl₀ hr' hmul₀
    p' l' r' hp' hl' hr' hmul' g φ.symm (by rw [hback]) hconj
    (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀)⟩

end Langlands.Aubert.General.RepresentedParabolic
