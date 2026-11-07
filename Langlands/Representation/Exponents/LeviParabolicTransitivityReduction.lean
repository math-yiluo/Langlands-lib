import Langlands.Representation.Exponents.LeviParabolicTransitivityStatement
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Aubert.General.RepresentedDynamicTransport
import Langlands.Representation.Aubert.General.NestedParabolicTransitivity
import Langlands.Representation.Aubert.General.RationalPointSecondCountable

/-! # Reduction of represented transitivity to the nested radical identities -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

private def inversePullbackIso
    {H K : Type u} [Group H] [Group K] [TopologicalSpace H] [TopologicalSpace K]
    (e : H ≃ₜ* K) :
    SmoothRep.pullbackFunctor.{u, u, v} e.symm ⋙ SmoothRep.pullbackFunctor e ≅
      𝟭 (SmoothRep.{0, u, v} ℂ H) :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun h => by
        ext a
        change A.representation (e.symm (e h)) a = A.representation h a
        rw [e.symm_apply_apply]))
    (fun _ => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      rfl)

private def pullbackPairIso
    {A B C D : Type u} [Group A] [Group B] [Group C] [Group D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (e : A ≃ₜ* B) (f : B ≃ₜ* C) (e' : A ≃ₜ* D) (f' : D ≃ₜ* C)
    (h : ∀ x, f (e x) = f' (e' x)) :
    SmoothRep.pullbackFunctor.{u, u, v} f ⋙ SmoothRep.pullbackFunctor e ≅
      SmoothRep.pullbackFunctor f' ⋙ SmoothRep.pullbackFunctor e' :=
  NatIso.ofComponents
    (fun X => SmoothRep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl ℂ X) fun x => by
        ext a
        change X.representation (f (e x)) a = X.representation (f' (e' x)) a
        rw [h x]))
    (fun _ => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      rfl)

private def pullbackTripleIso
    {A B C D : Type u} [Group A] [Group B] [Group C] [Group D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (e : A ≃ₜ* B) (f : B ≃ₜ* C) (g : C ≃ₜ* D) (e' : A ≃ₜ* D)
    (h : ∀ x, g (f (e x)) = e' x) :
    SmoothRep.pullbackFunctor.{u, u, v} g ⋙ SmoothRep.pullbackFunctor f ⋙
        SmoothRep.pullbackFunctor e ≅ SmoothRep.pullbackFunctor e' :=
  NatIso.ofComponents
    (fun X => SmoothRep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl ℂ X) fun x => by
        ext a
        change X.representation (g (f (e x))) a = X.representation (e' x) a
        rw [h x]))
    (fun _ => by
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      rfl)

private theorem pointImage_composite_mem_iff
    {k : Type u} [Field k]
    {A B C : GroupScheme (Spec (CommRingCat.of k))}
    (j : A ⟶ B) (f : B ⟶ C) (hf : Function.Injective (rationalPoints.map f))
    (x : rationalPoints B) :
    rationalPoints.map f x ∈ pointImage (j ≫ f) ↔ x ∈ pointImage j := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hf ((pointMap_comp_apply j f y).symm.trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, pointMap_comp_apply j f y⟩

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    {G P M N Q L U PL NL : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

local instance reductionAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (q : Q ⟶ G) (l : L ⟶ Q) (uQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
    (huQ : LeviSubgroup.IsGeometricUnipotentRadical uQ)
    (hmulQ : IsIso (subgroupMultiplication l uQ))
    (pL : PL ⟶ L) (mL : M ⟶ PL) (nL : NL ⟶ PL)
    (hpL : IsParabolicSubgroup pL) (hmL : IsRationalLeviSubgroup mL)
    (hnL : LeviSubgroup.IsGeometricUnipotentRadical nL)
    (hmulL : IsIso (subgroupMultiplication mL nL))
    (hPQ : pointImage p ≤ pointImage q)
    (hM : mL ≫ pL ≫ l ≫ q = m ≫ p)
    (hPL : pointImage (pL ≫ l ≫ q) = pointImage (l ≫ q) ⊓ pointImage p)
    (hNL : pointImage (nL ≫ pL ≫ l ≫ q) =
      pointImage (l ≫ q) ⊓ pointImage (n ≫ p))

include hM in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
private theorem nestedLevi_le : pointImage (m ≫ p) ≤ pointImage (l ≫ q) := by
  rw [← hM]
  simpa only [Category.assoc] using pointImage_comp_le (l ≫ q) (mL ≫ pL)

include hPL in
omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
private theorem nested_parabolic_mem (x : rationalPoints L) :
    let := leviPointTopology l hl
    x ∈ pointImage pL ↔
      leviPointsEquiv q l hq hl x ∈ (pointImage p).subgroupOf (pointImage (l ≫ q)) := by
  let := leviPointTopology l hl
  let e := leviPointsEquiv q l hq hl
  have hi : Function.Injective (rationalPoints.map (l ≫ q)) :=
    fun a b hab => e.injective (Subtype.ext hab)
  have h := pointImage_composite_mem_iff pL (l ≫ q) hi x
  rw [show pointImage (pL ≫ l ≫ q) = _ from hPL] at h
  exact h.symm.trans (and_iff_right (e x).property)

include hM in
omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
private theorem nested_levi_mem (x : rationalPoints L) :
    let := leviPointTopology l hl
    x ∈ pointImage (mL ≫ pL) ↔
      leviPointsEquiv q l hq hl x ∈
        (pointImage (m ≫ p)).subgroupOf (pointImage (l ≫ q)) := by
  let := leviPointTopology l hl
  let e := leviPointsEquiv q l hq hl
  have hi : Function.Injective (rationalPoints.map (l ≫ q)) :=
    fun a b hab => e.injective (Subtype.ext hab)
  have h := pointImage_composite_mem_iff (mL ≫ pL) (l ≫ q) hi x
  change x ∈ pointImage (mL ≫ pL) ↔
    rationalPoints.map (l ≫ q) x ∈ pointImage (m ≫ p)
  simpa only [Category.assoc, hM] using h.symm

include hNL in
omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
private theorem nested_radical_mem (x : rationalPoints L) :
    let := leviPointTopology l hl
    x ∈ pointImage (nL ≫ pL) ↔
      leviPointsEquiv q l hq hl x ∈
        (pointImage (n ≫ p)).subgroupOf (pointImage (l ≫ q)) := by
  let := leviPointTopology l hl
  let e := leviPointsEquiv q l hq hl
  have hi : Function.Injective (rationalPoints.map (l ≫ q)) :=
    fun a b hab => e.injective (Subtype.ext hab)
  have h := pointImage_composite_mem_iff (nL ≫ pL) (l ≫ q) hi x
  simp only [Category.assoc] at h
  rw [hNL] at h
  exact h.symm.trans (and_iff_right (e x).property)

include hPQ hM hPL hNL in
/-- The exact represented-Levi comparisons follow from the two nested radical
identities. This is a conditional reduction, not the unconditional VI.1.4 theorem. -/
theorem leviParabolicTransitivity_of_radical_decomposition
    (hG : IsConnectedReductive G)
    (hprod : (pointImage (n ≫ p) : Set (rationalPoints G)) =
      (pointImage (l ≫ q) ⊓ pointImage (n ≫ p) : Subgroup (rationalPoints G)) *
        (pointImage (uQ ≫ q) : Set (rationalPoints G))) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    haveI := hm.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
    Nonempty (leviInductionFunctor.{u, v} p m n hp hn hm hmul ≅
        leviInductionFunctor.{u, v} pL mL nL hpL hnL hmL hmulL ⋙
          leviInductionFunctor.{u, max u v} q l uQ hq huQ hl hmulQ) ∧
      Nonempty (leviJacquetFunctor.{u, v} p m n hp hn hm hmul ≅
        leviJacquetFunctor.{u, v} q l uQ hq huQ hl hmulQ ⋙
          leviJacquetFunctor.{u, v} pL mL nL hpL hnL hmL hmulL) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q l hq hl
  have := hm.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  let eL := leviPointsEquiv q l hq hl
  let eM := leviPointsEquiv p m hp hm
  let eML := leviPointsEquiv pL mL hpL hmL
  let hP := isSemidirectDecomposition_pointImage p m n hp.isClosedSubgroup hn hmul
  let hQ := isSemidirectDecomposition_pointImage q l uQ hq.isClosedSubgroup huQ hmulQ
  let hI := isSemidirectDecomposition_pointImage pL mL nL hpL.isClosedSubgroup hnL hmulL
  have hL : IsClosed (pointImage (l ≫ q) : Set (rationalPoints G)) :=
    isClosed_leviPoints q l hq hl
  have hN : IsClosed (pointImage (n ≫ p) : Set (rationalPoints G)) :=
    isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup
  have hU : IsClosed (pointImage (uQ ≫ q) : Set (rationalPoints G)) :=
    isClosed_pointImage_comp q uQ hq.isClosedSubgroup huQ.1.isClosedSubgroup
  have hNLc : IsClosed (pointImage (nL ≫ pL) : Set (rationalPoints L)) :=
    isClosed_pointImage_comp pL nL hpL.isClosedSubgroup hnL.1.isClosedSubgroup
  let := hL.locallyCompactSpace
  have hML : pointImage (m ≫ p) ≤ pointImage (l ≫ q) :=
    nestedLevi_le p m q l pL mL hM
  have hPMem : ∀ x, x ∈ pointImage pL ↔
      eL x ∈ (pointImage p).subgroupOf (pointImage (l ≫ q)) :=
    nested_parabolic_mem p q l hq hl pL hPL
  have hMMem : ∀ x, x ∈ pointImage (mL ≫ pL) ↔
      eL x ∈ (pointImage (m ≫ p)).subgroupOf (pointImage (l ≫ q)) :=
    nested_levi_mem p m q l hq hl pL mL hM
  have hNMem : ∀ x, x ∈ pointImage (nL ≫ pL) ↔
      eL x ∈ (pointImage (n ≫ p)).subgroupOf (pointImage (l ≫ q)) :=
    nested_radical_mem p n q l hq hl pL nL hNL
  let hInner := GroupTransport.semidirectDecomposition hI eL.toMulEquiv hPMem hMMem hNMem
  let eInner := GroupTransport.subgroupEquiv eL hMMem
  let c := subgroupOfContinuousEquiv hML
  have hCompat (x : rationalPoints M) : eInner (eML x) = c.symm (eM x) := by
    apply Subtype.ext
    apply Subtype.ext
    change rationalPoints.map (l ≫ q) (rationalPoints.map (mL ≫ pL) x) =
      rationalPoints.map (m ≫ p) x
    rw [← pointMap_comp_apply, Category.assoc, hM]
  have hCompatInv (x : pointImage (mL ≫ pL)) :
      eM.symm (c (eInner x)) = eML.symm x := by
    obtain ⟨y, rfl⟩ := eML.surjective x
    rw [hCompat, c.apply_symm_apply, eM.symm_apply_apply, eML.symm_apply_apply]
  have hproj : Continuous hQ.projection :=
    continuous_projection_pointImage q l uQ hq hl huQ hmulQ
  have hHalf := NestedParabolic.halfCharacterProduct hP hQ hL hN hU hPQ hprod hproj hInner
  have hδN := isUnimodularModulus_pointImage_radical p n hp.isClosedSubgroup hn.1
  have hδU := isUnimodularModulus_pointImage_radical q uQ hq.isClosedSubgroup huQ.1
  have hWc := isLimitOfCompactSubgroups_subgroupOf _ _ hL
    (isLimitOfCompactSubgroups_pointImage_radical p n hp.isClosedSubgroup hn.1)
  let IP := normalizedInductionFunctor.{u, v} hP hN
  let IQ := normalizedInductionFunctor.{u, max u v} hQ hU
  let IL := inductionFunctor.{u, v} pL mL nL hpL hnL hmL hmulL
  let II := normalizedInductionFunctor.{u, v} hInner (hN.preimage continuous_subtype_val)
  have hTransportI : II ≅ SmoothRep.pullbackFunctor eInner ⋙ IL ⋙
      SmoothRep.pullbackFunctor eL.symm := by
    have hInsert : II ≅ (II ⋙ SmoothRep.pullbackFunctor eL) ⋙
        SmoothRep.pullbackFunctor eL.symm := by
      simpa only [Functor.comp_id, Functor.assoc, ContinuousMulEquiv.symm_symm] using
        (Functor.isoWhiskerLeft II (inversePullbackIso.{u, max u v} eL.symm).symm)
    exact hInsert ≪≫ Functor.isoWhiskerRight
      (GroupTransport.inductionIso hInner hI eL hPMem hMMem hNMem
        (hN.preimage continuous_subtype_val) hNLc)
      (SmoothRep.pullbackFunctor eL.symm)
  have hInd : IP ≅ leviNormalizedInductionFunctor hL hML hInner hN ⋙ IQ :=
    NestedInduction.iso hP hQ hL hML hInner hN hU hPQ
      (NestedParabolic.unipotent_le hprod) hproj hδN hδU hHalf
  have hI1 : SmoothRep.pullbackFunctor eM.symm ⋙ IP ≅
      SmoothRep.pullbackFunctor eM.symm ⋙ SmoothRep.pullbackFunctor c ⋙ II ⋙ IQ := by
    simpa only [leviNormalizedInductionFunctor, Functor.assoc] using
      Functor.isoWhiskerLeft (SmoothRep.pullbackFunctor eM.symm) hInd
  have hI2 : SmoothRep.pullbackFunctor eM.symm ⋙ SmoothRep.pullbackFunctor c ⋙ II ⋙ IQ ≅
      SmoothRep.pullbackFunctor eM.symm ⋙ SmoothRep.pullbackFunctor c ⋙
        SmoothRep.pullbackFunctor eInner ⋙ IL ⋙ SmoothRep.pullbackFunctor eL.symm ⋙ IQ := by
    simpa only [Functor.assoc] using
      Functor.isoWhiskerLeft (SmoothRep.pullbackFunctor eM.symm ⋙ SmoothRep.pullbackFunctor c)
        (Functor.isoWhiskerRight hTransportI IQ)
  have hI3 : SmoothRep.pullbackFunctor eM.symm ⋙ SmoothRep.pullbackFunctor c ⋙
      SmoothRep.pullbackFunctor eInner ⋙ IL ⋙ SmoothRep.pullbackFunctor eL.symm ⋙ IQ ≅
      SmoothRep.pullbackFunctor eML.symm ⋙ IL ⋙ SmoothRep.pullbackFunctor eL.symm ⋙ IQ := by
    simpa only [Functor.assoc] using
      Functor.isoWhiskerRight (pullbackTripleIso eInner c eM.symm eML.symm hCompatInv)
        (IL ⋙ SmoothRep.pullbackFunctor eL.symm ⋙ IQ)
  have hJ : Langlands.Aubert.General.jacquetFunctor.{u, v} hP hN ≅
      Langlands.Aubert.General.jacquetFunctor hQ hU ⋙
        leviNormalizedJacquetFunctor hL hML hInner hN :=
    NestedParabolic.jacquetIso hP hQ hL hN hU hPQ hprod hproj hML hInner hWc
  let JP := Langlands.Aubert.General.jacquetFunctor.{u, v} hP hN
  let JQ := Langlands.Aubert.General.jacquetFunctor.{u, v} hQ hU
  let JL := jacquetFunctor.{u, v} pL mL nL hpL hnL hmL hmulL
  let JI := Langlands.Aubert.General.jacquetFunctor.{u, v} hInner
    (hN.preimage continuous_subtype_val)
  have hJ1 : JP ⋙ SmoothRep.pullbackFunctor eM ≅
      JQ ⋙ JI ⋙ SmoothRep.pullbackFunctor c.symm ⋙ SmoothRep.pullbackFunctor eM := by
    simpa only [leviNormalizedJacquetFunctor, Functor.assoc] using
      Functor.isoWhiskerRight hJ (SmoothRep.pullbackFunctor eM)
  have hJ2 : JQ ⋙ JI ⋙ SmoothRep.pullbackFunctor c.symm ⋙ SmoothRep.pullbackFunctor eM ≅
      JQ ⋙ JI ⋙ SmoothRep.pullbackFunctor eInner ⋙ SmoothRep.pullbackFunctor eML := by
    simpa only [Functor.assoc] using Functor.isoWhiskerLeft (JQ ⋙ JI)
      (pullbackPairIso eM c.symm eML eInner (fun x => (hCompat x).symm))
  have hJ3 : JQ ⋙ JI ⋙ SmoothRep.pullbackFunctor eInner ⋙ SmoothRep.pullbackFunctor eML ≅
      JQ ⋙ SmoothRep.pullbackFunctor eL ⋙ JL ⋙ SmoothRep.pullbackFunctor eML := by
    simpa only [Functor.assoc] using Functor.isoWhiskerLeft JQ
      (Functor.isoWhiskerRight
        (GroupTransport.jacquetIso hInner hI eL hMMem hNMem
          (hN.preimage continuous_subtype_val) hNLc)
        (SmoothRep.pullbackFunctor eML))
  constructor
  · exact ⟨by simpa only [leviInductionFunctor, inductionFunctor, Functor.assoc] using
      hI1 ≪≫ hI2 ≪≫ hI3⟩
  · exact ⟨by simpa only [leviJacquetFunctor, jacquetFunctor, Functor.assoc] using
      hJ1 ≪≫ hJ2 ≪≫ hJ3⟩

include hPQ hM hPL hNL in
/-- The two actual natural isomorphisms, constructed conditionally on the inner
radical-image identity and the ambient radical product. -/
def leviParabolicTransitivityComparisons
    (hG : IsConnectedReductive G)
    (hprod : (pointImage (n ≫ p) : Set (rationalPoints G)) =
      (pointImage (l ≫ q) ⊓ pointImage (n ≫ p) : Subgroup (rationalPoints G)) *
        (pointImage (uQ ≫ q) : Set (rationalPoints G))) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    haveI := hm.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
    (leviInductionFunctor.{u, v} p m n hp hn hm hmul ≅
        leviInductionFunctor.{u, v} pL mL nL hpL hnL hmL hmulL ⋙
          leviInductionFunctor.{u, max u v} q l uQ hq huQ hl hmulQ) ×
      (leviJacquetFunctor.{u, v} p m n hp hn hm hmul ≅
        leviJacquetFunctor.{u, v} q l uQ hq huQ hl hmulQ ⋙
          leviJacquetFunctor.{u, v} pL mL nL hpL hnL hmL hmulL) := by
  have h := leviParabolicTransitivity_of_radical_decomposition p m n hp hm hn hmul
    q l uQ hq hl huQ hmulQ pL mL nL hpL hmL hnL hmulL hPQ hM hPL hNL hG hprod
  exact ⟨h.1.some, h.2.some⟩

end Langlands.Aubert.General.RepresentedParabolic
