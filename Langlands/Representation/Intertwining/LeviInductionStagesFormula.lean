import Langlands.Representation.Exponents.LeviParabolicTransitivityReduction
import Langlands.GroupScheme.Rational.NestedParabolicPointDecompositionProof

/-! # Induction in stages with its explicit formula

For a represented parabolic `P = MN` of `G` contained in a represented parabolic `Q = LU`, and
a represented parabolic `P_L = M N_L` of `L` with the same embedded `M` and
`P_L(F) = L(F) ∩ P(F)`, we construct the natural isomorphism
`i_P^G ≅ i_Q^G ∘ i_{P_L}^L` and record its formula
`f̃(g)(x) = δ_U(x)^{-1/2} f(x g)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

namespace LeviInductionStages

/-- Pulling back along `e.symm` and then `e` is the identity. -/
def inversePullbackIso
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

/-- Three successive pullbacks agree with one pullback along an equal composite. -/
def pullbackTripleIso
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

theorem pointImage_composite_mem_iff
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

end LeviInductionStages

open LeviInductionStages

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    {G P M N Q L U PL NL : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

local instance stagesAmbientTopology : TopologicalSpace (rationalPoints G) :=
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

include hPQ hM hPL in
/-- Normalized induction in stages `i_P^G ≅ i_Q^G ∘ i_{P_L}^L` for the represented triples,
built at the level of functions so that its formula is definitional. -/
def leviInductionStagesIso (hG : IsConnectedReductive G) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    haveI := hm.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
    leviInductionFunctor.{u, v} p m n hp hn hm hmul ≅
        leviInductionFunctor.{u, v} pL mL nL hpL hnL hmL hmulL ⋙
          leviInductionFunctor.{u, max u v} q l uQ hq huQ hl hmulQ := by
  have hdec := nestedParabolicPointDecomposition k G hG P M N Q L U PL NL
      p m n hp hm hn hmul q l uQ hq hl huQ hmulQ
      pL mL nL hpL hmL hnL hmulL hPQ hM hPL
  have hNL : pointImage (nL ≫ pL ≫ l ≫ q) = pointImage (l ≫ q) ⊓ pointImage (n ≫ p) :=
    hdec.1
  have hprod : (pointImage (n ≫ p) : Set (rationalPoints G)) =
      (pointImage (l ≫ q) ⊓ pointImage (n ≫ p) : Subgroup (rationalPoints G)) *
        (pointImage (uQ ≫ q) : Set (rationalPoints G)) := hdec.2.1
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
  have hi : Function.Injective (rationalPoints.map (l ≫ q)) :=
    fun a b hab => eL.injective (Subtype.ext hab)
  have hML : pointImage (m ≫ p) ≤ pointImage (l ≫ q) := by
    rw [← hM]
    simpa only [Category.assoc] using pointImage_comp_le (l ≫ q) (mL ≫ pL)
  have hPMem : ∀ x, x ∈ pointImage pL ↔
      eL x ∈ (pointImage p).subgroupOf (pointImage (l ≫ q)) := by
    intro x
    have h := pointImage_composite_mem_iff pL (l ≫ q) hi x
    rw [show pointImage (pL ≫ l ≫ q) = _ from hPL] at h
    exact h.symm.trans (and_iff_right (eL x).property)
  have hMMem : ∀ x, x ∈ pointImage (mL ≫ pL) ↔
      eL x ∈ (pointImage (m ≫ p)).subgroupOf (pointImage (l ≫ q)) := by
    intro x
    have h := pointImage_composite_mem_iff (mL ≫ pL) (l ≫ q) hi x
    change x ∈ pointImage (mL ≫ pL) ↔
      rationalPoints.map (l ≫ q) x ∈ pointImage (m ≫ p)
    simpa only [Category.assoc, hM] using h.symm
  have hNMem : ∀ x, x ∈ pointImage (nL ≫ pL) ↔
      eL x ∈ (pointImage (n ≫ p)).subgroupOf (pointImage (l ≫ q)) := by
    intro x
    have h := pointImage_composite_mem_iff (nL ≫ pL) (l ≫ q) hi x
    simp only [Category.assoc] at h
    rw [hNL] at h
    exact h.symm.trans (and_iff_right (eL x).property)
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
  let IP := normalizedInductionFunctor.{u, v} hP hN
  let IQ := normalizedInductionFunctor.{u, max u v} hQ hU
  let IL := inductionFunctor.{u, v} pL mL nL hpL hnL hmL hmulL
  let II := normalizedInductionFunctor.{u, v} hInner (hN.preimage continuous_subtype_val)
  let hTransportI : II ≅ SmoothRep.pullbackFunctor eInner ⋙ IL ⋙
      SmoothRep.pullbackFunctor eL.symm :=
    (Functor.isoWhiskerLeft II (inversePullbackIso.{u, max u v} eL.symm).symm) ≪≫
      Functor.isoWhiskerRight
        (GroupTransport.inductionIso hInner hI eL hPMem hMMem hNMem
          (hN.preimage continuous_subtype_val) hNLc)
        (SmoothRep.pullbackFunctor eL.symm)
  let hInd : IP ≅ leviNormalizedInductionFunctor hL hML hInner hN ⋙ IQ :=
    NestedInduction.iso hP hQ hL hML hInner hN hU hPQ
      (NestedParabolic.unipotent_le hprod) hproj hδN hδU hHalf
  let hI1 : SmoothRep.pullbackFunctor eM.symm ⋙ IP ≅
      SmoothRep.pullbackFunctor eM.symm ⋙ SmoothRep.pullbackFunctor c ⋙ II ⋙ IQ :=
    Functor.isoWhiskerLeft (SmoothRep.pullbackFunctor eM.symm) hInd
  let hI2 : SmoothRep.pullbackFunctor eM.symm ⋙ SmoothRep.pullbackFunctor c ⋙ II ⋙ IQ ≅
      SmoothRep.pullbackFunctor eM.symm ⋙ SmoothRep.pullbackFunctor c ⋙
        SmoothRep.pullbackFunctor eInner ⋙ IL ⋙ SmoothRep.pullbackFunctor eL.symm ⋙ IQ :=
    Functor.isoWhiskerLeft (SmoothRep.pullbackFunctor eM.symm ⋙ SmoothRep.pullbackFunctor c)
      (Functor.isoWhiskerRight hTransportI IQ)
  let hI3 : SmoothRep.pullbackFunctor eM.symm ⋙ SmoothRep.pullbackFunctor c ⋙
      SmoothRep.pullbackFunctor eInner ⋙ IL ⋙ SmoothRep.pullbackFunctor eL.symm ⋙ IQ ≅
      SmoothRep.pullbackFunctor eML.symm ⋙ IL ⋙ SmoothRep.pullbackFunctor eL.symm ⋙ IQ :=
    Functor.isoWhiskerRight (pullbackTripleIso eInner c eM.symm eML.symm hCompatInv)
      (IL ⋙ SmoothRep.pullbackFunctor eL.symm ⋙ IQ)
  exact hI1 ≪≫ hI2 ≪≫ hI3

include hPQ hM hPL in
/-- The stage isomorphism on functions: `f̃(g)(x) = δ_U(x)^{-1/2} f(x g)`. -/
theorem leviInductionStagesIso_eval (hG : IsConnectedReductive G) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (f : (leviInductionFunctor p m n hp hn hm hmul).obj σ)
      (g : rationalPoints G) (x : rationalPoints L),
      Induction.eval (pointImage pL)
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage pL mL nL hpL.isClosedSubgroup hnL hmulL)
            (isClosed_pointImage_comp pL nL hpL.isClosedSubgroup hnL.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv pL mL hpL hmL).symm σ))
          (Induction.eval (pointImage q)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage q l uQ hq.isClosedSubgroup huQ hmulQ)
              (isClosed_pointImage_comp q uQ hq.isClosedSubgroup huQ.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv q l hq hl).symm
                ((leviInductionFunctor pL mL nL hpL hnL hmL hmulL).obj σ)))
            (SmoothRep.hom ((leviInductionStagesIso p m n hp hm hn hmul q l uQ hq hl huQ hmulQ
              pL mL nL hpL hmL hnL hmulL hPQ hM hPL hG).hom.app σ) f) g) x =
        ((HaarModulus.closedHalfCharacter (pointImage (uQ ≫ q))
            (isClosed_pointImage_comp q uQ hq.isClosedSubgroup huQ.1.isClosedSubgroup)
            (pointImage q)
            (isSemidirectDecomposition_pointImage q l uQ hq.isClosedSubgroup huQ
              hmulQ).le_normalizer
            (Subgroup.inclusion (pointImage_comp_le q l) (leviPointsEquiv q l hq hl x)))⁻¹ :
              ℂˣ) •
          Induction.eval (pointImage p)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage p m n hp.isClosedSubgroup hn hmul)
              (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv p m hp hm).symm σ)) f
            (rationalPoints.map (l ≫ q) x * g) := by
  intro σ f g x
  rfl

include hPQ hM hPL in
/-- The stage isomorphism on functions, with the scalar in `ℂ`:
`f̃(g)(x) = c(x)⁻¹ f(x g)` where `c(x) = δ_U(x)^{1/2}`. -/
theorem leviInductionStagesIso_eval' (hG : IsConnectedReductive G) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (f : (leviInductionFunctor p m n hp hn hm hmul).obj σ)
      (g : rationalPoints G) (x : rationalPoints L),
      Induction.eval (pointImage pL)
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage pL mL nL hpL.isClosedSubgroup hnL hmulL)
            (isClosed_pointImage_comp pL nL hpL.isClosedSubgroup hnL.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv pL mL hpL hmL).symm σ))
          (Induction.eval (pointImage q)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage q l uQ hq.isClosedSubgroup huQ hmulQ)
              (isClosed_pointImage_comp q uQ hq.isClosedSubgroup huQ.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv q l hq hl).symm
                ((leviInductionFunctor pL mL nL hpL hnL hmL hmulL).obj σ)))
            (SmoothRep.hom ((leviInductionStagesIso p m n hp hm hn hmul q l uQ hq hl huQ hmulQ
              pL mL nL hpL hmL hnL hmulL hPQ hM hPL hG).hom.app σ) f) g) x =
        (((HaarModulus.closedHalfCharacter (pointImage (uQ ≫ q))
            (isClosed_pointImage_comp q uQ hq.isClosedSubgroup huQ.1.isClosedSubgroup)
            (pointImage q)
            (isSemidirectDecomposition_pointImage q l uQ hq.isClosedSubgroup huQ
              hmulQ).le_normalizer
            (Subgroup.inclusion (pointImage_comp_le q l) (leviPointsEquiv q l hq hl x)) :
              ℂˣ) : ℂ))⁻¹ •
          Induction.eval (pointImage p)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage p m n hp.isClosedSubgroup hn hmul)
              (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv p m hp hm).symm σ)) f
            (rationalPoints.map (l ≫ q) x * g) := by
  intro σ f g x
  rw [leviInductionStagesIso_eval p m n hp hm hn hmul q l uQ hq hl huQ hmulQ
    pL mL nL hpL hmL hnL hmulL hPQ hM hPL hG σ f g x, Units.smul_def, Units.val_inv_eq_inv_val]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- A function `F` in `i_Q^G(i_{P_L}^L(σ))` is determined by the values `F(g)(x)`. -/
theorem leviInductionStages_ext :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology mL hmL
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (F F' : (leviInductionFunctor.{u, max u v} q l uQ hq huQ hl hmulQ).obj
        ((leviInductionFunctor pL mL nL hpL hnL hmL hmulL).obj σ)),
      (∀ (g : rationalPoints G) (x : rationalPoints L),
        Induction.eval (pointImage pL)
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage pL mL nL hpL.isClosedSubgroup hnL hmulL)
            (isClosed_pointImage_comp pL nL hpL.isClosedSubgroup hnL.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv pL mL hpL hmL).symm σ))
          (Induction.eval (pointImage q)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage q l uQ hq.isClosedSubgroup huQ hmulQ)
              (isClosed_pointImage_comp q uQ hq.isClosedSubgroup huQ.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv q l hq hl).symm
                ((leviInductionFunctor pL mL nL hpL hnL hmL hmulL).obj σ))) F g) x =
        Induction.eval (pointImage pL)
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage pL mL nL hpL.isClosedSubgroup hnL hmulL)
            (isClosed_pointImage_comp pL nL hpL.isClosedSubgroup hnL.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv pL mL hpL hmL).symm σ))
          (Induction.eval (pointImage q)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage q l uQ hq.isClosedSubgroup huQ hmulQ)
              (isClosed_pointImage_comp q uQ hq.isClosedSubgroup huQ.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv q l hq hl).symm
                ((leviInductionFunctor pL mL nL hpL hnL hmL hmulL).obj σ))) F' g) x) →
      F = F' := by
  intro σ F F' h
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact h g x

end Langlands.Aubert.General.RepresentedParabolic
