import Langlands.Representation.Exponents.LeviParabolicTransitivityProof
import Langlands.Representation.Exponents.LeviParabolicExtensionProof
import Mathlib.RingTheory.Noetherian.Basic

/-! # Induction in stages through an actual parabolic of the Levi

Let `P = M U` be an actual rational parabolic of a connected reductive `G` and `Q = N V` an
actual rational parabolic of its Levi `M`. The published extension result
`leviParabolicExtension` supplies an actual rational parabolic `R = N W` of `G` with the same
Levi `N`, with `R(F) ⊆ P(F)` and `Q(F) = M(F) ∩ R(F)` inside `G(F)`. The published
transitivity `leviParabolicTransitivity` (Renard VI.1.4) then identifies `i_R^G` with
`i_P^G ∘ i_Q^M`. This module packages the extension data, proves the identification, and
transfers Noetherianity of group-algebra modules along it.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidAlgebra

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]
  {G P M U Q N V : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual rational parabolic `R = N W` of `G` extending the actual parabolic `Q` of the
Levi `M` of `P`, with Levi `N`: the Levi embeddings agree, `R(F) ⊆ P(F)`, and
`Q(F) = M(F) ∩ R(F)` inside `G(F)`. These are the hypotheses of
`LeviParabolicTransitivityStatement` for the triple `R ⊆ P` with inner parabolic `Q`. -/
structure LeviParabolicExtensionDatum (p : P ⟶ G) (l : M ⟶ P) (q : Q ⟶ M) (n : N ⟶ Q) where
  /-- The extended parabolic group scheme. -/
  R : GroupScheme (Spec (CommRingCat.of k))
  /-- Its unipotent radical. -/
  W : GroupScheme (Spec (CommRingCat.of k))
  /-- The inclusion of the extended parabolic. -/
  pR : R ⟶ G
  /-- The inclusion of the Levi `N` into the extended parabolic. -/
  nR : N ⟶ R
  /-- The inclusion of the radical into the extended parabolic. -/
  rR : W ⟶ R
  hpR : IsParabolicSubgroup pR
  hnR : IsRationalLeviSubgroup nR
  hrR : LeviSubgroup.IsGeometricUnipotentRadical rR
  hmulR : IsIso (subgroupMultiplication nR rR)
  /-- The Levi `N` has the same embedding in `G`. -/
  levi_comp : nR ≫ pR = n ≫ q ≫ l ≫ p
  /-- `R(F) ⊆ P(F)`. -/
  pointImage_le : pointImage pR ≤ pointImage p
  /-- `Q(F) = M(F) ∩ R(F)`. -/
  pointImage_inf : pointImage (q ≫ l ≫ p) = pointImage (l ≫ p) ⊓ pointImage pR

namespace LeviParabolicExtensionDatum

variable (hG : IsConnectedReductive G)
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ M) (n : N ⟶ Q) (s : V ⟶ Q)
  (hq : IsParabolicSubgroup q) (hn : IsRationalLeviSubgroup n)
  (hs : LeviSubgroup.IsGeometricUnipotentRadical s)
  (hmulQ : IsIso (subgroupMultiplication n s))

include hG hp hl hr hmul hq hn hs hmulQ in
/-- An extension datum exists: this is the published `leviParabolicExtension`, with its
subgroup-functor conclusions evaluated on rational points. -/
theorem nonempty : Nonempty (LeviParabolicExtensionDatum p l q n) := by
  obtain ⟨R, W, pR, nR, rR, hpR, hnR, hrR, hmulR, hcomp, hle, hinf⟩ :=
    leviParabolicExtension k G hG P M U p l r hp hl hr hmul Q N V q n s hq hn hs hmulQ
  exact ⟨{ R, W, pR, nR, rR, hpR, hnR, hrR, hmulR
           levi_comp := hcomp
           pointImage_le := hle _
           pointImage_inf := congrArg (fun F : SubgroupFunctor G =>
             F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) hinf }⟩

/-- A chosen extension datum, supplied by the published `leviParabolicExtension`. -/
noncomputable def ofExtension : LeviParabolicExtensionDatum p l q n :=
  Classical.choice (nonempty hG p l r hp hl hr hmul q n s hq hn hs hmulQ)

end LeviParabolicExtensionDatum

section Induction

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom]

local instance leviInductionStagesAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (hG : IsConnectedReductive G)
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ M) (n : N ⟶ Q) (s : V ⟶ Q)
  (hq : IsParabolicSubgroup q) (hn : IsRationalLeviSubgroup n)
  (hs : LeviSubgroup.IsGeometricUnipotentRadical s)
  (hmulQ : IsIso (subgroupMultiplication n s))

include hG in
/-- Induction in stages (Renard VI.1.4): for every extension datum `D` of the parabolic `Q`
of `M`, normalized induction from `D.R` is isomorphic to induction from `Q` to `M` followed
by induction from `P` to `G`. -/
theorem LeviParabolicExtensionDatum.leviInduction_iso
    (D : LeviParabolicExtensionDatum p l q n) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    haveI := D.hnR.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints N) := leviPointTopology D.nR D.hnR
    Nonempty (leviInductionFunctor.{u, v} D.pR D.nR D.rR D.hpR D.hrR D.hnR D.hmulR ≅
      leviInductionFunctor.{u, v} q n s hq hs hn hmulQ ⋙
        leviInductionFunctor.{u, max u v} p l r hp hr hl hmul) :=
  (leviParabolicTransitivity k G hG D.R N D.W P M U Q V
    D.pR D.nR D.rR D.hpR D.hnR D.hrR D.hmulR p l r hp hl hr hmul
    q n s hq hn hs hmulQ D.pointImage_le D.levi_comp.symm D.pointImage_inf).1

/-- An isomorphism of smooth representations transfers Noetherianity of the group-algebra
module. -/
private theorem isNoetherian_of_iso {H : Type u} [Group H] [TopologicalSpace H]
    {A B : SmoothRep.{0, u, v} ℂ H} (e : A ≅ B)
    (hA : _root_.IsNoetherian ℂ[H] A.representation.asModule) :
    _root_.IsNoetherian ℂ[H] B.representation.asModule :=
  isNoetherian_of_surjective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (SmoothRep.equivOfIso e).toIntertwiningMap)
    (LinearMap.range_eq_top.mpr (SmoothRep.equivOfIso e).toLinearEquiv.surjective)

include hG in
/-- Through an extension datum, the induction `i_R^G(σ)` is Noetherian over `ℂ[G(F)]` exactly
when `i_P^G(i_Q^M(σ))` is. -/
theorem LeviParabolicExtensionDatum.isNoetherian_leviInduction_iff
    (D : LeviParabolicExtensionDatum p l q n) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    haveI := D.hnR.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints N) := leviPointTopology D.nR D.hnR
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints N),
      _root_.IsNoetherian ℂ[rationalPoints G]
          ((leviInductionFunctor.{u, v} D.pR D.nR D.rR D.hpR D.hrR D.hnR D.hmulR).obj
            σ).representation.asModule ↔
        _root_.IsNoetherian ℂ[rationalPoints G]
          ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
            ((leviInductionFunctor.{u, v} q n s hq hs hn hmulQ).obj
              σ)).representation.asModule := by
  intro σ
  obtain ⟨e⟩ := D.leviInduction_iso hG p l r hp hl hr hmul q n s hq hn hs hmulQ
  exact ⟨isNoetherian_of_iso (e.app σ), isNoetherian_of_iso (e.app σ).symm⟩

end Induction

end Langlands.Aubert.General.RepresentedParabolic
