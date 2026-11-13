import Langlands.Representation.CuspidalSupport.BernsteinRepresentedInduction
import Langlands.Representation.CuspidalSupport.BernsteinRepresentedCuspidality
import Langlands.Representation.CuspidalSupport.BernsteinInducedProgeneratorStatement
import Langlands.Representation.CuspidalSupport.BernsteinBlockJacquetFaithfulStatement
import Langlands.Representation.CuspidalSupport.InducedProgeneratorIndependenceStatement
import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement
import Langlands.Representation.LanglandsClassification.OppositeLeviParabolic
import Langlands.Representation.Aubert.General.CuspidalRemainderTransport
import Langlands.Representation.Aubert.General.InertiaInductionCompression
import Langlands.Representation.Category.CoproductSize
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Jacquet detection on a Bernstein block from the induced progenerator (Renard VI.10.3)

A conditional reduction. Assume the induced progenerator statement (VI.10.1, Theorem), the
independence of the induced progenerator from the parabolic (VI.10.1, Proposition) and
Bernstein's second adjointness (VI.9.6). Then every object `X ≠ 0` of the Bernstein block
`M(G)_𝔰` admits a nonzero morphism `Π_D ⟶ r_P^G(X)`. This is
`BernsteinBlockJacquetFaithfulStatement`.

Proof: since `Π_Ω = i_P^G(Π_D)` generates the block, there is a nonzero morphism
`i_P^G(Π_D) ⟶ X`. By independence, `i_P^G(Π_D) ≅ i_{P̄}^G(Π_D)` for the opposite parabolic
`P̄`. Second adjointness `i_{P̄}^G ⊣ r_P^G` then turns the morphism into a nonzero morphism
`Π_D ⟶ r_P^G(X)`. The comparison of the represented and literal standard Jacquet modules
(`bernsteinStandardFaithfulRepresentedJacquetIso`) moves this to the literal Jacquet module of the
statement.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV uG uL

/-- Equal embedded Levi and radical subgroups, with Levi identifications agreeing pointwise,
give isomorphic pulled-back normalized Jacquet modules. -/
def jacquetPullbackIsoOfEmbeddedLevi {H : Type uG} [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [NonarchimedeanGroup H]
    {L : Type uL} [Group L] [TopologicalSpace L]
    {M M' U U' : Subgroup H} (hM : M = M') (hU : U = U')
    (hUc : IsClosed (U : Set H)) (hU'c : IsClosed (U' : Set H))
    (hMU : M ≤ Subgroup.normalizer (U : Set H)) (hMU' : M' ≤ Subgroup.normalizer (U' : Set H))
    (e : L ≃ₜ* M) (e' : L ≃ₜ* M') (he : ∀ x : L, (e x : H) = (e' x : H))
    (X : SmoothRep.{0, uG, uV} ℂ H) :
    SmoothRep.pullback e ((normalizedJacquetFunctor U M hUc hMU).obj X) ≅
      SmoothRep.pullback e' ((normalizedJacquetFunctor U' M' hU'c hMU').obj X) := by
  subst M'
  subst U'
  have hee : e = e' := by
    ext x
    exact he x
  subst hee
  exact Iso.refl _

/-- Pullback along the identity is isomorphic to the original smooth representation, with the
identity carrier map. -/
def smoothRepPullbackReflIso {H : Type uG} [Group H] [TopologicalSpace H]
    (A : SmoothRep.{0, uG, uV} ℂ H) :
    SmoothRep.pullback (ContinuousMulEquiv.refl H) A ≅ A :=
  SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun _ => rfl)

section Core

open RepresentedParabolic

variable {k : Type uF} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance bernsteinJacquetCoreAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

set_option maxHeartbeats 400000 in
/-- Core of Renard VI.10.3 for one actual parabolic `P = MN`: given the independence of the
induced progenerator (VI.10.1) and second adjointness (VI.9.6), a nonzero morphism
`i_P^G(Π_D) ⟶ X` yields a nonzero morphism `Π_D ⟶ r_P^G(X)`. -/
theorem exists_ne_zero_leviJacquet_of_ne_zero_leviInduction
    (hIndep : InducedProgeneratorIndependenceStatement.{uF, max uF uV})
    (hAdj : LeviSecondAdjointnessStatement.{uF, uV})
    (hG : IsConnectedReductive G)
    {P M N : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints M), π.IsIrreducible →
      IsSupercuspidal π →
    ∀ ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ (Plancherel.rationalCommonNormKernel M),
      ρ₀.IsIrreducible →
    ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
      Function.Injective (SmoothRep.hom j) →
    ∀ (X : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
      (f : (leviInductionFunctor.{uF, max uF uV} p l r hp hr hl hmul).obj
          (rationalNormKernelSummandInduction M ρ₀) ⟶ X), f ≠ 0 →
      ∃ g : rationalNormKernelSummandInduction M ρ₀ ⟶
          (leviJacquetFunctor.{uF, max uF uV} p l r hp hr hl hmul).obj X, g ≠ 0 := by
  intro π hπ hsc ρ₀ hρ₀ j hj X f hf
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  let O := oppositeLeviParabolic hG p l hp hl
  have hcond : (Iso.refl M).hom ≫ O.levi ≫ O.inclusion = l ≫ p ≫ (G.innerIso 1).hom := by
    rw [Iso.refl_hom, Category.id_comp, G.innerIso_one_hom, Category.comp_id, O.levi_comp]
  have he : ∀ m : rationalPoints M,
      ContinuousMulEquiv.refl _ m = rationalPoints.map (Iso.refl M).inv m := by
    intro m
    rw [Iso.refl_inv, rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]
    rfl
  obtain ⟨ψ⟩ := hIndep k G hG P M N O.parabolic M O.radical p l r hp hl hr hmul
    O.inclusion O.levi O.unipotent O.isParabolic O.isLevi O.isRadical O.multiplication
    1 (Iso.refl M) hcond (ContinuousMulEquiv.refl _) he π hπ hsc ρ₀ hρ₀ j hj
  have hint : pointImage O.inclusion ⊓ pointImage p = pointImage (O.levi ≫ O.inclusion) := by
    rw [inf_comm, O.intersection, O.levi_comp]
  obtain ⟨adj⟩ := hAdj k G hG O.parabolic P M O.radical N
    O.inclusion O.levi O.unipotent O.isParabolic O.isLevi O.isRadical O.multiplication
    p l r hp hl hr hmul O.levi_comp.symm hint
  refine ⟨(smoothRepPullbackReflIso _).inv ≫ adj.homEquiv _ _ (ψ.inv ≫ f), ?_⟩
  intro hg
  apply hf
  have h1 : adj.homEquiv _ _ (ψ.inv ≫ f) = 0 := by
    rwa [Preadditive.IsIso.comp_left_eq_zero] at hg
  have h2 : ψ.inv ≫ f = 0 := by
    have := adj.isLeftAdjoint
    rw [← (adj.homEquiv _ _).symm_apply_apply (ψ.inv ≫ f), h1,
      Adjunction.homEquiv_counit, Functor.map_zero, Limits.zero_comp]
  rwa [Preadditive.IsIso.comp_left_eq_zero] at h2

end Core

section Standard

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinStandardJacquetInstance1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinStandardJacquetInstance2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinStandardJacquetInstance3 : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance bernsteinStandardJacquetInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinStandardJacquetInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinStandardJacquetInstance6 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinStandardJacquetInstance7 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Actual represented normalized Jacquet functor along the standard parabolic of `I`. -/
def bernsteinStandardFaithfulRepresentedJacquetFunctor (I : Finset (SimpleRoot i ν)) :
    SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)) :=
  let h := bernsteinStandardRepresentativesGeometric i ν family I
  RepresentedParabolic.leviJacquetFunctor
    (Standard.parabolicHom i ν (rootSet i ν I))
    (Standard.leviToParabolic i ν (rootSet i ν I))
    (Standard.unipotentToParabolic i ν (rootSet i ν I))
    h.1 h.2.2.1 h.2.1 h.2.2.2

/-- Literal standard normalized Jacquet module, pulled back to the Levi's own points. -/
def bernsteinStandardLiteralJacquetFunctor (I : Finset (SimpleRoot i ν)) :
    SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)) :=
  normalizedJacquetFunctor (unipotent i ν I) (levi i ν I) (family.closedUnipotent I)
      (family.decomposition I).levi_le_normalizer ⋙
    SmoothRep.pullbackFunctor (leviRationalPointHomeomorph i ν I)

/-- The represented and literal standard Jacquet modules agree. -/
def bernsteinStandardFaithfulRepresentedJacquetIso (I : Finset (SimpleRoot i ν))
    (X : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) :
    (bernsteinStandardFaithfulRepresentedJacquetFunctor.{uF, uV} i ν family I).obj X ≅
      (bernsteinStandardLiteralJacquetFunctor.{uF, uV} i ν family I).obj X := by
  let p := Standard.parabolicHom i ν (rootSet i ν I)
  let l := Standard.leviToParabolic i ν (rootSet i ν I)
  let hgeom := bernsteinStandardRepresentativesGeometric i ν family I
  have he (x : rationalPoints (bernsteinLeviScheme i ν I)) :
      (RepresentedParabolic.leviPointsEquiv p l hgeom.1 hgeom.2.1 x :
        rationalPoints G) = (leviRationalPointHomeomorph i ν I x : rationalPoints G) := by
    rw [RepresentedParabolic.leviPointsEquiv_apply_coe,
      leviRationalPointHomeomorph_apply_coe]
    change rationalPoints.map
      (Standard.leviToParabolic i ν (rootSet i ν I) ≫
        Standard.parabolicHom i ν (rootSet i ν I)) x = _
    rw [Standard.leviToParabolic_comp]
  let r := Standard.unipotentToParabolic i ν (rootSet i ν I)
  let c := jacquetPullbackIsoOfEmbeddedLevi (H := rationalPoints G)
    (M := RepresentedParabolic.pointImage (l ≫ p))
    (U := RepresentedParabolic.pointImage (r ≫ p))
    (M' := levi i ν I) (U' := unipotent i ν I)
    (standardCompression_leviPoints i ν I) (standardCompression_unipotentPoints i ν I)
    (RepresentedParabolic.isClosed_pointImage_comp p r hgeom.1.isClosedSubgroup
      hgeom.2.2.1.1.isClosedSubgroup)
    (family.closedUnipotent I)
    (RepresentedParabolic.pointImage_le_normalizer p l r hgeom.2.2.1)
    (family.decomposition I).levi_le_normalizer
    (RepresentedParabolic.leviPointsEquiv p l hgeom.1 hgeom.2.1)
    (leviRationalPointHomeomorph i ν I) he X
  dsimp only [bernsteinStandardFaithfulRepresentedJacquetFunctor,
    RepresentedParabolic.leviJacquetFunctor, bernsteinStandardLiteralJacquetFunctor,
    Functor.comp_obj]
  simpa only [Functor.comp_obj, SmoothRep.pullbackFunctor] using c

set_option maxHeartbeats 600000 in
/-- Renard VI.10.3 for the actual standard cuspidal data: given VI.10.1 and VI.9.6, a nonzero
morphism from the literal standard induction `i_P^G(Π_D)` to `X` yields a nonzero morphism from
`Π_D` (transported to the literal standard Levi) to the literal normalized Jacquet module
`r_P^G(X)`. -/
theorem exists_ne_zero_bernsteinLiteralJacquet_of_ne_zero
    (hIndep : RepresentedParabolic.InducedProgeneratorIndependenceStatement.{uF, max uF uV})
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hρ₀ : ρ₀.IsIrreducible)
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j))
    (X : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (h0 : (normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)) ⟶ X)
    (hh0 : h0 ≠ 0) :
    ∃ f : bernsteinLiteralLeviRep i ν a.roots
          (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀) ⟶
        (normalizedJacquetFunctor (unipotent i ν a.roots) (levi i ν a.roots)
          (family.closedUnipotent a.roots)
          (family.decomposition a.roots).levi_le_normalizer).obj X, f ≠ 0 := by
  let h := bernsteinStandardRepresentativesGeometric i ν family a.roots
  obtain ⟨g, hg⟩ := exists_ne_zero_leviJacquet_of_ne_zero_leviInduction.{uF, uV} hIndep hAdj
    family.connectedReductive (M := bernsteinLeviScheme i ν a.roots)
    (Standard.parabolicHom i ν (rootSet i ν a.roots))
    (Standard.leviToParabolic i ν (rootSet i ν a.roots))
    (Standard.unipotentToParabolic i ν (rootSet i ν a.roots))
    h.1 h.2.1 h.2.2.1 h.2.2.2 a.representation a.irreducible (a.isSupercuspidal i ν family)
    ρ₀ hρ₀ j hj X ((bernsteinStandardRepresentedInductionIso i ν family a.roots _).hom ≫ h0)
    (by
      intro hz
      apply hh0
      rwa [Preadditive.IsIso.comp_left_eq_zero] at hz)
  let e := leviRationalPointHomeomorph i ν a.roots
  let g' := g ≫ (bernsteinStandardFaithfulRepresentedJacquetIso i ν family a.roots X).hom
  refine ⟨(SmoothRep.pullbackFunctor e.symm).map g' ≫ (SmoothRep.pullbackSymmIso e _).hom, ?_⟩
  intro hz
  apply hg
  have h1 : (SmoothRep.pullbackEquivalence e.symm).functor.map g' = 0 := by
    rwa [Preadditive.IsIso.comp_right_eq_zero] at hz
  have : (SmoothRep.pullbackEquivalence e.symm).functor.IsLeftAdjoint :=
    (SmoothRep.pullbackEquivalence e.symm).isLeftAdjoint_functor
  have : (SmoothRep.pullbackEquivalence e.symm).functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have h2 : g' = 0 := (Functor.map_eq_zero_iff _).mp h1
  rwa [Preadditive.IsIso.comp_right_eq_zero] at h2

end Standard

set_option maxHeartbeats 600000 in
/-- Renard VI.10.3, Proposition, reduced to VI.10.1 and VI.9.6: if the induced progenerator
statement (VI.10.1, Theorem), the independence statement (VI.10.1, Proposition) and second
adjointness (VI.9.6) hold, then the Jacquet functor along the standard parabolic detects every
nonzero object of the Bernstein block. -/
theorem bernsteinBlockJacquetFaithful_of_inducedProgenerator
    (hProg : BernsteinInducedProgeneratorStatement.{uF, uV})
    (hIndep : RepresentedParabolic.InducedProgeneratorIndependenceStatement.{uF, max uF uV})
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV}) :
    BernsteinBlockJacquetFaithfulStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family a ρ₀ hρ₀ j hj X hX
  obtain ⟨hmem, -, -, hgen⟩ := hProg F G T i ν family a ρ₀ hρ₀ j hj
  have hid : (𝟙 X : X ⟶ X) ≠ 0 := by
    intro h
    have h1 : (𝟙 X : X ⟶ X).hom = (0 : X ⟶ X).hom := by rw [h]
    rw [ObjectProperty.FullSubcategory.id_hom, ObjectProperty.zero_hom] at h1
    have hz : Limits.IsZero X.obj := (Limits.IsZero.iff_id_eq_zero X.obj).mpr h1
    let : TopologicalSpace (rationalPoints G) := pointTopology
    exact not_subsingleton X.obj ((SmoothRep.isZero_iff_subsingleton X.obj).mp hz)
  obtain ⟨h, hh⟩ := hgen X X (𝟙 X) 0 hid
  have hh0 : h.hom ≠ 0 := by
    intro hz
    apply hh
    rw [Category.comp_id, Limits.comp_zero]
    ext1
    rw [hz, ObjectProperty.zero_hom]
  exact exists_ne_zero_bernsteinLiteralJacquet_of_ne_zero.{uF, uV} i ν family hIndep hAdj a ρ₀
    hρ₀ j hj X.obj h.hom hh0

end Langlands.CuspidalSupport
