import Langlands.Representation.CuspidalSupport.BernsteinBlockJacquetFaithfulReduction
import Langlands.Representation.CuspidalSupport.BernsteinInducedProgeneratorProjectiveReduction
import Langlands.Representation.CuspidalSupport.BernsteinInducedProgeneratorFiniteReduction
import Langlands.Representation.CuspidalSupport.BernsteinInducedInertiaGeometricExclusion
import Langlands.Representation.CuspidalSupport.BernsteinSupportJacquetPresentation
import Langlands.Representation.CuspidalSupport.RationalSummandInductionSupercuspidal
import Langlands.Representation.CuspidalSupport.RationalUniversalMembership
import Langlands.Representation.CuspidalSupport.RationalNormKernelTwistEquivalenceProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.Category.ProjectiveGeneration
import Langlands.Representation.CuspidalSupport.RationalSummandEndCenterReduction
import Langlands.Representation.CuspidalSupport.BernsteinBlockHomEquivalenceReduction

/-! # The induced Bernstein progenerator from its structural inputs (Renard VI.10.1–VI.10.3)

A conditional reduction. Assume the independence of the induced progenerator (VI.10.1,
Proposition), Bernstein's second adjointness (VI.9.6), the joint special-compact basis existence,
the finite type of parabolic induction (VI.7.5) and the represented VI.5.2 Lemma (no irreducible
subquotient of the normalized induction of a smooth representation along a proper parabolic is
supercuspidal). Then `Π_Ω = i_P^G(Π_D)` lies in the Bernstein block of its inertial class and is
there a finitely generated projective generator (`BernsteinInducedProgeneratorStatement`, the
VI.10.1 Theorem). Its two consequences follow by the published reductions: the VI.10.2 Theorem
(`BernsteinBlockHomEquivalenceStatement`) and the VI.10.3 Proposition
(`BernsteinBlockJacquetFaithfulStatement`).

Generation adapts Renard's proof on PDF p.214: an irreducible `τ` of the block has a cuspidal
datum `c` whose representation is a quotient of the Jacquet module of `τ`; `Π_D`, transported to
the Levi of `c`, maps nontrivially to it; projectivity lifts this map to the Jacquet module;
second adjointness for the opposite parabolic and the independence statement turn it into a
nonzero morphism `Π_Ω ⟶ τ`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV uH uK

/-- Pulling back along `e` after pulling back along `e.symm` is isomorphic to the identity,
with the identity carrier map. -/
def smoothRepPullbackPullbackSymmIso {H : Type uH} [Group H] [TopologicalSpace H]
    {K : Type uK} [Group K] [TopologicalSpace K] (e : H ≃ₜ* K)
    (A : SmoothRep.{0, uH, uV} ℂ H) :
    SmoothRep.pullback e (SmoothRep.pullback e.symm A) ≅ A :=
  SmoothRep.pullbackSymmIso e.symm A

/-- A morphism of smooth representations is nonzero exactly when it moves some vector off
zero. Stating nonvanishing through vectors avoids comparing zero morphisms built from
different instance paths. -/
theorem smoothRep_ne_zero_iff_exists_apply_ne_zero {H : Type uH} [Group H] [TopologicalSpace H]
    {A B : SmoothRep.{0, uH, uV} ℂ H} (f : A ⟶ B) :
    f ≠ 0 ↔ ∃ v : A, SmoothRep.hom f v ≠ 0 := by
  constructor
  · intro hf
    by_contra hv
    apply hf
    ext v
    exact Classical.not_not.mp (not_exists.mp hv v)
  · rintro ⟨v, hv⟩ rfl
    exact hv rfl

section Core

open RepresentedParabolic

variable {k : Type uF} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance bernsteinGeneratorCoreAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

set_option maxHeartbeats 800000 in
/-- Core of the generator property in Renard VI.10.1 for two actual parabolics `P = MN` and
`Q = LU` whose Levis are conjugate by `g` through `φ : M ≅ L`: given the independence of the
induced progenerator (VI.10.1) and second adjointness (VI.9.6), if `Π_D` is projective, `X`
has a surjection `r_Q^G(X) ⟶ σ` and the pullback of `Π_D` along the point isomorphism
`(rationalPointIso φ).symm : L(F) ≃ M(F)` maps nontrivially to `σ`, then every object
isomorphic to `i_P^G(Π_D)` has a morphism to `X` that moves some vector off zero. -/
theorem exists_ne_zero_leviInduction_of_jacquet_epi
    (hIndep : InducedProgeneratorIndependenceStatement.{uF, max uF uV})
    (hAdj : LeviSecondAdjointnessStatement.{uF, uV})
    (hG : IsConnectedReductive G)
    {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (g : rationalPoints G) (φ : M ≅ L)
    (hφ : φ.hom ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso g).hom) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    haveI := hlQ.isConnectedReductive.isAffineHom
    haveI : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints M), π.IsIrreducible →
      IsSupercuspidal π →
    ∀ ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ (Plancherel.rationalCommonNormKernel M),
      ρ₀.IsIrreducible →
    ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
      Function.Injective (SmoothRep.hom j) →
      Projective (rationalNormKernelSummandInduction M ρ₀) →
    ∀ (X : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
      (σ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints L))
      (t : (leviJacquetFunctor.{uF, max uF uV} q lQ rQ hq hrQ hlQ hmulQ).obj X ⟶ σ),
      Function.Surjective (SmoothRep.hom t) →
    ∀ s : SmoothRep.pullback (rationalPointIso φ).symm (rationalNormKernelSummandInduction M ρ₀) ⟶
        σ,
      (∃ v, SmoothRep.hom s v ≠ 0) →
    ∀ (Y : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
      ((leviInductionFunctor.{uF, max uF uV} p l r hp hr hl hmul).obj
          (rationalNormKernelSummandInduction M ρ₀) ≅ Y) →
      ∃ f : Y ⟶ X, ∃ v, SmoothRep.hom f v ≠ 0 := by
  intro π hπ hsc ρ₀ hρ₀ j hj hproj X σ t ht s hs' Y eY
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have := hlQ.isConnectedReductive.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
  let e : rationalPoints L ≃ₜ* rationalPoints M := (rationalPointIso φ).symm
  have he : ∀ x, e x = rationalPoints.map φ.inv x := fun _ => rfl
  have hs : s ≠ 0 := (smoothRep_ne_zero_iff_exists_apply_ne_zero s).mpr hs'
  let O := oppositeLeviParabolic hG q lQ hq hlQ
  have hcond : φ.hom ≫ O.levi ≫ O.inclusion = l ≫ p ≫ (G.innerIso g).hom := by
    rw [O.levi_comp]
    exact hφ
  obtain ⟨ψ⟩ := hIndep k G hG P M N O.parabolic L O.radical p l r hp hl hr hmul
    O.inclusion O.levi O.unipotent O.isParabolic O.isLevi O.isRadical O.multiplication
    g φ hcond e he π hπ hsc ρ₀ hρ₀ j hj
  have hint : pointImage O.inclusion ⊓ pointImage q = pointImage (O.levi ≫ O.inclusion) := by
    rw [inf_comm, O.intersection, O.levi_comp]
  obtain ⟨adj⟩ := hAdj k G hG O.parabolic Q L O.radical U
    O.inclusion O.levi O.unipotent O.isParabolic O.isLevi O.isRadical O.multiplication
    q lQ rQ hq hlQ hrQ hmulQ O.levi_comp.symm hint
  have hproj' : Projective (SmoothRep.pullback e (rationalNormKernelSummandInduction M ρ₀)) :=
    ((SmoothRep.pullbackEquivalence e).map_projective_iff _).mpr hproj
  have : Epi t := (SmoothRep.epi_iff_surjective t).mpr ht
  let u := Projective.factorThru s t
  have hu : u ≫ t = s := Projective.factorThru_comp s t
  have hu0 : u ≠ 0 := by
    intro hz
    apply hs
    rw [← hu, hz, Limits.zero_comp]
  refine ⟨eY.inv ≫ ψ.hom ≫ (adj.homEquiv _ _).symm u,
    (smoothRep_ne_zero_iff_exists_apply_ne_zero _).mp ?_⟩
  intro hz
  apply hu0
  have h1 : (adj.homEquiv _ _).symm u = 0 := by
    rwa [Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_left_eq_zero] at hz
  rw [← (adj.homEquiv _ _).apply_symm_apply u, h1, Adjunction.homEquiv_unit,
    Functor.map_zero, Limits.comp_zero]

end Core

section Standard

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinProgeneratorGenInstance1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinProgeneratorGenInstance2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinProgeneratorGenInstance3 : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance bernsteinProgeneratorGenInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinProgeneratorGenInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinProgeneratorGenInstance6 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinProgeneratorGenInstance7 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

local instance bernsteinProgeneratorGenInstance8 (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) := by
  have := (isClosed_levi i ν I).locallyCompactSpace
  exact (leviRationalPointHomeomorph i ν I).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance bernsteinProgeneratorGenInstance9 (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) := by
  let e := leviRationalPointHomeomorph i ν I
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

variable (family : BernsteinStandardFamily i ν)

set_option maxHeartbeats 800000 in
/-- The membership conjunct of the VI.10.1 Theorem, conditional on the represented VI.5.2
(`LeviInductionNoSupercuspidalSubquotientStatement`) and on the joint special-compact basis
existence: `Π_Ω = i_P^G(Π_D)` lies in the Bernstein block of the inertial class of `a`. -/
theorem bernsteinInducedProgenerator_mem
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF,
      max uF uV})
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j)) :
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      (bernsteinInducedProgenerator.{uF, uV} i ν family a ρ₀) := by
  have hM := (bernsteinStandardRepresentativesGeometric i ν family
    a.roots).2.1.isConnectedReductive
  have hc := hasCompactNormKernelRestriction_bernsteinCuspidalDatum.{uF, uV} i ν family hJoint a
  have hc' : HasCompactSmoothDualCoefficients
      (a.representation.representation.comp
        (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)).subtype) := hc
  have hmem₁ := rationalNormKernelCompactInduction_mem_of_restriction
    (bernsteinLeviScheme i ν a.roots) hM a.representation a.irreducible hc'
    rationalNormKernelFiniteRestriction rationalNormKernelTwistEquivalence
  have hmem₂ := rationalNormKernelSummandInduction_mem (bernsteinLeviScheme i ν a.roots)
    a.representation ρ₀ j hmem₁ hj
  have hτ : rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation
      (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀) := by
    intro D hD hDS
    exact (IsRationalInertiaRelated.of_iso
      (SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF} a.representation))).trans
      (hmem₂ D hD hDS)
  exact bernsteinJacquetExclusion_implies_block i ν family a _
    (bernsteinJacquetExclusion_of_inertiaBlock_supercuspidal i ν family hind a _ hτ
      (RepresentedParabolic.isSupercuspidal_rationalNormKernelSummandInduction
        a.representation (a.isSupercuspidal i ν family) ρ₀ j hj))

/-- Renard's `Π_Ω = i_P^G(Π_D)` as an object of the Bernstein block of the inertial class of `a`,
with the membership proof `bernsteinInducedProgenerator_mem`; that proof keeps the represented
VI.5.2 and the joint special-compact basis existence as premises. -/
def bernsteinInducedProgeneratorBlockObject
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF,
      max uF uV})
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j)) :
    BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a) :=
  ⟨bernsteinInducedProgenerator.{uF, uV} i ν family a ρ₀,
    bernsteinInducedProgenerator_mem.{uF, uV} i ν family hind hJoint a ρ₀ j hj⟩

set_option maxHeartbeats 1600000 in
/-- The Jacquet step of generation: an irreducible `τ` with inertial support the class of `a`
has, for some cuspidal datum `c` inertia-related to `a`, the literal representation of `c` as
a quotient of its normalized Jacquet module along the standard parabolic of `c`. The
represented VI.5.2 is a premise; through the published geometric exclusion
`bernsteinJacquetExclusion_of_inertiaBlock_supercuspidal` it shows that `c` is related to `a`. -/
theorem exists_related_jacquet_quotient_of_inertialSupport
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF,
      max uF uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hτ : IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family a) τ) :
    ∃ c : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
      IsBernsteinInertiaRelated i ν family a c ∧
      SmoothRep.IsQuotient (bernsteinLiteralLeviRep i ν c.roots c.representation)
        ((jacquetFunctor (family.decomposition c.roots)
          (family.closedUnipotent c.roots)).obj τ) := by
  obtain ⟨b, hb, hτirr, hτb⟩ := hτ
  have hab : IsBernsteinInertiaRelated i ν family a b :=
    (bernsteinInertialClass_eq_iff i ν family a b).mp hb.symm
  obtain ⟨c, hcq, -⟩ :=
    exists_bernsteinCuspidalDatum_jacquet_quotient_induction_embedding i ν family τ hτirr
  have hbself : rationalInertiaBlockProperty (bernsteinLeviScheme i ν b.roots) b.representation
      b.representation := by
    intro D hD hDb
    obtain ⟨e⟩ := NormalHecke.nonempty_iso_of_isSubquotient b.irreducible hD hDb
    exact IsRationalInertiaRelated.of_iso e.symm
  have hexcl := bernsteinJacquetExclusion_of_inertiaBlock_supercuspidal i ν family hind b
    b.representation hbself (b.isSupercuspidal i ν family)
  have hcV := smoothSubquotientTransitivity ℂ _ _ _ _ hcq.isSubquotient
    (bernsteinJacquet_isSubquotient i ν family c.roots hτb)
  have hbc : IsBernsteinInertiaRelated i ν family b c := by
    by_contra h
    exact hexcl c h hcV
  exact ⟨c, hab.trans hbc, hcq⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- A quotient of the literal standard Jacquet module gives a surjection from the represented
standard Jacquet module onto the representation of the standard Levi. -/
theorem exists_surjective_bernsteinStandardRepresentedJacquet_of_isQuotient
    (I : Finset (SimpleRoot i ν))
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (X : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (h : SmoothRep.IsQuotient (bernsteinLiteralLeviRep i ν I σ)
      ((jacquetFunctor (family.decomposition I) (family.closedUnipotent I)).obj X)) :
    ∃ t : (bernsteinStandardRepresentedJacquetFunctor i ν family I).obj X ⟶ σ,
      Function.Surjective (SmoothRep.hom t) := by
  obtain ⟨f, hf⟩ := h
  let eC := leviRationalPointHomeomorph i ν I
  refine ⟨(bernsteinStandardRepresentedJacquetIso i ν family I X).hom ≫
      (SmoothRep.pullbackFunctor eC).map f ≫ (smoothRepPullbackPullbackSymmIso eC σ).hom, ?_⟩
  have hfe : Epi f := (SmoothRep.epi_iff_surjective f).mpr hf
  have e1 : Epi (bernsteinStandardRepresentedJacquetIso i ν family I X).hom := inferInstance
  have e2 : Epi ((SmoothRep.pullbackFunctor eC).map f) :=
    (SmoothRep.pullbackEquivalence eC).functor.map_epi f
  have e3 : Epi (smoothRepPullbackPullbackSymmIso eC σ).hom := inferInstance
  have e4 := @epi_comp _ _ _ _ _ _ e2 _ e3
  exact (SmoothRep.epi_iff_surjective _).mp (@epi_comp _ _ _ _ _ _ e1 _ e4)

/-- The norm-kernel summand induction `Π_D` of `a`, transported along an algebraic Levi
conjugacy `φ : M_a ≅ M_c`, maps nontrivially to the representation of `c` when `a` and the
transport of `c` are inertia-related. -/
theorem exists_ne_zero_pullback_rationalNormKernelSummandInduction
    (a c : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (φ : bernsteinLeviScheme i ν a.roots ≅ bernsteinLeviScheme i ν c.roots)
    (hrel : IsRationalInertiaRelated (bernsteinLeviScheme i ν a.roots) a.representation
      (rationalIsoPullback φ c.representation))
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hρ₀ : ρ₀.IsIrreducible)
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j)) :
    ∃ s : SmoothRep.pullback (rationalPointIso φ).symm
        (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀) ⟶
      c.representation, ∃ v, SmoothRep.hom s v ≠ 0 := by
  have hrel' : IsRationalInertiaRelated (bernsteinLeviScheme i ν a.roots)
      (rationalInertiaBaseLift (bernsteinLeviScheme i ν a.roots) a.representation)
      (rationalIsoPullback φ c.representation) :=
    (IsRationalInertiaRelated.of_iso
      (SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF} a.representation))).symm.trans hrel
  obtain ⟨s₀, hs₀⟩ := exists_nonzero_rationalNormKernelSummandInduction
    (bernsteinLeviScheme i ν a.roots) a.representation ρ₀ j hρ₀ hj
    (rationalIsoPullback φ c.representation) hrel'
  let e := (rationalPointIso φ).symm
  refine ⟨(SmoothRep.pullbackFunctor e).map s₀ ≫
      (SmoothRep.pullbackSymmIso (rationalPointIso φ) c.representation).hom,
    (smoothRep_ne_zero_iff_exists_apply_ne_zero _).mp ?_⟩
  intro hz
  apply hs₀
  have h1 : (SmoothRep.pullbackEquivalence e).functor.map s₀ = 0 := by
    rwa [Preadditive.IsIso.comp_right_eq_zero] at hz
  have : (SmoothRep.pullbackEquivalence e).functor.IsLeftAdjoint :=
    (SmoothRep.pullbackEquivalence e).isLeftAdjoint_functor
  have : (SmoothRep.pullbackEquivalence e).functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  exact (Functor.map_eq_zero_iff _).mp h1

set_option maxHeartbeats 800000 in
/-- Generation of the irreducible objects of the block, conditional on the independence of the
induced progenerator (VI.10.1), second adjointness (VI.9.6), the joint special-compact basis
existence and the represented VI.5.2: every irreducible `τ` with inertial support the class of
`a` receives a nonzero morphism from `Π_Ω`. -/
theorem exists_ne_zero_bernsteinInducedProgenerator_of_inertialSupport
    (hIndep : RepresentedParabolic.InducedProgeneratorIndependenceStatement.{uF, max uF uV})
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV})
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF})
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF,
      max uF uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hρ₀ : ρ₀.IsIrreducible)
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j))
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hτ : IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family a) τ) :
    ∃ f : (normalizedInductionFunctor (family.decomposition a.roots)
          (family.closedUnipotent a.roots)).obj
        (bernsteinLiteralLeviRep i ν a.roots
          (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)) ⟶ τ,
      f ≠ 0 := by
  obtain ⟨c, ⟨cc, hrel⟩, hcq⟩ :=
    exists_related_jacquet_quotient_of_inertialSupport.{uF, uV} i ν family hind a τ hτ
  obtain ⟨t, ht⟩ := exists_surjective_bernsteinStandardRepresentedJacquet_of_isQuotient.{uF, uV}
    i ν family c.roots c.representation τ hcq
  obtain ⟨s, hs⟩ := exists_ne_zero_pullback_rationalNormKernelSummandInduction.{uF, uV}
    i ν family a c cc.iso hrel ρ₀ hρ₀ j hj
  have hA := bernsteinStandardRepresentativesGeometric i ν family a.roots
  have hC := bernsteinStandardRepresentativesGeometric i ν family c.roots
  have hφ : cc.iso.hom ≫ Standard.leviToParabolic i ν (rootSet i ν c.roots) ≫
        Standard.parabolicHom i ν (rootSet i ν c.roots) =
      Standard.leviToParabolic i ν (rootSet i ν a.roots) ≫
        Standard.parabolicHom i ν (rootSet i ν a.roots) ≫ (G.innerIso cc.point).hom := by
    rw [Standard.leviToParabolic_comp, ← Category.assoc, Standard.leviToParabolic_comp]
    exact cc.commutes.symm
  have hproj := projective_rationalNormKernelSummandInduction_of_datum.{uF, uV} i ν family
    hJoint a ρ₀ j hj
  obtain ⟨f', hf'⟩ := exists_ne_zero_leviInduction_of_jacquet_epi.{uF, uV} hIndep hAdj
    family.connectedReductive (M := bernsteinLeviScheme i ν a.roots)
    (L := bernsteinLeviScheme i ν c.roots)
    (Standard.parabolicHom i ν (rootSet i ν a.roots))
    (Standard.leviToParabolic i ν (rootSet i ν a.roots))
    (Standard.unipotentToParabolic i ν (rootSet i ν a.roots))
    hA.1 hA.2.1 hA.2.2.1 hA.2.2.2
    (Standard.parabolicHom i ν (rootSet i ν c.roots))
    (Standard.leviToParabolic i ν (rootSet i ν c.roots))
    (Standard.unipotentToParabolic i ν (rootSet i ν c.roots))
    hC.1 hC.2.1 hC.2.2.1 hC.2.2.2 cc.point cc.iso hφ
    a.representation a.irreducible (a.isSupercuspidal i ν family) ρ₀ hρ₀ j hj hproj
    τ c.representation t ht s hs
    ((normalizedInductionFunctor (family.decomposition a.roots)
          (family.closedUnipotent a.roots)).obj
        (bernsteinLiteralLeviRep i ν a.roots
          (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)))
    (bernsteinStandardRepresentedInductionIso i ν family a.roots _)
  exact ⟨f', (smoothRep_ne_zero_iff_exists_apply_ne_zero f').mpr hf'⟩


set_option maxHeartbeats 800000 in
/-- The generator conjunct of the VI.10.1 Theorem, conditional on the independence of the
induced progenerator (VI.10.1), second adjointness (VI.9.6), the joint special-compact basis
existence and the represented VI.5.2: once `Π_Ω` lies in the block, two different morphisms of
the block are separated by a morphism out of `Π_Ω`. -/
theorem bernsteinInducedProgenerator_separates
    (hIndep : RepresentedParabolic.InducedProgeneratorIndependenceStatement.{uF, max uF uV})
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV})
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF})
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF,
      max uF uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hρ₀ : ρ₀.IsIrreducible)
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation)
    (hj : Function.Injective (SmoothRep.hom j))
    (hmem : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))))
    (X Y : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a))
    (f g : X ⟶ Y) (hfg : f ≠ g) :
    ∃ h : (⟨_, hmem⟩ :
        BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)) ⟶ X,
      h ≫ f ≠ h ≫ g := by
  have hproj := projective_bernsteinInducedProgenerator.{uF, uV} i ν family hAdj hJoint a ρ₀ j hj
  have hn : f.hom - g.hom ≠ 0 := by
    intro h
    exact hfg (ObjectProperty.hom_ext _ (sub_eq_zero.mp h))
  obtain ⟨s, hs⟩ := SmoothRep.exists_comp_ne_zero_of_projective_subquotients _
    (f.hom - g.hom) hn (fun D hD hDY =>
      exists_ne_zero_bernsteinInducedProgenerator_of_inertialSupport.{uF, uV} i ν family
        hIndep hAdj hJoint hind a ρ₀ hρ₀ j hj D (Y.property D hD hDY))
  refine ⟨ObjectProperty.homMk s, fun h => hs ?_⟩
  have h' : s ≫ f.hom = s ≫ g.hom := congrArg (fun m => m.hom) h
  rw [Preadditive.comp_sub, h', sub_self]

end Standard

set_option maxHeartbeats 800000 in
/-- Renard VI.10.1, Theorem, reduced to its structural inputs: the independence of the induced
progenerator (VI.10.1, Proposition), second adjointness (VI.9.6), the joint special-compact
basis existence, the finite type of parabolic induction (VI.7.5) and the represented VI.5.2. -/
theorem bernsteinInducedProgenerator_of_secondAdjointness
    (hIndep : RepresentedParabolic.InducedProgeneratorIndependenceStatement.{uF, max uF uV})
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV})
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF})
    (hFT : RepresentedParabolic.LeviInductionFiniteTypeStatement.{uF, max uF uV})
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF,
      max uF uV}) :
    BernsteinInducedProgeneratorStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family a ρ₀ hρ₀ j hj
  have hmem := bernsteinInducedProgenerator_mem.{uF, uV} i ν family hind hJoint a ρ₀ j hj
  exact ⟨hmem,
    bernsteinInducedProgenerator_lift_of_secondAdjointness.{uF, uV} i ν family hAdj hJoint a ρ₀
      j hj hmem,
    finite_bernsteinInducedProgenerator_of_leviInductionFiniteType.{uF, uV} i ν family hFT a ρ₀
      hρ₀,
    bernsteinInducedProgenerator_separates.{uF, uV} i ν family hIndep hAdj hJoint hind a ρ₀ hρ₀
      j hj hmem⟩

/-- Renard VI.10.2 (the block is equivalent to modules over `End(Π_Ω)`), reduced to the
structural inputs of `bernsteinInducedProgenerator_of_secondAdjointness`. -/
theorem bernsteinBlockHomEquivalence_of_secondAdjointness
    (hIndep : RepresentedParabolic.InducedProgeneratorIndependenceStatement.{uF, max uF uV})
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV})
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF})
    (hFT : RepresentedParabolic.LeviInductionFiniteTypeStatement.{uF, max uF uV})
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF,
      max uF uV}) :
    BernsteinBlockHomEquivalenceStatement.{uF, uV} :=
  bernsteinBlockHomEquivalence_of_inducedProgenerator
    (bernsteinInducedProgenerator_of_secondAdjointness hIndep hAdj hJoint hFT hind)

/-- Renard VI.10.3 (Jacquet detection on the block), reduced to the structural inputs of
`bernsteinInducedProgenerator_of_secondAdjointness`. -/
theorem bernsteinBlockJacquetFaithful_of_secondAdjointness
    (hIndep : RepresentedParabolic.InducedProgeneratorIndependenceStatement.{uF, max uF uV})
    (hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV})
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF})
    (hFT : RepresentedParabolic.LeviInductionFiniteTypeStatement.{uF, max uF uV})
    (hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF,
      max uF uV}) :
    BernsteinBlockJacquetFaithfulStatement.{uF, uV} :=
  bernsteinBlockJacquetFaithful_of_inducedProgenerator
    (bernsteinInducedProgenerator_of_secondAdjointness hIndep hAdj hJoint hFT hind) hIndep hAdj

end Langlands.CuspidalSupport
