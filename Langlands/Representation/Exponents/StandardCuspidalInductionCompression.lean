import Langlands.Representation.Plancherel.RationalCuspidalInductionCompression
import Langlands.Representation.Exponents.RationalLeviCompressionTransport

/-! # Native compression on actual standard cuspidal inductions -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.LinearAlgebra.StableEndomorphism

namespace Langlands.Aubert.General

universe u uV uG

section InductionComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F))) [IsAffine L.X.left]
  [LocallyOfFiniteType L.X.hom]

local instance standardCompressionComparisonPointTopology :
    TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X

variable {H : Type uG} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P M U P' M' U' : Subgroup H}

/-- Identical embedded parabolic, Levi and radical groups, and identical
embedded inverse Levi maps, give the same actual induced object. -/
def rationalInertiaInductionIsoOfEmbeddedLevi
    (hP : P = P') (hM : M = M') (hN : U = U')
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set H))
    (e : M ≃ₜ* rationalPoints L) (e' : M' ≃ₜ* rationalPoints L)
    (he : ∀ x : rationalPoints L, (e.symm x : H) = (e'.symm x : H))
    (B : SmoothRep.{0, u, max u uV} ℂ (rationalPoints L)) :
    (rationalInertiaInductionFunctor L h hU e).obj B ≅
      (rationalInertiaInductionFunctor L h' hU' e').obj B := by
  subst P'
  subst M'
  subst U'
  have heq : e.symm = e'.symm := by
    ext x
    exact he x
  have heq' : e = e' := by
    simpa only [ContinuousMulEquiv.symm_symm] using
      congrArg (fun f : rationalPoints L ≃ₜ* M => f.symm) heq
  subst e'
  exact Iso.refl _

end InductionComparison

namespace RationalPointFamily

open Plancherel Plancherel.RationalNormalized CuspidalSupport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))

local instance standardCompressionAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardCompressionAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance standardCompressionLeviClosed :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance standardCompressionLeviAffine :
    IsAffine (Standard.leviScheme i ν (rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance standardCompressionLeviTopology :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
  pointTopology

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The represented standard parabolic has exactly the literal standard points. -/
theorem standardCompression_parabolicPoints :
    ParabolicPoints (Standard.parabolicHom i ν (rootSet i ν I)) = parabolic i ν I :=
  congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
    (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν I)).2

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The represented standard Levi has exactly the literal standard points. -/
theorem standardCompression_leviPoints :
    parabolicLeviPointSubgroup (Standard.parabolicHom i ν (rootSet i ν I))
      (Standard.leviToParabolic i ν (rootSet i ν I)) = levi i ν I := by
  unfold parabolicLeviPointSubgroup
  rw [Standard.leviToParabolic_comp]
  exact congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I)).2

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The represented standard radical has exactly the literal standard points. -/
theorem standardCompression_unipotentPoints :
    UnipotentPoints (p := Standard.parabolicHom i ν (rootSet i ν I))
      (Standard.unipotentToParabolic i ν (rootSet i ν I)) = unipotent i ν I := by
  unfold UnipotentPoints
  rw [Standard.unipotentToParabolic_comp]
  exact congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
    (Standard.isRepresentedBy_unipotentHom i ν (rootSet i ν I)).2

variable {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {a : A.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)}
  (r : ParabolicRootPresentation (Standard.parabolicHom i ν (rootSet i ν I))
    (Standard.leviToParabolic i ν (rootSet i ν I)) a)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Both canonical Levi homeomorphisms give the same actual ambient point. -/
theorem standardCompression_leviHomeomorph_coe
    (x : rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :
    (parabolicLeviPointHomeomorph r x : rationalPoints G) =
      (leviRationalPointHomeomorph i ν I x : rationalPoints G) := by
  rw [parabolicLeviPointHomeomorph_apply_coe, leviRationalPointHomeomorph_apply_coe,
    Standard.leviToParabolic_comp]

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyOfFiniteType (Standard.leviScheme i ν (rootSet i ν I)).X.hom]
  (h : ∀ J, IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (hU : ∀ J, IsClosed (unipotent i ν J : Set (rationalPoints G)))
  (hR : IsSemidirectDecomposition
    (ParabolicPoints (Standard.parabolicHom i ν (rootSet i ν I)))
    (parabolicLeviPointSubgroup (Standard.parabolicHom i ν (rootSet i ν I))
      (Standard.leviToParabolic i ν (rootSet i ν I)))
    (UnipotentPoints (p := Standard.parabolicHom i ν (rootSet i ν I))
      (Standard.unipotentToParabolic i ν (rootSet i ν I))))
  (hUR : IsClosed (UnipotentPoints (p := Standard.parabolicHom i ν (rootSet i ν I))
      (Standard.unipotentToParabolic i ν (rootSet i ν I)) : Set (rationalPoints G)))

/-- The native represented-standard induction is the actual literal-standard
induction after its canonical rational-Levi pullback. -/
def standardCompression_inductionIso
    (B : SmoothRep.{0, u, max u uV} ℂ
      (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))) :
    (rationalInertiaInductionFunctor (Standard.leviScheme i ν (rootSet i ν I))
      hR hUR (parabolicLeviPointHomeomorph r).symm).obj B ≅
    (rationalInertiaInductionFunctor (Standard.leviScheme i ν (rootSet i ν I))
      (h I) (hU I) (leviRationalPointHomeomorph i ν I).symm).obj B :=
  rationalInertiaInductionIsoOfEmbeddedLevi _
    (standardCompression_parabolicPoints i ν I) (standardCompression_leviPoints i ν I)
    (standardCompression_unipotentPoints i ν I) hR hUR (h I) (hU I)
    (parabolicLeviPointHomeomorph r).symm (leviRationalPointHomeomorph i ν I).symm
    (standardCompression_leviHomeomorph_coe i ν I r) B


variable [LocallyCompactSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))] [NonarchimedeanGroup (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))]
  [Fintype (SimpleRoot (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν)]
  (hOwn : ∀ J, IsSemidirectDecomposition
    (parabolic (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J) (levi (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J) (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J))
  (hUL : ∀ J, IsClosed (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J : Set (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))))
  (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
  (hr : Continuous hR.projection)
  (hCompact : CompactSpace
    (Induction.LeftQuotient (ParabolicPoints (Standard.parabolicHom i ν (rootSet i ν I)))))
  (hn : LeviSubgroup.IsGeometricUnipotentRadical
    (Standard.unipotentToParabolic i ν (rootSet i ν I)))
  (hdecomp : IsRationalCuspidalInertiaProductDecomposition.{u, max u uV}
    (Standard.leviScheme i ν (rootSet i ν I)) (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν hOwn hUL)
  (hfinite : ∀ Q : OpenSubgroup (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))),
    IsCompact (Q : Set (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))) →
    Set.Finite {c : RationalIrreducibleInertiaClass.{u, max u uV} (Standard.leviScheme i ν (rootSet i ν I)) |
      ∃ (D : SmoothRep.{0, u, max u uV} ℂ (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))) (hD : D.IsIrreducible),
        IsCuspidal (parabolic (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν) (levi (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν) (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν) hOwn hUL D ∧
        rationalIrreducibleInertiaClass (Standard.leviScheme i ν (rootSet i ν I)) D hD = c ∧
        Nontrivial (fixedVectors D.representation Q.toSubgroup)})
  (hgen : ∀ π : SmoothRep.{0, u, max u uV} ℂ (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))),
    π.IsIrreducible →
    IsCuspidal (parabolic (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν) (levi (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν) (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν) hOwn hUL π →
    IsRationalNormKernelSmallProgenerator (Standard.leviScheme i ν (rootSet i ν I)) π)
  (hNative : RationalCuspidalNativeJacquetInputs.{u, uV} r hR hUR (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν hOwn hUL)
  (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (g : rationalPoints G)
  (hc : Jacquet.IsIwahoriContraction K
    (BruhatTits.DynamicUnipotentContainment.unipotentPoints ξ) (outputLeviPoints ξ)
    (BruhatTits.DynamicUnipotentContainment.unipotentPoints (Dynamic.inverseCocharacter ξ)) g)
  (hcentral : ∀ m ∈ outputLeviPoints ξ, m * g = g * m)

include hL hr hCompact hn hdecomp hfinite hgen hNative hc hcentral

set_option maxHeartbeats 800000 in
/-- Native irreducible Jacquet inputs and the actual whole-cuspidal decomposition
supply stability on the canonical standard rational-Levi induced image. -/
theorem standardCuspidalInduction_eventuallyStable_of_nativeJacquet
    (hDynamic : DynamicLieStatement.{u}) (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (E : SmoothRep.{0, u, max u uV} ℂ (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))))
    (hE : IsCuspidal (parabolic (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν) (levi (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν) (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν) hOwn hUL E) :
    EventuallyStable (Jacquet.compressedAction
      (((rationalInertiaInductionFunctor (Standard.leviScheme i ν (rootSet i ν I)) (h I) (hU I)
        (leviRationalPointHomeomorph i ν I).symm).obj E).representation)
      (((rationalInertiaInductionFunctor (Standard.leviScheme i ν (rootSet i ν I)) (h I) (hU I)
        (leviRationalPointHomeomorph i ν I).symm).obj E).isSmooth) K hK g) := by
  have hj : IsMaximalSplitTorus (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))
  have hνL : IsGenericCocharacter (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν :=
    (standardLeviStandardFamilies hDynamic hStandard F G hG T i hi ν hν
      (rootSet i ν I) (rootSet_subset i ν I) (Standard.leviScheme i ν (rootSet i ν I)) hL
      (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))).2.1
  obtain ⟨b, hb, hp⟩ := rationalCuspidalInduction_eventuallyStable_of_nativeJacquet
    r hR hUR (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν hOwn hUL hStandard hL hj hνL hG hn hr hCompact
    hdecomp hfinite hgen hNative ξ K hK g hc hcentral E hE
  let e := SmoothRep.equivOfIso (standardCompression_inductionIso i ν I r h hU hR hUR E)
  refine ⟨b, hb, ?_⟩
  exact Jacquet.compactCompressionStablePower_of_retract _ _ _ _ K hK g
    e.symm.toIntertwiningMap e.toIntertwiningMap
    (by ext x; exact e.apply_symm_apply x) b hp

variable (hMI : IsClosed (levi i ν I : Set (rationalPoints G)))
  (hInner : ∀ J : Finset I, IsSemidirectDecomposition
    ((parabolic i ν (leviIndex I J)).subgroupOf (levi i ν I))
    ((levi i ν (leviIndex I J)).subgroupOf (levi i ν I))
    ((unipotent i ν (leviIndex I J)).subgroupOf (levi i ν I)))

set_option maxHeartbeats 800000 in
/-- The actual normalized induction of every literal inside-Levi cuspidal object
is eventually stable under the retained native and structural hypotheses. -/
theorem literalLeviInduction_eventuallyStable_of_nativeJacquet
    (hDynamic : DynamicLieStatement.{u}) (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (D : SmoothRep.{0, u, max u uV} ℂ (levi i ν I))
    (hD : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU I hMI hInner D) :
    EventuallyStable (Jacquet.compressedAction
      ((normalizedInductionFunctor (h I) (hU I)).obj D).representation
      ((normalizedInductionFunctor (h I) (hU I)).obj D).isSmooth K hK g) := by
  apply literalLeviInduction_eventuallyStable_of_rationalImages
    i ν I hL h hU hUL hMI hInner hOwn K hK g hDynamic hStandard hG hi hν
    ?_ D hD
  intro E hE
  exact standardCuspidalInduction_eventuallyStable_of_nativeJacquet
    i ν I r h hU hR hUR hOwn hUL hL hr hCompact hn hdecomp hfinite hgen hNative
    ξ K hK g hc hcentral hDynamic hStandard hG hi hν E hE

end RationalPointFamily
end Langlands.Aubert.General
