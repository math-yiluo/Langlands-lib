import Langlands.Representation.Category.CoproductSize
import Langlands.Representation.Aubert.General.InertiaInductionCompression
import Langlands.Representation.CuspidalSupport.RationalCuspidalBlockVisibility
import Langlands.CategoryTheory.Renard.CategoryDecompositionSimpleClassesProof

/-! # Compression from the actual whole cuspidal inertia decomposition -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.LinearAlgebra.StableEndomorphism
open scoped CategoryTheory.MonObj

universe uF uV uG uH uI

namespace Langlands.SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] {I : Type uI}

/-- Finite compact-level support passes through actual same-carrier pullback
by a continuous group equivalence. -/
theorem compactFiniteFixedVectorSupport_pullback
    (e : H ≃ₜ* G) (A : I → SmoothRep.{0, uG, uV} ℂ G)
    (hA : CompactFiniteFixedVectorSupport A) :
    CompactFiniteFixedVectorSupport (fun i => pullback e (A i)) := by
  intro K hK
  let L := K.comap e.symm.toMonoidHom e.symm.continuous
  have hL : IsCompact (L : Set G) :=
    e.symm.toHomeomorph.isCompact_preimage.mpr hK
  have hf := hA L hL
  apply hf.subset
  intro i hi
  change Nontrivial (fixedVectors ((A i).representation.comp e.toMonoidHom)
    K.toSubgroup) at hi
  rwa [fixedVectors_comp_mulEquiv (A i).representation e.toMulEquiv K.toSubgroup] at hi

end Langlands.SmoothRep

namespace Langlands.CuspidalSupport

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (L : GroupScheme (Spec (CommRingCat.of F))) [IsAffine L.X.left]
  [LocallyOfFiniteType L.X.hom]

local instance rationalCuspidalCompressionPointTopology :
    TopologicalSpace (rationalPoints L) :=
  rationalPointTopology F L.X

local instance rationalCuspidalCompressionTopologicalGroup :
    IsTopologicalGroup (rationalPoints L) :=
  rationalPoint_isTopologicalGroup F L

variable [LocallyCompactSpace (rationalPoints L)]
  [NonarchimedeanGroup (rationalPoints L)]
variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ L) (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hL : ∀ J, IsSemidirectDecomposition
    (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (hUL : ∀ J, IsClosed (unipotent i ν J : Set (rationalPoints L)))
variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (e : M ≃ₜ* rationalPoints L)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)

/-- Eventual compression stability for the actual induced norm-kernel
generator of every actual irreducible cuspidal inertia representative. -/
def RationalCuspidalGeneratorImageEventuallyStable : Prop :=
  ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints L),
    π.IsIrreducible →
    IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hL hUL π →
    EventuallyStable (Jacquet.compressedAction
      ((rationalInertiaInductionFunctor L h hU e).obj
        (rationalNormKernelCompactInduction L π)).representation
      ((rationalInertiaInductionFunctor L h hU e).obj
        (rationalNormKernelCompactInduction L π)).isSmooth K hK g)

/-- The actual whole inertia decomposition, compact-level class finiteness,
and eventual stability of the actual induced generators imply eventual
stability for induction of every all-cuspidal object. -/
theorem rationalAllCuspidalInduction_eventuallyStable_of_generators [T2Space G]
    (hStandard : StandardCocharacterStatement.{uF}) (hRed : IsConnectedReductive L)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hcof : CompactOpenCofinal G) (hP : IsClosed (P : Set G))
    (hproj : Continuous h.projection) (hM : IsClosed (M : Set G))
    [CompactSpace (Induction.LeftQuotient P)]
    (hdecomp : IsRationalCuspidalInertiaProductDecomposition.{uF, max uF uV}
      L i ν hL hUL)
    (hfinite : ∀ Q : OpenSubgroup (rationalPoints L),
      IsCompact (Q : Set (rationalPoints L)) →
      Set.Finite {c : RationalIrreducibleInertiaClass.{uF, max uF uV} L |
        ∃ (D : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints L))
          (hD : D.IsIrreducible),
          IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hL hUL D ∧
          rationalIrreducibleInertiaClass L D hD = c ∧
          Nontrivial (fixedVectors D.representation Q.toSubgroup)})
    (hgen : ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints L),
      π.IsIrreducible →
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hL hUL π →
      IsRationalNormKernelSmallProgenerator L π)
    (hstable : RationalCuspidalGeneratorImageEventuallyStable.{uF, uV}
      L i ν hL hUL h hU e K hK g)
    (A : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints L))
    (hA : rationalAllCuspidalSubquotientProperty L i ν hL hUL A) :
    EventuallyStable (Jacquet.compressedAction
      ((rationalInertiaInductionFunctor L h hU e).obj A).representation
      ((rationalInertiaInductionFunctor L h hU e).obj A).isSmooth K hK g) := by
  classical
  obtain ⟨B, j, hB, ⟨hs⟩⟩ := hdecomp.1 A
  let Tind := rationalInertiaInductionFunctor.{uF, uV, uG} L h hU e
  have hzero : IsZero (B none) := by
    apply (SmoothRep.isZero_iff_subsingleton _).mpr
    apply not_nontrivial_iff_subsingleton.mp
    intro hne
    have : Mono (j none) :=
      Renard.CategoryDecompositionSimpleClassesProof.cofan_leg_mono hs none
    have hsub : SmoothRep.IsSubquotient (B none) A :=
      SmoothRep.IsSubrepresentation.isSubquotient
        ⟨j none, (SmoothRep.mono_iff_injective _).mp inferInstance⟩
    have hc := hA (B none) hsub
    exact hB none (B none) hne
      (SmoothRep.IsSubrepresentation.isSubquotient ⟨𝟙 _, Function.injective_id⟩) hc
  have hsource : SmoothRep.CompactFiniteFixedVectorSupport
      (fun c => B (some c)) := by
    exact compactFiniteFixedVectorSupport_rationalCuspidalBlocks
      L i ν hStandard hRed hi hν hL hUL hfinite
      (fun c => ⟨B (some c), hB (some c)⟩)
  have hpull := SmoothRep.compactFiniteFixedVectorSupport_pullback e _ hsource
  have hsome := finite_fixedVectorSupport_normalizedInduction h hU hM
    (fun c => SmoothRep.pullback e (B (some c))) hpull K
  have hsupport : Jacquet.FiniteFixedVectorSupport
      (fun o => (Tind.obj (B o)).representation) K.toSubgroup := by
    apply ((hsome.image some).union (Set.finite_singleton none)).subset
    intro o ho
    cases o with
    | none => exact Or.inr (Set.mem_singleton _)
    | some c => exact Or.inl ⟨c, ho, rfl⟩
  have hpoint : ∀ o, EventuallyStable (Jacquet.compressedAction
      (Tind.obj (B o)).representation (Tind.obj (B o)).isSmooth K hK g) := by
    intro o
    cases o with
    | none =>
        have : Subsingleton (Tind.obj (B none)) :=
          (SmoothRep.isZero_iff_subsingleton _).mp (Tind.map_isZero hzero)
        exact ⟨1, by omega, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    | some c =>
        obtain ⟨π, hπ, hc, hπc⟩ := c.property
        have hblock : rationalInertiaBlockProperty L π (B (some c)) := by
          intro D hD hDB
          exact (rationalIrreducibleInertiaClass_eq_iff L π D hπ hD).mp
            (hπc.trans (hB (some c) D hD hDB).symm)
        have hrelated : IsRationalInertiaRelated L π (rationalInertiaBaseLift L π) :=
          .of_iso (SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF} π))
        have hblock' : rationalInertiaBlockProperty L
            (rationalInertiaBaseLift L π) (B (some c)) :=
          (rationalInertiaBlockProperty_iff_of_related hrelated).mp hblock
        obtain ⟨b, _, hb⟩ :=
          rationalInertiaInduction_stationary_of_normKernel
            L h hU e π K hK g hcof hP hproj (hgen π hπ hc) (hstable π hπ hc)
        exact (Jacquet.compactCompression_eventuallyStable_iff_exists_stationaryFrom
          _ _ K hK g).mpr ⟨b, hb ⟨B (some c), hblock'⟩⟩
  have hcop (J : Type (max uF uV)) :
      PreservesColimitsOfShape (Discrete J) Tind := by
    have : PreservesColimitsOfShape (Discrete J)
        (normalizedInductionFunctor.{uG, max uF uV} h hU) :=
      normalizedInductionFunctor_preservesCoproducts.{uG, max uF uV, 0} h hU
    dsimp only [Tind, rationalInertiaInductionFunctor]
    exact comp_preservesColimitsOfShape _ _
  exact SmoothRep.compressedAction_eventuallyStable_of_cofan_finite_support
    (fun o => Tind.obj (B o))
    (Limits.Cofan.mk (Tind.obj A) (fun o => Tind.map (j o)))
    (SmoothRep.mapCofanIsColimit_of_carrierCoproducts Tind hcop B
      (Limits.Cofan.mk A j) hs) K hK g hsupport hpoint

end Langlands.CuspidalSupport
