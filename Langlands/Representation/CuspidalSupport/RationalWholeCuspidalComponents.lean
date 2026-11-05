import Langlands.Representation.CuspidalSupport.RationalCompactRestrictionDecomposition

/-!
# Actual whole-cuspidal components under the remaining comparison

The components are the actual kernel and range of the rational norm-kernel
compact projector. Fixed-level finiteness and the full objectwise equivalence
with proper-standard cuspidality remain intermediate proof obligations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable [LocallyCompactSpace (GroupScheme.rationalPoints G)]
  [NonarchimedeanGroup (GroupScheme.rationalPoints G)]

local instance : LocallyCompactSpace (Plancherel.rationalCommonNormKernel G) :=
  (Plancherel.isOpen_rationalCommonNormKernel G).locallyCompactSpace

variable (hstrata :
  ∀ K : OpenSubgroup (Plancherel.rationalCommonNormKernel G),
    IsCompact (K : Set (Plancherel.rationalCommonNormKernel G)) →
      (CompactCoefficientClass.fixedStratum.{uF, uV} K.toSubgroup).Finite)

/-- The actual range (`true`) and kernel (`false`) of the norm-kernel compact
projector, as smooth ambient subrepresentations. -/
def rationalNormKernelCompactComponents
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    Bool → SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G) :=
  let p := rationalNormKernelCompactProjector G hstrata A
  SmoothRep.complementaryComponents A p.range p.ker

/-- The literal inclusions of the compact-projector components into `A`. -/
def rationalNormKernelCompactCofan
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    Cofan (rationalNormKernelCompactComponents G hstrata A) :=
  let p := rationalNormKernelCompactProjector G hstrata A
  SmoothRep.complementaryCofan A p.range p.ker

/-- Idempotence supplies the actual coproduct universal property. -/
def rationalNormKernelCompactCofanIsColimit
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    IsColimit (rationalNormKernelCompactCofan G hstrata A) := by
  apply SmoothRep.complementaryCofanIsColimit
  apply LinearMap.IsIdempotentElem.isCompl
  ext v
  exact rationalNormKernelCompactProjector_idempotent G hstrata A v

private theorem kernel_compactOpen_cofinal :
    ∀ K : OpenSubgroup (Plancherel.rationalCommonNormKernel G),
      ∃ L : OpenSubgroup (Plancherel.rationalCommonNormKernel G),
        IsCompact (L : Set (Plancherel.rationalCommonNormKernel G)) ∧ L ≤ K := by
  intro K
  exact compactOpenSubgroupBasis (Plancherel.rationalCommonNormKernel G)
    (K : Set (Plancherel.rationalCommonNormKernel G)) (K.isOpen.mem_nhds K.one_mem)

/-- The range has compact coefficients on its actual norm-kernel restriction,
including every smooth functional of that restricted action. -/
theorem rationalNormKernelCompactProjector_range_compact
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    SmoothRep.compactRestrictionProperty (Plancherel.rationalCommonNormKernel G)
      (SmoothRep.subrepresentation A
        (rationalNormKernelCompactProjector G hstrata A).range) := by
  change HasCompactSmoothDualCoefficients
    (SmoothRep.restrictSubrepresentation (Plancherel.rationalCommonNormKernel G)
      (rationalNormKernelCompactProjector G hstrata A).range).toRepresentation
  rw [rationalNormKernelCompactProjector_range]
  exact CompactCoefficientClass.totalIsotypicSubrepresentation_hasCompactSmoothDualCoefficients
    (kernel_compactOpen_cofinal G) _

variable [T2Space (GroupScheme.rationalPoints G)]

/-- Compact restriction forces the norm-kernel compact projector to act as
the identity. All exhaustion, topology and Haar hypotheses are discharged. -/
theorem rationalNormKernelCompactProjector_eq_self_of_compactRestriction
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (hA : SmoothRep.compactRestrictionProperty (Plancherel.rationalCommonNormKernel G) A)
    (v : A) :
    rationalNormKernelCompactProjector G hstrata A v = v := by
  let : TotallyDisconnectedSpace F := BruhatTits.localField_totallyDisconnectedSpace F
  let : TotallyDisconnectedSpace (GroupScheme.rationalPoints G) :=
    BruhatTits.rationalPoint_totallyDisconnectedSpace F G
  let : MeasurableSpace (Plancherel.rationalCommonNormKernel G) :=
    borel (Plancherel.rationalCommonNormKernel G)
  let : BorelSpace (Plancherel.rationalCommonNormKernel G) := ⟨rfl⟩
  exact CompactCoefficientClass.normalSubgroupProjector_eq_self
    (Plancherel.rationalCommonNormKernel G) _ hstrata
    (fun D hD => CompactCoefficientClass.totalIsotypicSubrepresentation_eq_top_of_compactCoefficients
      (MeasureTheory.Measure.haar (G := Plancherel.rationalCommonNormKernel G)) D hD) A hA v

omit [T2Space (GroupScheme.rationalPoints G)] in
private theorem projector_zero_on_subquotient
    {A D : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)}
    (hA : ∀ v : A, rationalNormKernelCompactProjector G hstrata A v = 0)
    (hDA : SmoothRep.IsSubquotient D A) :
    ∀ v : D, rationalNormKernelCompactProjector G hstrata D v = 0 := by
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
  have hC : ∀ v : C, rationalNormKernelCompactProjector G hstrata C v = 0 := by
    intro v
    apply hi
    rw [← rationalNormKernelCompactProjector_natural G hstrata C A (SmoothRep.hom i) v,
      hA, map_zero]
  intro v
  obtain ⟨w, rfl⟩ := hq v
  rw [rationalNormKernelCompactProjector_natural G hstrata C D (SmoothRep.hom q),
    hC, map_zero]

/-- The concrete kernel and range belong to the exact all/no arbitrary-
subquotient compact-restriction factors. -/
theorem rationalNormKernelCompactComponents_mem
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) (b : Bool) :
    SmoothRep.compactRestrictionSubquotientProperties
      (Plancherel.rationalCommonNormKernel G) b
      (rationalNormKernelCompactComponents G hstrata A b) := by
  cases b
  · intro D hD hDA hcompact
    have hker : ∀ v : rationalNormKernelCompactComponents G hstrata A false,
        rationalNormKernelCompactProjector G hstrata
          (rationalNormKernelCompactComponents G hstrata A false) v = 0 := by
      change ∀ v : SmoothRep.subrepresentation A
          (rationalNormKernelCompactProjector G hstrata A).ker,
        rationalNormKernelCompactProjector G hstrata
          (SmoothRep.subrepresentation A
            (rationalNormKernelCompactProjector G hstrata A).ker) v = 0
      intro v
      apply SmoothRep.subtype_injective A
        (rationalNormKernelCompactProjector G hstrata A).ker
      rw [← rationalNormKernelCompactProjector_natural G hstrata _ A
        (SmoothRep.hom (SmoothRep.subtype A
          (rationalNormKernelCompactProjector G hstrata A).ker)), map_zero]
      exact v.property
    have hzero := projector_zero_on_subquotient G hstrata hker hDA
    have hz : ∀ v : D, v = 0 := fun v =>
      (rationalNormKernelCompactProjector_eq_self_of_compactRestriction
        G hstrata D hcompact v).symm.trans (hzero v)
    exact (not_nontrivial_iff_subsingleton.mpr
      ⟨fun x y => (hz x).trans (hz y).symm⟩) hD
  · intro D hDA
    exact SmoothRep.compactRestrictionProperty_of_isSubquotient _
      (kernel_compactOpen_cofinal G)
      (rationalNormKernelCompactProjector_range_compact G hstrata A) hDA

section FactorComparison

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (h : ∀ I, IsSemidirectDecomposition
    (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G)))

omit [LocallyOfFiniteType G.X.hom] [T2Space (GroupScheme.rationalPoints G)] in
/-- Both directions of the objectwise comparison identify the actual all/no
arbitrary-subquotient factors without changing any objects or morphisms. -/
theorem rationalWholeCuspidalDecompositionProperties_eq_compactRestriction
    (hcompare : ∀ A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
      SmoothRep.compactRestrictionProperty (Plancherel.rationalCommonNormKernel G) A ↔
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A) :
    rationalWholeCuspidalDecompositionProperties.{uF, uV} G i ν h hU =
      SmoothRep.compactRestrictionSubquotientProperties.{uF, uV}
        (Plancherel.rationalCommonNormKernel G) := by
  funext b A
  apply propext
  cases b
  · constructor
    · intro hA D hD hDA hc
      exact hA D hD hDA ((hcompare D).mp hc)
    · intro hA D hD hDA hc
      exact hA D hD hDA ((hcompare D).mpr hc)
  · constructor
    · intro hA D hDA
      exact (hcompare D).mpr (hA D hDA)
    · intro hA D hDA
      exact (hcompare D).mp (hA D hDA)

/-- The literal projector components are whole-cuspidal components once
the full objectwise comparison is proved. -/
theorem rationalNormKernelCompactComponents_mem_cuspidal
    (hcompare : ∀ A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
      SmoothRep.compactRestrictionProperty (Plancherel.rationalCommonNormKernel G) A ↔
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A)
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) (b : Bool) :
    rationalWholeCuspidalDecompositionProperties.{uF, uV} G i ν h hU b
      (rationalNormKernelCompactComponents G hstrata A b) := by
  rw [rationalWholeCuspidalDecompositionProperties_eq_compactRestriction
    G i ν h hU hcompare]
  exact rationalNormKernelCompactComponents_mem G hstrata A b

include hstrata in
/-- Fixed-level finiteness and the full objectwise comparison supply the
unchanged actual whole-cuspidal category decomposition. -/
theorem rationalWholeCuspidalCategoryDecomposition_of_fixedStrata_of_comparison
    (hcompare : ∀ A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
      SmoothRep.compactRestrictionProperty (Plancherel.rationalCommonNormKernel G) A ↔
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A) :
    IsRationalWholeCuspidalCategoryDecomposition.{uF, uV} G i ν h hU := by
  refine ⟨?_, rationalWholeCuspidalDecompositionProperties_offDiagonalHomsZero
    G i ν h hU⟩
  intro A
  exact ⟨rationalNormKernelCompactComponents G hstrata A,
    (rationalNormKernelCompactCofan G hstrata A).inj,
    rationalNormKernelCompactComponents_mem_cuspidal G hstrata i ν h hU hcompare A,
    ⟨rationalNormKernelCompactCofanIsColimit G hstrata A⟩⟩

end FactorComparison

end Langlands.CuspidalSupport
