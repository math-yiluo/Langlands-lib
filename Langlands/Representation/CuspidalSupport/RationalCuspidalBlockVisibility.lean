import Langlands.Representation.Aubert.General.InductionFiniteSupport
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Aubert.General.CharacterTwistEquivalences
import Langlands.Representation.Aubert.General.CuspidalityTransport
import Langlands.Representation.CuspidalSupport.RationalCuspidalCategory
import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaFinitenessStatement

/-! # Compact visibility of actual cuspidal inertia blocks

Proper-standard cuspidality is invariant under actual rational unramified
twists. Compact-level inertia finiteness therefore controls arbitrary objects
in the quotient-class blocks, without finite length or admissibility.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

universe uG uV uI

/-- A smooth character trivial on all the tested radicals preserves the
actual family cuspidality predicate. -/
theorem isCuspidalFor_characterTwist_iff
    {G : Type uG} [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [NonarchimedeanGroup G] {κ : Type uI}
    (P M U : κ → Subgroup G)
    (h : ∀ j, IsSemidirectDecomposition (P j) (M j) (U j))
    (hU : ∀ j, IsClosed (U j : Set G))
    (χ : Induction.SmoothCharacter ℂ G)
    (hχ : ∀ j, U j ≤ χ.toMonoidHom.ker)
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    IsCuspidalFor P M U h hU (A.twist χ.toMonoidHom χ.isOpen_ker) ↔
      IsCuspidalFor P M U h hU A := by
  constructor
  · intro hc j
    exact (normalizedJacquetCharacterTwistEquiv (U j) (M j) (hU j)
      (h j).levi_le_normalizer χ (hχ j) A).toEquiv.subsingleton_congr.mp (hc j)
  · intro hc j
    exact (normalizedJacquetCharacterTwistEquiv (U j) (M j) (hU j)
      (h j).levi_le_normalizer χ (hχ j) A).toEquiv.subsingleton_congr.mpr (hc j)

end Langlands.Aubert.General

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- A subgroup exhausted by compact subgroups lies in the actual common
rational-character norm kernel. -/
theorem limitOfCompactSubgroups_le_rationalCommonNormKernel
    (U : Subgroup (GroupScheme.rationalPoints G))
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    U ≤ Plancherel.rationalCommonNormKernel G := by
  intro x hx
  obtain ⟨C, hCc, hC⟩ := hU {⟨x, hx⟩} isCompact_singleton
  have hxC : (⟨x, hx⟩ : U) ∈ C := hC (Set.mem_singleton _)
  have hc : IsCompact (C.map U.subtype : Set (GroupScheme.rationalPoints G)) := by
    rw [Subgroup.coe_map]
    exact hCc.image continuous_subtype_val
  exact Plancherel.compactSubgroup_le_rationalCommonNormKernel G _ hc ⟨_, hxC, rfl⟩

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{uF})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hStandard hG hi hν

/-- The actual standard radicals lie in the common rational norm kernel. -/
theorem standardUnipotent_le_rationalCommonNormKernel
    (I : Finset (SimpleRoot i ν)) :
    unipotent i ν I ≤ Plancherel.rationalCommonNormKernel G :=
  limitOfCompactSubgroups_le_rationalCommonNormKernel G _
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν I)

variable [LocallyOfFiniteType G.X.hom]
  [LocallyCompactSpace (GroupScheme.rationalPoints G)]
  [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
  [Fintype (SimpleRoot i ν)]
  (h : ∀ I, IsSemidirectDecomposition
    (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G)))

/-- The exact proper-standard cuspidality predicate is invariant under an
actual full rational unramified twist. -/
theorem isCuspidal_rationalUnramifiedTwist_iff
    (χ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters G c).toMul))
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU
        (rationalUnramifiedTwist G χ A) ↔
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A := by
  let ψ : Induction.SmoothCharacter ℂ (GroupScheme.rationalPoints G) :=
    ⟨χ.val.toMonoidHom, isOpen_rationalUnramifiedCharacter_ker G χ⟩
  exact isCuspidalFor_characterTwist_iff _ _ _ _ _ ψ
    (fun I x hx => χ.property
      (standardUnipotent_le_rationalCommonNormKernel
        G i ν hStandard hG hi hν I.val hx)) A

/-- Inertia-related actual smooth objects have the same proper-standard
cuspidality. Irreducibility is not required for this comparison. -/
theorem isCuspidal_iff_of_rationalInertiaRelated
    {A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)}
    (hAB : IsRationalInertiaRelated G A B) :
    IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A ↔
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU B := by
  obtain ⟨χ, ⟨e⟩⟩ := hAB
  constructor
  · intro hc
    exact IsCuspidalFor.of_iso
      ((isCuspidal_rationalUnramifiedTwist_iff
        G i ν hStandard hG hi hν h hU χ A).mpr hc) e
  · intro hc
    exact (isCuspidal_rationalUnramifiedTwist_iff
      G i ν hStandard hG hi hν h hU χ A).mp (IsCuspidalFor.of_iso hc e.symm)

/-- Every irreducible object with a cuspidal inertia class is cuspidal. -/
theorem isCuspidal_of_rationalCuspidalInertiaClass_eq
    (c : RationalCuspidalInertiaClass.{uF, uV} G i ν h hU)
    (D : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (hD : D.IsIrreducible)
    (hDc : rationalIrreducibleInertiaClass G D hD = c.val) :
    IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU D := by
  obtain ⟨π, hπ, hc, hπc⟩ := c.property
  exact (isCuspidal_iff_of_rationalInertiaRelated G i ν hStandard hG hi hν h hU
    ((rationalIrreducibleInertiaClass_eq_iff G π D hπ hD).mp
      (hπc.trans hDc.symm))).mp hc

omit hStandard hG hi hν in
/-- The full category of arbitrary objects with a specified actual cuspidal
inertia class for every irreducible actual subquotient. -/
abbrev RationalCuspidalInertiaClassBlock
    (c : RationalCuspidalInertiaClass.{uF, uV} G i ν h hU) :=
  (rationalCuspidalInertiaClassBlockProperty G i ν h hU c).FullSubcategory

/-- Compact-level inertia finiteness implies compact-level fixed-vector
support finiteness for arbitrary objects of the actual cuspidal class blocks. -/
theorem compactFiniteFixedVectorSupport_rationalCuspidalBlocks
    (hfinite : ∀ K : OpenSubgroup (GroupScheme.rationalPoints G),
      IsCompact (K : Set (GroupScheme.rationalPoints G)) →
      Set.Finite {c : RationalIrreducibleInertiaClass.{uF, uV} G |
        ∃ (D : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
          (hD : D.IsIrreducible),
          IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU D ∧
          rationalIrreducibleInertiaClass G D hD = c ∧
          Nontrivial (fixedVectors D.representation K.toSubgroup)})
    (A : ∀ c, RationalCuspidalInertiaClassBlock.{uF, uV} G i ν h hU c) :
    SmoothRep.CompactFiniteFixedVectorSupport (fun c => (A c).obj) := by
  intro K hK
  have hf := Set.Finite.preimage
    (f := fun c : RationalCuspidalInertiaClass.{uF, uV} G i ν h hU => c.val)
    Subtype.val_injective.injOn (hfinite K hK)
  apply hf.subset
  intro c hc
  obtain ⟨D, hD, hDA, hfix⟩ :=
    SmoothRep.hasFixedVectorConstituent_of_nontrivial (A c).obj K.toSubgroup hc
  have hDc := (A c).property D hD hDA
  exact ⟨D, hD, isCuspidal_of_rationalCuspidalInertiaClass_eq
    G i ν hStandard hG hi hν h hU c D hD hDc, hDc, hfix⟩

end Langlands.CuspidalSupport
