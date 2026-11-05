import Langlands.Representation.CuspidalSupport.RationalInertiaDecompositionStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitTwistStatement
import Langlands.Representation.Category.IdempotentDecomposition
import Langlands.Representation.CompactCoefficient.FiniteFamilyIrreducibleTest
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Langlands.Representation.CompactCoefficient.TotalCompactness
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The compact-restriction inertia decomposition from Renard VI.3.2(ii),(iii)

The published finite-restriction and twist-equivalence statements for the
actual common norm kernel imply the compact-restriction inertia decomposition.
The finite spanning family of the restriction of `π` selects a natural ambient
projector; its identity action on an irreducible object is exactly membership
in the inertia class of `π`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV uG uW uU

section OpenSubgroup

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G]

/-- In an open subgroup of a locally compact nonarchimedean group, compact
open subgroups are cofinal among open subgroups. -/
theorem openSubgroup_compactOpenCofinal (N : Subgroup G) (hN : IsOpen (N : Set G)) :
    ∀ K : OpenSubgroup N, ∃ L : OpenSubgroup N, IsCompact (L : Set N) ∧ L ≤ K := by
  intro K
  have hKopen : IsOpen ((Subtype.val : N → G) '' (K : Set N)) :=
    hN.isOpenMap_subtype_val _ K.isOpen
  obtain ⟨V, hVc, hVK⟩ := compactOpenSubgroupBasis G _
    (hKopen.mem_nhds ⟨1, K.one_mem, rfl⟩)
  have hVN : (V : Set G) ⊆ N := fun x hx => by
    obtain ⟨k, -, rfl⟩ := hVK hx
    exact k.property
  refine ⟨OpenSubgroup.comap N.subtype continuous_subtype_val V, ?_, ?_⟩
  · rw [Subtype.isCompact_iff]
    have himage : (Subtype.val : N → G) ''
        (OpenSubgroup.comap N.subtype continuous_subtype_val V : Set N) = V := by
      ext x
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact hn
      · intro hx
        exact ⟨⟨x, hVN hx⟩, hx, rfl⟩
    rw [himage]
    exact hVc
  · intro n hn
    obtain ⟨k, hk, hkn⟩ := hVK hn
    rwa [← Subtype.ext hkn]

/-- On an open subgroup of a locally compact nonarchimedean group, the intrinsic
isotypic and annihilator subrepresentations of every compact-coefficient class
are complementary in every smooth object. The Haar measure is chosen on the
subgroup. -/
theorem openSubgroup_isCompl_isotypic_annihilator (N : Subgroup G)
    (hN : IsOpen (N : Set G)) (c : CompactCoefficientClass.{uG, uV} N)
    (X : SmoothRep.{0, uG, uW} ℂ N) :
    IsCompl (CompactCoefficientClass.isotypicSubrepresentation c X).toSubmodule
      (CompactCoefficientClass.annihilatorSubrepresentation c X).toSubmodule := by
  have : LocallyCompactSpace N := hN.locallyCompactSpace
  let : MeasurableSpace N := borel N
  have : BorelSpace N := ⟨rfl⟩
  exact CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation
    (MeasureTheory.Measure.haar (G := N)) (openSubgroup_compactOpenCofinal N hN) c X

end OpenSubgroup

section OpenNormalFamily

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
  (π : SmoothRep.{0, uG, uV} ℂ G)
  (hc : HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N π).representation)
  {m : ℕ} (W : Fin m → Subrepresentation (π.representation.comp N.subtype))
  (hWirr : ∀ i, (W i).toRepresentation.IsIrreducible)
  (hWspan : (⨆ i, (W i).toSubmodule) = ⊤)

/-- A member of an irreducible family of subrepresentations of the restriction
of `π`, as an irreducible compact-coefficient object of `N`. Its coefficients
are compact because those of the restriction are. -/
def openNormalFamilyObject (i : Fin m) : IrreducibleCompactCoefficientRep.{uG, uV} N :=
  ⟨SmoothRep.of (W i).toRepresentation
      (CompactSplitting.isSmooth_subrepresentation
        (SmoothRep.restrictSubgroup N π).isSmooth (W i)),
    hWirr i, hasCompactSmoothDualCoefficients_subrepresentation
      (openSubgroup_compactOpenCofinal N hN) (SmoothRep.restrictSubgroup N π) hc (W i)⟩

/-- The inclusion of a family member into the restriction of `π`. -/
def openNormalFamilyInclusion (i : Fin m) :
    (openNormalFamilyObject N hN π hc W hWirr i).obj.representation.IntertwiningMap
      (SmoothRep.restrictSubgroup N π).representation where
  toLinearMap := (W i).toSubmodule.subtype
  isIntertwining' _ := rfl

omit [N.Normal] in
theorem openNormalFamilyInclusion_injective (i : Fin m) :
    Function.Injective (openNormalFamilyInclusion N hN π hc W hWirr i) :=
  fun _ _ h => Subtype.ext h

omit [N.Normal] in
include hWspan in
theorem openNormalFamilyInclusion_span :
    (⨆ i, (openNormalFamilyInclusion N hN π hc W hWirr i).range.toSubmodule) = ⊤ :=
  (iSup_congr fun i => Submodule.range_subtype (W i).toSubmodule).trans hWspan

/-- The natural ambient projector on smooth `G`-objects selected by a finite
irreducible family spanning the restriction of `π` to `N`. -/
def openNormalFamilyProjector (X : SmoothRep.{0, uG, uW} ℂ G) :
    X.representation.IntertwiningMap X.representation :=
  CompactCoefficientClass.finiteFamilyAmbientProjector N
    (openNormalFamilyObject N hN π hc W hWirr) π
    (openNormalFamilyInclusion N hN π hc W hWirr)
    (openNormalFamilyInclusion_injective N hN π hc W hWirr)
    (openNormalFamilyInclusion_span N hN π hc W hWirr hWspan)
    (fun c => openSubgroup_isCompl_isotypic_annihilator N hN c.val _) X
    (fun c => openSubgroup_isCompl_isotypic_annihilator N hN c.val _)

theorem openNormalFamilyProjector_idempotent (X : SmoothRep.{0, uG, uW} ℂ G) (v : X) :
    openNormalFamilyProjector N hN π hc W hWirr hWspan X
        (openNormalFamilyProjector N hN π hc W hWirr hWspan X v) =
      openNormalFamilyProjector N hN π hc W hWirr hWspan X v :=
  LinearMap.ext_iff.mp (CompactCoefficientClass.finiteFamilyAmbientProjector_idempotent
    N _ π _ _ _ _ X _) v

/-- Naturality for every ambient intertwiner, across carrier universes. -/
theorem openNormalFamilyProjector_natural {X : SmoothRep.{0, uG, uW} ℂ G}
    {Y : SmoothRep.{0, uG, uU} ℂ G} (q : X.representation.IntertwiningMap Y.representation)
    (v : X) :
    openNormalFamilyProjector N hN π hc W hWirr hWspan Y (q v) =
      q (openNormalFamilyProjector N hN π hc W hWirr hWspan X v) :=
  CompactCoefficientClass.finiteFamilyAmbientProjector_natural N _ π _ _ _ _ _ _ q v

/-- On an irreducible object, the projector is the identity exactly when the
restriction has a nonzero intertwiner to the restriction of `π`. -/
theorem openNormalFamilyProjector_fixes_iff (X : SmoothRep.{0, uG, uW} ℂ G)
    (hX : X.IsIrreducible) :
    (∀ v, openNormalFamilyProjector N hN π hc W hWirr hWspan X v = v) ↔
      ∃ q : (SmoothRep.restrictSubgroup N X).representation.IntertwiningMap
          (SmoothRep.restrictSubgroup N π).representation, q ≠ 0 :=
  CompactCoefficientClass.finiteFamilyAmbientProjector_fixes_iff_restricted_hom
    N _ π _ _ _ _ X hX _

include hN hc W hWirr hWspan in
/-- If nonzero restricted intertwiners into the restriction of `π` detect `P`
on irreducible objects, then the all/no irreducible-subquotient properties
of `P` decompose the category of smooth `G`-objects. -/
theorem openNormalFamily_categoryDecomposition
    (P : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G))
    (hP : ∀ D : SmoothRep.{0, uG, uV} ℂ G, D.IsIrreducible →
      ((∃ q : (SmoothRep.restrictSubgroup N D).representation.IntertwiningMap
          (SmoothRep.restrictSubgroup N π).representation, q ≠ 0) ↔ P D)) :
    Renard.IsCategoryDecomposition (SmoothRep.irreducibleSubquotientProperties P) :=
  SmoothRep.categoryDecomposition_of_natural_idempotent P
    (openNormalFamilyProjector N hN π hc W hWirr hWspan)
    (fun _ _ g v => openNormalFamilyProjector_natural N hN π hc W hWirr hWspan
      (SmoothRep.hom g) v)
    (openNormalFamilyProjector_idempotent N hN π hc W hWirr hWspan)
    (fun D hD => (openNormalFamilyProjector_fixes_iff N hN π hc W hWirr hWspan D hD).trans
      (hP D hD))

end OpenNormalFamily

/-- The compact-restriction inertia decomposition follows from the published
VI.3.2(ii) finite-restriction and VI.3.2(iii) twist-equivalence statements. -/
theorem rationalCompactRestrictionInertiaDecomposition_of_normKernel
    (hfin : RationalNormKernelFiniteRestrictionStatement.{uF, uV})
    (htw : RationalNormKernelTwistEquivalenceStatement.{uF, uV, uV}) :
    RationalCompactRestrictionInertiaDecompositionStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro _ _ _ π hπ hc
  let N := Plancherel.rationalCommonNormKernel G
  -- the finite spanning family of the restriction, from VI.3.2(ii)
  obtain ⟨-, -, m, W, hWirr, hWspan⟩ := hfin F G hG π hπ
  have hP : rationalInertiaDecompositionProperties G π =
      SmoothRep.irreducibleSubquotientProperties (IsRationalInertiaRelated G π) := by
    funext b
    cases b <;> rfl
  change Renard.IsCategoryDecomposition (rationalInertiaDecompositionProperties G π)
  rw [hP]
  refine openNormalFamily_categoryDecomposition N (Plancherel.isOpen_rationalCommonNormKernel G)
    π hc W hWirr hWspan _ fun D hD => ?_
  -- nonzero restricted intertwiners are unramified twists, by VI.3.2(iii)
  have h3 := htw F G hG D π hD hπ
  refine (h3.2.symm.trans h3.1).trans ⟨?_, ?_⟩
  · rintro ⟨χ, ⟨i⟩⟩
    exact IsRationalInertiaRelated.symm
      ⟨χ, ⟨(SmoothRep.mkIso (A := rationalUnramifiedTwist G χ D) (B := π) i).symm⟩⟩
  · intro h
    obtain ⟨χ, ⟨i⟩⟩ := h.symm
    exact ⟨χ, ⟨SmoothRep.equivOfIso i.symm⟩⟩

end Langlands.CuspidalSupport
