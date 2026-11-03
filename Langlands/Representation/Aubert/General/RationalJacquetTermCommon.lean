import Langlands.Representation.Aubert.General.RationalJacquetTermStages

/-! # Supported rational intersection terms reduce to the common term -/

noncomputable section

open Classical

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})

omit [Mono i.hom.hom.left] in
/-- The source subtype intersection is the inverse image of the target
intersection label. No minimum-representative hypothesis is needed here. -/
theorem intersectionSourceIndex_eq_common
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) :
    leviIndex I ((simpleImage cs w⁻¹ J ∩ I).subtype (· ∈ I)) =
      simpleImage cs w⁻¹ (simpleImage cs w I ∩ J) := by
  calc
    _ = simpleImage cs w⁻¹ J ∩ I :=
      Finset.subtype_map_of_mem fun _ ha => (Finset.mem_inter.mp ha).2
    _ = _ := by
      symm
      simpa only [inv_inv] using simpleImage_inv_inter cs w⁻¹ J I

include hLength hSimple hG hi hν hConj in
/-- The specified lift conjugates the actual fine Levis at the source
and target subtype intersection indices. -/
theorem intersectionJacquetConjugationMembership
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w) :
    ∀ x : RationalPoint k G.X,
      x ∈ levi i ν (leviIndex J ((simpleImage cs w I ∩ J).subtype (· ∈ J))) ↔
        (n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X) ∈
          levi i ν (leviIndex I ((simpleImage cs w⁻¹ J ∩ I).subtype (· ∈ I))) := by
  rw [intersectionSourceIndex_eq_common]
  exact commonJacquetConjugationMembership
    i ν hN hZ cs hLength hSimple hG hi hν hConj J w
    (simpleImage cs w I ∩ J) ⟨I, hw, rfl⟩ n hn

section Topology

variable [TopologicalSpace k]

local instance rationalTermCommonPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hInter : StandardLeviIntersectionStatement.{u})
  (hStandard : StandardCocharacterStatement.{u})
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hfl : ∀ A, ParabolicFiniteLength.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A) (hU A))
  (hLfl : ∀ J, letI := (hM J).locallyCompactSpace
    ∀ I : Finset J, ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val))

omit [Mono i.hom.hom.left] [Fintype (SimpleRoot i ν)] in
/-- Reindexing the actual source Levi reindexes the entire conjugated term.
Membership witnesses may be chosen independently on the two sides. -/
theorem standardConjugatedJacquetTerm_congr_source
    (J : Finset (SimpleRoot i ν)) (K : Finset J)
    (H H' : Finset (SimpleRoot i ν)) (hH : H = H')
    (g : RationalPoint k G.X)
    (hFine : ∀ x : RationalPoint k G.X,
      x ∈ levi i ν (leviIndex J K) ↔ g⁻¹ * x * g ∈ levi i ν H)
    (hFine' : ∀ x : RationalPoint k G.X,
      x ∈ levi i ν (leviIndex J K) ↔ g⁻¹ * x * g ∈ levi i ν H') :
    standardConjugatedJacquetTerm.{u, v}
        i ν hInter hG hi hν hStandard hU hM hfl hLfl J K H g hFine =
      standardConjugatedJacquetTerm.{u, v}
        i ν hInter hG hi hν hStandard hU hM hfl hLfl J K H' g hFine' := by
  subst H'
  rfl

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (hproj : ∀ A, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A).projection)
  (hLUc : ∀ (A : Finset (SimpleRoot i ν)) (B : Finset A),
    Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex A B)).subgroupOf (levi i ν A)))
  (J : Finset (SimpleRoot i ν))
  (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
  (hlift : ∀ w, QuotientGroup.mk (lift w) = w)

/-- The actual standard restricted term at the two intersection subtypes,
with fine-Levi conjugation derived from minimum-representative support. -/
def rationalIntersectionJacquetTerm
    (I : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w) :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν I) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) :=
  rationalRestrictedJacquetTerm.{u, v}
    i ν hInter hG hi hν hU hM hLfl J I
    ((simpleImage cs w⁻¹ J ∩ I).subtype (· ∈ I))
    ((simpleImage cs w I ∩ J).subtype (· ∈ J)) (lift w)
    (intersectionJacquetConjugationMembership
      i ν hN hZ cs hLength hSimple hG hi hν hConj I J w hw (lift w) (hlift w))

include hproj hLUc in
/-- For every minimum representative the literal restricted intersection
term, after ambient source Jacquet restriction, is the supported common
term. The right side retains no source coarse label. -/
theorem rationalRestrictedJacquetTerm_comp_ambient_eq_common
    (I : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (hFine : ∀ x : RationalPoint k G.X,
      x ∈ levi i ν (leviIndex J ((simpleImage cs w I ∩ J).subtype (· ∈ J))) ↔
        (lift w : RationalPoint k G.X)⁻¹ * x * (lift w : RationalPoint k G.X) ∈
          levi i ν (leviIndex I ((simpleImage cs w⁻¹ J ∩ I).subtype (· ∈ I)))) :
    (rationalRestrictedJacquetTerm.{u, v}
        i ν hInter hG hi hν hU hM hLfl J I
        ((simpleImage cs w⁻¹ J ∩ I).subtype (· ∈ I))
        ((simpleImage cs w I ∩ J).subtype (· ∈ J)) (lift w) hFine).comp
        (standardAmbientJacquetK0.{u, v}
          i ν hG hi hν hStandard hU hfl I) =
      rationalCommonJacquetTerm.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hConj
        hInter hStandard hU hM hfl hLfl J lift hlift w (simpleImage cs w I ∩ J) := by
  have hSupport : ∃ A, IsMinimal cs J A w ∧
      simpleImage cs w A ∩ J = simpleImage cs w I ∩ J := ⟨I, hw, rfl⟩
  have hFine' := commonJacquetConjugationMembership
    i ν hN hZ cs hLength hSimple hG hi hν hConj
    J w (simpleImage cs w I ∩ J) hSupport (lift w) (hlift w)
  rw [rationalRestrictedJacquetTerm_comp_ambient
    i ν hInter hG hi hν hStandard hU hM hfl hLfl
    J I _ _ (lift w) hFine hproj hLUc]
  trans standardConjugatedJacquetTerm.{u, v}
    i ν hInter hG hi hν hStandard hU hM hfl hLfl J
    ((simpleImage cs w I ∩ J).subtype (· ∈ J))
    (simpleImage cs w⁻¹ (simpleImage cs w I ∩ J)) (lift w) hFine'
  · exact standardConjugatedJacquetTerm_congr_source
      i ν hG hi hν hInter hStandard hU hM hfl hLfl
      J _ _ _ (intersectionSourceIndex_eq_common i ν cs I J w) (lift w) hFine hFine'
  · symm
    exact rationalCommonJacquetTerm_of_supported
      i ν hN hZ cs hLength hSimple hG hi hν hConj
      hInter hStandard hU hM hfl hLfl J lift hlift w _ hSupport hFine'

include hproj hLUc in
/-- The canonical standard intersection term also reduces to the common
term after ambient source Jacquet restriction. -/
theorem rationalIntersectionJacquetTerm_comp_ambient_eq_common
    (I : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w) :
    (rationalIntersectionJacquetTerm.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hConj
        hInter hU hM hLfl J lift hlift I w hw).comp
        (standardAmbientJacquetK0.{u, v}
          i ν hG hi hν hStandard hU hfl I) =
      rationalCommonJacquetTerm.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hConj
        hInter hStandard hU hM hfl hLfl J lift hlift w (simpleImage cs w I ∩ J) := by
  exact rationalRestrictedJacquetTerm_comp_ambient_eq_common
    i ν hN hZ cs hLength hSimple hG hi hν hConj
    hInter hStandard hU hM hfl hLfl hproj hLUc J lift hlift I w hw _

end Topology

end Langlands.Aubert.General.RationalPointFamily
