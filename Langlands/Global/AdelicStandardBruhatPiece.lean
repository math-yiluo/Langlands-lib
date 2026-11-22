import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicEisensteinGeometricLemmaProof
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicStandardNestedLeviParabolic
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyReduction

/-! # Geometric Bruhat pieces for a supplied standard parabolic family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Root" => SimpleRoot fam.i fam.ν

/-- Regard a finite family of simple relative roots as a standard index. -/
def indexOfSimpleRoots (S : Finset Root) : Idx :=
  ⟨rootSet fam.i fam.ν S, rootSet_subset fam.i fam.ν S⟩

omit [NumberField F] in
@[simp] theorem indexOfSimpleRoots_le (S T : Finset Root) :
    fam.indexOfSimpleRoots S ≤ fam.indexOfSimpleRoots T ↔ S ⊆ T :=
  rootSet_subset_iff fam.i fam.ν S T

/-- Every supplied standard index can be indexed by a finite set of
the actual simple relative roots. -/
def simpleRootsOfIndex (J : Idx) : Finset Root := by
  classical
  let : Fintype Root := (fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν).fintype
  exact Finset.univ.filter (fun a => a.val ∈ J.val)

omit [NumberField F] in
@[simp] theorem indexOfSimpleRoots_simpleRootsOfIndex (J : Idx) :
    fam.indexOfSimpleRoots (fam.simpleRootsOfIndex J) = J := by
  classical
  let : Fintype Root := (fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν).fintype
  apply Subtype.ext
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Finset.mem_filter.mp ha).2
  · intro hx
    exact ⟨⟨x, J.2 hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

/-- The smaller parabolics and Levi conjugation for one Bruhat piece,
using the schemes already specified by the supplied standard family. -/
structure StandardBruhatPiece (fam : StandardParabolicFamily F G)
    (I J I₁ J₁ : StandardIndex F G fam.i fam.ν) (n : normalizerPoints fam.i) where
  source : NestedLeviParabolic fam I₁ I
  target : NestedLeviParabolic fam J₁ J
  conjugation : fam.M J₁ ⟶ fam.M I₁
  geometry : IsGeometricLemmaDatum (fam.p I) (fam.iU I) (fam.p J) (fam.iU J)
    source.inclusion target.inclusion n.val
  weylLevi : IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J₁) (fam.l J₁) n.val conjugation
  iwasawa : ∀ K : Subgroup (AdelicGroupPoints F G),
    IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K →
      IsIwasawaCompact (source.inclusion ≫ fam.p I) K ∧
      IsIwasawaCompact (target.inclusion ≫ fam.p J) K

variable (n : normalizerPoints fam.i)
  {CM : CoxeterMatrix (SimpleRoot fam.i fam.ν)}
  (cs : CoxeterSystem CM (relativeWeylGroup fam.i))

local notation "w" => (QuotientGroup.mk (s := Subgroup.subgroupOf (centralizerPoints fam.i)
  (normalizerPoints fam.i)) n)
local notation "L(" J ")" => (fam.l J ≫ fam.p J)
local notation "Pₛ(" T ")" => Standard.parabolicHom fam.i fam.ν (rootSet fam.i fam.ν T)
local notation "Uₛ(" T ")" => Standard.unipotentToParabolic fam.i fam.ν (rootSet fam.i fam.ν T)
local notation "Mₛ(" T ")" => Standard.leviToParabolic fam.i fam.ν (rootSet fam.i fam.ν T)

set_option maxHeartbeats 3000000 in
/-- At a minimal Weyl representative the canonical intersection indices
give geometric data for the actual supplied standard family. -/
def StandardBruhatPieceStatement (P Q : Finset Root) : Prop :=
  IsRelativeWeylCoxeterRealization fam.i fam.ν cs →
  IsMinimal cs Q P w →
    Nonempty (StandardBruhatPiece fam (fam.indexOfSimpleRoots P) (fam.indexOfSimpleRoots Q)
      (fam.indexOfSimpleRoots (intersectionSubset cs Q P w))
      (fam.indexOfSimpleRoots (intersectionSubset cs P Q w⁻¹)) n)

set_option maxHeartbeats 2400000 in
theorem standardBruhatPiece (P Q : Finset Root) : StandardBruhatPieceStatement fam n cs P Q := by
  intro hcs hmin
  let P₁ := intersectionSubset cs Q P w
  let Q₁ := intersectionSubset cs P Q w⁻¹
  let I  := fam.indexOfSimpleRoots P
  let J  := fam.indexOfSimpleRoots Q
  let I₁ := fam.indexOfSimpleRoots P₁
  let J₁ := fam.indexOfSimpleRoots Q₁
  obtain ⟨s⟩ := standardNestedLeviParabolic fam I₁ I
    ((fam.indexOfSimpleRoots_le P₁ P).mpr (intersectionSubset_subset cs Q P w))
  obtain ⟨t⟩ := standardNestedLeviParabolic fam J₁ J
    ((fam.indexOfSimpleRoots_le Q₁ Q).mpr (intersectionSubset_subset cs P Q w⁻¹))
  obtain ⟨f, g', hf, hg, hgeom, hK, c, hc⟩ := eisensteinGeometricLemmaDatum_of_minimal
    F G fam.connectedReductive fam.T fam.i fam.maximalSplit fam.ν fam.generic cs hcs P Q n hmin
  have hP (A : Finset Root) : SubgroupFunctor.range (fam.p (fam.indexOfSimpleRoots A)) =
      SubgroupFunctor.range (Pₛ(A)) :=
    (fam.isCompatible _).parabolic_eq.trans (Standard.isRepresentedBy_parabolicHom _ _ _).2.symm
  have hU (A : Finset Root) : SubgroupFunctor.range (fam.iU (fam.indexOfSimpleRoots A) ≫
        fam.p (fam.indexOfSimpleRoots A)) = SubgroupFunctor.range (Uₛ(A) ≫ Pₛ(A)) := by
    rw [fam.range_radical_eq_standardUnipotent, Standard.unipotentToParabolic_comp]
    exact (Standard.isRepresentedBy_unipotentHom _ _ _).2.symm
  have hM (A : Finset Root) : SubgroupFunctor.range (L((fam.indexOfSimpleRoots A))) =
      SubgroupFunctor.range (Mₛ(A) ≫ Pₛ(A)) := by
    rw [Standard.leviToParabolic_comp]
    exact (fam.isCompatible _).levi_eq.trans (Standard.isRepresentedBy_leviHom _ _ _).2.symm
  have hPL : SubgroupFunctor.range (L(I₁)) =
      (SubgroupFunctor.range (L(J₁))).comap (G.innerIso n.val).hom := by
    let : IsIso c := hc.isIso
    rw [hM P₁, hM Q₁]
    exact SubgroupFunctor.range_eq_comap_of_iso_square (G.innerIso n.val) (asIso c).symm
      (by
        rw [Iso.symm_hom, Iso.eq_inv_comp]
        simpa only [asIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
          congrArg (fun x => x ≫ (G.innerIso n.val).hom) hc.comp_eq)
  let hRepI : (SubgroupFunctor.range (L(I₁))).IsRepresentedBy (L(I₁)) :=
    ⟨((fam.isCompatible I₁).levi.isClosedSubgroup.comp
      (fam.isCompatible I₁).parabolic.isClosedSubgroup).mono_overHom, rfl⟩
  let hRepJ : (SubgroupFunctor.range (L(J₁))).IsRepresentedBy (L(J₁)) :=
    ⟨((fam.isCompatible J₁).levi.isClosedSubgroup.comp
      (fam.isCompatible J₁).parabolic.isClosedSubgroup).mono_overHom, rfl⟩
  let e := hRepI.isoOfComap hRepJ (G.innerIso n.val) hPL.symm
  refine ⟨⟨s, t, e.inv, ?_, ⟨inferInstance, ?_⟩, ?_⟩⟩
  · have hPR (A : Finset Root) : rationalImage F (fam.p (fam.indexOfSimpleRoots A)) =
        rationalImage F (Pₛ(A)) := rationalImage_eq_of_range_eq _ _ (hP A)
    have hUR (A : Finset Root) : rationalImage F (fam.iU (fam.indexOfSimpleRoots A) ≫
          fam.p (fam.indexOfSimpleRoots A)) = rationalImage F (Uₛ(A) ≫ Pₛ(A)) :=
      rationalImage_eq_of_range_eq _ _ (hU A)
    constructor
    · rw [s.inclusion_comp, hPR P₁, hPR P, hPR Q, hUR P, ← hf]
      exact hgeom.rationalImage_left
    · rw [t.inclusion_comp, hPR Q₁, hPR Q, hPR P, hUR Q, ← hg]
      exact hgeom.rationalImage_right
  · exact hRepI.isoOfComap_inv_comp hRepJ (G.innerIso n.val) hPL.symm
  · intro K hKmin
    have hMin := hKmin.of_range_eq (hP ∅)
    rw [rootSet_empty] at hMin
    have h := hK K hMin
    rw [hf, hg] at h
    rw [s.inclusion_comp, t.inclusion_comp]
    exact ⟨h.1.of_range_eq (hP P₁).symm, h.2.of_range_eq (hP Q₁).symm⟩

end Langlands.Global.StandardParabolicFamily
