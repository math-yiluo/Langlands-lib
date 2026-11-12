import Langlands.Representation.CuspidalSupport.BernsteinSupportJacquetPresentation
import Langlands.Representation.Aubert.General.RationalLeviCuspidalEmbedding
import Langlands.Representation.Aubert.General.RationalLeviQuotientCompactness
import Langlands.Representation.Aubert.General.CuspidalityTransport

/-! # Simultaneous cuspidal presentations inside a standard Levi -/

noncomputable section

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

private theorem leviQuotientOfIso
    {H : Type*} [Group H] [TopologicalSpace H]
    {A B C : SmoothRep ℂ H} (q : SmoothRep.IsQuotient A B) (e : C ≅ A) :
    SmoothRep.IsQuotient C B := by
  obtain ⟨q, hq⟩ := q
  exact ⟨q ≫ e.inv, (SmoothRep.equivOfIso e.symm).surjective.comp hq⟩

private theorem leviEmbeddingOfIso
    {H : Type*} [Group H] [TopologicalSpace H]
    {A B C : SmoothRep ℂ H} (f : SmoothRep.IsSubrepresentation A B) (e : C ≅ B) :
    SmoothRep.IsSubrepresentation A C := by
  obtain ⟨f, hf⟩ := f
  exact ⟨f ≫ e.inv, (SmoothRep.equivOfIso e.symm).injective.comp hf⟩

private theorem leviInductionEmbeddingOfIso
    {H M : Type*} [Group H] [TopologicalSpace H] [Group M] [TopologicalSpace M]
    (ind : SmoothRep ℂ M ⥤ SmoothRep ℂ H)
    {A : SmoothRep ℂ H} {B C : SmoothRep ℂ M}
    (f : SmoothRep.IsSubrepresentation A (ind.obj B)) (e : C ≅ B) :
    SmoothRep.IsSubrepresentation A (ind.obj C) :=
  leviEmbeddingOfIso f (ind.mapIso e)

private def choosePresentationPair {A B : Type*} (P : A → B → Prop)
    (h : ∃ a b, P a b) : { p : A × B // P p.1 p.2 } := by
  apply Classical.indefiniteDescription
  obtain ⟨a, b, hab⟩ := h
  exact ⟨⟨a, b⟩, hab⟩

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance leviSupportAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance leviSupportAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance leviSupportClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance leviSupportAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance leviSupportTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- A single datum supplies both literal inner-Levi presentations. -/
def bernsteinLeviCuspidalPresentationProperty
    (J : Finset (SimpleRoot i ν))
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J))
    (I : Finset J) (b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) : Prop :=
  ∃ h : leviIndex J I = b.roots,
    SmoothRep.IsQuotient (bernsteinLiteralLeviRep i ν b.roots b.representation)
        ((leviNormalizedJacquetFunctor (family.closedLevi J)
          (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
            family.maximalSplitTorus family.genericCocharacter b.roots J
            (h ▸ leviIndex_subset J I))
          (h ▸ family.leviDecomposition J I) (family.closedUnipotent b.roots)).obj τ) ∧
      SmoothRep.IsSubrepresentation τ
        ((leviNormalizedInductionFunctor (family.closedLevi J)
          (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
            family.maximalSplitTorus family.genericCocharacter b.roots J
            (h ▸ leviIndex_subset J I))
          (h ▸ family.leviDecomposition J I) (family.closedUnipotent b.roots)).obj
          (bernsteinLiteralLeviRep i ν b.roots b.representation))

/-- Every irreducible of a standard Levi has one genuine Bernstein datum
inside that Levi providing both an induction embedding and a Jacquet quotient.
The carrier universe is unchanged. -/
theorem exists_bernsteinLeviCuspidalDatum_jacquet_quotient_induction_embedding
    (J : Finset (SimpleRoot i ν))
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)) (hτ : τ.IsIrreducible) :
    ∃ (I : Finset J) (b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family),
      bernsteinLeviCuspidalPresentationProperty i ν family J τ I b := by
  classical
  let := (family.closedLevi J).locallyCompactSpace
  obtain ⟨I, hI, hcusp⟩ := exists_nonzero_cuspidal_leviJacquet
    i ν standardLeviIntersection family.connectedReductive family.maximalSplitTorus
    family.genericCocharacter standardCocharacter family.closedUnipotent family.closedLevi J τ hτ
  let h := family.leviDecomposition J I
  let hUK := (family.closedUnipotent (leviIndex J I)).preimage
    (continuous_subtype_val : Continuous (fun x : levi i ν J => (x : rationalPoints G)))
  let hAK := levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
    family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I)
  let e := subgroupOfContinuousEquiv hAK
  have : Nontrivial ((jacquetFunctor h hUK).obj τ) := hI
  let := compactSpace_leftQuotient_in_levi_of_dynamic i ν standardLeviIntersection
    family.connectedReductive family.maximalSplitTorus family.genericCocharacter
    standardCocharacter BruhatTits.dynamicParabolicQuotientCompact J I
  obtain ⟨σ, hσ, q, hq, hemb⟩ := CuspidalEmbedding.exists_irreducible_quotient_embedding
    h hUK (isUnimodularModulus_standardUnipotent_in_levi
      i ν family.connectedReductive family.maximalSplitTorus family.genericCocharacter
      standardCocharacter family.closedUnipotent family.closedLevi J I) e τ hτ
  have hσc := hcusp.of_surjective q hq
  let eS := leviRationalPointHomeomorph i ν (leviIndex J I)
  let D := SmoothRep.pullback eS σ
  have hD : D.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff σ.representation eS).mpr hσ
  let cancel : bernsteinLiteralLeviRep i ν (leviIndex J I) D ≅ σ :=
    SmoothRep.mkIso (equivOfRepresentationEq (by
      ext x v
      change σ.representation (eS (eS.symm x)) v = σ.representation x v
      rw [eS.apply_symm_apply]))
  have hDc : Langlands.Aubert.General.IsLeviCuspidal
      (parabolic i ν) (levi i ν) (unipotent i ν) family.closedUnipotent
      (leviIndex J I) (family.closedLevi (leviIndex J I))
      (family.leviDecomposition (leviIndex J I))
      (bernsteinLiteralLeviRep i ν (leviIndex J I) D) :=
    Langlands.Aubert.General.IsLeviCuspidal.of_iso family.closedUnipotent
      (family.closedLevi (leviIndex J I)) (family.leviDecomposition (leviIndex J I)) hσc cancel
  let b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family :=
    ⟨leviIndex J I, D, hD, hDc⟩
  refine ⟨I, b, rfl, ?_, ?_⟩
  · exact leviQuotientOfIso ⟨q, hq⟩ cancel
  · exact leviInductionEmbeddingOfIso
      (leviNormalizedInductionFunctor (family.closedLevi J) hAK h
        (family.closedUnipotent (leviIndex J I))) hemb cancel

/-- Choose the subset and the genuine datum simultaneously, retaining the
Jacquet quotient and the induction embedding in the subtype property. -/
def bernsteinLeviCuspidalJacquetPresentation
    (J : Finset (SimpleRoot i ν))
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)) (hτ : τ.IsIrreducible) :
    { p : Finset J × BernsteinCuspidalDatum.{uF, max uF uV} i ν family //
      bernsteinLeviCuspidalPresentationProperty i ν family J τ p.1 p.2 } :=
  choosePresentationPair (bernsteinLeviCuspidalPresentationProperty i ν family J τ)
    (exists_bernsteinLeviCuspidalDatum_jacquet_quotient_induction_embedding i ν family J τ hτ)

end Langlands.CuspidalSupport
