import Langlands.Galois.Local.SpectralDefinitions
import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalPoints
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeCoordinates
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Compatible algebraic extensions and descent of regular-function bounds -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ValuativeRel

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Every extension-field bound is dominated by the image of a nonzero base element. -/
def IsValuativelyCofinal (F K : Type u) [Field F] [Field K] [Algebra F K]
    [ValuativeRel F] [ValuativeRel K] : Prop :=
  ∀ c : K, ∃ b : F, b ≠ 0 ∧ c ≤ᵥ algebraMap F K b

/-- A compatible valuative relation on an algebraic extension, including the
cofinality certificate needed for descent of bounds. -/
structure CofinalValuativeExtension (F K : Type u) [Field F] [Field K]
    [Algebra F K] [ValuativeRel F] where
  relation : ValuativeRel K
  extension : letI := relation; ValuativeExtension F K
  cofinal : letI := relation; IsValuativelyCofinal F K

/-- The spectral valuation gives a compatible and cofinal valued extension of
an actual nonarchimedean local field. -/
def localFieldAlgebraicValuation (F K : Type u) [Field F] [Field K]
    [Algebra F K] [Algebra.IsAlgebraic F K] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    CofinalValuativeExtension F K := by
  let _ := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let _ : (Valued.v (R := F)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let _ : NontriviallyNormedField F :=
    Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  have : CompleteSpace F := inferInstance
  let w := LocalGalois.spectralValuation F K
  letI : ValuativeRel K := ValuativeRel.ofValuation w
  refine ⟨inferInstance, ⟨fun a b => ?_⟩, ?_⟩
  · change spectralNorm F K (algebraMap F K a) ≤
        spectralNorm F K (algebraMap F K b) ↔ a ≤ᵥ b
    rw [spectralNorm_extends, spectralNorm_extends,
      Valued.toNormedField.norm_le_iff]
    exact ((Valued.v (R := F)).vle_iff_le).symm
  · intro c
    obtain ⟨b, hb⟩ := NormedField.exists_lt_norm F (spectralNorm F K c)
    have hb0 : b ≠ 0 := by
      intro h
      rw [h, norm_zero] at hb
      exact (not_lt_of_ge (spectralNorm_nonneg c)) hb
    refine ⟨b, hb0, ?_⟩
    change spectralNorm F K c ≤ spectralNorm F K (algebraMap F K b)
    rw [spectralNorm_extends]
    exact hb.le

/-- In particular, the actual algebraic closure has a compatible cofinal valuation. -/
def localFieldAlgebraicClosureValuation (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    CofinalValuativeExtension F (AlgebraicClosure F) :=
  localFieldAlgebraicValuation F (AlgebraicClosure F)

section Points

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  (X : Over (Spec (CommRingCat.of F))) [IsAffine X.left]

/-- Evaluation of a pulled-back regular function at the actual scalar extension
of a rational point is the scalar extension of its original value. -/
theorem rationalPointAlgebraHom_geometricRationalPoint
    (p : RationalPoint F X) (a : AffineCoordinateRing F X) :
    rationalPointAlgebraHom K
      (ringBaseChange F K X)
      (geometricRationalPoint (K := K) X p)
      ((pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))).appTop.hom a) =
        algebraMap F K (rationalPointAlgebraHom F X p a) := by
  let Y := ringBaseChange F K X
  let q : RationalPoint K Y := geometricRationalPoint (K := K) X p
  let f := pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))
  have h : f.appTop ≫ Spec.preimage (q.left ≫ Y.left.isoSpec.hom) =
      Spec.preimage (p.left ≫ X.left.isoSpec.hom) ≫
        CommRingCat.ofHom (algebraMap F K) := by
    apply Spec.map_injective
    simp only [Spec.map_comp, Spec.map_preimage]
    calc
      _ = q.left ≫ (Y.left.isoSpec.hom ≫ Spec.map f.appTop) := Category.assoc _ _ _
      _ = q.left ≫ (f ≫ X.left.isoSpec.hom) :=
        congrArg (fun t => q.left ≫ t) (Scheme.isoSpec_hom_naturality f)
      _ = (q.left ≫ f) ≫ X.left.isoSpec.hom := (Category.assoc _ _ _).symm
      _ = _ := (congrArg (fun t => t ≫ X.left.isoSpec.hom)
        (geometricRationalPoint_fst X p)).trans (Category.assoc _ _ _)
  change (Spec.preimage (q.left ≫ Y.left.isoSpec.hom)).hom (f.appTop.hom a) =
    algebraMap F K ((Spec.preimage (p.left ≫ X.left.isoSpec.hom)).hom a)
  exact congrArg (fun g => g.hom a) h

variable [ValuativeRel F] [ValuativeRel K] [ValuativeExtension F K]

/-- Cofinality and compatibility reflect boundedness from actual scalar-extended
rational points to the original field. -/
theorem isAlgebraicallyBounded_of_geometricRationalPoint
    (hcofinal : IsValuativelyCofinal F K) (S : Set (RationalPoint F X))
    (hS : IsAlgebraicallyBounded K
      (ringBaseChange F K X)
      (geometricRationalPoint (K := K) X '' S)) :
    IsAlgebraicallyBounded F X S := by
  intro a
  obtain ⟨c, _, hc⟩ := hS
    ((pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))).appTop.hom a)
  obtain ⟨b, hb, hcb⟩ := hcofinal c
  refine ⟨b, hb, fun p hp => ?_⟩
  apply (ValuativeExtension.vle_iff_vle (A := F) (B := K) _ _).mp
  rw [← rationalPointAlgebraHom_geometricRationalPoint X p a]
  exact (hc _ ⟨p, hp, rfl⟩).trans hcb

end Points

/-- Descent over an algebraic extension of an actual local field has no
additional compatibility or cofinality hypotheses. -/
theorem isAlgebraicallyBounded_of_localFieldAlgebraicExtension
    {F K : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (X : Over (Spec (CommRingCat.of F))) [IsAffine X.left]
    (S : Set (RationalPoint F X))
    (hS : letI := (localFieldAlgebraicValuation F K).relation
      IsAlgebraicallyBounded K (ringBaseChange F K X)
        (geometricRationalPoint (K := K) X '' S)) :
    IsAlgebraicallyBounded F X S := by
  let e := localFieldAlgebraicValuation F K
  let := e.relation
  let := e.extension
  exact isAlgebraicallyBounded_of_geometricRationalPoint X e.cofinal S hS

end Langlands.AlgebraicGeometry.PointTopology
