import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.DedekindDomain.Basic

/-! # The scheme reduced fibre theorem in Mathlib vocabulary -/

open AlgebraicGeometry CategoryTheory Limits Topology

noncomputable section

universe u v

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

/-- The canonical morphism from the coproduct of the spectra of the
residue fields of the generic points. -/
abbrev genericPointResidueMorphism (X : Scheme.{u}) :
    (∐ fun x : genericPoints X => Spec (X.residueField x.1)) ⟶ X :=
  Sigma.desc fun x => X.fromSpecResidueField x.1

private theorem finite_genericPoints_in_open (X : Scheme.{u}) (U : X.Opens)
    (hU : (irreducibleComponents U).Finite) :
    {x : genericPoints X | x.1 ∈ U}.Finite := by
  let i : U → X := Subtype.val
  have hi : IsOpenEmbedding i := U.2.isOpenEmbedding_subtypeVal
  have hmem (x : {x : genericPoints X // x.1 ∈ U}) :
      (⟨x.1.1, x.2⟩ : U) ∈ genericPoints U := by
    let y : U := ⟨x.1.1, x.2⟩
    have hy : i ⁻¹' ({i y} : Set X) = {y} := by
      ext z
      simp [hi.injective.eq_iff]
    change closure {y} ∈ irreducibleComponents U
    rw [← hy, ← hi.isOpenMap.preimage_closure_eq_closure_preimage hi.continuous]
    exact preimage_mem_irreducibleComponents x.1.2 hi
      ⟨i y, subset_closure (Set.mem_singleton _), ⟨y, rfl⟩⟩
  let : Finite (genericPoints U) := genericPoints.finite hU
  apply Set.finite_coe_iff.mp
  exact Finite.of_injective (fun x => (⟨⟨x.1.1, x.2⟩, hmem x⟩ : genericPoints U))
    fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : genericPoints U => t.1.1) h))

private theorem quasiCompact_genericPointResidueMorphism (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    QuasiCompact (genericPointResidueMorphism X) := by
  constructor
  intro U hU hc
  let F := fun x : genericPoints X => Spec (X.residueField x.1)
  let e := sigmaMk F
  apply e.isCompact_preimage.mp
  convert Set.isCompact_sigma (finite_genericPoints_in_open X ⟨U, hU⟩ (hX ⟨U, hU⟩ hc))
    (fun (x : genericPoints X) _ => (isCompact_univ : IsCompact (Set.univ : Set (F x)))) using 1
  ext p
  obtain ⟨x, p⟩ := p
  change genericPointResidueMorphism X (e ⟨x, p⟩) ∈ U ↔ x.1 ∈ U ∧ p ∈ Set.univ
  rw [show e ⟨x, p⟩ = Sigma.ι F x p from sigmaMk_mk _ _ _,
    ← Scheme.Hom.comp_apply]
  simp only [genericPointResidueMorphism, Sigma.ι_comp_desc, Set.mem_univ, and_true]
  change X.fromSpecResidueField x.1 (p : Spec (X.residueField x.1)) ∈ U ↔ x.1 ∈ U
  rw [X.fromSpecResidueField_apply]

private theorem quasiSeparated_genericPointResidueMorphism (X : Scheme.{u}) :
    QuasiSeparated (genericPointResidueMorphism X) := by
  let F := fun x : genericPoints X => Spec (X.residueField x.1)
  have : QuasiSeparatedSpace ↥(∐ F : Scheme.{u}) := by
    refine Scheme.quasiSeparatedSpace_of_isOpenCover
      (fun x => (Sigma.ι F x).opensRange) (sigmaOpenCover F).isOpenCover_opensRange
      (fun x => isAffineOpen_opensRange (Sigma.ι F x)) ?_
    intro x y
    rcases eq_or_ne x y with rfl | h
    · simpa using (isAffineOpen_opensRange (Sigma.ι F x)).isCompact
    · rw [← TopologicalSpace.Opens.coe_inf,
        disjoint_iff.mp (disjoint_opensRange_sigmaι F x y h)]
      exact isCompact_empty
  infer_instance

/-- The normalization in the generic-point residue fields, for a scheme
whose quasi-compact opens have finitely many irreducible components. -/
abbrev schemeNormalization (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Scheme.{u} :=
  letI := quasiCompact_genericPointResidueMorphism X hX
  letI := quasiSeparated_genericPointResidueMorphism X
  (genericPointResidueMorphism X).normalization

/-- The morphism from the normalization to the original scheme. -/
abbrev schemeNormalizationHom (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    schemeNormalization X hX ⟶ X :=
  letI := quasiCompact_genericPointResidueMorphism X hX
  letI := quasiSeparated_genericPointResidueMorphism X
  (genericPointResidueMorphism X).fromNormalization

/-- Stacks Project, Tag 09IL, with the Nagata and smooth-at-point
conditions written in Mathlib vocabulary. -/
def SchemeReducedFibreStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDedekindDomain A] (K : Type v) [Field K]
    [Algebra A K] [IsFractionRing A K],
    (IsNoetherianRing A ∧ ∀ (p : Ideal A) [p.IsPrime]
      (L : Type u) [Field L] [Algebra (FractionRing (A ⧸ p)) L] [Algebra (A ⧸ p) L]
      [IsScalarTower (A ⧸ p) (FractionRing (A ⧸ p)) L]
      [FiniteDimensional (FractionRing (A ⧸ p)) L],
      Module.Finite (A ⧸ p) (integralClosure (A ⧸ p) L)) →
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f],
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
        (_ : Algebra A L) (_ : IsScalarTower A K L),
      let g := Spec.algebraMap A (integralClosure A L)
      let W := pullback f g
      ∃ hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite,
        let h := schemeNormalizationHom W hW ≫ pullback.snd f g
        ∀ (b : Spec (.of ↥(integralClosure A L))) (y : h.fiber b),
          y ∈ genericPoints (h.fiber b) →
          ∃ U : (schemeNormalization W hW).Opens, h.fiberι b y ∈ U ∧
            Smooth (h.resLE ⊤ U le_top)

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
