import Langlands.Representation.Jacquet.CoefficientScalarRestriction
import Langlands.Representation.Smooth.FixedVectors.DetectionConsequencesProof
import Mathlib.CategoryTheory.Center.Basic

/-! # Finite generation of coefficient families from constituent detection -/

noncomputable section

open CategoryTheory
open Langlands.Jacquet.CoefficientRestriction

namespace Langlands.Renard.AlgebraicFamily

universe uG uV uB

/-- The generation step of Renard VI.10.7 for coefficient families, with an
explicit compact-open constituent detector. -/
def CoefficientFamilyGenerationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (B : Type uB) [CommRing B] [Algebra ℂ B]
    (V : Type uV) [AddCommGroup V] [Module B V] [Module ℂ V]
    [IsScalarTower ℂ B V]
    (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G), IsCompact (K : Set G) →
    let A := SmoothRep.of (complexRepresentation ρ)
      ((isSmooth_complexRepresentation ρ).mpr hρ)
    (∀ D : SmoothRep.{0, uG, uV} ℂ G, D.IsIrreducible →
      SmoothRep.IsSubquotient D A →
      ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0) →
    (∃ (n : ℕ) (s : Fin n → V),
      fixedVectors ρ K.toSubgroup ≤ Submodule.span B
        {y : V | ∃ (j : Fin n) (z : CatCenter (SmoothRep.{0, uG, uV} ℂ G)),
          y = SmoothRep.hom (z.app A) (s j)}) →
    Module.Finite (MonoidAlgebra B G) ρ.asModule

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A natural endomorphism of the identity preserves every actual
subrepresentation, by naturality along its inclusion. -/
theorem center_mem_subrepresentation
    (A : SmoothRep.{0, uG, uV} ℂ G) (S : Subrepresentation A.representation)
    (z : CatCenter (SmoothRep.{0, uG, uV} ℂ G)) {v : A} (hv : v ∈ S) :
    SmoothRep.hom (z.app A) v ∈ S := by
  let w : SmoothRep.subrepresentation A S := ⟨v, hv⟩
  have h := congrArg
    (fun f : SmoothRep.subrepresentation A S ⟶ A => SmoothRep.hom f w)
    (z.naturality (SmoothRep.subtype A S))
  change SmoothRep.hom (z.app A) v =
    (SmoothRep.hom (z.app (SmoothRep.subrepresentation A S)) w).val at h
  rw [h]
  exact (SmoothRep.hom (z.app (SmoothRep.subrepresentation A S)) w).property

variable [IsTopologicalGroup G]
  {B : Type uB} [CommRing B] [Algebra ℂ B]
  {V : Type uV} [AddCommGroup V] [Module B V] [Module ℂ V]
  [IsScalarTower ℂ B V]

/-- A finite family whose centre orbits span the fixed space over `B`
generates the full `B[G]`-module whenever `K` detects every irreducible
subquotient of the underlying complex representation. -/
theorem groupAlgebra_span_eq_top_of_center_span_and_detection
    (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hdet : ∀ D : SmoothRep.{0, uG, uV} ℂ G, D.IsIrreducible →
      SmoothRep.IsSubquotient D (SmoothRep.of (complexRepresentation ρ)
        ((isSmooth_complexRepresentation ρ).mpr hρ)) →
      ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0)
    {n : ℕ} (s : Fin n → V)
    (hspan : fixedVectors ρ K.toSubgroup ≤ Submodule.span B
      {y : V | ∃ (j : Fin n) (z : CatCenter (SmoothRep.{0, uG, uV} ℂ G)),
        y = SmoothRep.hom (z.app (SmoothRep.of (complexRepresentation ρ)
          ((isSmooth_complexRepresentation ρ).mpr hρ))) (s j)}) :
    Submodule.span (MonoidAlgebra B G)
      (Set.range fun j => ρ.asModuleEquiv.symm (s j)) = ⊤ := by
  let A := SmoothRep.of (complexRepresentation ρ)
    ((isSmooth_complexRepresentation ρ).mpr hρ)
  let N := Submodule.span (MonoidAlgebra B G)
    (Set.range fun j => ρ.asModuleEquiv.symm (s j))
  let S₀ := Subrepresentation.ofSubmodule' N
  let S : Subrepresentation A.representation :=
    { toSubmodule := S₀.toSubmodule.restrictScalars ℂ
      apply_mem_toSubmodule g v hv := S₀.apply_mem_toSubmodule g hv }
  have hs : ∀ j, s j ∈ S := by
    intro j
    change ρ.asModuleEquiv.symm (s j) ∈ N
    exact Submodule.subset_span (Set.mem_range_self j)
  have hcent : Submodule.span B
      {y : V | ∃ (j : Fin n) (z : CatCenter (SmoothRep.{0, uG, uV} ℂ G)),
        y = SmoothRep.hom (z.app A) (s j)} ≤ S₀.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro y ⟨j, z, rfl⟩
    exact center_mem_subrepresentation A S z (hs j)
  have hfixed : fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule :=
    fun _ hv => hcent (hspan hv)
  have hS : S = ⊤ :=
    SmoothRep.fixedVectors_generate_subquotients_of_detection A K hK
      (SmoothRep.fixedVector_of_irreducible_subquotient_detection A K hK hdet)
      A (SmoothRep.IsQuotient.isSubquotient ⟨𝟙 A, fun v => ⟨v, rfl⟩⟩) S hfixed
  apply top_unique
  intro v hv
  have hmem : (ρ.asModuleEquiv v) ∈ S := by
    rw [hS]
    exact Submodule.mem_top
  exact hmem

/-- The finite-generation consequence, with only the stated detection and
one fixed-space spanning hypothesis. -/
theorem coefficientFamilyGeneration :
    CoefficientFamilyGenerationStatement.{uG, uV, uB} := by
  intro G _ _ _ B _ _ V _ _ _ _ ρ hρ K hK A hdet hspan
  obtain ⟨n, s, hs⟩ := hspan
  apply Module.Finite.of_fg_top
  rw [← groupAlgebra_span_eq_top_of_center_span_and_detection ρ hρ K hK hdet s hs]
  exact Submodule.fg_span (Set.finite_range _)

end Langlands.Renard.AlgebraicFamily
