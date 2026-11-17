import Langlands.Representation.Jacquet.CoefficientScalarRestriction
import Langlands.Representation.Category.SubrepresentationSums

/-! # Irreducible constituents of a coefficient span -/

noncomputable section

open CategoryTheory
open Langlands.Jacquet.CoefficientRestriction

namespace Langlands.Renard.AlgebraicFamily

universe uG uV uB

/-- Internal coefficient-span constituent transfer, used for Renard VI.10.7. -/
def CoefficientSpanConstituentsStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (B : Type uB) [CommRing B] [Algebra ℂ B]
    (V : Type uV) [AddCommGroup V] [Module B V] [Module ℂ V]
    [IsScalarTower ℂ B V]
    (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (S : Subrepresentation (complexRepresentation ρ)),
    Submodule.span B (S : Set V) = ⊤ →
    ∀ D : SmoothRep.{0, uG, uV} ℂ G, D.IsIrreducible →
      SmoothRep.IsSubquotient D
        (SmoothRep.of (complexRepresentation ρ) ((isSmooth_complexRepresentation ρ).mpr hρ)) →
      SmoothRep.IsSubquotient D (SmoothRep.subrepresentation
        (SmoothRep.of (complexRepresentation ρ) ((isSmooth_complexRepresentation ρ).mpr hρ)) S)

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {B : Type uB} [CommRing B] [Algebra ℂ B]
  {V : Type uV} [AddCommGroup V] [Module B V] [Module ℂ V]
  [IsScalarTower ℂ B V]

/-- Multiplication by a coefficient, restricted to an actual complex subrepresentation. -/
def coefficientSubrepresentationMap (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (S : Subrepresentation (complexRepresentation ρ)) (b : B) :
    SmoothRep.subrepresentation
        (SmoothRep.of (complexRepresentation ρ) ((isSmooth_complexRepresentation ρ).mpr hρ)) S ⟶
      SmoothRep.of (complexRepresentation ρ) ((isSmooth_complexRepresentation ρ).mpr hρ) :=
  SmoothRep.ofHom {
    toLinearMap := {
      toFun := fun v => b • v.val
      map_add' := fun v w => smul_add b v.val w.val
      map_smul' := fun c v => smul_comm b c v.val }
    isIntertwining' g := by
      ext v
      exact ((ρ g).map_smul b v.val).symm }

/-- If an actual complex subrepresentation spans the ambient representation over the
coefficient ring, every irreducible subquotient of the ambient representation is a
subquotient of that complex subrepresentation. -/
theorem irreducibleSubquotient_of_coefficient_span
    (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (S : Subrepresentation (complexRepresentation ρ))
    (hspan : Submodule.span B (S : Set V) = ⊤)
    (D : SmoothRep.{0, uG, uV} ℂ G) (hD : D.IsIrreducible)
    (h : SmoothRep.IsSubquotient D
      (SmoothRep.of (complexRepresentation ρ) ((isSmooth_complexRepresentation ρ).mpr hρ))) :
    SmoothRep.IsSubquotient D (SmoothRep.subrepresentation
      (SmoothRep.of (complexRepresentation ρ) ((isSmooth_complexRepresentation ρ).mpr hρ)) S) := by
  let A := SmoothRep.of (complexRepresentation ρ) ((isSmooth_complexRepresentation ρ).mpr hρ)
  let f := coefficientSubrepresentationMap ρ hρ S
  let U : Subrepresentation A.representation := ⨆ b : B, (SmoothRep.hom (f b)).range
  have hU : U = ⊤ := by
    apply top_unique
    intro v hv
    have hv' : v ∈ Submodule.span B (S : Set V) := by
      rw [hspan]
      exact Submodule.mem_top
    have hmem : ∀ x ∈ Submodule.span B (S : Set V), ∀ b : B, b • x ∈ U := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          intro b
          exact (le_iSup (fun b : B => (SmoothRep.hom (f b)).range) b) ⟨⟨x, hx⟩, rfl⟩
      | zero =>
          intro b
          rw [smul_zero]
          exact U.toSubmodule.zero_mem
      | add x y hx hy ihx ihy =>
          intro b
          rw [smul_add]
          exact U.toSubmodule.add_mem (ihx b) (ihy b)
      | smul a x hx ih =>
          intro b
          rw [smul_smul]
          exact ih (b * a)
    simpa only [one_smul] using hmem v hv' 1
  have h' : SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A U) := by
    have hq : SmoothRep.IsQuotient A (SmoothRep.subrepresentation A U) := by
      refine ⟨SmoothRep.subtype A U, ?_⟩
      intro v
      exact ⟨⟨v, by rw [hU]; exact Submodule.mem_top⟩, rfl⟩
    exact Langlands.smoothSubquotientTransitivity ℂ G _ _ _ h hq.isSubquotient
  obtain ⟨b, hb⟩ := SmoothRep.irreducibleSubquotient_iSup hD
    (fun b : B => (SmoothRep.hom (f b)).range) h'
  let q : SmoothRep.subrepresentation A S ⟶
      SmoothRep.subrepresentation A (SmoothRep.hom (f b)).range :=
    SmoothRep.ofHom {
      toLinearMap := (SmoothRep.hom (f b)).toLinearMap.rangeRestrict
      isIntertwining' g := by
        ext v
        exact Subtype.ext
          (Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom (f b)) g v) }
  have hq : Function.Surjective (SmoothRep.hom q) := by
    intro v
    obtain ⟨w, hw⟩ := v.property
    exact ⟨w, Subtype.ext hw⟩
  exact Langlands.smoothSubquotientTransitivity ℂ G _ _ _ hb
    (SmoothRep.IsQuotient.isSubquotient ⟨q, hq⟩)

/-- The coefficient-span constituent transfer, with no Bernstein-theoretic inputs. -/
theorem coefficientSpanConstituents :
    CoefficientSpanConstituentsStatement.{uG, uV, uB} := by
  intro G _ _ B _ _ V _ _ _ _ ρ hρ S hspan D hD h
  exact irreducibleSubquotient_of_coefficient_span ρ hρ S hspan D hD h

end Langlands.Renard.AlgebraicFamily
