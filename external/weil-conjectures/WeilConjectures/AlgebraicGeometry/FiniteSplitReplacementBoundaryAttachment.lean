/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStage
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementAttachmentStructure

/-! Split simplicial attachment with a prescribed relative matching cover. -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Source: Stacks Project, Hypercoverings, 0DAV (split attachment) and 01GJ.

Let the new top object be the coproduct of N and the old nondegenerate objects
indexed by proper surjections [n+1] to [m], m at most n. On N, use b followed by
the projections of Q for every lower operator; on an old summand use its inclusion
and the old simplicial operator. To define a degeneracy from an old degree, use
its splitting cofan: concatenate the new surjection with the summand label. For
an arbitrary map into the top degree factor it as an epimorphism followed by a
monomorphism. Apply the prescribed proper face followed by the concatenated
surjection; a full-image self-map is the identity. Check composition after the
splitting coproduct injections. On old summands this is functoriality of A; on N
it is Q.naturality, together with uniqueness of epi--mono factorization. Thus
these formulas define the extended truncated simplicial object and its splitting.
Define its map to K on N by g and on old degenerate summands by A.f followed by
the corresponding degeneracy of K. The displayed compatibility gives naturality
on N; naturality of A.f gives it on the other summands. The new matching object
is Q.M, its projections are Q.π, and its universal property is Q.universal. Its
matching map restricts to b on N, so is surjective. The supplied finite coproduct
of N supplies the top finiteness property; all lower properties are retained.
Use the original objects, maps and matching witnesses in the old degrees, so
restriction is literally A (proof fields agree by proof irrelevance).
This theorem performs only the simplicial attachment: the matching object and
its finite covering lift into K are already supplied, and no hypercover
hypothesis on K is used.
(auxiliary; not a blueprint node) -/
theorem exists_replacement_stage_of_boundary_cover
    {X : Scheme.{u}} (K : SimplicialObject X.Etale)
    {n : ℕ} (A : FiniteSplitReplacementStage K n) (Q : ReplacementBoundary A.U)
    (N : X.Etale) (b : N ⟶ Q.M)
    (g : N ⟶ K.obj (op (SimplexCategory.mk (n + 1))))
    (hc : Surjective b.left)
    (hf : ∃ (k : ℕ) (V : Fin k → X.Etale) (ι : ∀ i, V i ⟶ N),
      Nonempty (IsColimit (Cofan.mk N ι)) ∧
        ∀ i, CompactSpace (V i).left ∧ QuasiSeparatedSpace (V i).left ∧
          LocallyOfFinitePresentation (V i).hom ∧ QuasiCompact (V i).hom ∧
            QuasiSeparated (V i).hom)
    (hcomp : ∀ (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
      b ≫ Q.π Δ θ ≫ A.f.app (op Δ) = g ≫ K.map θ.op) :
    ∃ B : FiniteSplitReplacementStage K (n + 1), B.restrict n (Nat.le_succ n) = A := by
  classical
  obtain ⟨U, hU, hr⟩ := SchemeSplitAttachment.exists_attached_split_structure
    A.U N Q b hc hf
  let B : FiniteSplitReplacementStage K (n + 1) :=
    ⟨U, eqToHom hU ≫ SchemeSplitAttachment.attachedRefinement A N Q b g hcomp⟩
  refine ⟨B, ?_⟩
  have stage_ext {A B : FiniteSplitReplacementStage K n} (h : A.U = B.U)
      (hf : A.f = eqToHom (congrArg TruncatedFiniteSplitEtaleHypercover.simplicial h) ≫
        B.f) : A = B := by
    cases A with
    | mk AU Af =>
      cases B with
      | mk BU Bf =>
        cases h
        simp only [eqToHom_refl, Category.id_comp] at hf
        cases hf
        rfl
  apply stage_ext hr
  change (SimplicialObject.Truncated.trunc X.Etale (n + 1) n).map
    (eqToHom hU ≫ SchemeSplitAttachment.attachedRefinement A N Q b g hcomp) = _
  rw [Functor.map_comp, eqToHom_map,
    SchemeSplitAttachment.attachedRefinement_restrict]
  simp only [eqToHom_trans_assoc]

end AlgebraicGeometry
