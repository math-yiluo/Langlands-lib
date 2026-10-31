import Langlands.Representation.Geometric.InducedOppositeCuspidalPieceStatement
import Langlands.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.Geometric.WholeLeviPieceTransport
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
import Langlands.Representation.CuspidalSupport.ProperInductionProof
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.CuspidalSupport.AssociationLawsProof
import Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Exponents.GeometricExcessBranchFromUpper

/-!
# Cuspidal pieces of opposite Jacquet modules from the geometric lemma

The cuspidal-piece statement follows from the geometric lemma for the pair
`(B, C.reverse)`. This file proves that implication; it does not prove the
geometric lemma.
-/

noncomputable section

namespace Langlands.InducedOppositeCuspidalPiece

open GeneralLinear Geometric CuspidalSupport OppositeCuspidalJacquetFiltration
open WeylBranchPieces CategoryTheory

universe uF uV uW

section Intersections

variable {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)
  (S : BlockRefinement B)

/-- If the source intersection is the refined Levi and the target intersection
is the whole target Levi, the flattened source refinement is conjugated onto
the whole target Levi. -/
theorem conjugatesLevi_flatten_of_intersections (w : Equiv.Perm (Fin n))
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hR : sourceLevi F C B w⁻¹ = ⊤) :
    ConjugatesLevi (F := F) (B.flatten S) C w := by
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, rfl⟩ := flattenedLeviSubgroup_le B S hx
    have hm : m ∈ sourceLevi F B C w :=
      hS ▸ (leviEmbedding_mem_flattenedLevi_iff B S m).mp hx
    exact hm
  · rintro ⟨m', rfl⟩
    have hm' : m' ∈ sourceLevi F C B w⁻¹ := hR ▸ Subgroup.mem_top m'
    obtain ⟨m, hm⟩ := hm'
    have key : (MulAut.conj (permutation n F w)).toMonoidHom (B.leviEmbedding F m) =
        C.leviEmbedding F m' := by
      change permutation n F w * B.leviEmbedding F m * (permutation n F w)⁻¹ = _
      change B.leviEmbedding F m =
        permutation n F w⁻¹ * C.leviEmbedding F m' * (permutation n F w⁻¹)⁻¹ at hm
      rw [hm, map_inv]
      group
    refine ⟨B.leviEmbedding F m, (leviEmbedding_mem_flattenedLevi_iff B S m).mpr ?_, key⟩
    rw [← hS]
    change (MulAut.conj (permutation n F w)).toMonoidHom (B.leviEmbedding F m) ∈
      C.leviSubgroup F
    rw [key]
    exact ⟨m', rfl⟩

end Intersections

section Reverse

variable {F : Type uF} [Field F] {n : ℕ} (C : BlockShape n)

/-- Inverse conjugation by the inverse reversal permutation is block
relabelling. -/
theorem leviConjugation_reverse_inv_symm
    (h : ConjugatesLevi (F := F) C C.reverse (C.reversePermutation⁻¹ * 1))
    (m : C.reverse.Levi F) :
    (leviConjugation C C.reverse (C.reversePermutation⁻¹ * 1) h).symm m =
      (leviReverseEquiv C).symm m := by
  obtain ⟨m, rfl⟩ := (leviReverseEquiv (R := F) C).surjective m
  rw [MulEquiv.symm_apply_apply,
    leviConjugation_symm_leviReverseEquiv h (conjugatesLevi_mul h (conjugatesLevi_reverse C))]
  apply C.leviEmbedding_injective F
  rw [leviConjugation_symm_embedding]
  simp

end Reverse

section Transport

variable {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A subquotient of a transported representation is a quotient of the
transport of a subrepresentation of the original representation. -/
theorem exists_transport_subrepresentation (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) (σ : Representation ℂ (B.Levi F) V)
    (τ : Representation ℂ (C.Levi F) W) (h : IsSubquotient (transport B C w hw σ) τ) :
    ∃ U : Subrepresentation σ,
      ∃ q : (transport B C w hw U.toRepresentation).IntertwiningMap τ,
        Function.Surjective q := by
  obtain ⟨U₀, q₀, hq₀⟩ := h
  let U : Subrepresentation σ :=
    { toSubmodule := U₀.toSubmodule
      apply_mem_toSubmodule := fun g v hv => by
        have h := U₀.apply_mem_toSubmodule (leviConjugation B C w hw g) hv
        change σ ((leviConjugation B C w hw).symm (leviConjugation B C w hw g)) v ∈
          U₀.toSubmodule at h
        rwa [MulEquiv.symm_apply_apply] at h }
  let q : (transport B C w hw U.toRepresentation).IntertwiningMap τ :=
    { toLinearMap := q₀.toLinearMap
      isIntertwining' := fun m => q₀.isIntertwining' m }
  exact ⟨U, q, hq₀⟩

end Transport

section Irreducible

variable {G : Type*} [Group G] {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- An irreducible representation has a nontrivial carrier. -/
theorem nontrivial_of_isIrreducible (τ : Representation ℂ G X) [hτ : τ.IsIrreducible] :
    Nontrivial X := by
  have := (Representation.irreducible_iff_isSimpleModule_asModule (ρ := τ)).mp hτ
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) τ.asModule

end Irreducible

section Main

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B C : BlockShape n)

/-- The geometric lemma for `(B, C.reverse)` gives the cuspidal-piece
conclusion for the opposite Jacquet module along `C` of the induction from
`B`. -/
theorem cuspidalPiece_of_geometricLemma (hn : 0 < n)
    (hgeo : GeometricLemmaTheorem.{uF, uW} T B C.reverse) :
    letI := T.topology
    ∀ (π : Rep.{uW} ℂ (B.Levi F.Carrier)), IsSmooth π.ρ →
      ∀ ρ : Rep.{uV} ℂ (C.Levi F.Carrier),
        Representation.IsIrreducible ρ.ρ →
        IsLeviCuspidal C ρ.ρ →
        (∃ U : Subrepresentation (CuspidalJacquetMultiplicity.oppositeJacquet T C
            (CuspidalJacquetMultiplicity.induced T B π)).ρ,
          ∃ q : U.toRepresentation.IntertwiningMap ρ.ρ, Function.Surjective q) →
        ∃ (S : BlockRefinement B) (w : Equiv.Perm (Fin n))
          (hw : ConjugatesLevi (F := F.Carrier) (B.flatten S) C w)
          (U : Subrepresentation ((T.normalizedRefinedJacquet B S π.ρ).comp
            (flattenedLeviEquiv F.Carrier B S).toMonoidHom)),
          ∃ q : (transport (B.flatten S) C w hw U.toRepresentation).IntertwiningMap ρ.ρ,
            Function.Surjective q := by
  let := T.topology
  intro π hπ ρ hirr hcusp hsub
  obtain ⟨Sf, Rf, hS, hR, m, e, hglue⟩ := hgeo
  let π' : SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier) := ⟨π, hπ⟩
  let r := leviReverseEquiv (R := F.Carrier) C
  let ρr := ρ.ρ.comp r.symm.toMonoidHom
  have : Representation.IsIrreducible ρr :=
    isIrreducible_comp_of_surjective ρ.ρ r.symm.toMonoidHom r.symm.surjective
  have hρr : IsLeviQuasicuspidal C.reverse ρr :=
    GeometricExcessBranch.isLeviQuasicuspidal_reverse C ρ.ρ hcusp.2
  -- The opposite Jacquet module along `C` is the upper one along `C.reverse`.
  have h₁ : IsSubquotient ((jacquetInductionFunctor.{uF, uW} T B C.reverse).obj π').ρ ρr := by
    have h := (IsSubquotient.of_equiv_left
      (oppositeJacquetReverseEquiv T C (CuspidalJacquetMultiplicity.induced T B π)) hsub).comp
      r.symm.toMonoidHom
    have hA : ((T.normalizedJacquet C.reverse
        (CuspidalJacquetMultiplicity.induced T B π).ρ).comp r.toMonoidHom).comp
        r.symm.toMonoidHom =
        T.normalizedJacquet C.reverse (CuspidalJacquetMultiplicity.induced T B π).ρ := by
      refine MonoidHom.ext fun g => ?_
      change T.normalizedJacquet C.reverse (CuspidalJacquetMultiplicity.induced T B π).ρ
        (r (r.symm g)) = _
      rw [MulEquiv.apply_symm_apply]
    rw [hA] at h
    exact h
  obtain ⟨i, hi⟩ := WeylBranchPieces.IsGluedFrom.exists_isSubquotient_piece hglue π' h₁
  have hSi := hS (e i)
  have hRi := hR (e i)
  by_cases hpar : refinedParabolic F.Carrier C.reverse (Rf (e i)) = ⊤
  swap
  · have hi' : IsSubquotient
        ((T.normalizedRefinedInductionFunctor C.reverse (Rf (e i))).obj _).representation ρr :=
      hi
    exact absurd hi' (GeometricExcessBranch.not_isSubquotient_properInduced T hn C.reverse
      (Rf (e i)) hpar _ ρr inferInstance hρr)
  -- The piece has the whole target Levi: it is a transported refined Jacquet module.
  have htop : sourceLevi F.Carrier C.reverse B (e i).val⁻¹ = ⊤ :=
    hRi.2.1.trans (refinedLevi_eq_top_of_refinedParabolic_eq_top C.reverse (Rf (e i)) hpar)
  have hw := conjugatesLevi_flatten_of_intersections B C.reverse (Sf (e i)) (e i).val
    hSi.2.1 htop
  let σ := (T.normalizedRefinedJacquet B (Sf (e i)) π.ρ).comp
    (flattenedLeviEquiv F.Carrier B (Sf (e i))).toMonoidHom
  have h₂ : IsSubquotient (transport (B.flatten (Sf (e i))) C.reverse (e i).val hw σ) ρr :=
    IsSubquotient.of_equiv_left
      (wholeLeviGeometricPieceEquiv T B C.reverse (e i).val (Sf (e i)) (Rf (e i))
        hSi.2.1 hRi.2.1 hw π').symm hi
  -- Undo the block relabelling.
  have hw' := conjugatesLevi_mul hw (conjugatesLevi_reverse (F := F.Carrier) C)
  have h₃ : IsSubquotient
      (transport (B.flatten (Sf (e i))) C (C.reversePermutation * (e i).val) hw' σ) ρ.ρ := by
    have h := h₂.comp r.toMonoidHom
    have hρ : ρr.comp r.toMonoidHom = ρ.ρ := by
      ext g v
      change ρ.ρ (r.symm (r g)) v = _
      rw [MulEquiv.symm_apply_apply]
    rw [hρ] at h
    exact IsSubquotient.of_equiv_left (transportReverseEquiv hw hw' σ).symm h
  obtain ⟨U, q, hq⟩ := exists_transport_subrepresentation (B.flatten (Sf (e i))) C
    (C.reversePermutation * (e i).val) hw' σ ρ.ρ h₃
  exact ⟨Sf (e i), C.reversePermutation * (e i).val, hw', U, q, hq⟩

end Main

/-- The p-adic geometric lemma implies the cuspidal-piece statement. -/
theorem glInducedOppositeJacquetCuspidalPiece_of_padicGeometricLemma
    (h : PadicGeometricLemmaTheorem.{uF, uW}) :
    GLInducedOppositeJacquetCuspidalPieceStatement.{uF, uV, uW} := by
  intro p _ F T n hn B C π hπ ρ hirr hcusp hsub
  exact cuspidalPiece_of_geometricLemma T B C hn (h p F T n hn B C.reverse)
    π hπ ρ hirr hcusp hsub

end Langlands.InducedOppositeCuspidalPiece
