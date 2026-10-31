import Langlands.Representation.Geometric.InducedOppositeCuspidalPieceConditional

/-! The actual whole geometric piece persists when the inducing object changes. -/

noncomputable section

namespace Langlands.InducedOppositeCuspidalPiece

open GeneralLinear Geometric CuspidalSupport OppositeCuspidalJacquetFiltration
open WeylBranchPieces CategoryTheory

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B C : BlockShape n)

/-- Retain the selected whole-target piece and its actual occurrence for every
smooth inducing object in the same universe. The same permutation and conjugacy
witness are used in both conclusions. -/
theorem persistentCuspidalPiece_of_geometricLemma (hn : 0 < n)
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
          (hw : ConjugatesLevi (F := F.Carrier) (B.flatten S) C w),
          IsSubquotient (transport (B.flatten S) C w hw
            ((T.normalizedRefinedJacquet B S π.ρ).comp
              (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) ρ.ρ ∧
          ∀ V : Rep.{uW} ℂ (B.Levi F.Carrier), IsSmooth V.ρ →
            IsSubquotient (CuspidalJacquetMultiplicity.oppositeJacquet T C
              (CuspidalJacquetMultiplicity.induced T B V)).ρ
              (transport (B.flatten S) C w hw
                ((T.normalizedRefinedJacquet B S V.ρ).comp
                  (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) := by
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
  refine ⟨Sf (e i), C.reversePermutation * (e i).val, hw', h₃, ?_⟩
  intro V hV
  let A : SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier) := ⟨V, hV⟩
  let σV := (T.normalizedRefinedJacquet B (Sf (e i)) V.ρ).comp
    (flattenedLeviEquiv F.Carrier B (Sf (e i))).toMonoidHom
  have hp := WeylBranchPieces.IsGluedFrom.isSubquotient_piece hglue A i
  have hp' : IsSubquotient
      ((jacquetInductionFunctor.{uF, uW} T B C.reverse).obj A).ρ
      (transport (B.flatten (Sf (e i))) C.reverse (e i).val hw σV) :=
    IsSubquotient.of_equiv_right hp
      (wholeLeviGeometricPieceEquiv T B C.reverse (e i).val (Sf (e i)) (Rf (e i))
        hSi.2.1 hRi.2.1 hw A)
  have hp'' := hp'.comp r.toMonoidHom
  have hpFinal : IsSubquotient
      (((jacquetInductionFunctor.{uF, uW} T B C.reverse).obj A).ρ.comp r.toMonoidHom)
      (transport (B.flatten (Sf (e i))) C
        (C.reversePermutation * (e i).val) hw' σV) :=
    IsSubquotient.of_equiv_right hp'' (transportReverseEquiv hw hw' σV)
  exact IsSubquotient.of_equiv_left
    (oppositeJacquetReverseEquiv T C (CuspidalJacquetMultiplicity.induced T B V)).symm hpFinal


end Langlands.InducedOppositeCuspidalPiece
