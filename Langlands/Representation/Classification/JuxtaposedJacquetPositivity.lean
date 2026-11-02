import Langlands.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.Representation.CuspidalSupport.LeviAssociation
import Langlands.Representation.Classification.Segments

/-!
# Nonzero Jacquet modules along a uniform shape

A standard Levi associated to the uniform Levi `GL_r × ⋯ × GL_r` is equal to it.
Hence, for quasicuspidal data `σ` on the uniform shape `C`, every nonzero
subquotient of the normalized induction `i_C(σ)` has a nonzero normalized
Jacquet module along `C` itself. This is the specialization to one uniform
shape of the positivity argument of `JacquetLength.one_le_jacquetLength_of_isSubquotient`,
from minimal nonzero Jacquet descent (BZ77 2.14(1)) and the vanishing of
quasicuspidal subquotients for nonassociated Levis (BZ77 2.13(b)), which enter as
hypotheses. It applies to the step quotients of any representation that embeds
into `i_C(σ)`.
-/

noncomputable section

open Representation CategoryTheory

namespace Langlands.Classification.JuxtaposedShuffle

open GeneralLinear CuspidalSupport CuspidalSupport.JacquetLength

universe uF uV

/-- A standard Levi associated to the uniform Levi is equal to it: a conjugating
permutation matches the blocks bijectively with equal sizes. -/
theorem eq_uniform_of_levisAssociated {F : Type uF} [Field F] {m r : ℕ} (hr : 0 < r)
    {C : BlockShape (m * r)}
    (h : LevisAssociated (F := F) (BlockShape.uniform m r hr) C) :
    C = BlockShape.uniform m r hr := by
  obtain ⟨⟨w, hw⟩⟩ := h
  refine TotalConjugatingCount.shape_ext (TotalConjugatingCount.length_eq hw).symm fun j => ?_
  obtain ⟨i, rfl⟩ := TotalConjugatingCount.blockMap_surjective hw j
  exact TotalConjugatingCount.size_blockMap hw i

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {m r : ℕ} (hr : 0 < r)

/-- Every nonzero smooth subquotient of the normalized induction of quasicuspidal
data on the uniform shape has a nonzero normalized Jacquet module along that
shape. -/
theorem nontrivial_jacquet_of_isSubquotient
    (hmin : MinimalNonzeroJacquetTheorem.{uF, max uF uV})
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T (m * r)) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ ((BlockShape.uniform m r hr).Levi F.Carrier)),
      IsLeviQuasicuspidal _ σ.representation →
      ∀ Q : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier),
        SmoothRep.IsSubquotient Q
          ((T.normalizedParabolicInductionFunctor (BlockShape.uniform m r hr)).obj σ) →
        Nontrivial Q →
          Nontrivial ((BlockShape.uniform m r hr).JacquetModule Q.representation) := by
  let := T.topology
  intro σ hσ Q hQ hnt
  obtain ⟨C, hJ, hJq⟩ := hmin p F T _ Q hnt
  by_cases hC : LevisAssociated (F := F.Carrier) (BlockShape.uniform m r hr) C
  · obtain rfl := eq_uniform_of_levisAssociated hr hC
    exact hJ
  · exfalso
    exact not_subsingleton _
      (hnon _ C σ hσ hC _ (normalizedJacquetSubquotient p F T _ C _ _ hQ) hJq)

/-- If `π` embeds into the normalized induction of quasicuspidal data on the
uniform shape, every nonzero step quotient of `π` has a nonzero normalized
Jacquet module along that shape. -/
theorem nontrivial_jacquet_stepQuotient
    (hmin : MinimalNonzeroJacquetTheorem.{uF, max uF uV})
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T (m * r))
    (σ : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ ((BlockShape.uniform m r hr).Levi F.Carrier))
    (hσ : letI := T.topology; IsLeviQuasicuspidal _ σ.representation)
    {V : Type (max uF uV)} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GeneralLinear (m * r) F.Carrier) V}
    (i : letI := T.topology; π.IntertwiningMap
      (T.normalizedParabolicInduced (BlockShape.uniform m r hr) σ.representation))
    (hi : Function.Injective i) :
    ∀ X Y : Subrepresentation π, X ≤ Y →
      Nontrivial (Y.toSubmodule ⧸ X.toSubmodule.comap Y.toSubmodule.subtype) →
        Nontrivial ((BlockShape.uniform m r hr).JacquetModule (stepQuotient X Y)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (m * r)
  intro X Y _ hnt
  let A := (T.normalizedParabolicInductionFunctor (BlockShape.uniform m r hr)).obj σ
  have hA : IsSmooth
      (T.normalizedParabolicInduced (BlockShape.uniform m r hr) σ.representation) :=
    T.isSmooth_normalizedParabolicInduced _ σ.representation
  have hπ : IsSmooth π := isSmooth_of_injective i hi hA
  have hY : IsSmooth Y.toRepresentation :=
    isSmooth_of_injective (subtypeMap Y) (subtypeMap_injective Y) hπ
  let qY : Y.toRepresentation.IntertwiningMap (stepQuotient X Y) :=
    { toLinearMap := (X.toSubmodule.comap Y.toSubmodule.subtype).mkQ
      isIntertwining' := fun _ => rfl }
  have hqY : Function.Surjective qY := Submodule.mkQ_surjective _
  have hQ : IsSmooth (stepQuotient X Y) := isSmooth_of_surjective qY hqY hY
  let Ys : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier) :=
    SmoothRep.of _ hY
  let Qs : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier) :=
    SmoothRep.of _ hQ
  have hsub : SmoothRep.IsSubquotient Qs A :=
    SmoothRep.isSubquotient_iff_exists.mpr
      ⟨Ys, SmoothRep.ofHom (A := Ys) (B := A) (i.comp (subtypeMap Y)),
        SmoothRep.ofHom (A := Ys) (B := Qs) qY,
        hi.comp (subtypeMap_injective Y), hqY⟩
  exact nontrivial_jacquet_of_isSubquotient T hr hmin hnon σ hσ Qs hsub hnt

end Langlands.Classification.JuxtaposedShuffle
