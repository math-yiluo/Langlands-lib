import Langlands.Representation.Classification.SegmentProductCuspidalEmbedding
import Langlands.Representation.Classification.SegmentProductCuspidalMembers
import Langlands.Representation.Classification.SegmentHeadSupportGeneric
import Langlands.Representation.Classification.SupercuspidalEmbeddingProof
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof

/-! # Supercuspidal supports of the constituents of normalized products -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory GeneralLinear Geometric PadicField.TopologicalData Classification

universe v z

section Padic

variable {p : ℕ} [Fact p.Prime] {E : PadicField.{v} p} (T : E.TopologicalData)

private def rankCastIso {ι : Type} (r : ι → ℕ)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, v, z} ℂ (GeneralLinear (r i) E.Carrier))
    {i j : ι} (h : i = j) :
    letI := T.topology
    (congrArg r h ▸ σ i) ≅ σ j := by
  subst j
  exact Iso.refl _

/-- A normalized product of supercuspidal products is the supercuspidal product of the
concatenated cuspidal data. -/
theorem nonempty_cuspidalProduct_flatten_iso {n : ℕ} (B : BlockShape n)
    {k : Fin B.length → ℕ} (ρ : ∀ i, Fin (k i) → CuspidalDatum.{z, v} T)
    (h : ∀ i, ∑ j, (ρ i j).rank = B.size i)
    (A : letI := T.topology
      ∀ i j, SupercuspidalRep.{v, z} (F := E.Carrier) (n := (ρ i j).rank)) :
    letI := T.topology
    let S : BlockRefinement B := fun i => T.cuspidalShape (ρ i) (h i)
    let e := B.flattenBlockEquiv S
    Nonempty (T.cuspidalProductInduced (fun q => ρ (e.symm q).1 (e.symm q).2)
        (B.flatten S).sum_eq (fun q => A (e.symm q).1 (e.symm q).2) ≅
      (T.normalizedProductInductionFunctor B).obj
        (fun i => T.cuspidalProductInduced (ρ i) (h i) (A i))) := by
  let := T.topology
  intro S e
  let Bf := B.flatten S
  let σ : ∀ q, SmoothRep.{0, v, z} ℂ (GeneralLinear (Bf.size q) E.Carrier) :=
    fun q => (A (e.symm q).1 (e.symm q).2).obj
  let hsz (q : (i : Fin B.length) × Fin (S i).length) : (S q.1).size q.2 = Bf.size (e q) :=
    (B.flatten_size_flattenBlockEquiv S q).symm
  obtain ⟨ereg⟩ := Parabolic.orderedProductRegrouping.{v, z} E T
    n Bf B S e hsz (fun j k x => B.index_index_eq_flatten S ⟨j, k⟩ x) σ
  refine ⟨ereg ≪≫ (T.normalizedProductInductionFunctor B).mapIso (Pi.isoMk fun j => ?_)⟩
  apply (T.normalizedProductInductionFunctor (S j)).mapIso
  apply Pi.isoMk
  intro k'
  exact rankCastIso T (fun q : (i : Fin B.length) × Fin (S i).length => (S q.1).size q.2)
    (fun q => (A q.1 q.2).obj) (e.symm_apply_apply ⟨j, k'⟩)

set_option maxHeartbeats 1600000 in
/-- All irreducible subquotients of a normalized product of irreducible blocks have one common
supercuspidal support. -/
theorem exists_supercuspidalSupport_of_normalizedProduct {n : ℕ} (B : BlockShape n)
    (Ξ : letI := T.topology; ∀ i, SmoothRep.{0, v, max v z} ℂ (GeneralLinear (B.size i) E.Carrier))
    (hirr : letI := T.topology; ∀ i, (Ξ i).IsIrreducible) :
    letI := T.topology
    ∃ s : Multiset (CuspidalDatum.{z, v} T),
      ∀ D : SmoothRep.{0, v, max v z} ℂ (GeneralLinear n E.Carrier), D.IsIrreducible →
        SmoothRep.IsSubquotient D ((T.normalizedProductInductionFunctor B).obj Ξ) →
        T.IsSupercuspidalSupport D s := by
  let := T.topology
  have hemb (i : Fin B.length) := glSupercuspidalEmbedding.{z, v} p E T (B.size i)
    (B.positive i) (Ξ i) (hirr i)
  choose k ρ hρ using hemb
  choose h A hA hsub using hρ
  let f (i : Fin B.length) : (Ξ i).representation.IntertwiningMap
      (T.cuspidalProductInduced (ρ i) (h i) (A i)).representation := (hsub i).2.choose
  have hf (i : Fin B.length) : Function.Injective (f i) := (hsub i).2.choose_spec
  let S : BlockRefinement B := fun i => T.cuspidalShape (ρ i) (h i)
  let e := B.flattenBlockEquiv S
  obtain ⟨eflat⟩ := nonempty_cuspidalProduct_flatten_iso T B ρ h A
  refine ⟨(List.ofFn fun q => ρ (e.symm q).1 (e.symm q).2 : Multiset _), fun D hD hDsub => ?_⟩
  let F : (T.normalizedProductInductionFunctor B).obj Ξ ⟶
      (T.normalizedProductInductionFunctor B).obj
        (fun i => T.cuspidalProductInduced (ρ i) (h i) (A i)) :=
    SmoothRep.ofHom (T.normalizedProductInducedMap B f)
  have hF : Function.Injective (SmoothRep.hom F) :=
    SegmentProductCuspidalEmbedding.normalizedProductInducedMap_injective B f hf
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDsub
  have hDflat : SmoothRep.IsSubquotient D (T.cuspidalProductInduced
      (fun q => ρ (e.symm q).1 (e.symm q).2) (B.flatten S).sum_eq
      (fun q => A (e.symm q).1 (e.symm q).2)) := by
    refine SmoothRep.isSubquotient_iff_exists.mpr ⟨C, i ≫ F ≫ eflat.inv, q, ?_, hq⟩
    rw [SmoothRep.hom_comp, SmoothRep.hom_comp]
    exact (SmoothRep.hom_hom_injective eflat.symm).comp (hF.comp hi)
  exact ⟨_, _, rfl, (B.flatten S).sum_eq, fun q => A (e.symm q).1 (e.symm q).2,
    fun q => hA (e.symm q).1 (e.symm q).2, hD, hDflat⟩

end Padic

end Langlands.BaseChange
