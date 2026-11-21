import Langlands.Geometry.Analytic.CompactAnalyticFibrePowers
import Langlands.Geometry.Analytic.CompactQuasiEtaleDiagonal
import Langlands.Geometry.Analytic.DistinguishedOpenRestriction
import Langlands.Geometry.Analytic.QuasiEtaleFieldPointImageLift

/-! # The distinct locus of a compact analytic fibre power -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation.CompactAnalyticFibrePower

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Y X R : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X} {s t : R ⟶ Y}
  {n : ℕ} (P : CompactAnalyticFibrePower.{u, v, uL} p n) (h : IsPullback s t p p)

/-- The ordered pair of coordinates in the analytic self-pullback. -/
def pair (i j : Fin (n + 1)) : P.obj ⟶ R :=
  h.lift (P.coord i) (P.coord j) ((P.coord_base i).trans (P.coord_base j).symm)

@[reassoc (attr := simp)] theorem pair_fst (i j : Fin (n + 1)) : P.pair h i j ≫ s = P.coord i :=
  h.lift_fst _ _ _

@[reassoc (attr := simp)] theorem pair_snd (i j : Fin (n + 1)) : P.pair h i j ≫ t = P.coord j :=
  h.lift_snd _ _ _

private def diag : Y ⟶ R := h.lift (𝟙 Y) (𝟙 Y) rfl

@[reassoc] private theorem diag_fst : diag h ≫ s = 𝟙 Y := h.lift_fst _ _ _

@[reassoc] private theorem diag_snd : diag h ≫ t = 𝟙 Y := h.lift_snd _ _ _

/-- The points for which every pair of different coordinate indices is
outside the analytic diagonal in the self-pullback. -/
def distinctLocus : Set (localizedSpaceFunctor.obj P.obj) :=
  {z | ∀ i j, i ≠ j →
    localizedSpaceFunctor.map (P.pair h i j) z ∉ range (localizedSpaceFunctor.map (diag h))}

private theorem closedDomain_iUnion {Z : LocalizedCategory.{u, v, v} (K := K)}
    {I : Type} [Finite I] (D : I → (presentationOf Z).AnalyticDomain)
    (hc : ∀ i, IsClosed (D i).carrier) :
    (presentationOf Z).presentation.atlas.IsOriginalChartDomain (⋃ i, (D i).carrier) := by
  classical
  let := Fintype.ofFinite I
  have aux (J : Finset I) :
      (presentationOf Z).presentation.atlas.IsOriginalChartDomain (⋃ i ∈ J, (D i).carrier) := by
    induction J using Finset.induction_on with
    | empty =>
      simpa only [Finset.notMem_empty, iUnion_false, iUnion_empty] using
        (presentationOf Z).presentation.atlas.isOriginalChartDomain_empty
    | insert j J _ ih =>
      have heq : (⋃ i ∈ insert j J, (D i).carrier) = (D j).carrier ∪ ⋃ i ∈ J, (D i).carrier := by
        ext z
        simp only [mem_iUnion, Finset.mem_insert, mem_union]
        constructor
        · rintro ⟨i, rfl | hi, hz⟩
          · exact Or.inl hz
          · exact Or.inr ⟨i, hi, hz⟩
        · rintro (hz | ⟨i, hi, hz⟩)
          · exact ⟨j, Or.inl rfl, hz⟩
          · exact ⟨i, Or.inr hi, hz⟩
      have hJ : IsClosed (⋃ i ∈ J, (D i).carrier) := J.finite_toSet.isClosed_biUnion fun i _ => hc i
      exact heq.symm ▸ (D j).is_domain.union_of_isClosed ih (hc j) hJ
  simpa only [Finset.mem_univ, iUnion_true] using aux Finset.univ

/-- The distinct locus is a distinguished open of the whole compact fibre power. -/
theorem isDistinguishedOpen_distinctLocus (hy : IsCompactSpace Y) (hp : quasiEtale p) :
    IsDistinguishedOpen P.obj (P.distinctLocus h) := by
  let : CompactSpace (localizedSpaceFunctor.obj Y) := hy.1
  let : T2Space (localizedSpaceFunctor.obj Y) := hy.2
  let : T2Space (localizedSpaceFunctor.obj R) := (hasCompactPairPreimages_of_quasiEtale h hp).1
  let S : Set (localizedSpaceFunctor.obj R) := range (localizedSpaceFunctor.map (diag h))
  have hS : IsClosed S := (isCompact_range (localizedSpaceFunctor.map (diag h)).hom.continuous).isClosed
  obtain ⟨D, e, he⟩ := compactQuasiEtaleDiagonalDomain h hy hp
  change diag h = e.hom ≫ domainι R D at he
  have hSD : S = D.carrier := by
    change range (localizedSpaceFunctor.map (diag h)) = _
    rw [he, localizedSpaceFunctor.map_comp]
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      rw [TopCat.comp_app, domainι_apply]
      exact (localizedSpaceFunctor.map e.hom y).property
    · intro hz
      obtain ⟨y, hy⟩ := (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)).surjective ⟨z, hz⟩
      exact ⟨y, by rw [TopCat.comp_app, domainι_apply]; exact congrArg Subtype.val hy⟩
  let I := {ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≠ ij.2}
  let E (ij : I) := domainPreimage (P.pair h ij.val.1 ij.val.2) D
  have hmem (ij : I) (z : localizedSpaceFunctor.obj P.obj) :
      z ∈ (E ij).carrier ↔ localizedSpaceFunctor.map (P.pair h ij.val.1 ij.val.2) z ∈ S :=
    (congrArg (fun A : Set (localizedSpaceFunctor.obj R) =>
      localizedSpaceFunctor.map (P.pair h ij.val.1 ij.val.2) z ∈ A) hSD.symm).to_iff
  have hE (ij : I) : IsClosed (E ij).carrier := by
    have heq : (E ij).carrier = localizedSpaceFunctor.map (P.pair h ij.val.1 ij.val.2) ⁻¹' S :=
      congrArg (fun A : Set (localizedSpaceFunctor.obj R) =>
        localizedSpaceFunctor.map (P.pair h ij.val.1 ij.val.2) ⁻¹' A) hSD.symm
    exact heq.symm ▸ hS.preimage (localizedSpaceFunctor.map (P.pair h ij.val.1 ij.val.2)).hom.continuous
  have hx : (P.distinctLocus h)ᶜ = ⋃ ij : I, (E ij).carrier := by
    classical
    ext z
    constructor
    · intro hz
      by_contra hn
      apply hz
      intro i j hij hd
      apply hn
      apply mem_iUnion.mpr
      exact ⟨⟨(i, j), hij⟩, (hmem ⟨(i, j), hij⟩ z).mpr hd⟩
    · intro hz hdz
      obtain ⟨ij, hij⟩ := mem_iUnion.mp hz
      exact hdz ij.val.1 ij.val.2 ij.property ((hmem ij z).mp hij)
  refine ⟨?_, ?_⟩
  · exact isClosed_compl_iff.mp (hx.symm ▸ isClosed_iUnion_of_finite hE)
  · exact (congrArg (fun U : Set (localizedSpaceFunctor.obj P.obj) =>
      (presentationOf P.obj).presentation.atlas.IsOriginalChartDomain U) hx).mpr
      (closedDomain_iUnion E hE)

/-- A full point lies in the distinct locus exactly when the full points
of its coordinates are distinct. -/
theorem mem_distinctLocus_iff_fieldPoint_injective (hY : IsCompactSpace Y) (hp : quasiEtale p)
    (L : Type uL) [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
    [CompleteSpace L] [IsAlgClosed L] (z : (localizedFieldPointFunctor L).obj P.obj) :
    ((localizedFieldPointProjection L).app P.obj z).down ∈ P.distinctLocus h ↔
      Function.Injective (fun i => (localizedFieldPointFunctor L).map (P.coord i) z) := by
  let Φ := localizedFieldPointFunctor (K := K) L
  have hφ := localizedQuasiEtaleFieldPointPullback (L := L) s t p p hp h
  have htest (i j : Fin (n + 1)) :
      localizedSpaceFunctor.map (P.pair h i j) (((localizedFieldPointProjection L).app P.obj z).down) ∈
        range (localizedSpaceFunctor.map (diag h)) ↔
      Φ.map (P.coord i) z = Φ.map (P.coord j) z := by
    let r := Φ.map (P.pair h i j) z
    have hpt : ((localizedFieldPointProjection L).app R r).down =
        localizedSpaceFunctor.map (P.pair h i j) (((localizedFieldPointProjection L).app P.obj z).down) :=
      localizedFieldPointProjection_map_down _ _
    have hs : Φ.map s r = Φ.map (P.coord i) z := by
      change Φ.map s (Φ.map (P.pair h i j) z) = _
      rw [← Φ.map_comp_apply, P.pair_fst]
    have ht : Φ.map t r = Φ.map (P.coord j) z := by
      change Φ.map t (Φ.map (P.pair h i j) z) = _
      rw [← Φ.map_comp_apply, P.pair_snd]
    have hfirst (q : Φ.obj Y) : Φ.map s (Φ.map (diag h) q) = q := by
      rw [← Φ.map_comp_apply, diag_fst, Φ.map_id_apply]
    have hsecond (q : Φ.obj Y) : Φ.map t (Φ.map (diag h) q) = q := by
      rw [← Φ.map_comp_apply, diag_snd, Φ.map_id_apply]
    constructor
    · rintro ⟨y, hy⟩
      have hd : PointedFieldPointLift L (diag h) := by
        obtain ⟨D, e, he⟩ := compactQuasiEtaleDiagonalDomain h hY hp
        have he' : diag h = e.hom ≫ domainι R D := he
        rw [he']
        exact (pointedFieldPointLift_of_isIso (L := L) e.hom).comp
          (pointedFieldPointLift_localizedDomainInclusion (L := L) _ D)
      obtain ⟨q, _, hq⟩ := hd r y (hy.trans hpt.symm)
      calc
        Φ.map (P.coord i) z = Φ.map s r := hs.symm
        _ = Φ.map s (Φ.map (diag h) q) := congrArg (fun r => Φ.map s r) hq.symm
        _ = q := hfirst q
        _ = Φ.map t (Φ.map (diag h) q) := (hsecond q).symm
        _ = Φ.map t r := congrArg (fun r => Φ.map t r) hq
        _ = Φ.map (P.coord j) z := ht
    · intro hij
      let q := Φ.map (P.coord i) z
      have hr : Φ.map (diag h) q = r := by
        apply Types.ext_of_isPullback hφ
        · exact (hfirst q).trans hs.symm
        · exact (hsecond q).trans (hij.trans ht.symm)
      refine ⟨((localizedFieldPointProjection L).app Y q).down, ?_⟩
      rw [← localizedFieldPointProjection_map_down (diag h), hr, hpt]
  constructor
  · intro hz i j hij
    by_contra hne
    exact hz i j hne ((htest i j).mpr hij)
  · intro hinj i j hij hdiag
    exact hij (hinj ((htest i j).mp hdiag))

/-- Permuting the coordinates preserves the distinct locus. -/
theorem permutations_mem_distinctLocus (σ : Equiv.Perm (Fin (n + 1)))
    {z : localizedSpaceFunctor.obj P.obj} (hz : z ∈ P.distinctLocus h) :
    localizedSpaceFunctor.map (P.permutations σ).hom z ∈ P.distinctLocus h := by
  intro i j hij
  have he : (P.permutations σ).hom ≫ P.pair h i j = P.pair h (σ.symm i) (σ.symm j) := by
    apply h.hom_ext <;> simp only [Category.assoc, pair_fst, pair_snd, permutations_coord]
  have he' := congrArg (fun f : P.obj ⟶ R => localizedSpaceFunctor.map f z) he
  rw [localizedSpaceFunctor.map_comp, TopCat.comp_app] at he'
  exact he'.symm ▸ hz _ _ (σ.symm.injective.ne hij)

end Langlands.Analytic.SaturatedAtlasPresentation.CompactAnalyticFibrePower
