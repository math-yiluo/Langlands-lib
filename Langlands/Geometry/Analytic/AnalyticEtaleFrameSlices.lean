import Langlands.Geometry.Analytic.AnalyticDistinctFrames
import Langlands.Geometry.Analytic.AnalyticOpenBaseChange
import Langlands.Geometry.Analytic.EtaleSectionsOpen

/-! # Étale slices of compact analytic frames -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation.CompactAnalyticFibrePower

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology TopologicalSpace
open AnalyticOpenBaseChange (baseInclusion inclusion projection)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X}
  {n : ℕ} (P : CompactAnalyticFibrePower.{u, v, uL} p n)

private def singleCoordIso (Q : CompactAnalyticFibrePower.{u, v, uL} p 0) : Q.obj ≅ Y where
  hom := Q.coord 0
  inv := Q.lift p (fun _ => 𝟙 Y) (fun _ => Category.id_comp p)
  hom_inv_id := by
    apply Q.hom_ext
    intro i
    rw [Category.assoc, Q.lift_coord, Category.comp_id, Category.id_comp, Fin.eq_zero i]
  inv_hom_id := Q.lift_coord _ _ _ 0

private theorem etale_projection_single (Q : CompactAnalyticFibrePower.{u, v, uL} p 0)
    (U : Opens (localizedSpaceFunctor.obj X)) (hp : etale (projection U p)) :
    etale (projection U Q.base) := by
  let e := singleCoordIso Q
  have he : e.hom ≫ p = Q.base := Q.coord_base 0
  have hinv : e.inv ≫ Q.base = p := by rw [← he, e.inv_hom_id_assoc]
  let q := AnalyticOpenBaseChange.map U e.hom he
  let r := AnalyticOpenBaseChange.map U e.inv hinv
  have hq : q ≫ inclusion U p = inclusion U Q.base ≫ e.hom :=
    AnalyticOpenBaseChange.map_inclusion U e.hom he
  have hr : r ≫ inclusion U Q.base = inclusion U p ≫ e.inv :=
    AnalyticOpenBaseChange.map_inclusion U e.inv hinv
  have : IsIso q := ⟨r, by
    apply (cancel_mono (inclusion U Q.base)).mp
    rw [Category.assoc, hr, ← Category.assoc, hq, Category.assoc, e.hom_inv_id,
      Category.comp_id, Category.id_comp], by
    apply (cancel_mono (inclusion U p)).mp
    rw [Category.assoc, hq, ← Category.assoc, hr, Category.assoc, e.inv_hom_id,
      Category.comp_id, Category.id_comp]⟩
  rw [← AnalyticOpenBaseChange.map_projection U e.hom he]
  exact etale_comp (etale_of_isIso q) hp

private def tail (Q : CompactAnalyticFibrePower.{u, v, uL} p (n + 1)) : Q.obj ⟶ P.obj :=
  P.lift Q.base (fun i => Q.coord i.succ) (fun i => Q.coord_base i.succ)

@[reassoc] private theorem tail_coord (Q : CompactAnalyticFibrePower.{u, v, uL} p (n + 1))
    (i : Fin (n + 1)) : P.tail Q ≫ P.coord i = Q.coord i.succ := P.lift_coord _ _ _ _

private theorem tail_base (Q : CompactAnalyticFibrePower.{u, v, uL} p (n + 1)) :
    P.tail Q ≫ P.base = Q.base := P.lift_base Q.base _ (fun i => Q.coord_base i.succ)

private theorem isPullback_tail (Q : CompactAnalyticFibrePower.{u, v, uL} p (n + 1)) :
    IsPullback (Q.coord 0) (P.tail Q) p P.base := by
  apply IsPullback.mk' ((Q.coord_base 0).trans (P.tail_base Q).symm)
  · intro T a b h₀ hs
    apply Q.hom_ext
    intro i
    induction i using Fin.cases with
    | zero => exact h₀
    | succ i => simpa only [Category.assoc, tail_coord] using congrArg (· ≫ P.coord i) hs
  · intro T a b hab
    let q : Fin (n + 1 + 1) → (T ⟶ Y) := Fin.cases a (fun i => b ≫ P.coord i)
    have hq : ∀ i, q i ≫ p = a ≫ p := by
      intro i
      induction i using Fin.cases with
      | zero => rfl
      | succ i =>
        change (b ≫ P.coord i) ≫ p = a ≫ p
        rw [Category.assoc, P.coord_base, hab]
    let r := Q.lift (a ≫ p) q hq
    refine ⟨r, Q.lift_coord _ _ _ 0, ?_⟩
    apply P.hom_ext
    intro i
    rw [Category.assoc, P.tail_coord]
    exact Q.lift_coord _ _ _ i.succ

/-- If a compact quasi-étale map is étale over a base open, its finite fibre
powers are étale over the same open. -/
theorem etale_openProjection (hp : quasiEtale p) (hY : IsCompactSpace Y)
    (S : Set (localizedSpaceFunctor.obj X)) [T2Space S] (hS : ∀ z, localizedSpaceFunctor.map p z ∈ S)
    (U : Opens (localizedSpaceFunctor.obj X)) (hU : etale (projection U p)) :
    etale (projection U P.base) := by
  induction n with
  | zero => exact etale_projection_single P U hU
  | succ m ih =>
    let Q := CompactAnalyticFibrePower.of_quasiEtale hp hY S hS m
    exact AnalyticOpenBaseChange.etale_projection_of_isPullback U (Q.isPullback_tail P)
      (P.coord_base 0) (Q.tail_base P) hU (ih Q)

variable {R : LocalizedCategory.{u, v, v} (K := K)} {s t : R ⟶ Y} (h : IsPullback s t p p)

/-- The distinct locus is relatively closed in the restriction of the
compact fibre power to any base open where the original arrow is étale. -/
theorem isClosed_distinctLocus_openSlice (U : Opens (localizedSpaceFunctor.obj X))
    (hU : etale (projection U p)) :
    IsClosed ({z : localizedSpaceFunctor.obj (AnalyticOpenBaseChange.obj U P.base) |
      z.val ∈ P.distinctLocus h}) := by
  let k := s ≫ p
  have hk : t ≫ p = k := h.w.symm
  let h' := AnalyticOpenBaseChange.isPullback_map U h (rfl : s ≫ p = k) hk
  let d : Y ⟶ R := h.lift (𝟙 Y) (𝟙 Y) rfl
  have ds : d ≫ s = 𝟙 Y := h.lift_fst _ _ _
  have dt : d ≫ t = 𝟙 Y := h.lift_snd _ _ _
  have hd : d ≫ k = p := by rw [← Category.assoc, ds, Category.id_comp]
  let d' := AnalyticOpenBaseChange.map U d hd
  have hdiag : d' = h'.lift (𝟙 _) (𝟙 _) rfl := by
    apply h'.hom_ext
    · rw [h'.lift_fst]
      apply (cancel_mono (inclusion U p)).mp
      rw [Category.assoc, AnalyticOpenBaseChange.map_inclusion, ← Category.assoc,
        AnalyticOpenBaseChange.map_inclusion, Category.assoc, ds, Category.comp_id, Category.id_comp]
    · rw [h'.lift_snd]
      apply (cancel_mono (inclusion U p)).mp
      rw [Category.assoc, AnalyticOpenBaseChange.map_inclusion, ← Category.assoc,
        AnalyticOpenBaseChange.map_inclusion, Category.assoc, dt, Category.comp_id, Category.id_comp]
  have hopen : IsOpen (range (localizedSpaceFunctor.map d')) := by
    rw [hdiag]
    exact (openImmersion_etale_diagonal h' hU).isOpenEmbedding.isOpen_range
  let I := {ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≠ ij.2}
  let a (ij : I) := P.pair h ij.val.1 ij.val.2
  have ha (ij : I) : a ij ≫ k = P.base := by
    rw [← Category.assoc, P.pair_fst, P.coord_base]
  let a' (ij : I) := AnalyticOpenBaseChange.map U (a ij) (ha ij)
  have hs (ij : I) (z : localizedSpaceFunctor.obj (AnalyticOpenBaseChange.obj U P.base)) :
      (localizedSpaceFunctor.map (a' ij) z).val = localizedSpaceFunctor.map (a ij) z.val := by
    change @Eq (localizedSpaceFunctor.obj R) _ _
    simpa only [Functor.map_comp, TopCat.comp_app, domainι_apply] using
      congrArg (fun q => localizedSpaceFunctor.map q z)
        (AnalyticOpenBaseChange.map_inclusion U (a ij) (ha ij))
  have hmem (ij : I) (z : localizedSpaceFunctor.obj (AnalyticOpenBaseChange.obj U P.base)) :
      localizedSpaceFunctor.map (a' ij) z ∈ range (localizedSpaceFunctor.map d') ↔
        localizedSpaceFunctor.map (a ij) z.val ∈ range (localizedSpaceFunctor.map d) := by
    exact (AnalyticOpenBaseChange.mem_range_map_iff U d hd _).trans
      (congrArg (fun x : localizedSpaceFunctor.obj R => x ∈ range (localizedSpaceFunctor.map d))
        (hs ij z)).to_iff
  have heq : {z : localizedSpaceFunctor.obj (AnalyticOpenBaseChange.obj U P.base) |
        z.val ∈ P.distinctLocus h} =
      ⋂ ij : I, localizedSpaceFunctor.map (a' ij) ⁻¹' (range (localizedSpaceFunctor.map d'))ᶜ := by
    ext z
    constructor
    · intro hz
      exact mem_iInter.mpr fun ij hdiag => hz ij.val.1 ij.val.2 ij.property ((hmem ij z).mp hdiag)
    · intro hz i j hij hdiag
      exact mem_iInter.mp hz ⟨(i, j), hij⟩ ((hmem ⟨(i, j), hij⟩ z).mpr hdiag)
  rw [heq]
  exact isClosed_iInter fun ij => hopen.isClosed_compl.preimage
    (localizedSpaceFunctor.map (a' ij)).hom.continuous

/-- Étale and relative closedness properties of the open slices of the
finite powers of a compact quasi-étale map. -/
def AnalyticEtaleFrameSlicesStatement (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {Y X R : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X} {s t : R ⟶ Y}
    (h : IsPullback s t p p) (S : Set (localizedSpaceFunctor.obj X)) [T2Space S]
    (U : Opens (localizedSpaceFunctor.obj X)),
    quasiEtale p → IsCompactSpace Y → (∀ z, localizedSpaceFunctor.map p z ∈ S) →
    etale (projection U p) →
      ∀ {n : ℕ} (P : CompactAnalyticFibrePower.{u, v, uL} p n),
        etale (projection U P.base) ∧
          IsClosed ({z : localizedSpaceFunctor.obj (AnalyticOpenBaseChange.obj U P.base) |
            z.val ∈ P.distinctLocus h})

theorem analyticEtaleFrameSlices : AnalyticEtaleFrameSlicesStatement.{u, v, uL} K := by
  intro Y X R p s t h S _ U hp hY hS hU n P
  exact ⟨P.etale_openProjection hp hY S hS U hU, P.isClosed_distinctLocus_openSlice h U hU⟩

end Langlands.Analytic.SaturatedAtlasPresentation.CompactAnalyticFibrePower
