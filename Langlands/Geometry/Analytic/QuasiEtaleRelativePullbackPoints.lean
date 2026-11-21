import Langlands.Geometry.Analytic.CompatibleLocalizedFieldPoints
import Langlands.Geometry.Analytic.QuasiEtaleFieldPointPullbacks
import Langlands.Geometry.Analytic.CompactQuasiEtaleDiagonal

/-! # Point lifting over compact quasi-étale objects -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {U V B X R : LocalizedCategory.{u, v, v} (K := K)}

/-- The localized pullback over a compact quasi-étale object lifts all
compatible ordinary pairs if the first composite to the ambient base is
quasi-étale. -/
theorem exists_point_of_isPullback_over_compactQuasiEtale
    {p : R ⟶ U} {q : R ⟶ V} {f : U ⟶ B} {g : V ⟶ B} (b : B ⟶ X)
    (h : IsPullback p q f g) (hf : quasiEtale (f ≫ b)) (hb : quasiEtale b)
    (hB : IsCompactSpace B)
    (x : localizedSpaceFunctor.obj U) (y : localizedSpaceFunctor.obj V)
    (hxy : localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y) :
    ∃ z : localizedSpaceFunctor.obj R,
      localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y := by
  let P := localizedQuasiEtalePullback (f ≫ b) (g ≫ b) hf
  let Q := localizedQuasiEtalePullback b b hb
  have hP := IsPullback.of_isLimit P.2
  have hQ := IsPullback.of_isLimit Q.2
  have hw : (P.1.fst ≫ f) ≫ b = (P.1.snd ≫ g) ≫ b := by
    simpa only [Category.assoc] using hP.w
  let m := hQ.lift (P.1.fst ≫ f) (P.1.snd ≫ g) hw
  let d := hQ.lift (𝟙 B) (𝟙 B) rfl
  have hm₁ : m ≫ Q.1.fst = P.1.fst ≫ f := hQ.lift_fst _ _ hw
  have hm₂ : m ≫ Q.1.snd = P.1.snd ≫ g := hQ.lift_snd _ _ hw
  have hd₁ : d ≫ Q.1.fst = 𝟙 B := hQ.lift_fst _ _ rfl
  have hd₂ : d ≫ Q.1.snd = 𝟙 B := hQ.lift_snd _ _ rfl
  obtain ⟨D, e, he⟩ := compactQuasiEtaleDiagonalDomain hQ hB hb
  change d = e.hom ≫ domainι Q.1.pt D at he
  let E := domainPreimage m D
  let j := domainι P.1.pt E
  let a := domainPreimageMap m D ≫ e.inv
  have ha : j ≫ m = a ≫ d := by
    simpa only [a, he, Category.assoc, Iso.inv_hom_id_assoc] using
      (domainPreimageMap_comp_inclusion m D).symm
  have hw' : (j ≫ P.1.fst) ≫ f = (j ≫ P.1.snd) ≫ g := by
    calc
      (j ≫ P.1.fst) ≫ f = a := by
        rw [Category.assoc, ← hm₁, ← Category.assoc, ha, Category.assoc, hd₁,
          Category.comp_id]
      _ = (j ≫ P.1.snd) ≫ g := by
        rw [Category.assoc, ← hm₂, ← Category.assoc, ha, Category.assoc, hd₂,
          Category.comp_id]
  let l := h.lift (j ≫ P.1.fst) (j ≫ P.1.snd) hw'
  have hl₁ : l ≫ p = j ≫ P.1.fst := h.lift_fst _ _ hw'
  have hl₂ : l ≫ q = j ≫ P.1.snd := h.lift_snd _ _ hw'
  obtain ⟨L, _, _, _, _, _, x', y', hx, hy, hxy'⟩ :=
    exists_compatible_localizedFieldPoints f g x y hxy
  let F := localizedFieldPointFunctor (K := K) L
  have hc : F.map (f ≫ b) x' = F.map (g ≫ b) y' := by
    rw [F.map_comp_apply, F.map_comp_apply, hxy']
  have hPF := localizedFieldPoint_isPullback_of_quasiEtale (L := L) hP hf
  have hQF := localizedFieldPoint_isPullback_of_quasiEtale (L := L) hQ hb
  obtain ⟨w, hw₁, hw₂⟩ := Types.exists_of_isPullback hPF x' y' hc
  let c := F.map f x'
  have hmc : F.map m w = F.map d c := by
    apply Types.ext_of_isPullback hQF
    · rw [← F.map_comp_apply, hm₁, F.map_comp_apply, hw₁,
        ← F.map_comp_apply, hd₁, F.map_id]
      rfl
    · rw [← F.map_comp_apply, hm₂, F.map_comp_apply, hw₂,
        ← F.map_comp_apply, hd₂, F.map_id]
      exact hxy'.symm
  have hpre := localizedFieldPoint_isPullback_domainPreimage (L := L) m D
  have hcompat : F.map m w = F.map (domainι Q.1.pt D) (F.map e.hom c) := by
    rw [← F.map_comp_apply, ← he]
    exact hmc
  obtain ⟨t, ht, -⟩ := Types.exists_of_isPullback hpre w (F.map e.hom c) hcompat
  have ht₁ : F.map p (F.map l t) = x' := by
    rw [← F.map_comp_apply, hl₁, F.map_comp_apply, ht, hw₁]
  have ht₂ : F.map q (F.map l t) = y' := by
    rw [← F.map_comp_apply, hl₂, F.map_comp_apply, ht, hw₂]
  refine ⟨((localizedFieldPointProjection L).app R (F.map l t)).down, ?_, ?_⟩
  · rw [← localizedFieldPointProjection_map_down, ht₁]
    exact hx
  · rw [← localizedFieldPointProjection_map_down, ht₂]
    exact hy

end Langlands.Analytic.SaturatedAtlasPresentation
