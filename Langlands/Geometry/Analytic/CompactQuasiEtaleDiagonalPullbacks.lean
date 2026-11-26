import Langlands.Geometry.Analytic.CompactLocalizedQuasiEtalePullback
import Langlands.Geometry.Analytic.QuasiEtalePullbackLocality

/-! # Compact site pullbacks from analytic-domain diagonals -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Restriction to an actual source domain preserves local domain–étale
factorizations. -/
theorem HasLocalDomainEtaleFactorizations.domainι_comp
    {A X : LocalizedCategory.{u, v, v} (K := K)}
    {f : A ⟶ X} (hf : HasLocalDomainEtaleFactorizations f)
    (D : (presentationOf A).AnalyticDomain) :
    HasLocalDomainEtaleFactorizations (domainι A D ≫ f) := by
  intro y
  let j := domainι A D
  obtain ⟨C, hC, hn, hCfact⟩ := hf (localizedSpaceFunctor.map j y)
  refine ⟨domainPreimage j '' C, hC.image _, ?_, ?_⟩
  · refine Filter.mem_of_superset
      ((localizedSpaceFunctor.map j).hom.continuous.continuousAt.preimage_mem_nhds hn) ?_
    intro z hz
    obtain ⟨E, hE, hzE⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨domainPreimage j E, ⟨E, hE, rfl⟩, hzE⟩
  · rintro _ ⟨E, hE, rfl⟩
    refine ⟨(hCfact E hE).1, ?_⟩
    let E' := domainPreimage j E
    let F := D.subspaceExtend E'
    have hFE : F ≤ E := by
      rintro _ ⟨z, hz, rfl⟩
      change localizedSpaceFunctor.map j z ∈ E.carrier at hz
      rw [show localizedSpaceFunctor.map j z = z.val from domainι_apply D z] at hz
      exact hz
    let e := domainNestedLocalizationIso (presentationOf A) D E'
    have he : e.hom ≫ domainι A F = domainι (domainObj A D) E' ≫ j :=
      domainNestedLocalizationIso_hom_inclusion (presentationOf A) D E'
    have hw : e.hom ≫ (domainι A F ≫ f) =
        domainι (domainObj A D) E' ≫ (j ≫ f) := by
      rw [← Category.assoc e.hom, he]
      exact Category.assoc _ _ _
    exact hw ▸ (((hCfact E hE).2.of_domain_le hFE).iso_comp e)

theorem isPullback_of_relative_diagonal
    {C : Type*} [Category* C] {A B X U V P Q : C}
    {f : U ⟶ B} {g : V ⟶ B} {b : B ⟶ X} {p : P ⟶ U} {q : P ⟶ V}
    {s : Q ⟶ B} {t : Q ⟶ B} {m : P ⟶ Q} {d : B ⟶ Q} {a : A ⟶ B} {j : A ⟶ P}
    (hp : IsPullback p q (f ≫ b) (g ≫ b)) (hq : IsPullback s t b b)
    (hs : m ≫ s = p ≫ f) (ht : m ≫ t = q ≫ g)
    (hd₁ : d ≫ s = 𝟙 B) (hd₂ : d ≫ t = 𝟙 B)
    (ha : IsPullback a j d m) : IsPullback (j ≫ p) (j ≫ q) f g := by
  have hf : (j ≫ p) ≫ f = a := by
    rw [Category.assoc, ← hs, ← Category.assoc, ← ha.w, Category.assoc, hd₁, Category.comp_id]
  have hg : (j ≫ q) ≫ g = a := by
    rw [Category.assoc, ← ht, ← Category.assoc, ← ha.w, Category.assoc, hd₂, Category.comp_id]
  refine IsPullback.mk' (hf.trans hg.symm) ?_ ?_
  · intro T l r hl hr
    apply ha.hom_ext
    · rw [← hf, ← Category.assoc l, ← Category.assoc r, hl]
    · apply hp.hom_ext
      · simpa only [Category.assoc] using hl
      · simpa only [Category.assoc] using hr
  · intro T x y hw
    have hxy : x ≫ (f ≫ b) = y ≫ (g ≫ b) := by
      rw [← Category.assoc, ← Category.assoc, hw]
    let k := hp.lift x y hxy
    have hk₁ : k ≫ p = x := hp.lift_fst x y hxy
    have hk₂ : k ≫ q = y := hp.lift_snd x y hxy
    have hk : (x ≫ f) ≫ d = k ≫ m := by
      apply hq.hom_ext
      · rw [Category.assoc, hd₁, Category.comp_id, Category.assoc, hs,
          ← Category.assoc k, hk₁]
      · rw [Category.assoc, hd₂, Category.comp_id, Category.assoc, ht,
          ← Category.assoc k, hk₂, hw]
    refine ⟨ha.lift (x ≫ f) k hk, ?_, ?_⟩
    · rw [← Category.assoc, ha.lift_snd, hk₁]
    · rw [← Category.assoc, ha.lift_snd, hk₂]

/-- The diagonal of a compact quasi-étale source is represented by an
actual analytic domain in its full self-pullback. -/
def CompactQuasiEtaleDiagonalDomainStatement (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {B X Q : LocalizedCategory.{u, v, v} (K := K)}
    {b : B ⟶ X} {s t : Q ⟶ B} (h : IsPullback s t b b),
    IsCompactSpace B → quasiEtale b →
      IsAnalyticDomainEmbedding (h.lift (𝟙 B) (𝟙 B) rfl)

/-- The diagonal-domain construction gives compact site pullbacks over a
Hausdorff ambient space, for arbitrary morphisms in the site. -/
theorem exists_compactQuasiEtalePullback_of_diagonal
    (hdiag : CompactQuasiEtaleDiagonalDomainStatement.{u, v} K)
    (hetale : LocalizedEtaleBaseChangeStatement.{u, v} K)
    {X : LocalizedCategory.{u, v, v} (K := K)} (hX : T2Space (localizedSpaceFunctor.obj X))
    {B U V : QuasiEtaleSite X} (f : U ⟶ B) (g : V ⟶ B)
    (hB : IsCompactSpace B.left) (hU : IsCompactSpace U.left) (hV : IsCompactSpace V.left) :
    ∃ c : PullbackCone f g, IsCompactSpace c.pt.left ∧
      IsPullback c.fst.left c.snd.left f.left g.left := by
  let : (etale (K := K) : MorphismProperty
      (LocalizedCategory.{u, v, v} (K := K))).IsStableUnderBaseChange := hetale
  let c := compactLocalizedQuasiEtalePullback U.hom V.hom U.prop hU hV hX
  let b := compactLocalizedQuasiEtalePullback B.hom B.hom B.prop hB hB hX
  have hc := IsPullback.of_isLimit c.isLimit
  have hb := IsPullback.of_isLimit b.isLimit
  have hw : (c.cone.fst ≫ f.left) ≫ B.hom = (c.cone.snd ≫ g.left) ≫ B.hom := by
    simpa only [Category.assoc, MorphismProperty.Over.w] using hc.w
  let m := hb.lift (c.cone.fst ≫ f.left) (c.cone.snd ≫ g.left) hw
  let d := hb.lift (𝟙 B.left) (𝟙 B.left) rfl
  obtain ⟨D, e, hde⟩ := hdiag hb hB B.prop
  change B.left ≅ domainObj b.cone.pt D at e
  change d = e.hom ≫ domainι b.cone.pt D at hde
  let E := domainPreimage m D
  let j := domainι c.cone.pt E
  let a := domainPreimageMap m D ≫ e.inv
  have ha : IsPullback a j d m := by
    apply (domainPreimage_isPullback m D).flip.of_iso' (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simp [a]
    · simp [j, E]
    · simpa only [Iso.refl_hom, Category.comp_id] using hde.symm
    · simp
  have h : IsPullback (j ≫ c.cone.fst) (j ≫ c.cone.snd) f.left g.left := by
    have hc' : IsPullback c.cone.fst c.cone.snd (f.left ≫ B.hom) (g.left ≫ B.hom) := by
      simpa only [MorphismProperty.Over.w] using hc
    exact isPullback_of_relative_diagonal hc' hb
      (hb.lift_fst _ _ hw) (hb.lift_snd _ _ hw)
      (hb.lift_fst _ _ rfl) (hb.lift_snd _ _ rfl) ha
  let : T2Space (localizedSpaceFunctor.obj U.left) := hU.2
  let : T2Space (localizedSpaceFunctor.obj V.left) := hV.2
  have hUfact := hasLocalDomainEtaleFactorizations_of_quasiEtale (U := U.left) U.prop
  have hVfact := hasLocalDomainEtaleFactorizations_of_quasiEtale (U := V.left) V.prop
  have hQE := (hUfact.of_isPullback_comp hVfact hc).domainι_comp E
  let R := MorphismProperty.Over.mk ⊤ (j ≫ (c.cone.snd ≫ V.hom)) hQE.quasiEtale
  let p : R ⟶ U := MorphismProperty.Over.homMk (j ≫ c.cone.fst) (by
    change (j ≫ c.cone.fst) ≫ U.hom = j ≫ (c.cone.snd ≫ V.hom)
    rw [Category.assoc, hc.w])
  let q : R ⟶ V := MorphismProperty.Over.homMk (j ≫ c.cone.snd) (Category.assoc _ _ _)
  let t := PullbackCone.mk p q (MorphismProperty.Over.Hom.ext h.w)
  let : T2Space (presentationOf b.cone.pt).presentation.space := b.compact.2
  let : CompactSpace (localizedSpaceFunctor.obj c.cone.pt) := c.compact.1
  let : T2Space (presentationOf c.cone.pt).presentation.space := c.compact.2
  have hDc : IsCompact D.carrier := isCompact_iff_compactSpace.mpr (hB.of_iso e).1
  have hE : IsCompact E.carrier :=
    (hDc.isClosed.preimage (localizedSpaceFunctor.map m).hom.continuous).isCompact
  exact ⟨t, ⟨isCompact_iff_compactSpace.mp hE, inferInstanceAs (T2Space E.carrier)⟩, h⟩

end Langlands.Analytic.SaturatedAtlasPresentation
