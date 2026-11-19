import Langlands.Geometry.Analytic.QuasiEtaleDiagonalLocal
import Langlands.Geometry.Analytic.EtaleSectionsOpen

/-! # Diagonals of compact quasi-étale analytic spaces -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem isPullback_diagonal_of_domain_mono
    {C : Type*} [Category* C] {A B X P Q : C}
    {a : A ⟶ B} [Mono a] {f : B ⟶ X} {p₁ p₂ : P ⟶ A} {q₁ q₂ : Q ⟶ B}
    (hp : IsPullback p₁ p₂ (a ≫ f) (a ≫ f)) (hq : IsPullback q₁ q₂ f f) :
    IsPullback a (hp.lift (𝟙 A) (𝟙 A) rfl) (hq.lift (𝟙 B) (𝟙 B) rfl)
      (hq.lift (p₁ ≫ a) (p₂ ≫ a)
        (by simpa only [Category.assoc] using hp.w)) := by
  let d := hp.lift (𝟙 A) (𝟙 A) rfl
  let e := hq.lift (𝟙 B) (𝟙 B) rfl
  have hw : (p₁ ≫ a) ≫ f = (p₂ ≫ a) ≫ f := by
    simpa only [Category.assoc] using hp.w
  let i := hq.lift (p₁ ≫ a) (p₂ ≫ a) hw
  have hd₁ : d ≫ p₁ = 𝟙 A := hp.lift_fst _ _ _
  have hd₂ : d ≫ p₂ = 𝟙 A := hp.lift_snd _ _ _
  have he₁ : e ≫ q₁ = 𝟙 B := hq.lift_fst _ _ _
  have he₂ : e ≫ q₂ = 𝟙 B := hq.lift_snd _ _ _
  have hi₁ : i ≫ q₁ = p₁ ≫ a := hq.lift_fst _ _ _
  have hi₂ : i ≫ q₂ = p₂ ≫ a := hq.lift_snd _ _ _
  change IsPullback a d e i
  apply IsPullback.mk'
  · apply hq.hom_ext
    · rw [Category.assoc a, he₁, Category.comp_id, Category.assoc d, hi₁,
        ← Category.assoc d, hd₁, Category.id_comp]
    · rw [Category.assoc a, he₂, Category.comp_id, Category.assoc d, hi₂,
        ← Category.assoc d, hd₂, Category.id_comp]
  · intro _ _ _ hc _
    exact (cancel_mono a).1 hc
  · intro T x y hxy
    have hx₁ : x = (y ≫ p₁) ≫ a := by
      have h := congrArg (· ≫ q₁) hxy
      simpa only [Category.assoc, he₁, hi₁, Category.comp_id] using h
    have hx₂ : x = (y ≫ p₂) ≫ a := by
      have h := congrArg (· ≫ q₂) hxy
      simpa only [Category.assoc, he₂, hi₂, Category.comp_id] using h
    have hy : y ≫ p₁ = y ≫ p₂ := (cancel_mono a).1 (hx₁.symm.trans hx₂)
    refine ⟨y ≫ p₁, hx₁.symm, ?_⟩
    apply hp.hom_ext
    · simp only [Category.assoc, hd₁, Category.comp_id]
    · simpa only [Category.assoc, hd₂, Category.comp_id] using hy

private theorem diagonal_embedding_of_domainEtale
    {A X P : LocalizedCategory.{u, v, v} (K := K)}
    {f : A ⟶ X} {p q : P ⟶ A} (h : IsPullback p q f f)
    (hf : HasDomainEtaleFactorization f) :
    IsAnalyticDomainEmbedding (h.lift (𝟙 A) (𝟙 A) rfl) := by
  obtain ⟨W, a, w, ha, hw, rfl⟩ := hf
  let : Mono a := by
    obtain ⟨D, e, rfl⟩ := ha
    infer_instance
  let c := localizedEtalePullback w w hw
  have hc := IsPullback.of_isLimit c.2
  let d := hc.lift (𝟙 W) (𝟙 W) rfl
  obtain ⟨V, hV, e, he⟩ := openImmersion_etale_diagonal hc hw
  have hd : IsAnalyticDomainEmbedding d := ⟨(presentationOf c.1.pt).openDomain V hV, e, he.symm⟩
  exact hd.of_isPullback (isPullback_diagonal_of_domain_mono h hc)

set_option linter.defProp false in
/-- The diagonal of a compact quasi-étale source is an analytic-domain embedding. -/
def compactQuasiEtaleDiagonalDomain
    {B X Q : LocalizedCategory.{u, v, v} (K := K)} {b : B ⟶ X} {s t : Q ⟶ B}
    (h : IsPullback s t b b) (hB : IsCompactSpace B) (hb : quasiEtale b) :
    IsAnalyticDomainEmbedding (h.lift (𝟙 B) (𝟙 B) rfl) := by
  let : CompactSpace (localizedSpaceFunctor.obj B) := hB.1
  let : T2Space (localizedSpaceFunctor.obj B) := hB.2
  let U := MorphismProperty.Over.mk ⊤ b hb
  have : CompactSpace (localizedSpaceFunctor.obj U.left) := hB.1
  obtain ⟨C⟩ := exists_finiteCompactDomainChartCover U
  let d := h.lift (𝟙 B) (𝟙 B) rfl
  have hs : d ≫ s = 𝟙 B := h.lift_fst _ _ _
  have ht : d ≫ t = 𝟙 B := h.lift_snd _ _ _
  let D (i : C.Index) : (presentationOf B).AnalyticDomain := C.domain i
  let cover : FiniteCompactDomainEmbeddingCover d := {
    Index := C.Index
    finite := C.finite
    domain := D
    compact := fun i => (C.compact i).of_iso (C.domainIso i)
    covers := by
      intro x
      obtain ⟨i, y, hy⟩ := C.jointly_surjective x
      let eHom : (C.obj i).left ⟶ domainObj B (D i) := (C.domainIso i).hom
      have he : eHom ≫ domainι B (D i) = (C.arrow i).left :=
        C.domainIso_hom_inclusion i
      have hy' := congrArg (fun k : (C.obj i).left ⟶ B =>
        localizedSpaceFunctor.map k y) he
      rw [Functor.map_comp, TopCat.comp_app, domainι_apply] at hy'
      exact ⟨i, (hy'.trans hy) ▸ (localizedSpaceFunctor.map eHom y).property⟩
    embedding := by
      intro i
      let F := domainPreimage s (D i) ⊓ domainPreimage t (D i)
      let a := domainOrderMap (inf_le_left : F ≤ domainPreimage s (D i)) ≫
        domainPreimageMap s (D i)
      let c := domainOrderMap (inf_le_right : F ≤ domainPreimage t (D i)) ≫
        domainPreimageMap t (D i)
      have hF : IsPullback a c (domainι B (D i) ≫ b) (domainι B (D i) ≫ b) :=
        isPullback_domainPreimage_inf h (D i) (D i)
      have hf : HasDomainEtaleFactorization (domainι B (D i) ≫ b) :=
        C.domain_factorization i
      let dF := hF.lift (𝟙 _) (𝟙 _) rfl
      have ha : dF ≫ a = 𝟙 _ := hF.lift_fst _ _ _
      have hc : dF ≫ c = 𝟙 _ := hF.lift_snd _ _ _
      have ha' : a ≫ domainι B (D i) = domainι Q F ≫ s := by
        simp only [a, Category.assoc, domainPreimageMap_comp_inclusion,
          domainOrderMap_comp_inclusion_assoc]
        rfl
      have hc' : c ≫ domainι B (D i) = domainι Q F ≫ t := by
        simp only [c, Category.assoc, domainPreimageMap_comp_inclusion,
          domainOrderMap_comp_inclusion_assoc]
        rfl
      have hcomm : dF ≫ domainι Q F = domainι B (D i) ≫ d := by
        apply h.hom_ext
        · rw [Category.assoc, ← ha', ← Category.assoc dF, ha, Category.id_comp,
            Category.assoc, hs, Category.comp_id]
        · rw [Category.assoc, ← hc', ← Category.assoc dF, hc, Category.id_comp,
            Category.assoc, ht, Category.comp_id]
      exact hcomm ▸ (diagonal_embedding_of_domainEtale hF hf).comp
        (isAnalyticDomainEmbedding_domainι Q F) }
  exact cover.isAnalyticDomainEmbedding s hs

end Langlands.Analytic.SaturatedAtlasPresentation
