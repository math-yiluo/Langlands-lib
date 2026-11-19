import Langlands.Geometry.Analytic.StrongEtaleLocalAgreement
import Langlands.Geometry.Analytic.AnalyticSectionLocality
import Langlands.Geometry.Analytic.OpenImmersionFieldPointLifting
import Langlands.Geometry.Analytic.FieldPointChartExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCompletedResidueProof

/-! # Sections of analytic étale maps are open immersions -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set Topology AffinoidAtlasPresentation PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem exists_completedResidue_fieldPoint
    (A : SaturatedAtlasPresentation.{u, v, v} K) (x : A.presentation.space) :
    ∃ (i : A.presentation.atlas.Index) (t : BanachSpectrum (A.presentation.atlas.algebra i)),
      ∃ p : FieldPoint (BanachSpectrum.CompletedResidueField K t) A.presentation, p.point = x := by
  obtain ⟨i, t, ht⟩ := A.presentation.atlas.exists_mem_range_chart x
  obtain ⟨p, ⟨hp, -⟩, -⟩ := FieldPoint.existsUnique_of_chartCharacter
    domainCompletedResidueSurjectivity x i (BanachSpectrum.completedResidueMap K t).toAlgHom
    ⟨t, ht, BanachSpectrum.norm_completedResidueMap K t⟩
  exact ⟨i, t, p, hp⟩

private theorem exists_open_eq_of_strongEtale
    {T : SaturatedAtlasPresentation.{u, v, v} K} {A B : AffinoidAtlasPresentation.{u, v, v} K}
    {L : Type uL} [NormedField L] [NormedAlgebra K L]
    (f : ofSaturation A ⟶ ofSaturation B) (hf : f.IsEtaleAllPieces)
    (a b : localizationFunctor.obj T ⟶ localizationFunctor.obj (ofSaturation A))
    (hab : a ≫ localizationFunctor.map f = b ≫ localizationFunctor.map f)
    (p : FieldPoint L T.presentation)
    (hp : (localizedFieldPointFunctor L).map a p = (localizedFieldPointFunctor L).map b p) :
    ∃ (O : Set T.presentation.space) (hO : IsOpen O), p.point ∈ O ∧
      T.localizedDomainInclusion (T.openDomain O hO) ≫ a =
        T.localizedDomainInclusion (T.openDomain O hO) ≫ b := by
  obtain ⟨S, s, hs, a₀, b₀, ha₀, hb₀, h₀⟩ := exists_commutingStrongNumerators f f a b hab
  let E := ofSaturation S.presentation
  let a' : E ⟶ ofSaturation A := S.saturationIso.hom ≫ a₀
  let b' : E ⟶ ofSaturation A := S.saturationIso.hom ≫ b₀
  let e : localizationFunctor.obj E ≅ localizationFunctor.obj T :=
    localizationFunctor.mapIso S.saturationIso ≪≫ localizedQuasiIso s hs
  have ha : e.hom ≫ a = localizationFunctor.map a' := by
    change (localizationFunctor.map S.saturationIso.hom ≫ localizationFunctor.map s) ≫ a = _
    rw [Category.assoc, ha₀]
    exact (Functor.map_comp localizationFunctor _ _).symm
  have hb : e.hom ≫ b = localizationFunctor.map b' := by
    change (localizationFunctor.map S.saturationIso.hom ≫ localizationFunctor.map s) ≫ b = _
    rw [Category.assoc, hb₀]
    exact (Functor.map_comp localizationFunctor _ _).symm
  have h' : a' ≫ f = b' ≫ f := by
    simp only [a', b', Category.assoc, h₀]
  let F : LocalizedCategory.{u, v, v} (K := K) ⥤ Type (max u v uL) :=
    localizedFieldPointFunctor L
  let p₀ : F.obj (localizationFunctor.obj T) := p
  let q : FieldPoint L E.presentation := F.map e.inv p₀
  have hqp : F.map e.hom q = p₀ := Iso.inv_hom_id_apply (F.mapIso e) p₀
  have hq : q.map a' E.hasAllLocalDomains = q.map b' E.hasAllLocalDomains := by
    change F.map (localizationFunctor.map a') q = F.map (localizationFunctor.map b') q
    rw [← ha, ← hb, Functor.map_comp_apply, Functor.map_comp_apply, hqp]
    exact hp
  obtain ⟨_, _, hy, hpieces⟩ := hf (a'.baseMap q.point)
  obtain ⟨O, hO, hqO, heq⟩ := exists_open_eq_of_unramifiedAtAllPieces a' b' f h' q hq
    (hpieces _ hy).1
  let O' : Set T.presentation.space := localizedSpaceFunctor.map e.inv ⁻¹' O
  have hO' : IsOpen O' := hO.preimage (localizedSpaceFunctor.map e.inv).hom.continuous
  have hpO : p.point ∈ O' := by
    have h := localizedFieldPointProjection_map_down e.inv p
    change q.point = localizedSpaceFunctor.map e.inv p.point at h
    change localizedSpaceFunctor.map e.inv p.point ∈ O
    exact h ▸ hqO
  let j := E.localizedDomainInclusion (E.openDomain O hO)
  let j' := T.localizedDomainInclusion (T.openDomain O' hO')
  let c : localizationFunctor.obj (E.domain (E.openDomain O hO)) ≅
      localizationFunctor.obj (T.domain (T.openDomain O' hO')) := openDomainIso e O hO
  have hc : c.hom ≫ j' = j ≫ e.hom := openDomainIso_hom_domainι e O hO
  refine ⟨O', hO', hpO, (cancel_epi c.hom).1 ?_⟩
  change c.hom ≫ (j' ≫ a) = c.hom ≫ (j' ≫ b)
  calc
    c.hom ≫ (j' ≫ a) = (j ≫ e.hom) ≫ a :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ a) hc)
    _ = j ≫ localizationFunctor.map a' :=
      (Category.assoc _ _ _).trans (congrArg (j ≫ ·) ha)
    _ = j ≫ localizationFunctor.map b' := heq
    _ = (j ≫ e.hom) ≫ b :=
      (congrArg (j ≫ ·) hb.symm).trans (Category.assoc _ _ _).symm
    _ = c.hom ≫ (j' ≫ b) := (congrArg (· ≫ b) hc.symm).trans (Category.assoc _ _ _)

private theorem openImmersion_of_section_of_strongEtale
    {A B : AffinoidAtlasPresentation.{u, v, v} K}
    (f : ofSaturation A ⟶ ofSaturation B) (hf : f.IsEtaleAllPieces)
    (s : localizationFunctor.obj (ofSaturation B) ⟶ localizationFunctor.obj (ofSaturation A))
    (hs : s ≫ localizationFunctor.map f = 𝟙 _) : openImmersion s := by
  let X := localizationFunctor.obj (ofSaturation A)
  let Y := localizationFunctor.obj (ofSaturation B)
  let g : X ⟶ Y := localizationFunctor.map f
  let r := g ≫ s
  have hs' : s ≫ g = 𝟙 Y := hs
  have hrg : r ≫ g = (𝟙 X) ≫ g := by
    simp only [r, Category.assoc, hs', Category.comp_id, Category.id_comp]
  apply openImmersion_of_section_locallyFixed hs
  rintro y ⟨x, rfl⟩
  obtain ⟨i, t, p, hp⟩ := exists_completedResidue_fieldPoint (ofSaturation B) x
  let L := BanachSpectrum.CompletedResidueField K t
  let F : LocalizedCategory.{u, v, v} (K := K) ⥤ Type (max u v) :=
    localizedFieldPointFunctor L
  let p₀ : F.obj Y := p
  let q : FieldPoint L (ofSaturation A).presentation := F.map s p₀
  have hq : q.point = localizedSpaceFunctor.map s x := by
    have h := localizedFieldPointProjection_map_down s p
    change q.point = localizedSpaceFunctor.map s p.point at h
    exact h.trans (congrArg (localizedSpaceFunctor.map s) hp)
  have hqr : F.map r q = F.map (𝟙 X) q := by
    have h : s ≫ r = s := (Category.assoc s g s).symm.trans
      ((congrArg (· ≫ s) hs').trans (Category.id_comp s))
    change F.map r (F.map s p₀) = F.map (𝟙 X) (F.map s p₀)
    calc
      _ = F.map (s ≫ r) p₀ := (Functor.map_comp_apply F s r p₀).symm
      _ = F.map s p₀ := congrArg (fun k : Y ⟶ X => F.map k p₀) h
      _ = _ := (congrArg (fun k : F.obj X ⟶ F.obj X => k (F.map s p₀)) (F.map_id X)).symm
  obtain ⟨O, hO, hqO, hloc⟩ := exists_open_eq_of_strongEtale f hf r (𝟙 X) hrg q hqr
  exact ⟨O, hO, hq ▸ hqO, hloc.trans (Category.comp_id _)⟩

set_option linter.defProp false in
/-- A section of any localized étale morphism is an analytic open immersion. -/
def localizedEtaleSectionsOpen
    {X Y : LocalizedCategory.{u, v, v} (K := K)} {f : X ⟶ Y} {s : Y ⟶ X}
    (hf : etale f) (hsf : s ≫ f = 𝟙 Y) : openImmersion s := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  let a : localizationFunctor.obj (ofSaturation A) ≅ X := Arrow.leftFunc.mapIso e
  let b : localizationFunctor.obj (ofSaturation B) ≅ Y := Arrow.rightFunc.mapIso e
  let s' := b.hom ≫ s ≫ a.inv
  have ha : a.inv ≫ localizationFunctor.map g = f ≫ b.inv := e.inv.w
  have hs' : s' ≫ localizationFunctor.map g = 𝟙 _ := by
    dsimp only [s']
    rw [Category.assoc, Category.assoc, ha, ← Category.assoc s, hsf, Category.id_comp, b.hom_inv_id]
  have ho := openImmersion_of_section_of_strongEtale g hg s' hs'
  have h₁ : openImmersion (b.inv ≫ s') :=
    MorphismProperty.RespectsIso.precomp openImmersion b.inv s' ho
  have h₂ : openImmersion ((b.inv ≫ s') ≫ a.hom) :=
    MorphismProperty.RespectsIso.postcomp openImmersion a.hom _ h₁
  simpa only [s', Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    using h₂

private theorem exists_open_eq_of_etale
    {T : SaturatedAtlasPresentation.{u, v, v} K}
    {A B : LocalizedCategory.{u, v, v} (K := K)}
    {L : Type uL} [NormedField L] [NormedAlgebra K L]
    (f : A ⟶ B) (hf : etale f) (a b : localizationFunctor.obj T ⟶ A)
    (hab : a ≫ f = b ≫ f)
    (p : FieldPoint L T.presentation)
    (hp : (localizedFieldPointFunctor L).map a p = (localizedFieldPointFunctor L).map b p) :
    ∃ (O : Set T.presentation.space) (hO : IsOpen O), p.point ∈ O ∧
      T.localizedDomainInclusion (T.openDomain O hO) ≫ a =
        T.localizedDomainInclusion (T.openDomain O hO) ≫ b := by
  obtain ⟨A₀, B₀, g, hg, ⟨e⟩⟩ := hf
  let α : localizationFunctor.obj (ofSaturation A₀) ≅ A := Arrow.leftFunc.mapIso e
  let β : localizationFunctor.obj (ofSaturation B₀) ≅ B := Arrow.rightFunc.mapIso e
  let a₀ := a ≫ α.inv
  let b₀ := b ≫ α.inv
  have hw : α.inv ≫ localizationFunctor.map g = f ≫ β.inv := e.inv.w
  have hab₀ : a₀ ≫ localizationFunctor.map g = b₀ ≫ localizationFunctor.map g := by
    dsimp only [a₀, b₀]
    rw [Category.assoc, Category.assoc, hw, ← Category.assoc a, ← Category.assoc b, hab]
  let F : LocalizedCategory.{u, v, v} (K := K) ⥤ Type (max u v uL) :=
    localizedFieldPointFunctor L
  let p₀ : F.obj (localizationFunctor.obj T) := p
  have hp₀ : F.map a₀ p₀ = F.map b₀ p₀ := by
    dsimp only [a₀, b₀]
    exact (Functor.map_comp_apply F a α.inv p₀).trans
      ((congrArg (F.map α.inv) hp).trans (Functor.map_comp_apply F b α.inv p₀).symm)
  obtain ⟨O, hO, hx, h⟩ := exists_open_eq_of_strongEtale g hg a₀ b₀ hab₀ p hp₀
  refine ⟨O, hO, hx, (cancel_mono α.inv).1 ?_⟩
  simpa only [a₀, b₀, ← Category.assoc] using h

set_option linter.defProp false in
/-- The diagonal of a localized étale morphism into any limiting
self-pullback is an open immersion. -/
def openImmersion_etale_diagonal
    {A X P : LocalizedCategory.{u, v, v} (K := K)}
    {f : A ⟶ X} {p q : P ⟶ A} (h : IsPullback p q f f) (hf : etale f) :
    openImmersion (h.lift (𝟙 A) (𝟙 A) rfl) := by
  obtain ⟨S, rfl⟩ := localizedObjectEquiv.surjective A
  obtain ⟨T, rfl⟩ := localizedObjectEquiv.surjective P
  let A := localizationFunctor.obj S
  let P := localizationFunctor.obj T
  let d : A ⟶ P := h.lift (𝟙 A) (𝟙 A) rfl
  have hdp : d ≫ p = 𝟙 A := h.lift_fst _ _ _
  have hdq : d ≫ q = 𝟙 A := h.lift_snd _ _ _
  apply openImmersion_of_section_locallyFixed hdp
  rintro y ⟨x, rfl⟩
  obtain ⟨i, t, z, hz⟩ := exists_completedResidue_fieldPoint S x
  let L := BanachSpectrum.CompletedResidueField K t
  let F : LocalizedCategory.{u, v, v} (K := K) ⥤ Type (max u v) :=
    localizedFieldPointFunctor L
  let z₀ : F.obj A := z
  let w : FieldPoint L T.presentation := F.map d z₀
  have hw : w.point = localizedSpaceFunctor.map d x := by
    have hh := localizedFieldPointProjection_map_down d z
    change w.point = localizedSpaceFunctor.map d z.point at hh
    exact hh.trans (congrArg (localizedSpaceFunctor.map d) hz)
  have hpq : F.map p w = F.map q w :=
    (Functor.map_comp_apply F d p z₀).symm.trans
      ((congrArg (fun a : A ⟶ A => F.map a z₀) (hdp.trans hdq.symm)).trans
        (Functor.map_comp_apply F d q z₀))
  obtain ⟨O, hO, hx, heq⟩ := exists_open_eq_of_etale f hf p q h.w w hpq
  let j := T.localizedDomainInclusion (T.openDomain O hO)
  refine ⟨O, hO, hw ▸ hx, ?_⟩
  change j ≫ (p ≫ d) = j
  apply h.hom_ext
  · calc
      (j ≫ (p ≫ d)) ≫ p = (j ≫ p) ≫ (d ≫ p) :=
        (congrArg (· ≫ p) (Category.assoc j p d).symm).trans (Category.assoc (j ≫ p) d p)
      _ = j ≫ p := (congrArg ((j ≫ p) ≫ ·) hdp).trans (Category.comp_id _)
  · calc
      (j ≫ (p ≫ d)) ≫ q = (j ≫ p) ≫ (d ≫ q) :=
        (congrArg (· ≫ q) (Category.assoc j p d).symm).trans (Category.assoc (j ≫ p) d q)
      _ = j ≫ p := (congrArg ((j ≫ p) ≫ ·) hdq).trans (Category.comp_id _)
      _ = j ≫ q := heq

end Langlands.Analytic.SaturatedAtlasPresentation
