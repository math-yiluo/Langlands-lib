import Langlands.Geometry.Analytic.QuasiEtaleDomainChartCover
import Langlands.Geometry.Analytic.QuasiEtalePullbackSmallness
import Langlands.Geometry.Analytic.SmallPullbackAction

/-! # Continuity on localized pullbacks along a quasi-étale leg -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G]

section Transport

variable {A B A' : LocalizedCategory.{u, v, v} (K := K)}

private theorem conjAut_hom_eq (e : A ≅ A') (a : Aut A) :
    (e.conjAut a).asIso.hom = e.inv ≫ a.asIso.hom ≫ e.hom := by
  rw [Iso.conjAut_apply]
  rfl

private theorem equivariant_conjAut_source
    (e : A ≅ A') (p : A ⟶ B) (p' : A' ⟶ B)
    (he : e.hom ≫ p' = p) (a : Aut A) (b : Aut B)
    (h : a.asIso.hom ≫ p = p ≫ b.asIso.hom) :
    (e.conjAut a).asIso.hom ≫ p' = p' ≫ b.asIso.hom := by
  calc
    (e.conjAut a).asIso.hom ≫ p' = e.inv ≫ (a.asIso.hom ≫ p) := by
      simp only [conjAut_hom_eq, Category.assoc, he]
    _ = e.inv ≫ (p ≫ b.asIso.hom) := congrArg (e.inv ≫ ·) h
    _ = p' ≫ b.asIso.hom := by rw [← he, Category.assoc, Iso.inv_hom_id_assoc]

/-- A continuous action transports through an equivariant analytic isomorphism. -/
theorem IsContinuousAction.of_equivariant_iso
    {σ : G →* Aut A} (hσ : IsContinuousAction σ) (e : A ≅ A') (σ' : G →* Aut A')
    (h : ∀ t, (σ t).asIso.hom ≫ e.hom = e.hom ≫ (σ' t).asIso.hom) :
    IsContinuousAction σ' := by
  have he : e.conjAut.toMonoidHom.comp σ = σ' := by
    apply MonoidHom.ext
    intro t
    apply Aut.ext
    apply Iso.ext
    change (e.conjAut (σ t)).asIso.hom = (σ' t).asIso.hom
    rw [conjAut_hom_eq, h, Iso.inv_hom_id_assoc]
  rw [← he]
  exact hσ.conjAut e

end Transport

section StrongCospan

variable {A B X : SaturatedAtlasPresentation.{u, v, v} K}
  (f : A ⟶ X) (g : B ⟶ X)
  [Small.{v} (FibreProduct.chartSystem (geometricCompatibleMap f) (geometricCompatibleMap g)).Space]
  {P : LocalizedCategory.{u, v, v} (K := K)}
  {p : P ⟶ localizationFunctor.obj A} {q : P ⟶ localizationFunctor.obj B}

/-- The comparison isomorphism from any supplied pullback of a mapped
strong cospan to the canonical small fibre product. -/
def smallFibreProductComparisonIso
    (hP : IsPullback p q (localizationFunctor.map f) (localizationFunctor.map g)) :
    P ≅ localizationFunctor.obj (smallFibreProduct f g) :=
  hP.isoIsPullback _ _ (smallFibreProduct_isPullback f g)

/-- The continuity result for the canonical small strong model applies
to every supplied pullback of the mapped strong cospan. -/
theorem isContinuousAction_of_isPullback_of_smallFibreProduct
    (hP : IsPullback p q (localizationFunctor.map f) (localizationFunctor.map g))
    (σ : G →* Aut P) {σA : G →* Aut (localizationFunctor.obj A)}
    {σB : G →* Aut (localizationFunctor.obj B)}
    (hA : IsContinuousAction σA) (hB : IsContinuousAction σB)
    (hp : ∀ t, (σ t).asIso.hom ≫ p = p ≫ (σA t).asIso.hom)
    (hq : ∀ t, (σ t).asIso.hom ≫ q = q ≫ (σB t).asIso.hom) :
    IsContinuousAction σ := by
  let e := smallFibreProductComparisonIso f g hP
  let p' := localizationFunctor.map (smallFibreProductFst f g)
  let q' := localizationFunctor.map (smallFibreProductSnd f g)
  let σ' := e.conjAut.toMonoidHom.comp σ
  have ep : e.hom ≫ p' = p :=
    hP.isoIsPullback_hom_fst _ _ (smallFibreProduct_isPullback f g)
  have eq : e.hom ≫ q' = q :=
    hP.isoIsPullback_hom_snd _ _ (smallFibreProduct_isPullback f g)
  have hp' (t : G) : (σ' t).asIso.hom ≫ p' = p' ≫ (σA t).asIso.hom :=
    equivariant_conjAut_source e p p' ep (σ t) (σA t) (hp t)
  have hq' (t : G) : (σ' t).asIso.hom ≫ q' = q' ≫ (σB t).asIso.hom :=
    equivariant_conjAut_source e q q' eq (σ t) (σB t) (hq t)
  have hc := isContinuousAction_smallFibreProduct f g σ' σA σB hA hB hp' hq'
  apply hc.of_equivariant_iso e.symm σ
  intro t
  change (e.conjAut (σ t)).asIso.hom ≫ e.inv = e.inv ≫ (σ t).asIso.hom
  rw [conjAut_hom_eq]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end StrongCospan

section LocalizedCospan

variable {P A B X : LocalizedCategory.{u, v, v} (K := K)}
  {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
  {σ : G →* Aut P} {σA : G →* Aut A} {σB : G →* Aut B}

omit [TopologicalSpace G] in
private theorem equivariant_comp_conjAut {A' : LocalizedCategory.{u, v, v} (K := K)}
    (e : A ≅ A') (hp : ∀ t, (σ t).asIso.hom ≫ p = p ≫ (σA t).asIso.hom) (t : G) :
    (σ t).asIso.hom ≫ (p ≫ e.hom) = (p ≫ e.hom) ≫ (e.conjAut (σA t)).asIso.hom := by
  rw [conjAut_hom_eq, ← Category.assoc (σ t).asIso.hom p, hp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem isContinuousAction_of_isPullback_of_strongQuasiEtale
    {C D : AffinoidAtlasPresentation.{u, v, v} K}
    {E : SaturatedAtlasPresentation.{u, v, v} K}
    {f : ofSaturation C ⟶ ofSaturation D} {g : E ⟶ ofSaturation D}
    {p : P ⟶ localizationFunctor.obj (ofSaturation C)} {q : P ⟶ localizationFunctor.obj E}
    (hP : IsPullback p q (localizationFunctor.map f) (localizationFunctor.map g))
    (hf : IsQuasiEtale f)
    (σ : G →* Aut P)
    {σC : G →* Aut (localizationFunctor.obj (ofSaturation C))}
    {σE : G →* Aut (localizationFunctor.obj E)}
    (hC : IsContinuousAction σC) (hE : IsContinuousAction σE)
    (hp : ∀ t, (σ t).asIso.hom ≫ p = p ≫ (σC t).asIso.hom)
    (hq : ∀ t, (σ t).asIso.hom ≫ q = q ≫ (σE t).asIso.hom) :
    IsContinuousAction σ := by
  let F := recognitionMap f
  let H := recognitionMap g
  let : Small.{v} (FibreProduct.chartSystem (geometricCompatibleMap F) (geometricCompatibleMap H)).Space :=
    small_recognition_fibreProductSpace_of_domainEtaleCharts f g (by
      intro y
      obtain ⟨s, _, hn, hs⟩ := hf.exists_local_domainEtale_charts y
      obtain ⟨V, hV, hy⟩ := Set.mem_sUnion.mp (mem_of_mem_nhds hn)
      obtain ⟨i, hi, hfactor⟩ := hs V hV
      exact ⟨i, hi.symm ▸ hy,
        by simpa only [CategoryTheory.Functor.map_comp, localizedDomainInclusion] using hfactor⟩)
  let eC := recognitionSourceIso f
  let eE := recognitionSourceIso g
  let p' := p ≫ eC.hom
  let q' := q ≫ eE.hom
  have hP' : IsPullback p' q' (localizationFunctor.map F) (localizationFunctor.map H) := by
    apply hP.of_iso (Iso.refl _) eC eE (recognitionBaseIso (ofSaturation D))
    · simp [p']
    · simp [q']
    · exact (recognitionMap_localized_square f).symm
    · exact (recognitionMap_localized_square g).symm
  exact isContinuousAction_of_isPullback_of_smallFibreProduct F H hP' σ
    (hC.conjAut eC) (hE.conjAut eE)
    (equivariant_comp_conjAut eC hp) (equivariant_comp_conjAut eE hq)

/-- Any supplied localized pullback along a quasi-étale first leg has
a continuous action if both projections intertwine continuous actions. -/
theorem isContinuousAction_of_isPullback_of_quasiEtale
    (hP : IsPullback p q f g) (hf : quasiEtale f)
    (hA : IsContinuousAction σA) (hB : IsContinuousAction σB)
    (hp : ∀ t, (σ t).asIso.hom ≫ p = p ≫ (σA t).asIso.hom)
    (hq : ∀ t, (σ t).asIso.hom ≫ q = q ≫ (σB t).asIso.hom) :
    IsContinuousAction σ := by
  obtain ⟨A₀, X₀, f₀, hf₀, ⟨e⟩⟩ := hf
  let eA : localizationFunctor.obj (ofSaturation A₀) ≅ A := Arrow.leftFunc.mapIso e
  let eX : localizationFunctor.obj (ofSaturation X₀) ≅ X := Arrow.rightFunc.mapIso e
  obtain ⟨B₀, hB₀⟩ := localizedObjectEquiv.surjective B
  change localizationFunctor.obj B₀ = B at hB₀
  subst B
  obtain ⟨φ, hφ⟩ := exists_localizedRightFraction (g ≫ eX.inv)
  let eB := localizedQuasiIso φ.s φ.hs
  let p₀ := p ≫ eA.inv
  let q₀ := q ≫ eB.inv
  have hP₀ : IsPullback p₀ q₀ (localizationFunctor.map f₀) (localizationFunctor.map φ.f) := by
    apply hP.of_iso (Iso.refl _) eA.symm eB.symm eX.symm
    · simp [p₀]
    · simp [q₀]
    · change f ≫ eX.inv = eA.inv ≫ localizationFunctor.map f₀
      apply (cancel_epi eA.hom).1
      have hw : eA.hom ≫ f = localizationFunctor.map f₀ ≫ eX.hom := e.hom.w
      rw [← Category.assoc, hw, Category.assoc]
      simp
    · change g ≫ eX.inv = eB.inv ≫ localizationFunctor.map φ.f
      apply (cancel_epi eB.hom).1
      rw [hφ, Iso.hom_inv_id_assoc]
      exact localizationFunctor_map_s_comp_localizedRightFraction φ
  exact isContinuousAction_of_isPullback_of_strongQuasiEtale hP₀ hf₀ σ
    (hA.conjAut eA.symm) (hB.conjAut eB.symm)
    (equivariant_comp_conjAut eA.symm hp) (equivariant_comp_conjAut eB.symm hq)

end LocalizedCospan

end Langlands.Analytic.SaturatedAtlasPresentation
