import Langlands.Geometry.Analytic.DomainEtaleFactorizations
import Langlands.Geometry.Analytic.LocalizedEtalePullbackExistence

/-! # Pullbacks along domains of étale spaces -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Restrict the first factor of an analytic pullback to a domain by taking
its inverse image along the first projection. -/
theorem isPullback_domainPreimage_comp
    {A B X P : LocalizedCategory.{u, v, w} (K := K)}
    {f : A ⟶ X} {g : B ⟶ X} {p : P ⟶ A} {q : P ⟶ B}
    (h : IsPullback p q f g) (D : (presentationOf A).AnalyticDomain) :
    IsPullback (domainPreimageMap p D) (domainι P (domainPreimage p D) ≫ q)
      (domainι A D ≫ f) g :=
  (domainPreimage_isPullback p D).flip.paste_vert h

/-- Pull back an analytic domain embedding in an étale space by restricting
the actual pullback of the étale space. -/
def domainEtalePullback
    {A B X : LocalizedCategory.{u, v, v} (K := K)}
    (f : A ⟶ X) (g : B ⟶ X) (hf : HasDomainEtaleFactorization f) :
    Σ c : PullbackCone f g, IsLimit c :=
  Classical.choice (show Nonempty (Σ c : PullbackCone f g, IsLimit c) from by
    obtain ⟨W, _, w, ⟨D, e, rfl⟩, hw, rfl⟩ := hf
    let t := localizedEtalePullback w g hw
    let a := domainPreimageMap t.1.fst D
    let b := domainι t.1.pt (domainPreimage t.1.fst D) ≫ t.1.snd
    have h : IsPullback a b (domainι W D ≫ w) g :=
      isPullback_domainPreimage_comp (IsPullback.of_isLimit t.2) D
    have h' : IsPullback (a ≫ e.inv) b ((e.hom ≫ domainι W D) ≫ w) g := by
      apply h.of_iso' (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      · simp
      · simp
      · simp [Category.assoc]
      · simp
    exact ⟨⟨PullbackCone.mk (a ≫ e.inv) b h'.w, h'.isLimit⟩⟩)

end Langlands.Analytic.SaturatedAtlasPresentation
