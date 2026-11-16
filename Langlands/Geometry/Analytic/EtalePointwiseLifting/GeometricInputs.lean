import Langlands.Geometry.Analytic.EtalePointwiseLifting.Statement
import Langlands.Geometry.Analytic.SaturatedLocalizedFractions

/-! # Geometric inputs and fraction transport for pointwise étale lifting -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Composition and right cancellation for the actual localized étale
predicate. These are geometric statements, without proofs here. -/
def LocalizedEtaleStabilityStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  MorphismProperty.IsStableUnderComposition
      (etale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))) ∧
    MorphismProperty.HasOfPostcompProperty
      (etale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K)))
      (etale (K := K))

/-- A point-dependent strong-map form of étale base change. The witnesses
are actual saturated presentations and strong maps, in the original space
and index universe. No universal property or Hausdorff hypothesis is imposed.
This is a geometric statement, without a proof here. -/
def StrongEtalePointwiseBaseChangeStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (A B C : SaturatedAtlasPresentation.{u, v, v} K) (f : A ⟶ C) (g : B ⟶ C),
    etale (localizationFunctor.map f) →
      ∀ (x : A.presentation.space) (y : B.presentation.space),
        f.baseMap x = g.baseMap y →
          ∃ (T : SaturatedAtlasPresentation.{u, v, v} K) (p : T ⟶ A) (q : T ⟶ B),
            p ≫ f = q ≫ g ∧ etale (localizationFunctor.map q) ∧
              ∃ t : T.presentation.space, p.baseMap t = x ∧ q.baseMap t = y

/-- The two geometric inputs used by the implemented site assembly. -/
def EtalePointwiseLiftingGeometricInputsStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  LocalizedEtaleStabilityStatement.{u, v} K ∧
    StrongEtalePointwiseBaseChangeStatement.{u, v} K

/-- Strong-map pointwise étale base change suffices for arbitrary localized
arrows. The denominators of both fractions transport the prescribed points;
the commuting equation retains equality of complete morphisms. -/
theorem exists_localized_etale_pointwise_square_of_strong
    (hbase : StrongEtalePointwiseBaseChangeStatement.{u, v} K)
    {A B C : LocalizedCategory.{u, v, v} (K := K)} (f : A ⟶ C) (g : B ⟶ C)
    (hf : etale f) (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B)
    (hxy : localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y) :
    ∃ (T : LocalizedCategory.{u, v, v} (K := K)) (p : T ⟶ A) (q : T ⟶ B),
      p ≫ f = q ≫ g ∧ etale q ∧
        ∃ t : localizedSpaceFunctor.obj T,
          localizedSpaceFunctor.map p t = x ∧ localizedSpaceFunctor.map q t = y := by
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective A
  obtain ⟨B, rfl⟩ := localizedObjectEquiv.surjective B
  obtain ⟨C, rfl⟩ := localizedObjectEquiv.surjective C
  simp only [localizedObjectEquiv_apply] at *
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  obtain ⟨ψ, rfl⟩ := exists_localizedRightFraction g
  have hφs : localizationFunctor.map φ.s ≫ localizedRightFraction φ =
      localizationFunctor.map φ.f := by
    change (localizedQuasiIso φ.s φ.hs).hom ≫
      (localizedQuasiIso φ.s φ.hs).inv ≫ localizationFunctor.map φ.f = _
    exact Iso.hom_inv_id_assoc _ _
  have hψs : localizationFunctor.map ψ.s ≫ localizedRightFraction ψ =
      localizationFunctor.map ψ.f := by
    change (localizedQuasiIso ψ.s ψ.hs).hom ≫
      (localizedQuasiIso ψ.s ψ.hs).inv ≫ localizationFunctor.map ψ.f = _
    exact Iso.hom_inv_id_assoc _ _
  have hφ : etale (localizationFunctor.map φ.f) := by
    have h := MorphismProperty.RespectsIso.precomp (etale (K := K))
      (localizedQuasiIso φ.s φ.hs).hom (localizedRightFraction φ) hf
    simpa [localizedRightFraction] using h
  have hxy' : φ.f.baseMap (φ.hs.inverseBaseMap x) =
      ψ.f.baseMap (ψ.hs.inverseBaseMap y) := by
    rw [localizedSpaceFunctor_map_rightFraction, localizedSpaceFunctor_map_rightFraction] at hxy
    exact hxy
  obtain ⟨T, p, q, hpq, hq, t, hpt, hqt⟩ :=
    hbase φ.X' ψ.X' C φ.f ψ.f hφ _ _ hxy'
  refine ⟨localizationFunctor.obj T,
    localizationFunctor.map p ≫ localizationFunctor.map φ.s,
    localizationFunctor.map q ≫ localizationFunctor.map ψ.s, ?_, ?_, t, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [hφs, hψs, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg localizationFunctor.map hpq
  · exact MorphismProperty.RespectsIso.postcomp (etale (K := K))
      (localizedQuasiIso ψ.s ψ.hs).hom (localizationFunctor.map q) hq
  · rw [← Functor.map_comp, localizedSpaceFunctor_map]
    change φ.s.baseMap (p.baseMap t) = x
    exact (congrArg φ.s.baseMap hpt).trans (φ.hs.baseMap_inverseBaseMap x)
  · rw [← Functor.map_comp, localizedSpaceFunctor_map]
    change ψ.s.baseMap (q.baseMap t) = y
    exact (congrArg ψ.s.baseMap hqt).trans (ψ.hs.baseMap_inverseBaseMap y)

/-- An arrow between two actual étale objects over a base is étale,
assuming localized right cancellation. -/
theorem etale_site_arrow_of_stability
    (hstable : LocalizedEtaleStabilityStatement.{u, v} K)
    {X : LocalizedCategory.{u, v, v} (K := K)} {U W : EtaleSite X} (f : U ⟶ W) :
    etale f.left := by
  have := hstable.2
  apply (etale (K := K)).of_postcomp f.left W.hom W.prop
  simpa only [MorphismProperty.Over.w] using U.prop

/-- Fraction transport and the over-category constructors assemble the two
geometric inputs into the unrestricted pointwise-lifting target. -/
theorem etalePointwiseLifting_of_geometricInputs
    (h : EtalePointwiseLiftingGeometricInputsStatement.{u, v} K) :
    EtalePointwiseLiftingStatement.{u, v} K := by
  have := h.1.1
  intro X U V W f g x y hxy
  have hf : etale f.left := etale_site_arrow_of_stability h.1 f
  obtain ⟨T, p, q, hpq, hq, t, hpt, hqt⟩ :=
    exists_localized_etale_pointwise_square_of_strong h.2 f.left g.left hf x y hxy
  let T' : EtaleSite X := MorphismProperty.Over.mk ⊤ (q ≫ V.hom)
    ((etale (K := K)).comp_mem q V.hom hq V.prop)
  have hp : p ≫ U.hom = q ≫ V.hom := by
    rw [← MorphismProperty.Over.w f, ← MorphismProperty.Over.w g,
      ← Category.assoc, ← Category.assoc, hpq]
  let p' : T' ⟶ U := MorphismProperty.Over.homMk p hp
  let q' : T' ⟶ V := MorphismProperty.Over.homMk q
  refine ⟨T', p', q', ?_, t, hpt, hqt⟩
  apply MorphismProperty.Over.Hom.ext
  exact hpq

end Langlands.Analytic.SaturatedAtlasPresentation
