import Langlands.AlgebraicGeometry.SchemeFilteredModelExistenceProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitUniquenessStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyUniqueness
import Mathlib.CategoryTheory.Filtered.Final

/-! # Scheme models and eventual scheme representation at affine limits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A scheme-model cartesian square identifies its represented top-left
corner with the base change of its represented top-right corner. -/
def schemeModelBaseChangeIso {S T : Scheme.{u}} (p : T ⟶ S)
    (U : Over T) (V : Over S) (π : U.left ⟶ V.left)
    (hpb : IsPullback π U.hom V.hom p) :
    (schemeToSpace T).obj U ≅ baseChange p ((schemeToSpace S).obj V) :=
  (schemeToSpace T).mapIso (Over.isoMk hpb.isoPullback hpb.isoPullback_hom_snd) ≪≫
    baseChangeSchemeIso p V

/-- A finitely presented scheme over a cofiltered affine scheme limit has a
finitely presented scheme model at a stage of the original diagram. -/
theorem exists_schemeModel_of_affineLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (U : Over c.pt)
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom] [QuasiSeparated U.hom] :
    ∃ (j : I) (Uj : Over (D.obj j)) (π : U.left ⟶ Uj.left),
      LocallyOfFinitePresentation Uj.hom ∧ QuasiCompact Uj.hom ∧
      QuasiSeparated Uj.hom ∧ IsPullback π U.hom Uj.hom (c.π.app j) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have (i : Iᵒᵖ) : IsAffine (D.op.obj i).unop := by dsimp; infer_instance
  let F := D.op ⋙ Scheme.Γ
  let d := Scheme.Γ.mapCocone c.op
  have hd : IsColimit d := isColimitOfPreserves Scheme.Γ hc.op
  obtain ⟨j, V, g, π, hg, hqc, hqs, hpb⟩ :=
    SchemeLimitModel.schemeFilteredModelExistence Iᵒᵖ F d hd U.left
      (U.hom ≫ c.pt.isoSpec.hom)
  let := hg
  let := hqc
  let := hqs
  let Uj : Over (D.obj j.unop) := Over.mk (g ≫ (D.obj j.unop).isoSpec.inv)
  refine ⟨j.unop, Uj, π, ?_, ?_, ?_, ?_⟩
  · change LocallyOfFinitePresentation (g ≫ (D.obj j.unop).isoSpec.inv)
    infer_instance
  · change QuasiCompact (g ≫ (D.obj j.unop).isoSpec.inv)
    infer_instance
  · change QuasiSeparated (g ≫ (D.obj j.unop).isoSpec.inv)
    infer_instance
  apply hpb.of_iso (Iso.refl _) (Iso.refl _) c.pt.isoSpec.symm
    (D.obj j.unop).isoSpec.symm
  · simp
  · simp
  · simp [Uj]
  · simpa [F, d] using
      (Scheme.isoSpec_inv_naturality
        (X := c.pt) (Y := D.obj j.unop) (c.π.app j.unop))

/-- Under essential uniqueness of algebraic-space models, a finitely
presented space whose limit base change is a finitely presented scheme
is represented by a finitely presented scheme after a later base change. -/
theorem exists_schemeRepresentation_of_limit_of_modelUniqueness
    (huni : SpaceLimitModelUniqueness.{u})
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I) (X : AlgebraicSpace (D.obj i))
    (hXqs : IsQuasiSeparated X)
    (hXfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (U : Over c.pt)
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom] [QuasiSeparated U.hom]
    (e : baseChange (c.π.app i) X ≅ (schemeToSpace c.pt).obj U) :
    ∃ (j : I) (r : j ⟶ i) (V : Over (D.obj j)),
      LocallyOfFinitePresentation V.hom ∧ QuasiCompact V.hom ∧
      QuasiSeparated V.hom ∧ Nonempty (baseChange (D.map r) X ≅
        (schemeToSpace (D.obj j)).obj V) := by
  let E := Over.forget i ⋙ D
  have (j : Over i) : IsAffine (E.obj j) := by dsimp [E]; infer_instance
  let c' := c.whisker (Over.forget i)
  have hc' : IsLimit c' :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  obtain ⟨j, V, π, hVfp, hVqc, hVqs, hpb⟩ :=
    exists_schemeModel_of_affineLimit E c' hc' U
  let := hVfp
  let := hVqc
  let := hVqs
  let Xj := baseChange (D.map j.hom) X
  let Yj := (schemeToSpace (D.obj j.left)).obj V
  have hXjqs : IsQuasiSeparated Xj := hXqs.baseChange
  have hXjfp : HasAtlasProperty
      (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Xj :=
    hXfp.baseChange
  have hYjqs : IsQuasiSeparated Yj := isQuasiSeparated_schemeToSpace V
  have hYjfp : HasAtlasProperty
      (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Yj :=
    HasAtlasProperty.of_scheme V ⟨hVfp, hVqc⟩
  let ej : baseChange (c.π.app j.left) Xj ≅
      baseChange (c.π.app j.left) Yj :=
    BaseChangeComparison.compIso (D.map j.hom) (c.π.app j.left)
      (c.π.app i) (c.w j.hom) X ≪≫ e ≪≫
      schemeModelBaseChangeIso (c.π.app j.left) U V π hpb
  obtain ⟨k, r, h, _⟩ :=
    (huni I D c hc j.left Xj Yj hXjqs hXjfp hYjqs hYjfp ej).1
  let W := (Over.pullback (D.map r)).obj V
  refine ⟨k, r ≫ j.hom, W, ?_, ?_, ?_, ⟨?_⟩⟩
  · change LocallyOfFinitePresentation (pullback.snd V.hom (D.map r))
    infer_instance
  · change QuasiCompact (pullback.snd V.hom (D.map r))
    infer_instance
  · change QuasiSeparated (pullback.snd V.hom (D.map r))
    infer_instance
  exact (BaseChangeComparison.compIso (D.map j.hom) (D.map r)
    (D.map (r ≫ j.hom)) (D.map_comp r j.hom).symm X).symm ≪≫ h ≪≫
    (baseChangeSchemeIso (D.map r) V).symm

end Langlands.AlgebraicGeometry.AlgebraicSpace
