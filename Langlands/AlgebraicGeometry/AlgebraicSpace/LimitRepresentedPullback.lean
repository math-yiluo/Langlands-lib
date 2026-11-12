import Langlands.AlgebraicGeometry.AlgebraicSpace.LimitSchemeRepresentation
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedSchemeFiniteness
import Langlands.AlgebraicGeometry.AlgebraicSpace.TargetAtlasLimitDescent

/-! # Eventual representations of actual pullbacks at affine limits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The finiteness hypotheses on a representing scheme at the limit follow
from the space hypotheses; only model uniqueness is an additional premise. -/
theorem exists_schemeRepresentation_of_presheafIso_of_modelUniqueness
    (huni : SpaceLimitModelUniqueness.{u})
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I) (X : AlgebraicSpace (D.obj i))
    (hXqs : IsQuasiSeparated X)
    (hXfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (U : Over c.pt)
    (e : (baseChange (c.π.app i) X).presheaf ≅ (schemeYoneda c.pt).obj U) :
    ∃ (j : I) (r : j ⟶ i) (V : Over (D.obj j)),
      LocallyOfFinitePresentation V.hom ∧ QuasiCompact V.hom ∧
      QuasiSeparated V.hom ∧ Nonempty ((baseChange (D.map r) X).presheaf ≅
        (schemeYoneda (D.obj j)).obj V) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  obtain ⟨hlfp, hqc, hqs⟩ :=
    schemeFiniteness_of_presheafIso (S := c.pt) (baseChange (c.π.app i) X)
      hXqs.baseChange hXfp.baseChange U e
  let := hlfp
  let := hqc
  let := hqs
  let e' : baseChange (c.π.app i) X ≅ (schemeToSpace c.pt).obj U :=
    { hom := homMk e.hom
      inv := homMk e.inv
      hom_inv_id := (homEquiv _ _).injective e.hom_inv_id
      inv_hom_id := (homEquiv _ _).injective e.inv_hom_id }
  obtain ⟨j, r, V, hVfp, hVqc, hVqs, ⟨eV⟩⟩ :=
    exists_schemeRepresentation_of_limit_of_modelUniqueness huni D c hc i X
      hXqs hXfp U e'
  exact ⟨j, r, V, hVfp, hVqc, hVqs, ⟨(forgetToPresheaf _).mapIso eV⟩⟩

variable {S T : Scheme.{u}} {X Y W : AlgebraicSpace S} {f : X ⟶ Y}
    {V : Over S}

/-- The actual represented pullback after base change identifies the
restriction of the supplied pullback square with its scheme model. -/
def baseChangePullbackSchemeIso
    (g : T ⟶ S) (b : (schemeYoneda S).obj V ⟶ Y.presheaf)
    (p : W.presheaf ⟶ X.presheaf) (q : W.presheaf ⟶ (schemeYoneda S).obj V)
    (h : IsPullback p q (hom f) b)
    (hf : IsRepresentableMorphism (hom (baseChangeMap g f))) :
    (baseChange g W).presheaf ≅
      (schemeYoneda T).obj (hf.pullback (restrictAtlas g b)) := by
  let b' := restrictAtlas g b
  let q' := (restrictPresheaf g).map q ≫ (schemeYonedaBaseChangeIso g V).inv
  have h' : IsPullback ((restrictPresheaf g).map p) q'
      (hom (baseChangeMap g f)) b' := by
    apply (h.map (restrictPresheaf g)).of_iso'
      (Iso.refl _) (Iso.refl _) (schemeYonedaBaseChangeIso g V) (Iso.refl _)
    · simp
    · simp [q']
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
    · simp [b', restrictAtlas]
  exact h'.isoIsPullback _ _ (hf.isPullback b')

/-- A represented limit morphism makes the limit of any actual pullback
along a scheme represented, with no representability assumption at a stage. -/
theorem exists_presheafIso_of_representable_baseChange
    (g : T ⟶ S) (b : (schemeYoneda S).obj V ⟶ Y.presheaf)
    (p : W.presheaf ⟶ X.presheaf) (q : W.presheaf ⟶ (schemeYoneda S).obj V)
    (h : IsPullback p q (hom f) b)
    (hf : IsRepresentableMorphism (hom (baseChangeMap g f))) :
    ∃ U : Over T, Nonempty ((baseChange g W).presheaf ≅ (schemeYoneda T).obj U) :=
  ⟨hf.pullback (restrictAtlas g b), ⟨baseChangePullbackSchemeIso g b p q h hf⟩⟩

/-- Once a represented pullback descends as a scheme, its actual projection
constructs the later target-atlas square. All three scheme finiteness
properties are conclusions for both corners. -/
theorem exists_schemeTargetAtlas_of_modelUniqueness
    (huni : SpaceLimitModelUniqueness.{u})
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y W : AlgebraicSpace (D.obj i)} {f : X ⟶ Y} {V : Over (D.obj i)}
    (b : (schemeYoneda (D.obj i)).obj V ⟶ Y.presheaf)
    (hb : IsEtale b) (hs : IsSurjective b)
    [LocallyOfFinitePresentation V.hom] [QuasiCompact V.hom] [QuasiSeparated V.hom]
    (p : W.presheaf ⟶ X.presheaf)
    (q : W.presheaf ⟶ (schemeYoneda (D.obj i)).obj V)
    (h : IsPullback p q (hom f) b)
    (hWqs : IsQuasiSeparated W)
    (hWfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) W)
    (hf : IsRepresentableMorphism (hom (baseChangeMap (c.π.app i) f))) :
    ∃ (j : I) (r : j ⟶ i) (a : SchemeTargetAtlas (baseChangeMap (D.map r) f)),
      LocallyOfFinitePresentation a.source.hom ∧ QuasiCompact a.source.hom ∧
      QuasiSeparated a.source.hom ∧ LocallyOfFinitePresentation a.target.hom ∧
      QuasiCompact a.target.hom ∧ QuasiSeparated a.target.hom := by
  obtain ⟨U, ⟨eU⟩⟩ :=
    exists_presheafIso_of_representable_baseChange (c.π.app i) b p q h hf
  obtain ⟨j, r, R, hRfp, hRqc, hRqs, ⟨eR⟩⟩ :=
    exists_schemeRepresentation_of_presheafIso_of_modelUniqueness huni D c hc i W
      hWqs hWfp U eU
  let g := D.map r
  let q' := (restrictPresheaf g).map q ≫ (schemeYonedaBaseChangeIso g V).inv
  have h' : IsPullback ((restrictPresheaf g).map p) q'
      (hom (baseChangeMap g f)) (restrictAtlas g b) := by
    apply (h.map (restrictPresheaf g)).of_iso'
      (Iso.refl _) (Iso.refl _) (schemeYonedaBaseChangeIso g V) (Iso.refl _)
    · simp
    · simp [q']
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
    · simp [restrictAtlas]
  let a := SchemeTargetAtlas.of_presheafIso
    (f := baseChangeMap g f) (W := baseChange g W) (restrictAtlas g b)
    (relative_restrictAtlas (g := g) _ hb) (relative_restrictAtlas (g := g) _ hs)
    ((restrictPresheaf g).map p) q' h' R eR
  refine ⟨j, r, a, hRfp, hRqc, hRqs, ?_, ?_, ?_⟩
  · change LocallyOfFinitePresentation (pullback.snd V.hom g)
    infer_instance
  · change QuasiCompact (pullback.snd V.hom g)
    infer_instance
  · change QuasiSeparated (pullback.snd V.hom g)
    infer_instance

end Langlands.AlgebraicGeometry.AlgebraicSpace
