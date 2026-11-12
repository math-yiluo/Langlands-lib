import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationEtaleAtlas
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationRelationQuotient
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitModelExistenceQuasiSeparatedStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleKernelPairComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismBaseChange
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationLimitModelStatement
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Reduction of space model existence to scheme-relation descent -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SpaceLimitModelExistenceQuasiSeparatedReduction

variable {S T : Scheme.{u}} (g : S ⟶ T)

/-- The slice comparison supplied by a cartesian square of actual schemes. -/
def overIso {U : Over S} {V : Over T} {f : U.left ⟶ V.left}
    (h : IsPullback f U.hom V.hom g) :
    U ≅ (Over.pullback g).obj V :=
  Over.isoMk h.isoPullback h.isoPullback_hom_snd

/-- The slice comparisons commute with a morphism of cartesian squares. -/
theorem overIso_naturality {U R : Over S} {V W : Over T}
    {fU : U.left ⟶ V.left} {fR : R.left ⟶ W.left}
    (hU : IsPullback fU U.hom V.hom g)
    (hR : IsPullback fR R.hom W.hom g)
    (t : R ⟶ U) (t₀ : W ⟶ V)
    (ht : fR ≫ t₀.left = t.left ≫ fU) :
    (overIso g hR).hom ≫ (Over.pullback g).map t₀ =
      t ≫ (overIso g hU).hom := by
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · simp only [Over.comp_left, Over.pullback_map_left, Limits.pullback.lift_fst,
      Category.assoc]
    change (hR.isoPullback.hom ≫ Limits.pullback.fst W.hom g) ≫ t₀.left =
      t.left ≫ hU.isoPullback.hom ≫ Limits.pullback.fst V.hom g
    rw [hR.isoPullback_hom_fst, hU.isoPullback_hom_fst, ht]
  · simp only [Over.comp_left, Over.pullback_map_left, Limits.pullback.lift_snd,
      Category.assoc]
    change hR.isoPullback.hom ≫ Limits.pullback.snd W.hom g =
      t.left ≫ hU.isoPullback.hom ≫ Limits.pullback.snd V.hom g
    rw [hR.isoPullback_hom_snd, hU.isoPullback_hom_snd, Over.w]

/-- A cartesian relation morphism over a cartesian object comparison also
gives the cartesian relation comparison over the base. -/
theorem relation_isPullback
    {E Ei : EtaleEquivalenceRelation.{u}} {b : E.U ⟶ S} {bi : Ei.U ⟶ T}
    (hb : E.t ≫ b = E.s ≫ b) (hbi : Ei.t ≫ bi = Ei.s ≫ bi)
    {fU : E.U ⟶ Ei.U} {fR : E.R ⟶ Ei.R}
    (hU : IsPullback fU b bi g) (hE : E.IsCartesianHom Ei fU fR) :
    IsPullback fR (E.t ≫ b) (Ei.t ≫ bi) g := by
  simpa only [← hb, ← hbi] using hE.2.paste_vert hU

/-- The represented relation of an atlas restricts to the actual base-changed
scheme relation. -/
theorem restrict_kernelPair {F : Presheaf T} {U R : Over T}
    {a : (schemeYoneda T).obj U ⟶ F} {t s : R ⟶ U}
    (h : IsPullback ((schemeYoneda T).map t) ((schemeYoneda T).map s) a a) :
    IsPullback
      ((schemeYoneda S).map ((Over.pullback g).map t))
      ((schemeYoneda S).map ((Over.pullback g).map s))
      (restrictAtlas g a) (restrictAtlas g a) := by
  apply (h.map (restrictPresheaf g)).of_iso'
    (schemeYonedaBaseChangeIso g R)
    (schemeYonedaBaseChangeIso g U)
    (schemeYonedaBaseChangeIso g U) (Iso.refl _)
  · exact ((schemeYonedaBaseChangeNatIso g).hom.naturality t).symm
  · exact ((schemeYonedaBaseChangeNatIso g).hom.naturality s).symm
  · simp [restrictAtlas]
  · simp [restrictAtlas]

/-- Two spaces with étale surjective presentations identified by cartesian
scheme comparisons become isomorphic after change of base. -/
def isoOfRelationComparison
    {Y : AlgebraicSpace S} {X : AlgebraicSpace T}
    {U R : Over S} {V W : Over T}
    (a : (schemeYoneda S).obj U ⟶ Y.presheaf)
    (b : (schemeYoneda T).obj V ⟶ X.presheaf)
    (ha : IsEtale a) (has : IsSurjective a) (hb : IsEtale b) (hbs : IsSurjective b)
    (t s : R ⟶ U) (t₀ s₀ : W ⟶ V)
    (hA : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hB : IsPullback ((schemeYoneda T).map t₀) ((schemeYoneda T).map s₀) b b)
    {fU : U.left ⟶ V.left} {fR : R.left ⟶ W.left}
    (hU : IsPullback fU U.hom V.hom g)
    (hR : IsPullback fR R.hom W.hom g)
    (ht : fR ≫ t₀.left = t.left ≫ fU)
    (hs : fR ≫ s₀.left = s.left ≫ fU) :
    baseChange g X ≅ Y := by
  let eU := overIso g hU
  let eR := overIso g hR
  let c : (schemeYoneda S).obj U ⟶ (baseChange g X).presheaf :=
    (schemeYoneda S).map eU.hom ≫ restrictAtlas g b
  have hc : IsEtale c :=
    (isEtale_map eU.hom (by infer_instance)).comp (relative_restrictAtlas _ hb)
  have hcs : IsSurjective c :=
    SpaceProductPoints.IsSurjective.comp
      (SpaceProductPoints.isSurjective_map eU.hom (by infer_instance))
      (relative_restrictAtlas _ hbs)
  have hC : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) c c := by
    apply (restrict_kernelPair g hB).of_iso'
      ((schemeYoneda S).mapIso eR)
      ((schemeYoneda S).mapIso eU)
      ((schemeYoneda S).mapIso eU) (Iso.refl _)
    · change (schemeYoneda S).map eR.hom ≫
        (schemeYoneda S).map ((Over.pullback g).map t₀) =
          (schemeYoneda S).map t ≫ (schemeYoneda S).map eU.hom
      rw [← Functor.map_comp, ← Functor.map_comp, overIso_naturality g hU hR t t₀ ht]
    · change (schemeYoneda S).map eR.hom ≫
        (schemeYoneda S).map ((Over.pullback g).map s₀) =
          (schemeYoneda S).map s ≫ (schemeYoneda S).map eU.hom
      rw [← Functor.map_comp, ← Functor.map_comp, overIso_naturality g hU hR s s₀ hs]
    · simp [c]
    · simp [c]
  let e : (baseChange g X).presheaf ≅ Y.presheaf :=
    commonEtaleKernelPairIso
      ((baseChange g X).toSheaf.property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver S))
      (Y.toSheaf.property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver S))
      t s c a
      (isLocallySurjective_etale_of_isEtale_isSurjective c hc hcs)
      (isLocallySurjective_etale_of_isEtale_isSurjective a ha has) hC hA
  exact
    { hom := homMk e.hom
      inv := homMk e.inv
      hom_inv_id := (homEquiv _ _).injective e.hom_inv_id
      inv_hom_id := (homEquiv _ _).injective e.inv_hom_id }

/-- An actual finite-stage model together with the full scheme-base-change isomorphism. -/
structure Model {I : Type u} [SmallCategory I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (Y : AlgebraicSpace c.pt) where
  stage : I
  space : AlgebraicSpace (D.obj stage)
  quasiSeparated : IsQuasiSeparated space
  finitePresentation :
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) space
  comparison : baseChange (c.π.app stage) space ≅ Y

/-- Scheme-relation descent constructs the actual model of a quasi-separated
algebraic space of finite presentation. -/
def model (hRel : EtaleEquivalenceRelation.LimitModelExistence.{u})
    (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (Y : AlgebraicSpace c.pt)
    (hqs : IsQuasiSeparated Y)
    (hfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y) :
    Model D c Y :=
  Classical.choice (by
    have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
    let P := FinitePresentationEtaleAtlas.presentation hqs hfp
    let E := EtaleEquivalenceRelation.ofKernelPair P.t P.s P.a P.kernelPair P.etale_t P.etale_s
    have : IsAffine E.U := P.affine
    have : LocallyOfFinitePresentation P.U.hom := P.locallyOfFinitePresentation_U
    have : QuasiCompact (E.t ≫ P.U.hom) := by
      change QuasiCompact (P.t.left ≫ P.U.hom)
      rw [Over.w]
      exact P.quasiCompact_R
    have hb : E.t ≫ P.U.hom = E.s ≫ P.U.hom := by
      change P.t.left ≫ P.U.hom = P.s.left ≫ P.U.hom
      rw [Over.w, Over.w]
    obtain ⟨i, Ei, bi, fU, fR, hi, hif, hir, hbi, hU, hE⟩ :=
      hRel I D c hc E P.U.hom hb
    have : IsAffine Ei.U := hi
    have : LocallyOfFinitePresentation bi := hif
    have : QuasiCompact (Ei.t ≫ bi) := hir
    let Q := FinitePresentationRelationQuotient.quotient Ei bi hbi
    let V : Over (D.obj i) := Over.mk bi
    let W : Over (D.obj i) := Over.mk (Ei.t ≫ bi)
    let t₀ : W ⟶ V := Over.homMk Ei.t
    let s₀ : W ⟶ V := Over.homMk Ei.s hbi.symm
    have hR : IsPullback fR P.R.hom W.hom (c.π.app i) := by
      have H := relation_isPullback (c.π.app i) hb hbi hU hE
      change IsPullback fR (P.t.left ≫ P.U.hom) W.hom (c.π.app i) at H
      simpa only [Over.w P.t] using H
    let e : baseChange (c.π.app i) Q.space ≅ Y :=
      isoOfRelationComparison (c.π.app i) P.a Q.a P.etale P.surjective Q.etale Q.surjective
        P.t P.s t₀ s₀ P.kernelPair Q.kernelPair hU hR hE.1 hE.2.w
    exact ⟨⟨i, Q.space, Q.quasiSeparated, Q.finitePresentation, e⟩⟩)

/-- The exact space target follows from the scheme-only relation descent statement. -/
theorem spaceLimitModelExistenceQuasiSeparated_of_relation
    (hRel : EtaleEquivalenceRelation.LimitModelExistence.{u}) :
    SpaceLimitModelExistenceQuasiSeparated.{u} := by
  intro I _ _ D _ c hc Y hqs hfp
  let M := model hRel I D c hc Y hqs hfp
  exact ⟨M.stage, M.space, M.quasiSeparated, M.finitePresentation, ⟨M.comparison⟩⟩

end SpaceLimitModelExistenceQuasiSeparatedReduction

end Langlands.AlgebraicGeometry.AlgebraicSpace
