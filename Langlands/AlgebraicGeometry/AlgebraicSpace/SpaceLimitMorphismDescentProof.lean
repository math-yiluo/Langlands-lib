import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitMorphismDescentStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredRingPointProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPointsSurjective
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation

/-!
# Morphisms of algebraic spaces along cofiltered limits of affine schemes: proof
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SpaceLimitMorphisms

open SpaceFilteredPoints

section Atlas

variable {B : Scheme.{u}}

/-- A morphism out of an algebraic space is determined by a section of the target over an
etale surjective atlas whose two pullbacks agree on every pair of atlas points with the same
image. -/
theorem exists_hom_of_atlas {Y Q : AlgebraicSpace B} {V : Over B}
    (α : (schemeYoneda B).obj V ⟶ Y.presheaf) (hα : IsEtale α) (hs : IsSurjective α)
    (q : Q.sections V)
    (hq : ∀ {T : Over B} (w₁ w₂ : T ⟶ V), atlasSection α w₁ = atlasSection α w₂ →
      Q.pullback w₁ q = Q.pullback w₂ q) :
    ∃ ψ : Y ⟶ Q, ∀ {T : Over B} (w : T ⟶ V),
      mapSections ψ T (atlasSection α w) = Q.pullback w q := by
  let a' : (schemeSheaf B).obj V ⟶ Y.toSheaf := ObjectProperty.homMk α
  let t' : (schemeSheaf B).obj V ⟶ Q.toSheaf := ObjectProperty.homMk (uliftYonedaEquiv.{u + 1}.symm q)
  have hloc : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology B) α :=
    CategoryTheory.Presheaf.isLocallySurjective_of_le
      (Sites.etaleTopologyOver_le_fppfTopologyOver B) α
      (isLocallySurjective_etale_of_isEtale_isSurjective α hα hs)
  have : Sheaf.IsLocallySurjective a' := hloc
  have : Epi a' := inferInstance
  have : IsRegularEpi a' := IsRegularEpiCategory.regularEpiOfEpi a'
  have hqa : ∀ {Z : FppfSheaf B} (g₁ g₂ : Z ⟶ (schemeSheaf B).obj V),
      g₁ ≫ a' = g₂ ≫ a' → g₁ ≫ t' = g₂ ≫ t' := by
    intro Z g₁ g₂ h
    apply ObjectProperty.hom_ext
    ext T x
    have hx := congrArg (fun k => k.hom.app T x) h
    change α.app T (g₁.hom.app T x) = α.app T (g₂.hom.app T x) at hx
    change (uliftYonedaEquiv.{u + 1}.symm q).app T (g₁.hom.app T x) =
      (uliftYonedaEquiv.{u + 1}.symm q).app T (g₂.hom.app T x)
    generalize g₁.hom.app T x = y₁ at hx ⊢
    generalize g₂.hom.app T x = y₂ at hx ⊢
    obtain ⟨w₁⟩ := y₁
    obtain ⟨w₂⟩ := y₂
    rw [schemeYoneda_app_up, schemeYoneda_app_up, Equiv.apply_symm_apply]
    exact hq w₁ w₂ hx
  refine ⟨ObjectProperty.homMk (EffectiveEpi.desc a' t' hqa), fun {T} w => ?_⟩
  have h := congrArg (fun k => k.hom.app (op T) (ULift.up w)) (EffectiveEpi.fac a' t' hqa)
  refine h.trans ?_
  change (uliftYonedaEquiv.{u + 1}.symm q).app (op T) ⟨w⟩ = _
  rw [schemeYoneda_app_up, Equiv.apply_symm_apply]

end Atlas

/-- A space with a quasi-compact atlas over a quasi-compact base has an affine atlas. -/
theorem exists_affine_qc_atlas {S : Scheme.{u}} [CompactSpace S] (X : AlgebraicSpace S)
    (hX : HasAtlasProperty (@QuasiCompact.{u}) X) :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsEtale a ∧ IsSurjective a ∧ IsAffine U.left := by
  obtain ⟨U, a, ha, hs, hU⟩ := hX
  have : QuasiCompact U.hom := hU
  have : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  obtain ⟨W, j, hW, hje, hjs⟩ := exists_affine_refinement (𝟙 U.left)
  let U' : Over S := Over.mk (j ≫ U.hom)
  let j' : U' ⟶ U := Over.homMk j
  have hje' : Etale j'.left := by
    change Etale j
    simpa using hje
  have hjs' : Surjective j'.left := by
    change Surjective j
    simpa using hjs
  exact ⟨U', (schemeYoneda S).map j' ≫ a, IsEtale.comp (isEtale_map j' hje') ha,
    SpaceProductPoints.IsSurjective.comp (SpaceProductPoints.isSurjective_map j' hjs') hs, hW⟩

/-- Over an affine base, an affine atlas of a separated space has an affine scheme of pairs
of atlas points with the same image, in the factorization sense. -/
theorem exists_equalizer_scheme {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S}
    (hX : IsSeparated X) {U : Over S} [IsAffine U.left]
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) :
    ∃ (E : Over S) (r₁ r₂ : E ⟶ U), IsAffine E.left ∧
      (∀ {T : Over S} (f f' : T ⟶ U), atlasSection a f = atlasSection a f' →
        ∃ r : T ⟶ E, r ≫ r₁ = f ∧ r ≫ r₂ = f') ∧
      (∀ {T : Over S} (r : T ⟶ E), atlasSection a (r ≫ r₁) = atlasSection a (r ≫ r₂)) := by
  let P : Over S := Over.mk (pullback.fst U.hom U.hom ≫ U.hom)
  let p₁ : P ⟶ U := Over.homMk (pullback.fst U.hom U.hom) rfl
  let p₂ : P ⟶ U := Over.homMk (pullback.snd U.hom U.hom) (by
    simp only [P, Over.mk_hom]
    exact pullback.condition.symm)
  obtain ⟨E, ι, hι, hci⟩ := exists_representsEqualizer_of_relative_diag
    (P := @_root_.AlgebraicGeometry.IsClosedImmersion) hX
    (atlasSection a p₁) (atlasSection a p₂)
  have : IsAffine P.left := inferInstanceAs (IsAffine (Limits.pullback U.hom U.hom))
  have : _root_.AlgebraicGeometry.IsClosedImmersion ι.left := hci
  have hE : IsAffine E.left := isAffine_of_isAffineHom ι.left
  refine ⟨E, ι ≫ p₁, ι ≫ p₂, hE, ?_, ?_⟩
  · intro T f f' h
    let g : T ⟶ P := Over.homMk (pullback.lift f.left f'.left (by rw [Over.w f, Over.w f']))
      (by simp [P])
    have hg₁ : g ≫ p₁ = f := by
      ext1
      exact pullback.lift_fst _ _ _
    have hg₂ : g ≫ p₂ = f' := by
      ext1
      exact pullback.lift_snd _ _ _
    obtain ⟨r, hr⟩ := (hι g).2 (by
      change X.pullback g (atlasSection a p₁) = X.pullback g (atlasSection a p₂)
      rw [atlasSection_pullback, atlasSection_pullback, hg₁, hg₂]
      exact h)
    exact ⟨r, by rw [← Category.assoc, hr, hg₁], by rw [← Category.assoc, hr, hg₂]⟩
  · intro T r
    have := (hι (r ≫ ι)).1 ⟨r, rfl⟩
    change X.pullback (r ≫ ι) (atlasSection a p₁) = X.pullback (r ≫ ι) (atlasSection a p₂)
      at this
    rwa [atlasSection_pullback, atlasSection_pullback, Category.assoc, Category.assoc] at this

/-- Finitely presented schemes over the limit of a cofiltered diagram of affine schemes have
finitely presented models at a stage. -/
theorem exists_model_of_affine_diagram {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    (W : Scheme.{u}) (g : W ⟶ c.pt)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g] :
    ∃ (i : I) (V : Scheme.{u}) (q : V ⟶ D.obj i) (π : W ⟶ V),
      LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q ∧
        IsPullback π g q (c.π.app i) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let A := D.op ⋙ Scheme.Γ
  let dA := Scheme.Γ.mapCocone c.op
  have hcA : IsColimit dA := (nonempty_isColimit_Γ_mapCocone D c hc).some
  obtain ⟨j, Xj, gj, π, hfp, hqc, hqs, hpb⟩ :=
    @SchemeLimitModel.schemeFilteredModelExistence.{u} Iᵒᵖ _ _ A dA hcA W
      (g ≫ c.pt.isoSpec.hom) inferInstance inferInstance inferInstance
  have := hfp
  have := hqc
  have := hqs
  refine ⟨j.unop, Xj, gj ≫ (D.obj j.unop).isoSpec.inv, π, inferInstance, inferInstance,
    inferInstance, ?_⟩
  refine hpb.of_iso (Iso.refl _) (Iso.refl _) c.pt.isoSpec.symm (D.obj j.unop).isoSpec.symm
    (by simp) (by simp) (by simp) ?_
  change Spec.map (c.π.app j.unop).appTop ≫ (D.obj j.unop).isoSpec.inv =
    c.pt.isoSpec.inv ≫ c.π.app j.unop
  exact Scheme.isoSpec_inv_naturality (X := c.pt) (Y := D.obj j.unop) (c.π.app j.unop)

section BaseAtlas

variable {S B : Scheme.{u}} (g : B ⟶ S)

/-- The base change of a scheme over `S` to `B`, with its first projection to `B`. -/
abbrev baseOver (U : Over S) : Over B := Over.mk (pullback.fst g U.hom)

/-- Its comparison with Mathlib's over-category pullback. -/
def baseSymm (U : Over S) : baseOver g U ⟶ (Over.pullback g).obj U :=
  Over.homMk (pullbackSymmetry g U.hom).hom (by simp)

variable {X : AlgebraicSpace S} {U : Over S}

/-- The base change of an atlas, on the scheme `B ×_S U`. -/
def baseAtlas (a : (schemeYoneda S).obj U ⟶ X.presheaf) :
    (schemeYoneda B).obj (baseOver g U) ⟶ (baseChange g X).presheaf :=
  (schemeYoneda B).map (baseSymm g U) ≫ restrictAtlas g a

/-- The base change of an atlas evaluates through the second projection. -/
theorem baseAtlas_app (a : (schemeYoneda S).obj U ⟶ X.presheaf) {T : Over B}
    (w : T ⟶ baseOver g U) :
    atlasSection (baseAtlas g a) w =
      atlasSection a (Over.homMk (w.left ≫ pullback.snd g U.hom) (by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc,
          show w.left ≫ pullback.fst g U.hom = T.hom from Over.w w]
        rfl) : (Over.map g).obj T ⟶ U) := by
  change a.app (op ((Over.map g).obj T))
      (ULift.up (((Over.mapPullbackAdj g).homEquiv T U).symm (w ≫ baseSymm g U))) = _
  congr 2
  apply Over.OverMorphism.ext
  simp [baseSymm, Over.mapPullbackAdj]

theorem isEtale_baseAtlas (a : (schemeYoneda S).obj U ⟶ X.presheaf) (ha : IsEtale a) :
    IsEtale (baseAtlas g a) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact IsEtale.comp (isEtale_map _ (inferInstanceAs (Etale (pullbackSymmetry g U.hom).hom)))
    (relative_restrictAtlas _ ha)

theorem isSurjective_baseAtlas (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (hs : IsSurjective a) : IsSurjective (baseAtlas g a) := by
  have : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact SpaceProductPoints.IsSurjective.comp
    (SpaceProductPoints.isSurjective_map _
      (inferInstanceAs (Surjective (pullbackSymmetry g U.hom).hom)))
    (relative_restrictAtlas _ hs)

end BaseAtlas

end SpaceLimitMorphisms

open SpaceFilteredPoints SpaceLimitMorphisms in
/-- **Morphism descent for algebraic spaces** along cofiltered limits of affine schemes
(the existence half of Conrad's Theorem 3.4(1) for spaces, printed p.13). -/
theorem spaceLimitMorphismDescent : SpaceLimitMorphismDescent.{u} := by
  intro I _ _ D _ S _ t c hc p hp X Z hXsep hXqc hZ φ
  obtain ⟨U, a, ha, hs, hU⟩ := exists_affine_qc_atlas X hXqc
  obtain ⟨E, r₁, r₂, hE, hlift, hcomp⟩ := exists_equalizer_scheme hXsep a
  obtain ⟨UZ, aZ, haZ, hsZ, hUZ⟩ := hZ
  have : LocallyOfFinitePresentation UZ.hom := hUZ
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have htf : ∀ {i j : I} (f : i ⟶ j), D.map f ≫ t.app j = t.app i := fun f => by
    have := t.naturality f
    simp only [Functor.const_obj_map] at this
    exact this
  -- The base changes of the atlas along the stages, with the limit.
  let DU := TargetLimit.diagram D t U.hom
  let tU : DU ⟶ (Functor.const I).obj S := TargetLimit.projection D t U.hom ≫ t
  let cU := TargetLimit.cone D t U.hom c p hp
  have hcU : IsLimit cU := TargetLimit.isLimitCone D t U.hom c p hp hc
  let pU : cU.pt ⟶ S := pullback.fst p U.hom ≫ p
  have hcUfst : ∀ i, cU.π.app i ≫ pullback.fst (t.app i) U.hom =
      pullback.fst p U.hom ≫ c.π.app i := fun i => AffineLimit.cone_π_fst D t U.hom c p hp i
  have hcUsnd : ∀ i, cU.π.app i ≫ pullback.snd (t.app i) U.hom = pullback.snd p U.hom :=
    fun i => AffineLimit.cone_π_snd D t U.hom c p hp i
  have hpU : ∀ i, cU.π.app i ≫ tU.app i = pU := fun i => by
    change cU.π.app i ≫ pullback.fst (t.app i) U.hom ≫ t.app i = _
    rw [← Category.assoc, hcUfst, Category.assoc, hp]
  have : IsAffine cU.pt := inferInstanceAs (IsAffine (Limits.pullback p U.hom))
  -- The universal atlas point over the limit and its image under `φ`.
  have hαp := isEtale_baseAtlas p a ha
  have hsp := isSurjective_baseAtlas p a hs
  let x₀ : (baseChange p X).sections (baseOver p U) := atlasSection (baseAtlas p a) (𝟙 _)
  let z : Z.sections (Over.mk pU) := mapSections φ (baseOver p U) x₀
  -- Descend the image to a stage.
  obtain ⟨j₀, y₀, hy₀⟩ := exists_stage aZ haZ hsZ tU hcU pU hpU
    (fun W _ g _ => by
      have : QuasiCompact g := inferInstance
      have : QuasiSeparated g := inferInstance
      exact exists_model_of_affine_diagram DU cU hcU W g) z
  -- The base changes of the equalizer scheme.
  let DE := TargetLimit.diagram D t E.hom
  let cE := TargetLimit.cone D t E.hom c p hp
  have hcE : IsLimit cE := TargetLimit.isLimitCone D t E.hom c p hp hc
  have hcEfst : ∀ i, cE.π.app i ≫ pullback.fst (t.app i) E.hom =
      pullback.fst p E.hom ≫ c.π.app i := fun i => AffineLimit.cone_π_fst D t E.hom c p hp i
  have hcEsnd : ∀ i, cE.π.app i ≫ pullback.snd (t.app i) E.hom = pullback.snd p E.hom :=
    fun i => AffineLimit.cone_π_snd D t E.hom c p hp i
  let TE : I → Over S := fun i => Over.mk (pullback.fst (t.app i) E.hom ≫ t.app i)
  let TU : I → Over S := fun i => Over.mk (pullback.fst (t.app i) U.hom ≫ t.app i)
  let ρ : (E ⟶ U) → ∀ i, Limits.pullback (t.app i) E.hom ⟶ Limits.pullback (t.app i) U.hom :=
    fun r i => pullback.lift (pullback.fst (t.app i) E.hom) (pullback.snd (t.app i) E.hom ≫ r.left)
      (by rw [pullback.condition, Category.assoc, Over.w r])
  have hρfst : ∀ r i, ρ r i ≫ pullback.fst (t.app i) U.hom = pullback.fst (t.app i) E.hom :=
    fun r i => pullback.lift_fst _ _ _
  have hρsnd : ∀ r i, ρ r i ≫ pullback.snd (t.app i) U.hom =
      pullback.snd (t.app i) E.hom ≫ r.left := fun r i => pullback.lift_snd _ _ _
  let ρ' : (E ⟶ U) → ∀ i, TE i ⟶ TU i := fun r i => Over.homMk (ρ r i) (by
    change ρ r i ≫ pullback.fst (t.app i) U.hom ≫ t.app i = _
    rw [← Category.assoc, hρfst]
    rfl)
  let ρl : (E ⟶ U) → (baseOver p E ⟶ baseOver p U) := fun r =>
    Over.homMk (pullback.lift (pullback.fst p E.hom) (pullback.snd p E.hom ≫ r.left)
      (by rw [pullback.condition, Category.assoc, Over.w r])) (pullback.lift_fst _ _ _)
  let eE : (Over.map p).obj (baseOver p E) ⟶ E :=
    Over.homMk (pullback.snd p E.hom) pullback.condition.symm
  have hρl : ∀ r : E ⟶ U, (baseChange p X).pullback (ρl r) x₀ = atlasSection a (eE ≫ r) := by
    intro r
    rw [atlasSection_pullback, Category.comp_id, baseAtlas_app]
    congr 2
    exact pullback.lift_snd _ _ _
  have : ∀ i, IsAffine (TE i).left := fun i =>
    inferInstanceAs (IsAffine (Limits.pullback (show D.obj i ⟶ S from t.app i) E.hom))
  -- The two pullbacks of the descended point agree over the limit.
  let ιE : overOf (T := TE j₀) (cE.π.app j₀) ⟶ (Over.map p).obj (baseOver p E) :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ pullback.fst p E.hom ≫ p =
        cE.π.app j₀ ≫ pullback.fst (t.app j₀) E.hom ≫ t.app j₀
      rw [Category.id_comp, ← Category.assoc, hcEfst, Category.assoc, hp])
  have hlimr : ∀ r : E ⟶ U, Z.pullback (overHom (T := TE j₀) (cE.π.app j₀))
      (Z.pullback (ρ' r j₀) y₀) =
        Z.pullback ιE (mapSections φ (baseOver p E) (atlasSection a (eE ≫ r))) := by
    intro r
    have hsq : overHom (T := TE j₀) (cE.π.app j₀) ≫ ρ' r j₀ =
        ιE ≫ (Over.map p).map (ρl r) ≫
          (Over.homMk (cU.π.app j₀) (hpU j₀) : Over.mk pU ⟶ Over.mk (tU.app j₀)) := by
      ext1
      change cE.π.app j₀ ≫ ρ r j₀ = 𝟙 _ ≫ (ρl r).left ≫ cU.π.app j₀
      rw [Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, hρfst, hcEfst, Category.assoc, hcUfst]
        change _ = (pullback.lift _ _ _ ≫ pullback.fst p U.hom) ≫ _
        rw [pullback.lift_fst]
      · rw [Category.assoc, hρsnd, ← Category.assoc, hcEsnd, Category.assoc, hcUsnd]
        change _ = pullback.lift _ _ _ ≫ pullback.snd p U.hom
        rw [pullback.lift_snd]
    rw [← Z.pullback_comp, hsq, Z.pullback_comp, Z.pullback_comp]
    refine congrArg (Z.pullback ιE) ?_
    refine (congrArg (Z.pullback ((Over.map p).map (ρl r))) hy₀).trans ?_
    rw [← hρl r]
    exact mapSections_naturality φ (ρl r) x₀
  obtain ⟨l, hl⟩ := exists_eq_of_limit aZ haZ hsZ (overDiagram DE j₀) (T := TE j₀)
    (overStructure DE j₀) (cE.whisker (Over.forget j₀)) (overConeIsLimit j₀ cE hcE)
    (cE.π.app j₀) (overCone_π_comp j₀ cE) (Z.pullback (ρ' r₁ j₀) y₀)
    (Z.pullback (ρ' r₂ j₀) y₀) (by rw [hlimr r₁, hlimr r₂, hcomp])
  -- The stage `j` and the descended point there.
  let j := l.left
  let f : j ⟶ j₀ := l.hom
  let τ : TU j ⟶ TU j₀ := Over.homMk (DU.map f) (by
    change DU.map f ≫ pullback.fst (t.app j₀) U.hom ≫ t.app j₀ = _
    rw [targetLimit_map_fst_assoc, htf]
    rfl)
  let y : Z.sections (TU j) := Z.pullback τ y₀
  have hcompat : Z.pullback (ρ' r₁ j) y = Z.pullback (ρ' r₂ j) y := by
    let κ : TE j ⟶ overOf (T := TE j₀) ((overStructure DE j₀).app l) := Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ DE.map f ≫ pullback.fst (t.app j₀) E.hom ≫ t.app j₀ =
        pullback.fst (t.app j) E.hom ≫ t.app j
      rw [Category.id_comp, targetLimit_map_fst_assoc, htf])
    have hκ : ∀ r : E ⟶ U, ρ' r j ≫ τ =
        κ ≫ overHom (T := TE j₀) ((overStructure DE j₀).app l) ≫ ρ' r j₀ := by
      intro r
      ext1
      change ρ r j ≫ DU.map f = 𝟙 _ ≫ DE.map f ≫ ρ r j₀
      have e1 : DU.map f ≫ pullback.fst (t.app j₀) U.hom = pullback.fst (t.app j) U.hom ≫ D.map f :=
        targetLimit_map_fst D t U.hom f
      have e2 : DU.map f ≫ pullback.snd (t.app j₀) U.hom = pullback.snd (t.app j) U.hom :=
        targetLimit_map_snd D t U.hom f
      have e3 : DE.map f ≫ pullback.fst (t.app j₀) E.hom = pullback.fst (t.app j) E.hom ≫ D.map f :=
        targetLimit_map_fst D t E.hom f
      have e4 : DE.map f ≫ pullback.snd (t.app j₀) E.hom = pullback.snd (t.app j) E.hom :=
        targetLimit_map_snd D t E.hom f
      apply pullback.hom_ext (f := t.app j₀) (g := U.hom)
      · rw [Category.assoc, e1, ← Category.assoc, hρfst, Category.id_comp, Category.assoc, hρfst,
          e3]
      · rw [Category.assoc, e2, hρsnd, Category.id_comp, Category.assoc, hρsnd, ← Category.assoc,
          e4]
    rw [← Z.pullback_comp, hκ, ← Z.pullback_comp, hκ, Z.pullback_comp, Z.pullback_comp,
      Z.pullback_comp, Z.pullback_comp, hl]
  -- The descended morphism at the stage `j`.
  obtain ⟨φj, hφj⟩ := exists_hom_of_atlas (Q := baseChange (t.app j) Z)
    (baseAtlas (t.app j) a) (isEtale_baseAtlas _ a ha) (isSurjective_baseAtlas _ a hs) y
    (by
      intro T w₁ w₂ hw
      rw [baseAtlas_app, baseAtlas_app] at hw
      obtain ⟨r, hr₁, hr₂⟩ := hlift _ _ hw
      let ν : (Over.map (t.app j)).obj T ⟶ TE j :=
        Over.homMk (pullback.lift T.hom r.left (Over.w r).symm) (by
          change pullback.lift T.hom r.left _ ≫ pullback.fst (t.app j) E.hom ≫ t.app j = _
          rw [pullback.lift_fst_assoc]
          rfl)
      have hν : ∀ (w : T ⟶ baseOver (t.app j) U) (r' : E ⟶ U),
          (Over.homMk (w.left ≫ pullback.snd (t.app j) U.hom) (by
            rw [Category.assoc, ← pullback.condition, ← Category.assoc,
              show w.left ≫ pullback.fst (t.app j) U.hom = T.hom from Over.w w]
            rfl) : (Over.map (t.app j)).obj T ⟶ U) = r ≫ r' →
          (Over.map (t.app j)).map w = ν ≫ ρ' r' j := by
        intro w r' h
        ext1
        change w.left = pullback.lift T.hom r.left _ ≫ ρ r' j
        apply pullback.hom_ext
        · rw [Category.assoc, hρfst, pullback.lift_fst]
          exact Over.w w
        · rw [Category.assoc, hρsnd, pullback.lift_snd_assoc]
          exact congrArg CommaMorphism.left h
      change Z.pullback ((Over.map (t.app j)).map w₁) y =
        Z.pullback ((Over.map (t.app j)).map w₂) y
      rw [hν w₁ r₁ hr₁.symm, hν w₂ r₂ hr₂.symm, Z.pullback_comp, Z.pullback_comp]
      exact congrArg (Z.pullback ν) hcompat)
  refine ⟨j, φj, fun W x => ?_⟩
  obtain ⟨W', e, v, he, hse, hv⟩ := exists_atlas_lift (baseAtlas p a) hαp hsp x
  have : Etale e.left := he
  have : Surjective e.left := hse
  apply pullback_injective (baseChange p Z) e
  -- The left side.
  have hL : (baseChange p Z).pullback e (mapSections φ W x) =
      (baseChange p Z).pullback v z := by
    rw [mapSections_naturality, ← hv]
    rw [show v = v ≫ 𝟙 _ from (Category.comp_id v).symm, ← atlasSection_pullback,
      mapSections_naturality]
    rfl
  rw [hL]
  -- The right side.
  let εW' : (Over.map p).obj W' ⟶ (Over.map (t.app j)).obj ((Over.map (c.π.app j)).obj W') :=
    Over.homMk (𝟙 W'.left) (by simp [← hp j])
  let εW'' : (Over.map (t.app j)).obj ((Over.map (c.π.app j)).obj W') ⟶ (Over.map p).obj W' :=
    Over.homMk (𝟙 W'.left) (by simp [← hp j])
  let e' := (Over.map (c.π.app j)).map e
  have hA : (Over.map p).map e ≫
      (Over.homMk (𝟙 W.left) (by simp [← hp j]) :
        (Over.map p).obj W ⟶ (Over.map (t.app j)).obj ((Over.map (c.π.app j)).obj W)) =
      εW' ≫ (Over.map (t.app j)).map e' := by
    ext1
    simp [εW', e']
  have hD : (Over.map (t.app j)).map e' ≫
      (Over.homMk (𝟙 W.left) (by simp [← hp j]) :
        (Over.map (t.app j)).obj ((Over.map (c.π.app j)).obj W) ⟶ (Over.map p).obj W) =
      εW'' ≫ (Over.map p).map e := by
    ext1
    simp [εW'', e']
  let vj : (Over.map (c.π.app j)).obj W' ⟶ baseOver (t.app j) U :=
    Over.homMk (v.left ≫ cU.π.app j) (by
      change (v.left ≫ cU.π.app j) ≫ pullback.fst (t.app j) U.hom = W'.hom ≫ c.π.app j
      rw [Category.assoc, hcUfst, ← Category.assoc,
        show v.left ≫ pullback.fst p U.hom = W'.hom from Over.w v])
  have hE' : X.pullback εW'' (atlasSection (baseAtlas p a) v) =
      atlasSection (baseAtlas (t.app j) a) vj := by
    rw [baseAtlas_app, atlasSection_pullback, baseAtlas_app]
    congr 2
    ext1
    change 𝟙 _ ≫ v.left ≫ pullback.snd p U.hom = (v.left ≫ cU.π.app j) ≫ _
    rw [Category.id_comp, Category.assoc, hcUsnd]
  have hG : εW' ≫ (Over.map (t.app j)).map vj =
      (Over.map p).map v ≫
        (Over.homMk (cU.π.app j) (hpU j) : Over.mk pU ⟶ Over.mk (tU.app j)) := by
    ext1
    simp [εW', vj]
  have hH : Z.pullback (Over.homMk (cU.π.app j) (hpU j) : Over.mk pU ⟶ Over.mk (tU.app j)) y =
      z := by
    change Z.pullback _ (Z.pullback τ y₀) = z
    rw [← Z.pullback_comp, ← hy₀]
    congr 1
    ext1
    exact cU.w f
  change Z.pullback ((Over.map p).map v) z = Z.pullback ((Over.map p).map e) _
  rw [← Z.pullback_comp, hA, Z.pullback_comp]
  erw [mapSections_naturality φj e']
  change _ = Z.pullback εW' (mapSections φj _ (X.pullback ((Over.map (t.app j)).map e')
    (X.pullback _ x)))
  rw [← X.pullback_comp, hD, X.pullback_comp]
  change _ = Z.pullback εW' (mapSections φj _ (X.pullback εW''
    ((baseChange p X).pullback e x)))
  rw [← hv, hE', hφj vj]
  change _ = Z.pullback εW' (Z.pullback ((Over.map (t.app j)).map vj) y)
  rw [← Z.pullback_comp, hG, Z.pullback_comp]
  exact congrArg (Z.pullback ((Over.map p).map v)) hH.symm

end Langlands.AlgebraicGeometry.AlgebraicSpace
