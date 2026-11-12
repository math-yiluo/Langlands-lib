import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitMorphismDescentQuasiSeparatedStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitMorphismDescentProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartFibreCount

/-!
# Morphisms of quasi-separated algebraic spaces along cofiltered limits: proof
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SpaceLimitMorphisms

open SpaceFilteredPoints FieldPointEtaleLift

/-- Over an affine base, an affine atlas of a quasi-separated space has an affine scheme `E`
with two maps to the atlas whose images agree, through which every pair of atlas points
with the same image factors etale locally. `E` is an affine etale cover of the
quasi-compact overlap `U ×_X U`. -/
theorem exists_local_equalizer_scheme {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S}
    (hX : IsQuasiSeparated X) {U : Over S} [IsAffine U.left]
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) :
    ∃ (E : Over S) (r₁ r₂ : E ⟶ U), IsAffine E.left ∧
      (∀ {T : Over S} (f f' : T ⟶ U), atlasSection a f = atlasSection a f' →
        ∃ (T' : Over S) (e : T' ⟶ T) (r : T' ⟶ E), Etale e.left ∧ Surjective e.left ∧
          r ≫ r₁ = e ≫ f ∧ r ≫ r₂ = e ≫ f') ∧
      (∀ {T : Over S} (r : T ⟶ E), atlasSection a (r ≫ r₁) = atlasSection a (r ≫ r₂)) := by
  have : IsAffine (U ⊗ U).left := by
    change IsAffine (Limits.pullback U.hom U.hom)
    infer_instance
  have := EtaleChartFibreCount.compactSpace_selfPullback a hX
  obtain ⟨W, j, hW, hje, hjs⟩ := exists_affine_refinement (𝟙 (selfPullback a).left)
  have : Etale j := by simpa using hje
  have : Surjective j := by simpa using hjs
  let E : Over S := Over.mk (j ≫ (selfPullback a).hom)
  let jE : E ⟶ selfPullback a := Over.homMk j
  refine ⟨E, jE ≫ selfFst a, jE ≫ selfSnd a, hW, ?_, ?_⟩
  · intro T f f' h
    let r := selfLift a f f' (KernelPair.map_comp_eq_of_app_eq a h)
    let T' : Over S := Over.mk (pullback.fst r.left j ≫ T.hom)
    let e : T' ⟶ T := Over.homMk (pullback.fst r.left j)
    let r' : T' ⟶ E := Over.homMk (pullback.snd r.left j) (by
      change pullback.snd r.left j ≫ j ≫ (selfPullback a).hom = pullback.fst r.left j ≫ T.hom
      rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w r])
    have hr' : r' ≫ jE = e ≫ r := by
      ext1
      exact pullback.condition.symm
    refine ⟨T', e, r', inferInstanceAs (Etale (pullback.fst r.left j)),
      inferInstanceAs (Surjective (pullback.fst r.left j)), ?_, ?_⟩
    · rw [← Category.assoc, hr', Category.assoc, Functor.relativelyRepresentable.lift'_fst]
    · rw [← Category.assoc, hr', Category.assoc, Functor.relativelyRepresentable.lift'_snd]
  · intro T r
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun φ : (schemeYoneda S).obj (selfPullback a) ⟶ X.presheaf =>
      φ.app (op T) ⟨r ≫ jE⟩) (selfPullback_isPullback a).w

end SpaceLimitMorphisms

open SpaceFilteredPoints SpaceLimitMorphisms in
/-- **Morphism descent for quasi-separated algebraic spaces** along cofiltered limits of
affine schemes (the existence half of Conrad's Theorem 3.4(1) for spaces, printed p.13). -/
theorem spaceLimitMorphismDescentQuasiSeparated : SpaceLimitMorphismDescentQuasiSeparated.{u} := by
  intro I _ _ D _ S _ t c hc p hp X Z hXqs hXqc hZ φ
  obtain ⟨U, a, ha, hs, hU⟩ := exists_affine_qc_atlas X hXqc
  obtain ⟨E, r₁, r₂, hE, hlift, hcomp⟩ := exists_local_equalizer_scheme hXqs a
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
      -- Pairs of atlas points factoring through `E` have equal images.
      have hexact : ∀ {T : Over (D.obj j)} (w₁ w₂ : T ⟶ baseOver (t.app j) U)
          (r : (Over.map (t.app j)).obj T ⟶ E),
          r.left ≫ r₁.left = w₁.left ≫ pullback.snd (t.app j) U.hom →
          r.left ≫ r₂.left = w₂.left ≫ pullback.snd (t.app j) U.hom →
          Z.pullback ((Over.map (t.app j)).map w₁) y =
            Z.pullback ((Over.map (t.app j)).map w₂) y := by
        intro T w₁ w₂ r hr₁ hr₂
        let ν : (Over.map (t.app j)).obj T ⟶ TE j :=
          Over.homMk (pullback.lift T.hom r.left (Over.w r).symm) (by
            change pullback.lift T.hom r.left _ ≫ pullback.fst (t.app j) E.hom ≫ t.app j = _
            rw [pullback.lift_fst_assoc]
            rfl)
        have hν : ∀ (w : T ⟶ baseOver (t.app j) U) (r' : E ⟶ U),
            r.left ≫ r'.left = w.left ≫ pullback.snd (t.app j) U.hom →
            (Over.map (t.app j)).map w = ν ≫ ρ' r' j := by
          intro w r' h
          ext1
          change w.left = pullback.lift T.hom r.left _ ≫ ρ r' j
          apply pullback.hom_ext
          · rw [Category.assoc, hρfst, pullback.lift_fst]
            exact Over.w w
          · rw [Category.assoc, hρsnd, pullback.lift_snd_assoc]
            exact h.symm
        rw [hν w₁ r₁ hr₁, hν w₂ r₂ hr₂, Z.pullback_comp, Z.pullback_comp]
        exact congrArg (Z.pullback ν) hcompat
      intro T w₁ w₂ hw
      rw [baseAtlas_app, baseAtlas_app] at hw
      obtain ⟨T', e, r, he, hse, hr₁, hr₂⟩ := hlift _ _ hw
      -- Pass to the etale cover on which the pair factors through `E`.
      let T'' : Over (D.obj j) := Over.mk (e.left ≫ T.hom)
      let eT : T'' ⟶ T := Over.homMk e.left
      have : Etale eT.left := he
      have : Surjective eT.left := hse
      apply pullback_injective (baseChange (t.app j) Z) eT
      rw [← (baseChange (t.app j) Z).pullback_comp, ← (baseChange (t.app j) Z).pullback_comp]
      have hr'' : r.left ≫ E.hom = ((Over.map (t.app j)).obj T'').hom := by
        rw [Over.w r, ← Over.w e]
        simp [T'']
      refine hexact (eT ≫ w₁) (eT ≫ w₂) (Over.homMk r.left hr'') ?_ ?_
      · simpa [eT] using congrArg CommaMorphism.left hr₁
      · simpa [eT] using congrArg CommaMorphism.left hr₂)
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
