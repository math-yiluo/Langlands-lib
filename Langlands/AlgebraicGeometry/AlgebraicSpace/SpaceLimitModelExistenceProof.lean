import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitModelExistenceStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitMorphismDescentProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfLocalEqualizer
import Langlands.AlgebraicGeometry.Descent.FppfClosedLocusDescentProof
import Langlands.AlgebraicGeometry.SchemeLimitOpenImmersionProof
import Langlands.AlgebraicGeometry.SchemeLimitRelativeClosedImmersionProof
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientProof

/-!
# Models of algebraic spaces along cofiltered limits of affine schemes: proof
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SpaceLimitModels

open SpaceFilteredPoints

section Separated

variable {S : Scheme.{u}} {F : Presheaf S}

/-- Closed-immersion representations of the equality locus on an fppf-covering sieve glue to a
closed-immersion representation for the original sections. -/
theorem exists_closed_representsEqualizer_of_fppf_local
    (hF : Presheaf.IsSheaf (fppfTopology S) F) {T : Over S}
    (x y : F.obj (op T)) (R : Sieve T) (hR : R ∈ (fppfTopology S) T)
    (h : ∀ ⦃V : Over S⦄ (g : V ⟶ T), R g →
      ∃ (Z : Over S) (ι : Z ⟶ V), _root_.AlgebraicGeometry.IsClosedImmersion ι.left ∧
        RepresentsEqualizer ι (F.map g.op x) (F.map g.op y)) :
    ∃ (Z : Over S) (ι : Z ⟶ T), RepresentsEqualizer ι x y ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ι.left := by
  let E := sectionEqualizerSieve x y
  obtain ⟨Z, ι, hι, hrep⟩ := fppfClosedLocusDescent T.left E
    (sectionEqualizerSieve_isClosed hF x y) ⟨Sieve.overEquiv T R,
      (GrothendieckTopology.mem_over_iff _ _).mp hR, by
      intro V g hg
      let V' : Over S := Over.mk (g ≫ T.hom)
      let g' : V' ⟶ T := Over.homMk g
      obtain ⟨Z, ι, hι, hrep⟩ := h g' ((Sieve.overEquiv_iff R g).mp hg)
      refine ⟨Z.left, ι.left, hι, fun W k ↦ ?_⟩
      rw [hrep.factors_iff_sectionEqualizerSieve k]
      have heq : (Presheaf.equalizerSieve (F := F) x y).pullback g' =
          Presheaf.equalizerSieve (F := F) (F.map g'.op x) (F.map g'.op y) := by
        ext A j
        change F.map (j ≫ g').op x = F.map (j ≫ g').op y ↔
          F.map j.op (F.map g'.op x) = F.map j.op (F.map g'.op y)
        simp only [op_comp, Functor.map_comp, types_comp_apply]
      change (Sieve.overEquiv V'
        (Presheaf.equalizerSieve (F := F) (F.map g'.op x) (F.map g'.op y))) k ↔
        ((Sieve.overEquiv T (Presheaf.equalizerSieve (F := F) x y)).pullback g) k
      rw [← heq, Sieve.overEquiv_pullback]
      rfl⟩
  refine ⟨Over.mk (ι ≫ T.hom), Over.homMk ι, fun V g ↦ ?_, hι⟩
  change _ ↔ (Presheaf.equalizerSieve (F := F) x y) g
  have he : E g.left ↔ (Presheaf.equalizerSieve (F := F) x y) g := by
    change Sieve.overEquiv T (Presheaf.equalizerSieve (F := F) x y) g.left ↔ _
    rw [← Sieve.overEquiv_symm_iff]
    simp only [OrderIso.symm_apply_apply]
  rw [← he, ← hrep g.left]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k.left, congrArg Over.Hom.left hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨Over.homMk k (by
      change k ≫ (ι ≫ T.hom) = V.hom
      rw [← Category.assoc, hk, Over.w g]), ?_⟩
    ext
    exact hk

variable {X : AlgebraicSpace S} {U : Over S}

/-- The square of an atlas scheme over the base, with its two projections. -/
abbrev pairOver (U : Over S) : Over S := Over.mk (pullback.fst U.hom U.hom ≫ U.hom)

/-- The first projection. -/
abbrev pairFst (U : Over S) : pairOver U ⟶ U := Over.homMk (pullback.fst U.hom U.hom) rfl

/-- The second projection. -/
abbrev pairSnd (U : Over S) : pairOver U ⟶ U := Over.homMk (pullback.snd U.hom U.hom) (by
  change pullback.snd U.hom U.hom ≫ U.hom = pullback.fst U.hom U.hom ≫ U.hom
  exact pullback.condition.symm)

/-- The pairing of two maps into the atlas scheme. -/
abbrev pairLift {T : Over S} (f f' : T ⟶ U) : T ⟶ pairOver U :=
  Over.homMk (pullback.lift f.left f'.left (by rw [Over.w f, Over.w f'])) (by
    change pullback.lift f.left f'.left _ ≫ pullback.fst U.hom U.hom ≫ U.hom = T.hom
    rw [pullback.lift_fst_assoc, Over.w f])

@[reassoc (attr := simp)]
theorem pairLift_fst {T : Over S} (f f' : T ⟶ U) : pairLift f f' ≫ pairFst U = f := by
  ext1
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pairLift_snd {T : Over S} (f f' : T ⟶ U) : pairLift f f' ≫ pairSnd U = f' := by
  ext1
  exact pullback.lift_snd _ _ _

/-- **Separatedness from a closed relation.** A space with an etale surjective atlas whose pairs
of atlas points with the same image are cut out by a closed immersion into the square of the
atlas scheme is separated. -/
theorem isSeparated_of_closed_relation (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) {E : Over S} (ι : E ⟶ pairOver U)
    [_root_.AlgebraicGeometry.IsClosedImmersion ι.left]
    (hι : RepresentsEqualizer ι (atlasSection a (pairFst U)) (atlasSection a (pairSnd U))) :
    IsSeparated X := by
  apply isClosedImmersion_diag_of_representsEqualizer
  intro T x y
  obtain ⟨W₁, e₁, v₁, he₁, hs₁, hv₁⟩ := exists_atlas_lift a ha hs x
  obtain ⟨W, e₂, v₂, he₂, hs₂, hv₂⟩ := exists_atlas_lift a ha hs (X.pullback e₁ y)
  let e : W ⟶ T := e₂ ≫ e₁
  have : Etale e.left := inferInstanceAs (Etale (e₂.left ≫ e₁.left))
  have : Surjective e.left := inferInstanceAs (Surjective (e₂.left ≫ e₁.left))
  have hx : X.pullback e x = atlasSection a (e₂ ≫ v₁) := by
    rw [X.pullback_comp, ← hv₁, atlasSection_pullback]
  have hy : X.pullback e y = atlasSection a v₂ := by
    rw [X.pullback_comp, ← hv₂]
  refine exists_closed_representsEqualizer_of_fppf_local X.toSheaf.property x y
    (Sieve.generate (Presieve.singleton e))
    (SpaceFilteredPoints.generate_singleton_mem_fppfTopology e) ?_
  rintro V g ⟨Y', h', f', hf', rfl⟩
  cases hf'
  let m : V ⟶ pairOver U := pairLift (h' ≫ e₂ ≫ v₁) (h' ≫ v₂)
  let Z : Over S := Over.mk (pullback.fst m.left ι.left ≫ V.hom)
  let ιg : Z ⟶ V := Over.homMk (pullback.fst m.left ι.left) rfl
  let σ : Z ⟶ E := Over.homMk (pullback.snd m.left ι.left) (by
    change pullback.snd m.left ι.left ≫ E.hom = pullback.fst m.left ι.left ≫ V.hom
    rw [← Over.w ι, ← pullback.condition_assoc, Over.w m])
  have hσ : σ ≫ ι = ιg ≫ m := by
    ext1
    exact pullback.condition.symm
  refine ⟨Z, ιg, inferInstanceAs
    (_root_.AlgebraicGeometry.IsClosedImmersion (pullback.fst m.left ι.left)), fun T' k => ?_⟩
  have k₁ : X.presheaf.map k.op (X.presheaf.map (h' ≫ e).op x) =
      atlasSection a ((k ≫ m) ≫ pairFst U) := by
    change X.pullback k (X.pullback (h' ≫ e) x) = _
    rw [← X.pullback_comp, show k ≫ h' ≫ e = (k ≫ h') ≫ e by simp, X.pullback_comp, hx,
      atlasSection_pullback]
    simp [m]
  have k₂ : X.presheaf.map k.op (X.presheaf.map (h' ≫ e).op y) =
      atlasSection a ((k ≫ m) ≫ pairSnd U) := by
    change X.pullback k (X.pullback (h' ≫ e) y) = _
    rw [← X.pullback_comp, show k ≫ h' ≫ e = (k ≫ h') ≫ e by simp, X.pullback_comp, hy,
      atlasSection_pullback]
    simp [m]
  rw [k₁, k₂, ← atlasSection_pullback a (k ≫ m) (pairFst U),
    ← atlasSection_pullback a (k ≫ m) (pairSnd U)]
  change _ ↔ X.presheaf.map (k ≫ m).op _ = X.presheaf.map (k ≫ m).op _
  rw [← hι (k ≫ m)]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z ≫ σ, by rw [Category.assoc, hσ, Category.assoc]⟩
  · rintro ⟨z, hz⟩
    refine ⟨Over.homMk (pullback.lift k.left z.left (congrArg Over.Hom.left hz).symm) (by
      change pullback.lift k.left z.left _ ≫ pullback.fst m.left ι.left ≫ V.hom = T'.hom
      rw [pullback.lift_fst_assoc, Over.w k]), ?_⟩
    ext1
    exact pullback.lift_fst _ _ _

end Separated

section KernelPair

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- The kernel pair of an etale atlas of a separated space: its projections are etale, form an
equivalence relation, and pair into a closed immersion into the square of the atlas scheme. -/
theorem exists_closed_kernel_pair (hX : IsSeparated X) (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) :
    ∃ (R : Over S) (r₁ r₂ : R ⟶ U),
      IsPullback ((schemeYoneda S).map r₁) ((schemeYoneda S).map r₂) a a ∧
      Etale r₁.left ∧ Etale r₂.left ∧ AtlasRelation.IsEquivRel r₁.left r₂.left ∧
      _root_.AlgebraicGeometry.IsClosedImmersion (pairLift r₁ r₂).left := by
  obtain ⟨R, r₁, r₂, h, hrel⟩ := AtlasRelation.exists_kernelPair a ha.representable
  refine ⟨R, r₁, r₂, h, ha.projection a _ r₁ h.flip, ha.projection a _ r₂ h, hrel, ?_⟩
  obtain ⟨E, ι, hι, hci⟩ := exists_representsEqualizer_of_relative_diag
    (P := @_root_.AlgebraicGeometry.IsClosedImmersion) hX
    (atlasSection a (pairFst U)) (atlasSection a (pairSnd U))
  have : _root_.AlgebraicGeometry.IsClosedImmersion ι.left := hci
  have : Mono ι := Over.mono_of_mono_left ι
  have hR : atlasSection a r₁ = atlasSection a r₂ :=
    congrArg (fun φ : (schemeYoneda S).obj R ⟶ X.presheaf => φ.app (op R) ⟨𝟙 R⟩) h.w
  obtain ⟨φ, hφ⟩ := (hι (pairLift r₁ r₂)).2 (by
    change X.pullback (pairLift r₁ r₂) (atlasSection a (pairFst U)) =
      X.pullback (pairLift r₁ r₂) (atlasSection a (pairSnd U))
    rw [atlasSection_pullback, atlasSection_pullback, pairLift_fst, pairLift_snd]
    exact hR)
  have hE : atlasSection a (ι ≫ pairFst U) = atlasSection a (ι ≫ pairSnd U) := by
    have := (hι ι).1 ⟨𝟙 _, Category.id_comp _⟩
    change X.pullback ι (atlasSection a (pairFst U)) = X.pullback ι (atlasSection a (pairSnd U))
      at this
    rwa [atlasSection_pullback, atlasSection_pullback] at this
  have hw : (schemeYoneda S).map (ι ≫ pairFst U) ≫ a = (schemeYoneda S).map (ι ≫ pairSnd U) ≫ a := by
    apply uliftYonedaEquiv.{u + 1}.injective
    change a.app (op E) ⟨𝟙 E ≫ (ι ≫ pairFst U)⟩ = a.app (op E) ⟨𝟙 E ≫ (ι ≫ pairSnd U)⟩
    rw [Category.id_comp, Category.id_comp]
    exact hE
  obtain ⟨ψ, hψ⟩ := (schemeYoneda S).map_surjective (h.lift _ _ hw)
  have hψ₁ : ψ ≫ r₁ = ι ≫ pairFst U :=
    (schemeYoneda S).map_injective (by rw [Functor.map_comp, hψ, IsPullback.lift_fst])
  have hψ₂ : ψ ≫ r₂ = ι ≫ pairSnd U :=
    (schemeYoneda S).map_injective (by rw [Functor.map_comp, hψ, IsPullback.lift_snd])
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply (schemeYoneda S).map_injective
    apply h.hom_ext
    · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, hψ₁, reassoc_of% hφ,
        pairLift_fst, Category.id_comp]
    · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, hψ₂, reassoc_of% hφ,
        pairLift_snd, Category.id_comp]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    rw [← cancel_mono ι, Category.assoc, hφ, Category.id_comp]
    ext1
    apply pullback.hom_ext
    · change ψ.left ≫ pullback.lift r₁.left r₂.left _ ≫ pullback.fst U.hom U.hom =
        ι.left ≫ pullback.fst U.hom U.hom
      rw [pullback.lift_fst]
      exact congrArg CommaMorphism.left hψ₁
    · change ψ.left ≫ pullback.lift r₁.left r₂.left _ ≫ pullback.snd U.hom U.hom =
        ι.left ≫ pullback.snd U.hom U.hom
      rw [pullback.lift_snd]
      exact congrArg CommaMorphism.left hψ₂
  have : IsIso φ := ⟨ψ, hφψ, hψφ⟩
  have : IsIso φ.left := (Over.forget _).map_isIso φ
  rw [← hφ, Over.comp_left]
  infer_instance

end KernelPair

section Calculus

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ i, IsAffine (D.obj i)] {c : Cone D} (hc : IsLimit c)
  {W V : Scheme.{u}} {g : W ⟶ c.pt} {i : I} {q : V ⟶ D.obj i} {π : W ⟶ V}

include hc in
/-- On an affine model, a morphism from the limit model to a locally finitely presented scheme
over the stage comes from a later stage of the model. -/
theorem exists_stage_lift [IsAffine V] {T : Scheme.{u}} (r : T ⟶ D.obj i)
    [LocallyOfFinitePresentation r] (b : W ⟶ T) (hb : b ≫ r = g ≫ c.π.app i)
    (hpb : IsPullback π g q (c.π.app i)) :
    ∃ (j : I) (f : j ⟶ i) (h : Limits.pullback (D.map f) q ⟶ T),
      modelLift c hpb f ≫ h = b ∧ h ≫ r = pullback.fst (D.map f) q ≫ D.map f := by
  let Dw := TargetLimit.diagram (overDiagram D i) (overStructure D i) q
  let tS : Dw ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    TargetLimit.comparison (overDiagram D i) (overStructure D i) q ≫
      (Functor.const (Over i)).map q
  let Cw := TargetLimit.coneOfPullback (overDiagram D i) (overStructure D i) q
    (c.whisker (Over.forget i)) (c.π.app i) (overCone_π_comp i c) hpb.flip
  have hCw : IsLimit Cw := TargetLimit.isLimitConeOfPullback _ _ _ _ _ _ _
    (overConeIsLimit i c hc)
  obtain ⟨l, h, hh₁, hh₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    Dw tS r Cw hCw b (by
      ext l
      simp only [tS, NatTrans.comp_app, Functor.const_map_app, TargetLimit.comparison, Cw,
        TargetLimit.coneOfPullback_π_snd_assoc]
      rw [hb, hpb.w])
  have hπ : (Cw.π.app l : W ⟶ Limits.pullback (D.map l.hom) q) = modelLift c hpb l.hom := by
    apply pullback.hom_ext
    · exact (TargetLimit.coneOfPullback_π_fst (overDiagram D i) (overStructure D i) q
        (c.whisker (Over.forget i)) (c.π.app i) (overCone_π_comp i c) hpb.flip l).trans
        (pullback.lift_fst _ _ _).symm
    · exact (TargetLimit.coneOfPullback_π_snd (overDiagram D i) (overStructure D i) q
        (c.whisker (Over.forget i)) (c.π.app i) (overCone_π_comp i c) hpb.flip l).trans
        (pullback.lift_snd _ _ _).symm
  refine ⟨l.left, l.hom, h, by rw [← hπ]; exact hh₁, ?_⟩
  rw [hh₂]
  change pullback.snd (D.map l.hom) q ≫ q = _
  exact pullback.condition.symm

include hc in
/-- **Descent of morphisms between models.** A morphism over the limit between two schemes
with models at a stage, the source model affine and the target model locally finitely
presented, comes from a morphism between the models at a later stage. -/
theorem exists_model_hom [IsAffine V] {W₂ V₂ : Scheme.{u}} {g₂ : W₂ ⟶ c.pt}
    {q₂ : V₂ ⟶ D.obj i} {π₂ : W₂ ⟶ V₂} [LocallyOfFinitePresentation q₂]
    (hpb : IsPullback π g q (c.π.app i)) (hpb₂ : IsPullback π₂ g₂ q₂ (c.π.app i))
    (φ : W ⟶ W₂) (hφ : φ ≫ g₂ = g) :
    ∃ (j : I) (f : j ⟶ i)
      (ψ : Limits.pullback (D.map f) q ⟶ Limits.pullback (D.map f) q₂),
      ψ ≫ pullback.fst (D.map f) q₂ = pullback.fst (D.map f) q ∧
      modelLift c hpb f ≫ ψ = φ ≫ modelLift c hpb₂ f := by
  obtain ⟨j, f, h, hh₁, hh₂⟩ := exists_stage_lift hc q₂ (φ ≫ π₂)
    (by rw [Category.assoc, hpb₂.w, reassoc_of% hφ]) hpb
  refine ⟨j, f, pullback.lift (pullback.fst (D.map f) q) h hh₂.symm,
    pullback.lift_fst _ _ _, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, modelLift]
    rw [reassoc_of% hφ]
  · simp only [Category.assoc, pullback.lift_snd, modelLift]
    exact hh₁

include hc in
/-- **Eventual equality on models.** Two morphisms from an affine model to a scheme locally of
finite type over the stage agree at a later stage once they agree on the limit model. -/
theorem exists_eq_model [IsAffine V] {T : Scheme.{u}} (r : T ⟶ D.obj i)
    [LocallyOfFiniteType r] (h h' : V ⟶ T) (hh : h ≫ r = q) (hh' : h' ≫ r = q)
    (hpb : IsPullback π g q (c.π.app i)) (e : π ≫ h = π ≫ h') :
    ∃ (j : I) (f : j ⟶ i),
      pullback.snd (D.map f) q ≫ h = pullback.snd (D.map f) q ≫ h' := by
  let Dw := TargetLimit.diagram (overDiagram D i) (overStructure D i) q
  let tS : Dw ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    TargetLimit.comparison (overDiagram D i) (overStructure D i) q ≫
      (Functor.const (Over i)).map q
  let Cw := TargetLimit.coneOfPullback (overDiagram D i) (overStructure D i) q
    (c.whisker (Over.forget i)) (c.π.app i) (overCone_π_comp i c) hpb.flip
  have hCw : IsLimit Cw := TargetLimit.isLimitConeOfPullback _ _ _ _ _ _ _
    (overConeIsLimit i c hc)
  let o : Over i := Over.mk (𝟙 i)
  have hsnd : Cw.π.app o ≫ pullback.snd (D.map (𝟙 i)) q = π :=
    TargetLimit.coneOfPullback_π_snd (overDiagram D i) (overStructure D i) q
      (c.whisker (Over.forget i)) (c.π.app i) (overCone_π_comp i c) hpb.flip o
  obtain ⟨k, hko, hk⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    Dw tS r Cw hCw (i := o) (pullback.snd (D.map (𝟙 i)) q ≫ h)
    (pullback.snd (D.map (𝟙 i)) q ≫ h')
    (by
      change pullback.snd (D.map (𝟙 i)) q ≫ q = (pullback.snd (D.map (𝟙 i)) q ≫ h) ≫ r
      rw [Category.assoc, hh])
    (by
      change pullback.snd (D.map (𝟙 i)) q ≫ q = (pullback.snd (D.map (𝟙 i)) q ≫ h') ≫ r
      rw [Category.assoc, hh'])
    (by rw [← Category.assoc, hsnd, ← Category.assoc, hsnd, e])
  refine ⟨k.left, k.hom, ?_⟩
  have h₀ : Dw.map hko ≫ pullback.snd (D.map (𝟙 i)) q = pullback.snd (D.map k.hom) q :=
    targetLimit_map_snd (overDiagram D i) (overStructure D i) q hko
  rw [← h₀, Category.assoc, Category.assoc]
  exact hk

end Calculus

section Restrict

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {i j : I}

/-- Restriction of a morphism between schemes over a stage along a transition map. -/
abbrev resHom {V₁ V₂ : Scheme.{u}} {q₁ : V₁ ⟶ D.obj i} {q₂ : V₂ ⟶ D.obj i} (ψ : V₁ ⟶ V₂)
    (hψ : ψ ≫ q₂ = q₁) (f : j ⟶ i) :
    Limits.pullback (D.map f) q₁ ⟶ Limits.pullback (D.map f) q₂ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ψ)
    (by rw [Category.assoc, hψ, pullback.condition])

section

variable {V₁ V₂ V₃ : Scheme.{u}} {q₁ : V₁ ⟶ D.obj i} {q₂ : V₂ ⟶ D.obj i} {q₃ : V₃ ⟶ D.obj i}
  (ψ : V₁ ⟶ V₂) (hψ : ψ ≫ q₂ = q₁) (f : j ⟶ i)

@[reassoc (attr := simp)]
theorem resHom_fst : resHom ψ hψ f ≫ pullback.fst (D.map f) q₂ = pullback.fst (D.map f) q₁ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem resHom_snd :
    resHom ψ hψ f ≫ pullback.snd (D.map f) q₂ = pullback.snd (D.map f) q₁ ≫ ψ :=
  pullback.lift_snd _ _ _

theorem resHom_comp (χ : V₂ ⟶ V₃) (hχ : χ ≫ q₃ = q₂) :
    resHom ψ hψ f ≫ resHom χ hχ f =
      resHom (ψ ≫ χ) (by rw [Category.assoc, hχ, hψ]) f := by
  apply pullback.hom_ext <;> simp

theorem resHom_id : resHom (𝟙 V₁) (Category.id_comp q₁) f = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

theorem modelLift_resHom (c : Cone D) {W₁ W₂ : Scheme.{u}} {g₁ : W₁ ⟶ c.pt} {g₂ : W₂ ⟶ c.pt}
    {π₁ : W₁ ⟶ V₁} {π₂ : W₂ ⟶ V₂} (hpb₁ : IsPullback π₁ g₁ q₁ (c.π.app i))
    (hpb₂ : IsPullback π₂ g₂ q₂ (c.π.app i)) (φ : W₁ ⟶ W₂) (hφ : φ ≫ g₂ = g₁)
    (hcomp : π₁ ≫ ψ = φ ≫ π₂) :
    modelLift c hpb₁ f ≫ resHom ψ hψ f = φ ≫ modelLift c hpb₂ f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, modelLift, pullback.lift_fst]
    rw [reassoc_of% hφ]
  · simp only [Category.assoc, modelLift, pullback.lift_snd_assoc, pullback.lift_snd]
    exact hcomp

end

section Pointwise

variable {VU VR : Scheme.{u}}

/-- Reflexivity of a pair of maps on points. -/
def PointRefl (t s : VR ⟶ VU) : Prop :=
  ∀ (T : Scheme.{u}) (x : T ⟶ VU), ∃ r : T ⟶ VR, r ≫ t = x ∧ r ≫ s = x

/-- Symmetry of a pair of maps on points. -/
def PointSymm (t s : VR ⟶ VU) : Prop :=
  ∀ (T : Scheme.{u}) (r : T ⟶ VR), ∃ r' : T ⟶ VR, r' ≫ t = r ≫ s ∧ r' ≫ s = r ≫ t

/-- Transitivity of a pair of maps on points. -/
def PointTrans (t s : VR ⟶ VU) : Prop :=
  ∀ (T : Scheme.{u}) (r r' : T ⟶ VR), r ≫ s = r' ≫ t →
    ∃ r'' : T ⟶ VR, r'' ≫ t = r ≫ t ∧ r'' ≫ s = r' ≫ s

variable {qU : VU ⟶ D.obj i} {qR : VR ⟶ D.obj i} {t s : VR ⟶ VU}
  (ht : t ≫ qU = qR) (hs : s ≫ qU = qR) (f : j ⟶ i)

include ht in
theorem PointRefl.res (h : PointRefl t s) : PointRefl (resHom t ht f) (resHom s hs f) := by
  intro T x
  obtain ⟨r₀, h₁, h₂⟩ := h T (x ≫ pullback.snd _ _)
  refine ⟨pullback.lift (x ≫ pullback.fst _ _) r₀ ?_, ?_, ?_⟩
  · rw [show r₀ ≫ qR = r₀ ≫ t ≫ qU by rw [ht], ← Category.assoc r₀, h₁]
    simp only [Category.assoc, pullback.condition]
  · apply pullback.hom_ext <;> simp [h₁]
  · apply pullback.hom_ext <;> simp [h₂]

include ht in
theorem PointSymm.res (h : PointSymm t s) : PointSymm (resHom t ht f) (resHom s hs f) := by
  intro T r
  obtain ⟨r₀, h₁, h₂⟩ := h T (r ≫ pullback.snd _ _)
  refine ⟨pullback.lift (r ≫ pullback.fst _ _) r₀ ?_, ?_, ?_⟩
  · rw [show r₀ ≫ qR = r₀ ≫ t ≫ qU by rw [ht], ← Category.assoc r₀, h₁]
    simp only [Category.assoc, hs, pullback.condition]
  · apply pullback.hom_ext <;> simp [h₁]
  · apply pullback.hom_ext <;> simp [h₂]

include ht hs in
theorem PointTrans.res (h : PointTrans t s) : PointTrans (resHom t ht f) (resHom s hs f) := by
  intro T r r' hrr
  have e₁ : r ≫ pullback.fst _ _ = r' ≫ pullback.fst _ _ := by
    simpa using congrArg (· ≫ pullback.fst (D.map f) qU) hrr
  have e₂ : (r ≫ pullback.snd _ _) ≫ s = (r' ≫ pullback.snd _ _) ≫ t := by
    simpa using congrArg (· ≫ pullback.snd (D.map f) qU) hrr
  obtain ⟨r₀, h₁, h₂⟩ := h T _ _ e₂
  refine ⟨pullback.lift (r ≫ pullback.fst _ _) r₀ ?_, ?_, ?_⟩
  · rw [show r₀ ≫ qR = r₀ ≫ t ≫ qU by rw [ht], ← Category.assoc r₀, h₁]
    simp only [Category.assoc, ht, pullback.condition]
  · apply pullback.hom_ext <;> simp [h₁]
  · apply pullback.hom_ext
    · simp [e₁]
    · simp [h₂]

end Pointwise

end Restrict

section FibreProduct

variable {T B : Scheme.{u}} (p : T ⟶ B)

/-- Models of a fibre product: the fibre product of models of the factors over a model of the
base is a model of the fibre product. -/
theorem isPullback_model_pullback {A B' E VA VB VE : Scheme.{u}}
    {gA : A ⟶ T} {gB : B' ⟶ T} {gE : E ⟶ T}
    {qA : VA ⟶ B} {qB : VB ⟶ B} {qE : VE ⟶ B}
    {πA : A ⟶ VA} {πB : B' ⟶ VB} {πE : E ⟶ VE}
    (hA : IsPullback πA gA qA p) (hB : IsPullback πB gB qB p)
    (hE : IsPullback πE gE qE p)
    (α : A ⟶ E) (β : B' ⟶ E) (hα : α ≫ gE = gA) (hβ : β ≫ gE = gB)
    (αi : VA ⟶ VE) (βi : VB ⟶ VE) (hαi : αi ≫ qE = qA) (hβi : βi ≫ qE = qB)
    (cα : πA ≫ αi = α ≫ πE) (cβ : πB ≫ βi = β ≫ πE) :
    IsPullback (pullback.map α β αi βi πA πB πE cα.symm cβ.symm)
      (pullback.fst α β ≫ gA) (pullback.fst αi βi ≫ qA) p := by
  have w : pullback.map α β αi βi πA πB πE cα.symm cβ.symm ≫ pullback.fst αi βi ≫ qA =
      (pullback.fst α β ≫ gA) ≫ p := by
    rw [pullback.lift_fst_assoc, Category.assoc, hA.w, Category.assoc]
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ w)
    (PullbackCone.IsLimit.mk w (fun s => ?_) (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · exact pullback.lift (hA.lift (s.fst ≫ pullback.fst αi βi) s.snd
      (by rw [Category.assoc]; exact s.condition))
      (hB.lift (s.fst ≫ pullback.snd αi βi) s.snd (by
        rw [Category.assoc, ← hβi, ← pullback.condition_assoc, hαi]
        exact s.condition))
      (by
        apply hE.hom_ext
        · simp only [Category.assoc]
          rw [← cα, ← cβ, hA.lift_fst_assoc, hB.lift_fst_assoc]
          simp only [Category.assoc, pullback.condition]
        · simp only [Category.assoc]
          rw [hα, hβ, hA.lift_snd, hB.lift_snd])
  · apply pullback.hom_ext
    · simp
    · simp
  · simp
  · apply pullback.hom_ext
    · apply hA.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, IsPullback.lift_fst]
        rw [← hm₁]
        simp
      · simp only [Category.assoc, pullback.lift_fst, IsPullback.lift_snd]
        rw [← hm₂]
    · apply hB.hom_ext
      · simp only [Category.assoc, pullback.lift_snd, IsPullback.lift_fst]
        rw [← hm₁]
        simp
      · simp only [Category.assoc, pullback.lift_snd, IsPullback.lift_snd]
        rw [← hm₂, ← hβ, ← pullback.condition_assoc, hα]

end FibreProduct

/-- The restriction of a morphism between schemes over a stage is its base change. -/
theorem isPullback_resHom {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {i j : I}
    {V₁ V₂ : Scheme.{u}} {q₁ : V₁ ⟶ D.obj i} {q₂ : V₂ ⟶ D.obj i} (ψ : V₁ ⟶ V₂)
    (hψ : ψ ≫ q₂ = q₁) (f : j ⟶ i) :
    IsPullback (pullback.snd (D.map f) q₁) (resHom ψ hψ f) ψ (pullback.snd (D.map f) q₂) := by
  refine IsPullback.of_bot (v₂₁ := pullback.fst (D.map f) q₂) (v₂₂ := q₂) (h₃₁ := D.map f) ?_
    (resHom_snd ψ hψ f).symm (IsPullback.of_hasPullback (D.map f) q₂).flip
  rw [resHom_fst, hψ]
  exact (IsPullback.of_hasPullback (D.map f) q₁).flip

section PropertyDescent

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ i, IsAffine (D.obj i)] {c : Cone D} (hc : IsLimit c) {i : I}
  {W₁ W₂ V₁ V₂ : Scheme.{u}} {g₁ : W₁ ⟶ c.pt} {g₂ : W₂ ⟶ c.pt}
  {q₁ : V₁ ⟶ D.obj i} {q₂ : V₂ ⟶ D.obj i} {π₁ : W₁ ⟶ V₁} {π₂ : W₂ ⟶ V₂}
  (hpb₁ : IsPullback π₁ g₁ q₁ (c.π.app i)) (hpb₂ : IsPullback π₂ g₂ q₂ (c.π.app i))
  (ψ : V₁ ⟶ V₂) (hψ : ψ ≫ q₂ = q₁) (φ : W₁ ⟶ W₂) (hφ : φ ≫ g₂ = g₁)
  (hcomp : π₁ ≫ ψ = φ ≫ π₂)

omit [IsCofiltered I] [∀ i, IsAffine (D.obj i)] in
include hφ hcomp in
/-- The base change of a morphism between models to the limit is the limit morphism. -/
theorem baseChangeMap_cone_eq :
    AffineLimit.baseChangeMap q₁ q₂ ψ hψ (c.π.app i) =
      hpb₁.flip.isoPullback.inv ≫ φ ≫ hpb₂.flip.isoPullback.hom := by
  rw [Iso.eq_inv_comp]
  apply pullback.hom_ext
  · simp [hφ]
  · simpa using hcomp

omit [IsCofiltered I] [∀ i, IsAffine (D.obj i)] in
include hpb₁ hpb₂ hφ hcomp in
/-- A property of the limit morphism that descends along the limit holds for a restriction of
the model morphism. -/
theorem exists_res_property (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hdesc : P (AffineLimit.baseChangeMap q₁ q₂ ψ hψ (c.π.app i)) →
      ∃ l : Over i, P (AffineLimit.baseChangeMap q₁ q₂ ψ hψ ((overStructure D i).app l)))
    (hP : P φ) : ∃ (j : I) (f : j ⟶ i), P (resHom ψ hψ f) := by
  obtain ⟨l, hl⟩ := hdesc (by
    rw [baseChangeMap_cone_eq hpb₁ hpb₂ ψ hψ φ hφ hcomp]
    exact MorphismProperty.RespectsIso.precomp P _ _
      (MorphismProperty.RespectsIso.postcomp P _ _ hP))
  exact ⟨l.left, l.hom, hl⟩

include hc hpb₁ hpb₂ hφ hcomp in
/-- Flatness of the limit morphism holds for a restriction of an affine model morphism. -/
theorem exists_res_flat [IsAffine V₁] [IsAffine V₂] [LocallyOfFinitePresentation ψ]
    [Flat φ] : ∃ (j : I) (f : j ⟶ i), Flat (resHom ψ hψ f) :=
  exists_res_property hpb₁ hpb₂ ψ hψ φ hφ hcomp @Flat
    (AffineLimit.relativeFlatDescent (overDiagram D i) (overStructure D i) q₁ q₂ ψ hψ
      (c.whisker (Over.forget i)) (overConeIsLimit i c hc) (c.π.app i)
      (overCone_π_comp i c)).mp inferInstance

end PropertyDescent

section EtaleDescent

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ i, IsAffine (D.obj i)] {c : Cone D} (hc : IsLimit c) {i : I}

omit [IsCofiltered I] [∀ i, IsAffine (D.obj i)] in
/-- The diagonal of a restricted morphism is the restriction of the diagonal, up to the
canonical isomorphism of fibre products. -/
theorem isOpenImmersion_diagonal_resHom {j : I} {V₁ V₂ : Scheme.{u}} {q₁ : V₁ ⟶ D.obj i}
    {q₂ : V₂ ⟶ D.obj i} (ψ : V₁ ⟶ V₂) (hψ : ψ ≫ q₂ = q₁) (f : j ⟶ i)
    (h : _root_.AlgebraicGeometry.IsOpenImmersion
      (resHom (pullback.diagonal ψ) (by simp : pullback.diagonal ψ ≫ pullback.fst ψ ψ ≫ q₁ = q₁)
        f)) :
    _root_.AlgebraicGeometry.IsOpenImmersion (pullback.diagonal (resHom ψ hψ f)) := by
  have hA := (IsPullback.of_hasPullback (D.map f) q₁).flip
  have hE := (IsPullback.of_hasPullback (D.map f) q₂).flip
  have hP := isPullback_model_pullback (D.map f) hA hA hE (resHom ψ hψ f) (resHom ψ hψ f)
    (resHom_fst ψ hψ f) (resHom_fst ψ hψ f) ψ ψ hψ hψ (resHom_snd ψ hψ f).symm
    (resHom_snd ψ hψ f).symm
  let e := hP.flip.isoPullback
  have he : pullback.diagonal (resHom ψ hψ f) ≫ e.hom =
      resHom (pullback.diagonal ψ) (by simp) f := by
    apply pullback.hom_ext
    · simp [e]
    · simp only [e, Category.assoc, IsPullback.isoPullback_hom_snd, resHom_snd]
      apply pullback.hom_ext <;> simp
  have : pullback.diagonal (resHom ψ hψ f) = resHom (pullback.diagonal ψ) (by simp) f ≫ e.inv := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this]
  infer_instance

variable {W₁ W₂ V₁ V₂ : Scheme.{u}} {g₁ : W₁ ⟶ c.pt} {g₂ : W₂ ⟶ c.pt}
  {q₁ : V₁ ⟶ D.obj i} {q₂ : V₂ ⟶ D.obj i} {π₁ : W₁ ⟶ V₁} {π₂ : W₂ ⟶ V₂}
  (hpb₁ : IsPullback π₁ g₁ q₁ (c.π.app i)) (hpb₂ : IsPullback π₂ g₂ q₂ (c.π.app i))
  (ψ : V₁ ⟶ V₂) (hψ : ψ ≫ q₂ = q₁) (φ : W₁ ⟶ W₂) (hφ : φ ≫ g₂ = g₁)
  (hcomp : π₁ ≫ ψ = φ ≫ π₂)

include hc hpb₁ hpb₂ hφ hcomp in
/-- An unramified limit morphism has unramified restrictions of an affine model morphism. -/
theorem exists_res_isOpenImmersion_diagonal [IsAffine V₁] [IsAffine V₂]
    [LocallyOfFinitePresentation q₁] [LocallyOfFinitePresentation ψ]
    [_root_.AlgebraicGeometry.IsOpenImmersion
      (pullback.diagonal φ)] :
    ∃ (j : I) (f : j ⟶ i),
      _root_.AlgebraicGeometry.IsOpenImmersion (pullback.diagonal (resHom ψ hψ f)) := by
  have hP := isPullback_model_pullback (c.π.app i) hpb₁ hpb₁ hpb₂ φ φ hφ hφ ψ ψ hψ hψ hcomp hcomp
  have : MorphismProperty.RespectsIso @_root_.AlgebraicGeometry.IsOpenImmersion.{u} :=
    inferInstance
  have : LocallyOfFinitePresentation (pullback.fst ψ ψ ≫ q₁) := inferInstance
  obtain ⟨j, f, h⟩ := exists_res_property hpb₁ hP (pullback.diagonal ψ) (by simp)
    (pullback.diagonal φ) (by simp) (by apply pullback.hom_ext <;> simp)
    @_root_.AlgebraicGeometry.IsOpenImmersion
    (AffineLimit.relativeOpenImmersionDescent (overDiagram D i) (overStructure D i) q₁
      (pullback.fst ψ ψ ≫ q₁) (pullback.diagonal ψ) (by simp)
      (c.whisker (Over.forget i)) (overConeIsLimit i c hc) (c.π.app i)
      (overCone_π_comp i c)).mp inferInstance
  exact ⟨j, f, isOpenImmersion_diagonal_resHom ψ hψ f h⟩

include hc hpb₁ hpb₂ hφ hcomp in
/-- An etale limit morphism has etale iterated restrictions of an affine model morphism. -/
theorem exists_res_etale [IsAffine V₁] [IsAffine V₂] [LocallyOfFinitePresentation q₁]
    [LocallyOfFinitePresentation q₂] [LocallyOfFinitePresentation ψ] [Etale φ] :
    ∃ (j₁ : I) (f₁ : j₁ ⟶ i) (j₂ : I) (f₂ : j₂ ⟶ j₁),
      Etale (resHom (resHom ψ hψ f₁) (resHom_fst ψ hψ f₁) f₂) := by
  obtain ⟨j₁, f₁, hfl⟩ := exists_res_flat hc hpb₁ hpb₂ ψ hψ φ hφ hcomp
  have hpb₁' := isPullback_modelLift c hpb₁ f₁
  have hpb₂' := isPullback_modelLift c hpb₂ f₁
  have hcomp₁ := modelLift_resHom ψ hψ f₁ c hpb₁ hpb₂ φ hφ hcomp
  have : LocallyOfFinitePresentation (resHom ψ hψ f₁) :=
    MorphismProperty.of_isPullback (isPullback_resHom ψ hψ f₁) inferInstance
  obtain ⟨j₂, f₂, hdiag⟩ := exists_res_isOpenImmersion_diagonal hc hpb₁' hpb₂'
    (resHom ψ hψ f₁) (resHom_fst ψ hψ f₁) φ hφ hcomp₁
  refine ⟨j₁, f₁, j₂, f₂, ?_⟩
  have : Flat (resHom (resHom ψ hψ f₁) (resHom_fst ψ hψ f₁) f₂) :=
    MorphismProperty.of_isPullback (isPullback_resHom _ (resHom_fst ψ hψ f₁) f₂) hfl
  have : LocallyOfFinitePresentation (resHom (resHom ψ hψ f₁) (resHom_fst ψ hψ f₁) f₂) :=
    MorphismProperty.of_isPullback (isPullback_resHom _ (resHom_fst ψ hψ f₁) f₂) inferInstance
  exact Etale.of_formallyUnramified_of_flat _

section ClosedPairing

variable {U R : Scheme.{u}} {gU : U ⟶ c.pt} {gR : R ⟶ c.pt} {VU VR : Scheme.{u}}
  {qU : VU ⟶ D.obj i} {qR : VR ⟶ D.obj i} {πU : U ⟶ VU} {πR : R ⟶ VR}
  (hU : IsPullback πU gU qU (c.π.app i)) (hR : IsPullback πR gR qR (c.π.app i))
  {r₁ r₂ : R ⟶ U} (hr₁ : r₁ ≫ gU = gR) (hr₂ : r₂ ≫ gU = gR)
  {t s : VR ⟶ VU} (ht : t ≫ qU = qR) (hs : s ≫ qU = qR)
  (ct : πR ≫ t = r₁ ≫ πU) (cs : πR ≫ s = r₂ ≫ πU)

include hc hU hR hr₁ ct cs in
/-- A closed limit pairing has closed restrictions of the model pairing. -/
theorem exists_res_closedImmersion_pairing [IsAffine VU] [IsAffine VR]
    [LocallyOfFinitePresentation qU] [LocallyOfFinitePresentation qR]
    (hcl : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.lift r₁ r₂ (by rw [hr₁, hr₂]) : R ⟶ Limits.pullback gU gU)) :
    ∃ (j : I) (f : j ⟶ i), _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.lift (resHom t ht f) (resHom s hs f) (by rw [resHom_fst, resHom_fst]) :
        Limits.pullback (D.map f) qR ⟶
          Limits.pullback (pullback.fst (D.map f) qU) (pullback.fst (D.map f) qU)) := by
  have hE : IsPullback (c.π.app i) (𝟙 c.pt) (𝟙 (D.obj i)) (c.π.app i) := IsPullback.of_id_snd
  have hPU := isPullback_model_pullback (c.π.app i) hU hU hE gU gU (Category.comp_id _)
    (Category.comp_id _) qU qU (Category.comp_id _) (Category.comp_id _) hU.w hU.w
  let ψ : VR ⟶ Limits.pullback qU qU := pullback.lift t s (ht.trans hs.symm)
  have hψ : ψ ≫ pullback.fst qU qU ≫ qU = qR := by simp [ψ, ht]
  have : LocallyOfFiniteType (ψ ≫ pullback.fst qU qU ≫ qU) := by rw [hψ]; infer_instance
  have : LocallyOfFiniteType ψ := locallyOfFiniteType_of_comp ψ (pullback.fst qU qU ≫ qU)
  have : MorphismProperty.RespectsIso @_root_.AlgebraicGeometry.IsClosedImmersion.{u} :=
    inferInstance
  obtain ⟨j, f, h⟩ := exists_res_property hR hPU ψ hψ
    (pullback.lift r₁ r₂ (by rw [hr₁, hr₂])) (by simp [hr₁])
    (by apply pullback.hom_ext <;> simp [ψ, ct, cs])
    @_root_.AlgebraicGeometry.IsClosedImmersion
    (AffineLimit.relativeClosedImmersionDescent (overDiagram D i) (overStructure D i) qR
      (pullback.fst qU qU ≫ qU) ψ hψ (c.whisker (Over.forget i)) (overConeIsLimit i c hc)
      (c.π.app i) (overCone_π_comp i c)).mp hcl
  refine ⟨j, f, ?_⟩
  have hA := (IsPullback.of_hasPullback (D.map f) qU).flip
  have hE' : IsPullback (D.map f) (𝟙 (D.obj j)) (𝟙 (D.obj i)) (D.map f) := IsPullback.of_id_snd
  have hP := isPullback_model_pullback (D.map f) hA hA hE' (pullback.fst (D.map f) qU)
    (pullback.fst (D.map f) qU) (Category.comp_id _) (Category.comp_id _) qU qU
    (Category.comp_id _) (Category.comp_id _) pullback.condition.symm pullback.condition.symm
  let e := hP.flip.isoPullback
  have he : (pullback.lift (resHom t ht f) (resHom s hs f) (by rw [resHom_fst, resHom_fst]) :
      Limits.pullback (D.map f) qR ⟶
        Limits.pullback (pullback.fst (D.map f) qU) (pullback.fst (D.map f) qU)) ≫ e.hom =
      resHom ψ hψ f := by
    apply pullback.hom_ext
    · simp [e]
    · simp only [e, Category.assoc, IsPullback.isoPullback_hom_snd, resHom_snd]
      apply pullback.hom_ext <;> simp [ψ]
  rw [show (pullback.lift (resHom t ht f) (resHom s hs f) (by rw [resHom_fst, resHom_fst]) :
      Limits.pullback (D.map f) qR ⟶
        Limits.pullback (pullback.fst (D.map f) qU) (pullback.fst (D.map f) qU)) =
      resHom ψ hψ f ≫ e.inv by rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]]
  infer_instance

end ClosedPairing

end EtaleDescent

section RelationModels

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ i, IsAffine (D.obj i)] (c : Cone D) {U R : Over c.pt} (r₁ r₂ : R ⟶ U)

/-- Affine finitely presented models at a stage of an atlas scheme `U`, a relation scheme `R`
and the two projections. -/
structure RelModel (i : I) where
  VU : Scheme.{u}
  VR : Scheme.{u}
  qU : VU ⟶ D.obj i
  qR : VR ⟶ D.obj i
  πU : U.left ⟶ VU
  πR : R.left ⟶ VR
  hU : IsPullback πU U.hom qU (c.π.app i)
  hR : IsPullback πR R.hom qR (c.π.app i)
  affU : IsAffine VU
  affR : IsAffine VR
  lfpU : LocallyOfFinitePresentation qU
  lfpR : LocallyOfFinitePresentation qR
  t : VR ⟶ VU
  s : VR ⟶ VU
  ht : t ≫ qU = qR
  hs : s ≫ qU = qR
  ct : πR ≫ t = r₁.left ≫ πU
  cs : πR ≫ s = r₂.left ≫ πU

attribute [instance] RelModel.affU RelModel.affR RelModel.lfpU RelModel.lfpR

variable {c r₁ r₂}

/-- The restriction of a relation model along a transition map. -/
def RelModel.restrict {i j : I} (M : RelModel c r₁ r₂ i) (f : j ⟶ i) : RelModel c r₁ r₂ j where
  VU := Limits.pullback (D.map f) M.qU
  VR := Limits.pullback (D.map f) M.qR
  qU := pullback.fst _ _
  qR := pullback.fst _ _
  πU := modelLift c M.hU f
  πR := modelLift c M.hR f
  hU := isPullback_modelLift c M.hU f
  hR := isPullback_modelLift c M.hR f
  affU := inferInstance
  affR := inferInstance
  lfpU := inferInstance
  lfpR := inferInstance
  t := resHom M.t M.ht f
  s := resHom M.s M.hs f
  ht := resHom_fst M.t M.ht f
  hs := resHom_fst M.s M.hs f
  ct := modelLift_resHom M.t M.ht f c M.hR M.hU r₁.left (Over.w r₁) M.ct
  cs := modelLift_resHom M.s M.hs f c M.hR M.hU r₂.left (Over.w r₂) M.cs

omit [IsCofiltered I] [∀ i, IsAffine (D.obj i)] in
theorem RelModel.lfp_t {i : I} (M : RelModel c r₁ r₂ i) : LocallyOfFinitePresentation M.t := by
  have : LocallyOfFinitePresentation (M.t ≫ M.qU) := by rw [M.ht]; infer_instance
  exact Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp M.t M.qU

omit [IsCofiltered I] [∀ i, IsAffine (D.obj i)] in
theorem RelModel.lfp_s {i : I} (M : RelModel c r₁ r₂ i) : LocallyOfFinitePresentation M.s := by
  have : LocallyOfFinitePresentation (M.s ≫ M.qU) := by rw [M.hs]; infer_instance
  exact Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp M.s M.qU

end RelationModels

/-- Two maps whose restrictions agree on the second projection have equal restrictions. -/
theorem resHom_eq_of_snd {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {i j : I}
    {V₁ V₂ : Scheme.{u}} {q₁ : V₁ ⟶ D.obj i} {q₂ : V₂ ⟶ D.obj i} {h h' : V₁ ⟶ V₂}
    (hh : h ≫ q₂ = q₁) (hh' : h' ≫ q₂ = q₁) (f : j ⟶ i)
    (e : pullback.snd (D.map f) q₁ ≫ h = pullback.snd (D.map f) q₁ ≫ h') :
    resHom h hh f = resHom h' hh' f := by
  apply pullback.hom_ext <;> simp [e]

section Assembly

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ i, IsAffine (D.obj i)] {c : Cone D} (hc : IsLimit c) {U R : Over c.pt}
  {r₁ r₂ : R ⟶ U}

/-- A property of relation models that is preserved by restriction. -/
def RStable (P : ∀ {k : I}, RelModel c r₁ r₂ k → Prop) : Prop :=
  ∀ {k l : I} (M : RelModel c r₁ r₂ k) (f : l ⟶ k), P M → P (M.restrict f)

omit [IsCofiltered I] in
theorem RelModel.etale_t_restrict {k l : I} (M : RelModel c r₁ r₂ k) (f : l ⟶ k)
    (h : Etale M.t) : Etale (M.restrict f).t :=
  MorphismProperty.of_isPullback (isPullback_resHom M.t M.ht f) h

omit [IsCofiltered I] in
theorem RelModel.etale_s_restrict {k l : I} (M : RelModel c r₁ r₂ k) (f : l ⟶ k)
    (h : Etale M.s) : Etale (M.restrict f).s :=
  MorphismProperty.of_isPullback (isPullback_resHom M.s M.hs f) h

/-- A reflexivity map of a relation model. -/
def RefMap {k : I} (M : RelModel c r₁ r₂ k) : Prop :=
  ∃ Δ : M.VU ⟶ M.VR, Δ ≫ M.t = 𝟙 _ ∧ Δ ≫ M.s = 𝟙 _

/-- A symmetry map of a relation model. -/
def SymmMap {k : I} (M : RelModel c r₁ r₂ k) : Prop :=
  ∃ σ : M.VR ⟶ M.VR, σ ≫ M.t = M.s ∧ σ ≫ M.s = M.t

omit [IsCofiltered I] in
theorem RefMap.restrict {k l : I} {M : RelModel c r₁ r₂ k} (f : l ⟶ k) (h : RefMap M) :
    RefMap (M.restrict f) := by
  obtain ⟨Δ, h₁, h₂⟩ := h
  have hΔ : Δ ≫ M.qR = M.qU := by rw [← M.ht, ← Category.assoc, h₁, Category.id_comp]
  refine ⟨resHom Δ hΔ f, ?_, ?_⟩
  · change resHom Δ hΔ f ≫ resHom M.t M.ht f = 𝟙 _
    rw [resHom_comp, resHom_eq_of_snd _ (Category.id_comp _) f (by rw [h₁]), resHom_id]
  · change resHom Δ hΔ f ≫ resHom M.s M.hs f = 𝟙 _
    rw [resHom_comp, resHom_eq_of_snd _ (Category.id_comp _) f (by rw [h₂]), resHom_id]

omit [IsCofiltered I] in
theorem SymmMap.restrict {k l : I} {M : RelModel c r₁ r₂ k} (f : l ⟶ k) (h : SymmMap M) :
    SymmMap (M.restrict f) := by
  obtain ⟨σ, h₁, h₂⟩ := h
  have hσ : σ ≫ M.qR = M.qR := by rw [← M.ht, ← Category.assoc, h₁, M.hs, M.ht]
  refine ⟨resHom σ hσ f, ?_, ?_⟩
  · change resHom σ hσ f ≫ resHom M.t M.ht f = resHom M.s M.hs f
    rw [resHom_comp, resHom_eq_of_snd _ M.hs f (by rw [h₁])]
  · change resHom σ hσ f ≫ resHom M.s M.hs f = resHom M.t M.ht f
    rw [resHom_comp, resHom_eq_of_snd _ M.ht f (by rw [h₂])]

include hc in
/-- Etaleness of the first projection holds after restriction. -/
theorem exists_etale_t [Etale r₁.left] {P : ∀ {k : I}, RelModel c r₁ r₂ k → Prop}
    (hP : RStable P) {i : I} (M : RelModel c r₁ r₂ i) (hM : P M) :
    ∃ (j : I) (M' : RelModel c r₁ r₂ j), P M' ∧ Etale M'.t := by
  have := M.lfp_t
  obtain ⟨j₁, f₁, j₂, f₂, h⟩ := exists_res_etale hc M.hR M.hU M.t M.ht r₁.left (Over.w r₁) M.ct
  exact ⟨j₂, (M.restrict f₁).restrict f₂, hP _ f₂ (hP _ f₁ hM), h⟩

include hc in
/-- Etaleness of the second projection holds after restriction. -/
theorem exists_etale_s [Etale r₂.left] {P : ∀ {k : I}, RelModel c r₁ r₂ k → Prop}
    (hP : RStable P) {i : I} (M : RelModel c r₁ r₂ i) (hM : P M) :
    ∃ (j : I) (M' : RelModel c r₁ r₂ j), P M' ∧ Etale M'.s := by
  have := M.lfp_s
  obtain ⟨j₁, f₁, j₂, f₂, h⟩ := exists_res_etale hc M.hR M.hU M.s M.hs r₂.left (Over.w r₂) M.cs
  exact ⟨j₂, (M.restrict f₁).restrict f₂, hP _ f₂ (hP _ f₁ hM), h⟩

include hc in
/-- A reflexivity map exists after restriction. -/
theorem exists_refMap (hrefl : ∃ Δ : U.left ⟶ R.left, Δ ≫ r₁.left = 𝟙 _ ∧ Δ ≫ r₂.left = 𝟙 _)
    {P : ∀ {k : I}, RelModel c r₁ r₂ k → Prop} (hP : RStable P) {i : I}
    (M : RelModel c r₁ r₂ i) (hM : P M) :
    ∃ (j : I) (M' : RelModel c r₁ r₂ j), P M' ∧ RefMap M' := by
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := hrefl
  have hΔ : Δ ≫ R.hom = U.hom := by rw [← Over.w r₁, ← Category.assoc, hΔ₁, Category.id_comp]
  obtain ⟨j₁, f₁, ψ, hψ, hψc⟩ := exists_model_hom hc M.hU M.hR Δ hΔ
  let M₁ := M.restrict f₁
  have hψ' : ψ ≫ M₁.qR = M₁.qU := hψ
  have hψc' : M₁.πU ≫ ψ = Δ ≫ M₁.πR := hψc
  have : LocallyOfFiniteType (pullback.fst M₁.qU M₁.qU ≫ M₁.qU) := inferInstance
  obtain ⟨j₂, f₂, e⟩ := exists_eq_model hc (pullback.fst M₁.qU M₁.qU ≫ M₁.qU)
    (ψ ≫ pullback.lift M₁.t M₁.s (M₁.ht.trans M₁.hs.symm)) (pullback.lift (𝟙 _) (𝟙 _) rfl)
    (by simp [M₁.ht, hψ']) (by simp) M₁.hU (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
        rw [reassoc_of% hψc', M₁.ct, reassoc_of% hΔ₁]
      · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
        rw [reassoc_of% hψc', M₁.cs, reassoc_of% hΔ₂])
  have e₁ : pullback.snd (D.map f₂) M₁.qU ≫ ψ ≫ M₁.t = pullback.snd (D.map f₂) M₁.qU ≫ 𝟙 _ := by
    simpa using congrArg (· ≫ pullback.fst M₁.qU M₁.qU) e
  have e₂ : pullback.snd (D.map f₂) M₁.qU ≫ ψ ≫ M₁.s = pullback.snd (D.map f₂) M₁.qU ≫ 𝟙 _ := by
    simpa using congrArg (· ≫ pullback.snd M₁.qU M₁.qU) e
  refine ⟨j₂, M₁.restrict f₂, hP _ f₂ (hP _ f₁ hM), resHom ψ hψ' f₂, ?_, ?_⟩
  · change resHom ψ hψ' f₂ ≫ resHom M₁.t M₁.ht f₂ = 𝟙 _
    rw [resHom_comp, resHom_eq_of_snd _ (Category.id_comp _) f₂ e₁, resHom_id]
  · change resHom ψ hψ' f₂ ≫ resHom M₁.s M₁.hs f₂ = 𝟙 _
    rw [resHom_comp, resHom_eq_of_snd _ (Category.id_comp _) f₂ e₂, resHom_id]

include hc in
/-- A symmetry map exists after restriction. -/
theorem exists_symmMap (hsymm : ∃ σ : R.left ⟶ R.left, σ ≫ r₁.left = r₂.left ∧ σ ≫ r₂.left = r₁.left)
    {P : ∀ {k : I}, RelModel c r₁ r₂ k → Prop} (hP : RStable P) {i : I}
    (M : RelModel c r₁ r₂ i) (hM : P M) :
    ∃ (j : I) (M' : RelModel c r₁ r₂ j), P M' ∧ SymmMap M' := by
  obtain ⟨σ, hσ₁, hσ₂⟩ := hsymm
  have hσ : σ ≫ R.hom = R.hom := by rw [← Over.w r₁, ← Category.assoc, hσ₁, Over.w r₂, Over.w r₁]
  obtain ⟨j₁, f₁, ψ, hψ, hψc⟩ := exists_model_hom hc M.hR M.hR σ hσ
  let M₁ := M.restrict f₁
  have hψ' : ψ ≫ M₁.qR = M₁.qR := hψ
  have hψc' : M₁.πR ≫ ψ = σ ≫ M₁.πR := hψc
  have : LocallyOfFiniteType (pullback.fst M₁.qU M₁.qU ≫ M₁.qU) := inferInstance
  obtain ⟨j₂, f₂, e⟩ := exists_eq_model hc (pullback.fst M₁.qU M₁.qU ≫ M₁.qU)
    (ψ ≫ pullback.lift M₁.t M₁.s (M₁.ht.trans M₁.hs.symm))
    (pullback.lift M₁.s M₁.t (M₁.hs.trans M₁.ht.symm))
    (by simp [M₁.ht, hψ']) (by simp [M₁.hs]) M₁.hR (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        rw [reassoc_of% hψc', M₁.ct, reassoc_of% hσ₁, M₁.cs]
      · simp only [Category.assoc, pullback.lift_snd]
        rw [reassoc_of% hψc', M₁.cs, reassoc_of% hσ₂, M₁.ct])
  have e₁ : pullback.snd (D.map f₂) M₁.qR ≫ ψ ≫ M₁.t = pullback.snd (D.map f₂) M₁.qR ≫ M₁.s := by
    simpa using congrArg (· ≫ pullback.fst M₁.qU M₁.qU) e
  have e₂ : pullback.snd (D.map f₂) M₁.qR ≫ ψ ≫ M₁.s = pullback.snd (D.map f₂) M₁.qR ≫ M₁.t := by
    simpa using congrArg (· ≫ pullback.snd M₁.qU M₁.qU) e
  refine ⟨j₂, M₁.restrict f₂, hP _ f₂ (hP _ f₁ hM), resHom ψ hψ' f₂, ?_, ?_⟩
  · change resHom ψ hψ' f₂ ≫ resHom M₁.t M₁.ht f₂ = resHom M₁.s M₁.hs f₂
    rw [resHom_comp, resHom_eq_of_snd _ M₁.hs f₂ e₁]
  · change resHom ψ hψ' f₂ ≫ resHom M₁.s M₁.hs f₂ = resHom M₁.t M₁.ht f₂
    rw [resHom_comp, resHom_eq_of_snd _ M₁.ht f₂ e₂]

/-- A transitivity map of a relation model. -/
def TransMap {k : I} (M : RelModel c r₁ r₂ k) : Prop :=
  ∃ τ : Limits.pullback M.s M.t ⟶ M.VR,
    τ ≫ M.t = pullback.fst M.s M.t ≫ M.t ∧ τ ≫ M.s = pullback.snd M.s M.t ≫ M.s

omit [IsCofiltered I] in
/-- A map on the fibre product whose equations hold after restriction gives a transitivity map
of the restricted model. -/
theorem TransMap.of_res {k l : I} (M : RelModel c r₁ r₂ k) (f : l ⟶ k)
    (τ : Limits.pullback M.s M.t ⟶ M.VR) (hτ : τ ≫ M.qR = pullback.fst M.s M.t ≫ M.qR)
    (e₁ : pullback.snd (D.map f) (pullback.fst M.s M.t ≫ M.qR) ≫ τ ≫ M.t =
      pullback.snd (D.map f) (pullback.fst M.s M.t ≫ M.qR) ≫ pullback.fst M.s M.t ≫ M.t)
    (e₂ : pullback.snd (D.map f) (pullback.fst M.s M.t ≫ M.qR) ≫ τ ≫ M.s =
      pullback.snd (D.map f) (pullback.fst M.s M.t ≫ M.qR) ≫ pullback.snd M.s M.t ≫ M.s) :
    TransMap (M.restrict f) := by
  let M' := M.restrict f
  let κ : Limits.pullback M'.s M'.t ⟶ Limits.pullback M.s M.t :=
    pullback.map M'.s M'.t M.s M.t (pullback.snd _ _) (pullback.snd _ _) (pullback.snd _ _)
      (resHom_snd M.s M.hs f) (resHom_snd M.t M.ht f)
  have hκ₁ : κ ≫ pullback.fst M.s M.t = pullback.fst M'.s M'.t ≫ pullback.snd (D.map f) M.qR :=
    pullback.lift_fst _ _ _
  have hκ₂ : κ ≫ pullback.snd M.s M.t = pullback.snd M'.s M'.t ≫ pullback.snd (D.map f) M.qR :=
    pullback.lift_snd _ _ _
  have hcond : (pullback.fst M'.s M'.t ≫ pullback.fst (D.map f) M.qR) ≫ D.map f =
      κ ≫ pullback.fst M.s M.t ≫ M.qR := by
    rw [reassoc_of% hκ₁, Category.assoc, pullback.condition]
  let κ' : Limits.pullback M'.s M'.t ⟶
      Limits.pullback (D.map f) (pullback.fst M.s M.t ≫ M.qR) := pullback.lift _ _ hcond
  have hκ' : κ' ≫ pullback.snd _ _ = κ := pullback.lift_snd _ _ _
  have hfst : pullback.fst M'.s M'.t ≫ pullback.fst (D.map f) M.qR =
      pullback.snd M'.s M'.t ≫ pullback.fst (D.map f) M.qR := by
    have := congrArg (· ≫ pullback.fst (D.map f) M.qU) (pullback.condition (f := M'.s) (g := M'.t))
    simpa [M', RelModel.restrict] using this
  refine ⟨pullback.lift (pullback.fst M'.s M'.t ≫ pullback.fst (D.map f) M.qR) (κ ≫ τ)
    (by rw [hcond, Category.assoc, hτ]), ?_, ?_⟩
  · apply pullback.hom_ext
    · simp [M', RelModel.restrict]
    · simp only [M', RelModel.restrict, Category.assoc, resHom_snd, pullback.lift_snd_assoc]
      rw [← hκ', Category.assoc, e₁, ← Category.assoc, hκ', reassoc_of% hκ₁]
      rfl
  · apply pullback.hom_ext
    · simp only [M', RelModel.restrict, Category.assoc, pullback.lift_fst]
      exact hfst
    · simp only [M', RelModel.restrict, Category.assoc, resHom_snd, pullback.lift_snd_assoc]
      rw [← hκ', Category.assoc, e₂, ← Category.assoc, hκ', reassoc_of% hκ₂]
      rfl

omit [IsCofiltered I] in
theorem TransMap.restrict {k l : I} {M : RelModel c r₁ r₂ k} (f : l ⟶ k) (h : TransMap M) :
    TransMap (M.restrict f) := by
  obtain ⟨τ, h₁, h₂⟩ := h
  refine TransMap.of_res M f τ (by rw [← M.ht, reassoc_of% h₁]) ?_ ?_
  · rw [h₁]
  · rw [h₂]

include hc in
/-- A transitivity map exists after restriction. -/
theorem exists_transMap
    (htrans : ∃ τ : Limits.pullback r₂.left r₁.left ⟶ R.left,
      τ ≫ r₁.left = pullback.fst r₂.left r₁.left ≫ r₁.left ∧
        τ ≫ r₂.left = pullback.snd r₂.left r₁.left ≫ r₂.left)
    {P : ∀ {k : I}, RelModel c r₁ r₂ k → Prop} (hP : RStable P) {i : I}
    (M : RelModel c r₁ r₂ i) (hM : P M) :
    ∃ (j : I) (M' : RelModel c r₁ r₂ j), P M' ∧ TransMap M' := by
  obtain ⟨τ₀, hτ₁, hτ₂⟩ := htrans
  have hτ₀ : τ₀ ≫ R.hom = pullback.fst r₂.left r₁.left ≫ R.hom := by
    rw [← Over.w r₁, reassoc_of% hτ₁]
  have hPm := isPullback_model_pullback (c.π.app i) M.hR M.hR M.hU r₂.left r₁.left (Over.w r₂)
    (Over.w r₁) M.s M.t M.hs M.ht M.cs M.ct
  obtain ⟨j₁, f₁, ψ, hψ, hψc⟩ := exists_model_hom hc hPm M.hR τ₀ hτ₀
  let M₁ := M.restrict f₁
  let μ : Limits.pullback M₁.s M₁.t ⟶ Limits.pullback M.s M.t :=
    pullback.map M₁.s M₁.t M.s M.t (pullback.snd _ _) (pullback.snd _ _) (pullback.snd _ _)
      (resHom_snd M.s M.hs f₁) (resHom_snd M.t M.ht f₁)
  have hμ₁ : μ ≫ pullback.fst M.s M.t = pullback.fst M₁.s M₁.t ≫ pullback.snd (D.map f₁) M.qR :=
    pullback.lift_fst _ _ _
  have hμ₂ : μ ≫ pullback.snd M.s M.t = pullback.snd M₁.s M₁.t ≫ pullback.snd (D.map f₁) M.qR :=
    pullback.lift_snd _ _ _
  let κ₁ : Limits.pullback M₁.s M₁.t ⟶
      Limits.pullback (D.map f₁) (pullback.fst M.s M.t ≫ M.qR) :=
    pullback.lift (pullback.fst M₁.s M₁.t ≫ pullback.fst (D.map f₁) M.qR) μ
      (by rw [reassoc_of% hμ₁, Category.assoc, pullback.condition])
  have hκ₁ : κ₁ ≫ pullback.fst _ _ = pullback.fst M₁.s M₁.t ≫ pullback.fst (D.map f₁) M.qR :=
    pullback.lift_fst _ _ _
  have hκ₂ : κ₁ ≫ pullback.snd _ _ = μ := pullback.lift_snd _ _ _
  let τ₁ := κ₁ ≫ ψ
  have hτq : τ₁ ≫ M₁.qR = pullback.fst M₁.s M₁.t ≫ M₁.qR := by
    change (κ₁ ≫ ψ) ≫ pullback.fst (D.map f₁) M.qR = _
    rw [Category.assoc, hψ, hκ₁]
    rfl
  have hP₁ := isPullback_model_pullback (c.π.app j₁) M₁.hR M₁.hR M₁.hU r₂.left r₁.left
    (Over.w r₂) (Over.w r₁) M₁.s M₁.t M₁.hs M₁.ht M₁.cs M₁.ct
  have hqq : pullback.fst M₁.s M₁.t ≫ M₁.qR = pullback.snd M₁.s M₁.t ≫ M₁.qR := by
    rw [← M₁.hs, pullback.condition_assoc, M₁.ht, M₁.hs]
  have hπκ : pullback.map r₂.left r₁.left M₁.s M₁.t M₁.πR M₁.πR M₁.πU M₁.cs.symm M₁.ct.symm ≫ κ₁ =
      modelLift c hPm f₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hκ₁, pullback.lift_fst_assoc]
      simp [M₁, RelModel.restrict, modelLift]
    · rw [Category.assoc, hκ₂]
      apply pullback.hom_ext
      · simp [μ, M₁, RelModel.restrict, modelLift]
      · simp [μ, M₁, RelModel.restrict, modelLift]
  have : LocallyOfFiniteType (pullback.fst M₁.qU M₁.qU ≫ M₁.qU) := inferInstance
  obtain ⟨j₂, f₂, e⟩ := exists_eq_model hc (pullback.fst M₁.qU M₁.qU ≫ M₁.qU)
    (τ₁ ≫ pullback.lift M₁.t M₁.s (M₁.ht.trans M₁.hs.symm))
    (pullback.lift (pullback.fst M₁.s M₁.t ≫ M₁.t) (pullback.snd M₁.s M₁.t ≫ M₁.s)
      (by rw [Category.assoc, Category.assoc, M₁.ht, M₁.hs, hqq]))
    (by rw [Category.assoc, pullback.lift_fst_assoc, M₁.ht, hτq])
    (by rw [pullback.lift_fst_assoc, Category.assoc, M₁.ht]) hP₁ (by
      rw [← Category.assoc, ← Category.assoc, hπκ, hψc]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        change τ₀ ≫ M₁.πR ≫ M₁.t = _
        rw [M₁.ct, reassoc_of% hτ₁, ← M₁.ct]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
        change τ₀ ≫ M₁.πR ≫ M₁.s = _
        rw [M₁.cs, reassoc_of% hτ₂, ← M₁.cs])
  have e₁ := congrArg (· ≫ pullback.fst M₁.qU M₁.qU) e
  have e₂ := congrArg (· ≫ pullback.snd M₁.qU M₁.qU) e
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at e₁ e₂
  exact ⟨j₂, M₁.restrict f₂, hP _ f₂ (hP _ f₁ hM),
    TransMap.of_res M₁ f₂ τ₁ hτq (by simpa only [Category.assoc] using e₁)
      (by simpa only [Category.assoc] using e₂)⟩

include hc in
/-- Affine finitely presented models of an atlas, its relation and the two projections exist at
some stage. -/
theorem exists_relModel [IsAffine U.left] [IsAffine R.left]
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom] [QuasiSeparated U.hom]
    [LocallyOfFinitePresentation R.hom] [QuasiCompact R.hom] [QuasiSeparated R.hom] :
    ∃ i, Nonempty (RelModel c r₁ r₂ i) := by
  obtain ⟨iU, VU₀, qU₀, πU₀, hlU, hqcU, hqsU, hU₀⟩ :=
    SpaceLimitMorphisms.exists_model_of_affine_diagram D c hc U.left U.hom
  have := hlU
  have := hqcU
  have := hqsU
  obtain ⟨jU, fU, haffU⟩ := exists_isAffine_model hc hU₀
  obtain ⟨iR, VR₀, qR₀, πR₀, hlR, hqcR, hqsR, hR₀⟩ :=
    SpaceLimitMorphisms.exists_model_of_affine_diagram D c hc R.left R.hom
  have := hlR
  have := hqcR
  have := hqsR
  obtain ⟨jR, fR, haffR⟩ := exists_isAffine_model hc hR₀
  have hU₁ := isPullback_modelLift c (isPullback_modelLift c hU₀ fU) (IsCofiltered.minToLeft jU jR)
  have hR₁ := isPullback_modelLift c (isPullback_modelLift c hR₀ fR) (IsCofiltered.minToRight jU jR)
  obtain ⟨k₁, f₁, ψ₁, hψ₁, hψ₁c⟩ := exists_model_hom hc hR₁ hU₁ r₁.left (Over.w r₁)
  have hU₂ := isPullback_modelLift c hU₁ f₁
  have hR₂ := isPullback_modelLift c hR₁ f₁
  obtain ⟨k₂, f₂, ψ₂, hψ₂, hψ₂c⟩ := exists_model_hom hc hR₂ hU₂ r₂.left (Over.w r₂)
  exact ⟨k₂, ⟨{
    VU := _
    VR := _
    qU := _
    qR := _
    πU := _
    πR := _
    hU := isPullback_modelLift c hU₂ f₂
    hR := isPullback_modelLift c hR₂ f₂
    affU := inferInstance
    affR := inferInstance
    lfpU := inferInstance
    lfpR := inferInstance
    t := resHom ψ₁ hψ₁ f₂
    s := ψ₂
    ht := resHom_fst ψ₁ hψ₁ f₂
    hs := hψ₂
    ct := modelLift_resHom ψ₁ hψ₁ f₂ c hR₂ hU₂ r₁.left (Over.w r₁) hψ₁c
    cs := hψ₂c }⟩⟩

include hc in
/-- A relation model at some stage whose projections are etale, form an equivalence relation
through actual maps, and pair into a closed immersion. -/
theorem exists_good_relModel [IsAffine U.left] [IsAffine R.left]
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom] [QuasiSeparated U.hom]
    [LocallyOfFinitePresentation R.hom] [QuasiCompact R.hom] [QuasiSeparated R.hom]
    [Etale r₁.left] [Etale r₂.left] (hrel : AtlasRelation.IsEquivRel r₁.left r₂.left)
    (hcl : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.lift r₁.left r₂.left (by rw [Over.w r₁, Over.w r₂]) :
        R.left ⟶ Limits.pullback U.hom U.hom)) :
    ∃ (j : I) (M : RelModel c r₁ r₂ j), Etale M.t ∧ Etale M.s ∧ RefMap M ∧ SymmMap M ∧
      TransMap M ∧ _root_.AlgebraicGeometry.IsClosedImmersion
        (pullback.lift M.t M.s (M.ht.trans M.hs.symm) : M.VR ⟶ Limits.pullback M.qU M.qU) := by
  obtain ⟨i₀, ⟨M₀⟩⟩ := exists_relModel (r₁ := r₁) (r₂ := r₂) hc
  obtain ⟨i₁, M₁, -, h₁⟩ := exists_etale_t hc (P := fun _ => True) (fun _ _ _ => trivial) M₀ trivial
  obtain ⟨i₂, M₂, h₂, h₂'⟩ := exists_etale_s hc (P := fun M => Etale M.t)
    (fun M f h => M.etale_t_restrict f h) M₁ h₁
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := hrel.refl U.left (𝟙 _)
  obtain ⟨σ, hσ₁, hσ₂⟩ := hrel.symm R.left (𝟙 _)
  obtain ⟨τ, hτ₁, hτ₂⟩ := hrel.trans _ (pullback.fst r₂.left r₁.left)
    (pullback.snd r₂.left r₁.left) pullback.condition
  obtain ⟨i₃, M₃, h₃, h₃'⟩ := exists_refMap hc ⟨Δ, hΔ₁, hΔ₂⟩
    (P := fun M => Etale M.t ∧ Etale M.s)
    (fun M f h => ⟨M.etale_t_restrict f h.1, M.etale_s_restrict f h.2⟩) M₂ ⟨h₂, h₂'⟩
  obtain ⟨i₄, M₄, h₄, h₄'⟩ := exists_symmMap hc
    ⟨σ, by simpa using hσ₁, by simpa using hσ₂⟩
    (P := fun M => (Etale M.t ∧ Etale M.s) ∧ RefMap M)
    (fun M f h => ⟨⟨M.etale_t_restrict f h.1.1, M.etale_s_restrict f h.1.2⟩, h.2.restrict f⟩)
    M₃ ⟨h₃, h₃'⟩
  obtain ⟨i₅, M₅, h₅, h₅'⟩ := exists_transMap hc ⟨τ, hτ₁, hτ₂⟩
    (P := fun M => ((Etale M.t ∧ Etale M.s) ∧ RefMap M) ∧ SymmMap M)
    (fun M f h => ⟨⟨⟨M.etale_t_restrict f h.1.1.1, M.etale_s_restrict f h.1.1.2⟩,
      h.1.2.restrict f⟩, h.2.restrict f⟩) M₄ ⟨h₄, h₄'⟩
  obtain ⟨j, f, hj⟩ := exists_res_closedImmersion_pairing hc M₅.hU M₅.hR (Over.w r₁) (Over.w r₂)
    M₅.ht M₅.hs M₅.ct M₅.cs hcl
  exact ⟨j, M₅.restrict f, M₅.etale_t_restrict f h₅.1.1.1, M₅.etale_s_restrict f h₅.1.1.2,
    h₅.1.2.restrict f, h₅.2.restrict f, h₅'.restrict f, hj⟩

end Assembly

section Quotient

variable {S : Scheme.{u}}

/-- Pairs of atlas points with equal images lift through a presheaf pullback square. -/
theorem lift_of_isPullback {F : Presheaf S} {U R : Over S} {a : (schemeYoneda S).obj U ⟶ F}
    {t s : R ⟶ U} (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    {T : Over S} (f f' : T ⟶ U) (hff : atlasSection a f = atlasSection a f') :
    ∃ z : T ⟶ R, z ≫ t = f ∧ z ≫ s = f' := by
  have hw := KernelPair.map_comp_eq_of_app_eq a hff
  obtain ⟨z, hz⟩ := (schemeYoneda S).map_surjective (h.lift _ _ hw)
  exact ⟨z, (schemeYoneda S).map_injective (by rw [Functor.map_comp, hz, h.lift_fst]),
    (schemeYoneda S).map_injective (by rw [Functor.map_comp, hz, h.lift_snd])⟩

/-- The two projections of a presheaf pullback square have equal atlas images. -/
theorem atlasSection_eq_of_isPullback {F : Presheaf S} {U R : Over S}
    {a : (schemeYoneda S).obj U ⟶ F} {t s : R ⟶ U}
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a) {T : Over S}
    (z : T ⟶ R) : atlasSection a (z ≫ t) = atlasSection a (z ≫ s) :=
  congrArg (fun φ : (schemeYoneda S).obj R ⟶ F => φ.app (op T) ⟨z⟩) h.w

end Quotient

section Relation

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ i, IsAffine (D.obj i)] {c : Cone D} {U R : Over c.pt} {r₁ r₂ : R ⟶ U}

/-- The etale equivalence relation of a good relation model. -/
def RelModel.relation {j : I} (M : RelModel c r₁ r₂ j) (het : Etale M.t) (hes : Etale M.s)
    (hrefl : RefMap M) (hsymm : SymmMap M) (htrans : TransMap M)
    (hcl : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.lift M.t M.s (M.ht.trans M.hs.symm) : M.VR ⟶ Limits.pullback M.qU M.qU)) :
    EtaleEquivalenceRelation.{u} where
  U := M.VU
  R := M.VR
  t := M.t
  s := M.s
  mono_lift := by
    have hm : Mono (prod.lift (pullback.fst M.qU M.qU) (pullback.snd M.qU M.qU)) :=
      ⟨fun g h e => by
        apply pullback.hom_ext
        · simpa using congrArg (· ≫ prod.fst) e
        · simpa using congrArg (· ≫ prod.snd) e⟩
    have : prod.lift M.t M.s = pullback.lift M.t M.s (M.ht.trans M.hs.symm) ≫
        prod.lift (pullback.fst M.qU M.qU) (pullback.snd M.qU M.qU) := by
      ext <;> simp
    rw [this]
    exact mono_comp _ _
  refl T x := by
    obtain ⟨Δ, h₁, h₂⟩ := hrefl
    exact ⟨x ≫ Δ, by rw [Category.assoc, h₁, Category.comp_id],
      by rw [Category.assoc, h₂, Category.comp_id]⟩
  symm T r := by
    obtain ⟨σ, h₁, h₂⟩ := hsymm
    exact ⟨r ≫ σ, by rw [Category.assoc, h₁], by rw [Category.assoc, h₂]⟩
  trans T r r' h := by
    obtain ⟨τ, h₁, h₂⟩ := htrans
    exact ⟨pullback.lift r r' h ≫ τ, by rw [Category.assoc, h₁, pullback.lift_fst_assoc],
      by rw [Category.assoc, h₂, pullback.lift_snd_assoc]⟩
  etale_t := het
  etale_s := hes

end Relation

end SpaceLimitModels

open SpaceFilteredPoints SpaceLimitMorphisms SpaceLimitModels in
/-- **Model existence for separated algebraic spaces** along cofiltered limits of affine schemes
(Conrad's Theorem 3.4(1) for spaces, printed p.13). -/
theorem spaceLimitModelExistence : SpaceLimitModelExistence.{u} := by
  intro I _ _ D _ c hc Y hYsep hYat
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  -- An affine, locally finitely presented atlas.
  obtain ⟨U₀, a₀, ha₀, hs₀, hl₀, hq₀⟩ := hYat
  have : LocallyOfFinitePresentation U₀.hom := hl₀
  have : QuasiCompact U₀.hom := hq₀
  have : CompactSpace U₀.left := QuasiCompact.compactSpace_of_compactSpace U₀.hom
  obtain ⟨W, jW, hW, hje, hjs⟩ := exists_affine_refinement (𝟙 U₀.left)
  have hje' : Etale jW := by simpa using hje
  have hjs' : Surjective jW := by simpa using hjs
  let U : Over c.pt := Over.mk (jW ≫ U₀.hom)
  let j' : U ⟶ U₀ := Over.homMk jW
  let a : (schemeYoneda c.pt).obj U ⟶ Y.presheaf := (schemeYoneda c.pt).map j' ≫ a₀
  have ha : IsEtale a := IsEtale.comp (isEtale_map j' hje') ha₀
  have hs : IsSurjective a :=
    SpaceProductPoints.IsSurjective.comp (SpaceProductPoints.isSurjective_map j' hjs') hs₀
  have : IsAffine U.left := hW
  have : LocallyOfFinitePresentation U.hom := by
    change LocallyOfFinitePresentation (jW ≫ U₀.hom)
    infer_instance
  have : QuasiCompact U.hom := inferInstance
  have : QuasiSeparated U.hom := inferInstance
  -- The kernel pair and its spreading.
  obtain ⟨R, r₁, r₂, hpbY, he₁, he₂, hrel, hcl⟩ := exists_closed_kernel_pair hYsep a ha
  have : Etale r₁.left := he₁
  have : Etale r₂.left := he₂
  have : IsAffine (pairOver U).left := inferInstanceAs (IsAffine (Limits.pullback U.hom U.hom))
  have : IsAffine R.left := isAffine_of_isAffineHom (pairLift r₁ r₂).left
  have : LocallyOfFinitePresentation R.hom := by
    rw [← Over.w r₁]
    infer_instance
  have : QuasiCompact R.hom := inferInstance
  have : QuasiSeparated R.hom := inferInstance
  obtain ⟨j, M, het, hes, hrefl, hsymm, htrans, hclM⟩ := exists_good_relModel hc hrel hcl
  let E := M.relation het hes hrefl hsymm htrans hclM
  have hb : E.t ≫ M.qU = E.s ≫ M.qU := M.ht.trans M.hs.symm
  obtain ⟨Q, aQ, haQ, hsQ, hpbQ⟩ :=
    etaleEquivalenceRelationAlgebraicSpaceQuotient (D.obj j) E M.qU hb
  let UQ : Over (D.obj j) := Over.mk M.qU
  let RQ : Over (D.obj j) := Over.mk (E.t ≫ M.qU)
  let tQ : RQ ⟶ UQ := Over.homMk E.t
  let sQ : RQ ⟶ UQ := Over.homMk E.s hb.symm
  have hpbQ' : IsPullback ((schemeYoneda _).map tQ) ((schemeYoneda _).map sQ) aQ aQ := hpbQ
  refine ⟨j, Q, ?_, ⟨UQ, aQ, haQ, hsQ, M.lfpU, by change QuasiCompact M.qU; infer_instance⟩, ⟨?_⟩⟩
  · -- Separatedness.
    have : _root_.AlgebraicGeometry.IsClosedImmersion (pairLift tQ sQ).left := hclM
    refine isSeparated_of_closed_relation aQ haQ hsQ (pairLift tQ sQ) fun T g => ?_
    change _ ↔ Q.pullback g (atlasSection aQ (pairFst UQ)) =
      Q.pullback g (atlasSection aQ (pairSnd UQ))
    rw [atlasSection_pullback, atlasSection_pullback]
    constructor
    · rintro ⟨z, rfl⟩
      rw [Category.assoc, Category.assoc, pairLift_fst, pairLift_snd]
      exact atlasSection_eq_of_isPullback hpbQ' z
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := lift_of_isPullback hpbQ' _ _ h
      refine ⟨z, ?_⟩
      ext1
      apply pullback.hom_ext
      · change z.left ≫ pullback.lift E.t E.s _ ≫ pullback.fst _ _ = _
        rw [pullback.lift_fst]
        exact congrArg CommaMorphism.left hz₁
      · change z.left ≫ pullback.lift E.t E.s _ ≫ pullback.snd _ _ = _
        rw [pullback.lift_snd]
        exact congrArg CommaMorphism.left hz₂
  · -- The base change of the model is the given space.
    let W' : Over c.pt := baseOver (c.π.app j) UQ
    let e₀ := M.hU.flip.isoPullback
    let θ : W' ⟶ U := Over.homMk e₀.inv (IsPullback.isoPullback_inv_fst _)
    have hθ : IsIso θ.left := by
      change IsIso e₀.inv
      infer_instance
    let aF := baseAtlas (c.π.app j) aQ
    let aG := (schemeYoneda c.pt).map θ ≫ a
    have haG : IsEtale aG := IsEtale.comp (isEtale_map θ inferInstance) ha
    have hsG : IsSurjective aG :=
      SpaceProductPoints.IsSurjective.comp (SpaceProductPoints.isSurjective_map θ inferInstance) hs
    have hθπ : e₀.inv ≫ M.πU = pullback.snd (c.π.app j) M.qU := IsPullback.isoPullback_inv_snd _
    have hker : ∀ (T : Over c.pt) (x y : T ⟶ W'),
        aF.app (op T) ⟨x⟩ = aF.app (op T) ⟨y⟩ ↔ aG.app (op T) ⟨x⟩ = aG.app (op T) ⟨y⟩ := by
      intro T x y
      change atlasSection aF x = atlasSection aF y ↔ atlasSection a (x ≫ θ) = atlasSection a (y ≫ θ)
      rw [baseAtlas_app, baseAtlas_app]
      constructor
      · intro h
        obtain ⟨z, hz₁, hz₂⟩ := lift_of_isPullback hpbQ' _ _ h
        have hzq : z.left ≫ M.qR = T.hom ≫ c.π.app j := by
          rw [← M.ht]
          exact Over.w z
        let w : T ⟶ R := Over.homMk (M.hR.lift z.left T.hom hzq) (M.hR.lift_snd _ _ _)
        have hw : ∀ (x : T ⟶ W') (r : R ⟶ U) (tm : M.VR ⟶ M.VU),
            M.πR ≫ tm = r.left ≫ M.πU → z.left ≫ tm = x.left ≫ pullback.snd _ _ →
            w ≫ r = x ≫ θ := by
          intro x r tm hct hz
          ext1
          apply M.hU.hom_ext
          · change (M.hR.lift z.left T.hom hzq ≫ r.left) ≫ M.πU = (x.left ≫ e₀.inv) ≫ M.πU
            rw [Category.assoc, ← hct, IsPullback.lift_fst_assoc, hz, Category.assoc, hθπ]
            rfl
          · change (M.hR.lift z.left T.hom hzq ≫ r.left) ≫ U.hom = (x.left ≫ e₀.inv) ≫ U.hom
            rw [Category.assoc, Over.w r, IsPullback.lift_snd, Category.assoc,
              IsPullback.isoPullback_inv_fst]
            exact (Over.w x).symm
        rw [← hw x r₁ M.t M.ct (congrArg CommaMorphism.left hz₁),
          ← hw y r₂ M.s M.cs (congrArg CommaMorphism.left hz₂)]
        exact atlasSection_eq_of_isPullback hpbY w
      · intro h
        obtain ⟨w, hw₁, hw₂⟩ := lift_of_isPullback hpbY _ _ h
        let z : (Over.map (c.π.app j)).obj T ⟶ RQ := Over.homMk (w.left ≫ M.πR) (by
          change (w.left ≫ M.πR) ≫ M.t ≫ M.qU = T.hom ≫ c.π.app j
          rw [M.ht, Category.assoc, M.hR.w, ← Category.assoc, Over.w w])
        have hz : ∀ (x : T ⟶ W') (r : R ⟶ U) (tm : RQ ⟶ UQ),
            M.πR ≫ tm.left = r.left ≫ M.πU → w ≫ r = x ≫ θ →
            (Over.homMk (x.left ≫ pullback.snd (c.π.app j) UQ.hom) (by
              rw [Category.assoc, ← pullback.condition, ← Category.assoc,
                show x.left ≫ pullback.fst (c.π.app j) UQ.hom = T.hom from Over.w x]
              rfl) : (Over.map (c.π.app j)).obj T ⟶ UQ) = z ≫ tm := by
          intro x r tm hct hwr
          ext1
          change x.left ≫ pullback.snd _ _ = (w.left ≫ M.πR) ≫ tm.left
          rw [Category.assoc, hct, ← Category.assoc, show w.left ≫ r.left = x.left ≫ e₀.inv from
            congrArg CommaMorphism.left hwr, Category.assoc, hθπ]
          rfl
        exact (congrArg (atlasSection aQ) (hz x r₁ tQ M.ct hw₁)).trans
          ((atlasSection_eq_of_isPullback hpbQ' z).trans
            (congrArg (atlasSection aQ) (hz y r₂ sQ M.cs hw₂)).symm)
    exact (forgetToPresheaf c.pt).preimageIso (commonEtalePresentationIso
      ((baseChange (c.π.app j) Q).toSheaf.property.of_le
        (Sites.etaleTopologyOver_le_fppfTopologyOver c.pt))
      (Y.toSheaf.property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver c.pt)) aF aG
      (isLocallySurjective_etale_of_isEtale_isSurjective aF (isEtale_baseAtlas _ aQ haQ)
        (isSurjective_baseAtlas _ aQ hsQ))
      (isLocallySurjective_etale_of_isEtale_isSurjective aG haG hsG) hker)

end Langlands.AlgebraicGeometry.AlgebraicSpace
