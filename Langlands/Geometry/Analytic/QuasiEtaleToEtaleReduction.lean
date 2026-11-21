import Langlands.CategoryTheory.Sites.FlatPrecoverageCoverPreserving
import Langlands.Geometry.Analytic.QuasiEtaleToEtaleStatement
import Langlands.Geometry.Analytic.EtalePullbackGSpaceStatement
import Langlands.Geometry.Analytic.EtaleGeometricPointPullbacks
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.CategoryTheory.PullbackActions
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Action.Limits

/-! # Reduction of the morphisms of sites `μ` and `μ_G` to geometric inputs -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Topology

namespace QuasiEtaleToEtale

section Flat

variable {T : Type*} [Category* T] {P P' : MorphismProperty T} (X : T)

/-- Let `P ≤ P'` be morphism properties, with `P` stable under composition, containing the
identities and cancellable on the right. If every `P`-morphism has a pullback along every
morphism whose base-changed leg is again in `P`, then the inclusion
`P.Over ⊤ X ⥤ P'.Over ⊤ X` is representably flat. -/
theorem representablyFlat_changeProp
    [P.IsStableUnderComposition] [P.ContainsIdentities] [P.HasOfPostcompProperty P]
    (hPP' : P ≤ P')
    (hbase : ∀ ⦃A B Y : T⦄ (f : A ⟶ Y) (g : B ⟶ Y), P f →
      ∃ (Z : T) (p : Z ⟶ A) (q : Z ⟶ B), IsPullback p q f g ∧ P q) :
    RepresentablyFlat
      (MorphismProperty.Over.changeProp X hPP' le_rfl : P.Over ⊤ X ⥤ P'.Over ⊤ X) := by
  constructor
  intro U
  let F : P.Over ⊤ X ⥤ P'.Over ⊤ X := MorphismProperty.Over.changeProp X hPP' le_rfl
  let I : P.Over ⊤ X := MorphismProperty.Over.mk ⊤ (𝟙 X) (P.id_mem X)
  have hne : Nonempty (StructuredArrow U F) :=
    ⟨StructuredArrow.mk (Y := I)
      (MorphismProperty.Over.homMk (B := F.obj I) U.hom (Category.comp_id _))⟩
  have hco : IsCofilteredOrEmpty (StructuredArrow U F) := by
    refine ⟨fun A B => ?_, fun A B f g => ?_⟩
    · obtain ⟨Z, p, q, hZ, hq⟩ := hbase A.right.hom B.right.hom A.right.prop
      let W : P.Over ⊤ X := MorphismProperty.Over.mk ⊤ (q ≫ B.right.hom)
        (P.comp_mem _ _ hq B.right.prop)
      have hw : A.hom.left ≫ A.right.hom = B.hom.left ≫ B.right.hom :=
        (MorphismProperty.Over.w A.hom).trans (MorphismProperty.Over.w B.hom).symm
      let l : U.left ⟶ Z := hZ.lift A.hom.left B.hom.left hw
      let h : U ⟶ F.obj W := MorphismProperty.Over.homMk l (by
        change l ≫ q ≫ B.right.hom = U.hom
        rw [← Category.assoc, show l ≫ q = B.hom.left from hZ.lift_snd _ _ _]
        exact MorphismProperty.Over.w B.hom)
      let p' : W ⟶ A.right := MorphismProperty.Over.homMk p hZ.w
      let q' : W ⟶ B.right := MorphismProperty.Over.homMk q
      refine ⟨StructuredArrow.mk h, StructuredArrow.homMk p' ?_,
        StructuredArrow.homMk q' ?_, trivial⟩
      · exact MorphismProperty.Over.Hom.ext (hZ.lift_fst _ _ _)
      · exact MorphismProperty.Over.Hom.ext (hZ.lift_snd _ _ _)
    · obtain ⟨D, a, b, hD, hb⟩ := hbase B.right.hom B.right.hom B.right.prop
      obtain ⟨d, hd₁, hd₂⟩ := hD.exists_lift (𝟙 B.right.left) (𝟙 B.right.left) rfl
      have hd : P d := by
        apply MorphismProperty.of_postcomp (W' := P) P d b hb
        rw [hd₂]
        exact P.id_mem _
      obtain ⟨c, hc₁, hc₂⟩ := hD.exists_lift f.right.left g.right.left
        ((MorphismProperty.Over.w f.right).trans (MorphismProperty.Over.w g.right).symm)
      obtain ⟨E, s, t, hE, ht⟩ := hbase d c hd
      let W : P.Over ⊤ X := MorphismProperty.Over.mk ⊤ (t ≫ A.right.hom)
        (P.comp_mem _ _ ht A.right.prop)
      let ah : U.left ⟶ A.right.left := A.hom.left
      let bh : U.left ⟶ B.right.left := B.hom.left
      have hfA : ah ≫ f.right.left = bh :=
        congrArg (fun k => k.left) (StructuredArrow.w f)
      have hgA : ah ≫ g.right.left = bh :=
        congrArg (fun k => k.left) (StructuredArrow.w g)
      have he : bh ≫ d = ah ≫ c := by
        apply hD.hom_ext
        · rw [Category.assoc, hd₁, Category.comp_id, Category.assoc, hc₁, hfA]
        · rw [Category.assoc, hd₂, Category.comp_id, Category.assoc, hc₂, hgA]
      let e : U.left ⟶ E := hE.lift bh ah he
      let h : U ⟶ F.obj W := MorphismProperty.Over.homMk e (by
        change e ≫ t ≫ A.right.hom = U.hom
        rw [← Category.assoc, show e ≫ t = ah from hE.lift_snd _ _ _]
        exact MorphismProperty.Over.w A.hom)
      let k : W ⟶ A.right := MorphismProperty.Over.homMk t
      have ht₁ : t ≫ f.right.left = s := by
        rw [← hc₁, ← Category.assoc, ← hE.w, Category.assoc, hd₁, Category.comp_id]
      have ht₂ : t ≫ g.right.left = s := by
        rw [← hc₂, ← Category.assoc, ← hE.w, Category.assoc, hd₂, Category.comp_id]
      refine ⟨StructuredArrow.mk h, StructuredArrow.homMk k
        (MorphismProperty.Over.Hom.ext (hE.lift_snd _ _ _)), ?_⟩
      apply StructuredArrow.hom_ext
      apply MorphismProperty.Over.Hom.ext
      exact ht₁.trans ht₂.symm
  exact { toIsCofilteredOrEmpty := hco, nonempty := hne }

end Flat

section Continuous

variable {C D : Type*} [Category* C] [Category* D]

/-- A representably flat functor that sends the sieves generated by the coverings of a
precoverage to covering sieves is cover-preserving for the generated topology. -/
theorem coverPreserving_toGrothendieck (F : C ⥤ D) [RepresentablyFlat F] (J : Precoverage C)
    (K : GrothendieckTopology D)
    (h : ∀ ⦃U : C⦄ (R : Presieve U), R ∈ J U →
      (Sieve.generate R).functorPushforward F ∈ K (F.obj U)) :
    CoverPreserving J.toGrothendieck K F := by
  constructor
  intro U S hS
  induction hS with
  | of X R hR => exact h R hR
  | top X =>
    rw [Sieve.functorPushforward_top]
    exact K.top_mem _
  | pullback X S _ Y f ih =>
    exact K.superset_covering (Langlands.CategoryTheory.functorPushforward_pullback_le F S f)
      (K.pullback_stable (F.map f) ih)
  | transitive X S R _ _ ihS ihR =>
    apply K.transitive ihS
    rintro Z h ⟨W, g, k, hg, rfl⟩
    rw [Sieve.pullback_comp]
    exact K.pullback_stable k
      (K.superset_covering (Sieve.functorPushforward_pullback_le F g R) (ihR hg))

/-- A representably flat functor that sends coverings of a precoverage to covering sieves is
continuous for the generated topology. -/
theorem isContinuous_of_flat (F : C ⥤ D) [RepresentablyFlat F] (J : Precoverage C)
    (K : GrothendieckTopology D)
    (h : ∀ ⦃U : C⦄ (R : Presieve U), R ∈ J U →
      (Sieve.generate R).functorPushforward F ∈ K (F.obj U)) :
    F.IsContinuous J.toGrothendieck K :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat K F)
    (coverPreserving_toGrothendieck F J K h)

end Continuous

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The images under an étale morphism `φ` of finitely many charts of its source through a
point `y` form a finite family whose union is a neighbourhood of `φ y`. -/
theorem exists_chartImages {V U : LocalizedCategory.{u, v, v} (K := K)} (φ : V ⟶ U)
    (hφ : etale φ) (y : localizedSpaceFunctor.obj V) :
    ∃ σ : Set (Set (localizedSpaceFunctor.obj U)), σ.Finite ∧
      ⋃₀ σ ∈ 𝓝 (localizedSpaceFunctor.map φ y) ∧
      ∀ T ∈ σ, ∃ i : (localizedObjectEquiv.symm V).presentation.atlas.Index,
        T = localizedSpaceFunctor.map φ ''
          Set.range ((localizedObjectEquiv.symm V).presentation.atlas.chart i) := by
  obtain ⟨σ₀, hσ, hστ, -, hnhds⟩ :=
    (localizedObjectEquiv.symm V).presentation.atlas.isNet_chartFamily.1 y
  let σ : Set (Set (localizedSpaceFunctor.obj V)) := σ₀
  refine ⟨(localizedSpaceFunctor.map φ '' ·) '' σ, hσ.image _, ?_, ?_⟩
  · rw [Set.sUnion_image, ← Set.image_iUnion₂, ← Set.sUnion_eq_biUnion]
    exact (etaleOpenMap K φ hφ).image_mem_nhds hnhds
  · rintro _ ⟨V', hV', rfl⟩
    obtain ⟨i, rfl⟩ := hστ hV'
    exact ⟨i, rfl⟩

section NonEquivariant

variable (h1 : LocalizedEtalePullbackStatement.{u, v} K)
  (h2 : LocalizedEtaleStabilityStatement.{u, v} K)
include h1 h2

/-- The inclusion `Ét(X) → Qét(X)` is representably flat. -/
theorem representablyFlat_toQuasiEtaleSite (X : LocalizedCategory.{u, v, v} (K := K)) :
    RepresentablyFlat (EtaleSite.toQuasiEtaleSite X) := by
  have := h2.2
  exact representablyFlat_changeProp X etale_le_quasiEtale
    (fun _ _ _ f g hf => h1 f g hf)

/-- The inclusion `Ét(X) → Qét(X)` is continuous. -/
theorem isContinuous_toQuasiEtaleSite (X : LocalizedCategory.{u, v, v} (K := K)) :
    (EtaleSite.toQuasiEtaleSite X).IsContinuous (etaleTopology X) (quasiEtaleTopology X) := by
  have := representablyFlat_toQuasiEtaleSite h1 h2 X
  apply isContinuous_of_flat _ (etalePrecoverage X)
  intro U R hR
  rw [← Sieve.generate_map_eq_functorPushforward]
  apply generate_mem_quasiEtaleTopology
  rw [mem_quasiEtalePrecoverage_iff]
  intro x
  obtain ⟨V, f, hf, y, rfl⟩ := mem_etalePrecoverage_iff.1 hR x
  have hfe : etale f.left := by
    apply h2.2.of_postcomp f.left U.hom U.prop
    rw [MorphismProperty.Over.w f]
    exact V.prop
  obtain ⟨σ, hσ, hn, hT⟩ := exists_chartImages f.left hfe y
  refine ⟨σ, hσ, hn, fun T hTσ => ?_⟩
  obtain ⟨i, rfl⟩ := hT T hTσ
  exact ⟨(EtaleSite.toQuasiEtaleSite X).obj V, (EtaleSite.toQuasiEtaleSite X).map f, i,
    Presieve.map.of hf, rfl⟩

end NonEquivariant

section Equivariant

variable {G : Type z} [Group G] [TopologicalSpace G]

/-- Pullbacks of étale `G`-morphisms: the localized pullback, with the induced action, is a
`G`-space, and it is a pullback in `G`-spaces with étale base-changed leg. -/
theorem exists_gSpace_pullback (h1 : LocalizedEtalePullbackStatement.{u, v} K)
    (h3 : EtalePullbackGSpaceStatement.{u, v, z} K)
    ⦃A B Y : GSpace.{u, v, v} K G⦄ (f : A ⟶ Y) (g : B ⟶ Y) (hf : GSpace.etale f) :
    ∃ (Z : GSpace.{u, v, v} K G) (p : Z ⟶ A) (q : Z ⟶ B),
      IsPullback p q f g ∧ GSpace.etale q := by
  obtain ⟨P, p, q, hP, hq⟩ := h1 (GSpace.forget.map f) (GSpace.forget.map g) hf
  have hfe : ∀ a, (A.obj.ρAut a).hom ≫ GSpace.forget.map f =
      GSpace.forget.map f ≫ (Y.obj.ρAut a).hom := fun a => f.hom.comm a
  have hge : ∀ a, (B.obj.ρAut a).hom ≫ GSpace.forget.map g =
      GSpace.forget.map g ≫ (Y.obj.ρAut a).hom := fun a => g.hom.comm a
  let σ := CategoricalPullback.pullbackAction hP A.obj.ρAut B.obj.ρAut Y.obj.ρAut hfe hge
  have hσp := CategoricalPullback.pullbackAction_fst hP A.obj.ρAut B.obj.ρAut Y.obj.ρAut hfe hge
  have hσq := CategoricalPullback.pullbackAction_snd hP A.obj.ρAut B.obj.ρAut Y.obj.ρAut hfe hge
  obtain ⟨hT2, hcont⟩ := h3 G (GSpace.forget.map f) (GSpace.forget.map g) p q hf hP
    A.property.1 B.property.1 Y.property.1 σ A.obj.ρAut B.obj.ρAut A.property.2 B.property.2
    hσp hσq
  let Pa : Action (LocalizedCategory.{u, v, v} (K := K)) G :=
    { V := P, ρ := (Aut.toEnd P).comp σ }
  have hρ : Pa.ρAut = σ := MonoidHom.ext fun a => Iso.ext rfl
  let Z : GSpace.{u, v, v} K G := ⟨Pa, hT2, by rw [hρ]; exact hcont⟩
  let p' : Z ⟶ A := ObjectProperty.homMk ⟨p, fun a => hσp a⟩
  let q' : Z ⟶ B := ObjectProperty.homMk ⟨q, fun a => hσq a⟩
  refine ⟨Z, p', q', ?_, hq⟩
  have : ReflectsLimit (cospan f g) (ObjectProperty.ι (gSpaceProperty.{u, v, v} K G)) :=
    inferInstance
  have : ReflectsLimit (cospan f g ⋙ ObjectProperty.ι (gSpaceProperty.{u, v, v} K G))
    (Action.forget _ G) := inferInstance
  have : ReflectsLimit (cospan f g) (GSpace.forget (K := K) (G := G)) :=
    comp_reflectsLimit _ _
  refine IsPullback.of_map GSpace.forget ?_ hP
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  exact hP.w

variable (h1 : LocalizedEtalePullbackStatement.{u, v} K)
  (h2 : LocalizedEtaleStabilityStatement.{u, v} K)
  (h3 : EtalePullbackGSpaceStatement.{u, v, z} K)
include h1 h2 h3

/-- The inclusion `Ét(X(G)) → Qét(X(G))` is representably flat. -/
theorem representablyFlat_ofEquivariantEtaleSite (X : GSpace.{u, v, v} K G) :
    RepresentablyFlat (EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X) := by
  have : (GSpace.etale (K := K) (G := G)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have : (GSpace.etale (K := K) (G := G)).HasOfPostcompProperty GSpace.etale :=
    ⟨fun f g hg hfg => h2.2.of_postcomp (GSpace.forget.map f) (GSpace.forget.map g) hg (by
      rw [← Functor.map_comp]
      exact hfg)⟩
  exact representablyFlat_changeProp X GSpace.etale_le_quasiEtale
    (exists_gSpace_pullback h1 h3)

omit h1 h3 in
/-- Étale `G`-morphisms over `X`: the underlying morphism of a morphism of `Ét(X(G))` is
étale. -/
theorem etale_forget_map_left {X : GSpace.{u, v, v} K G} {U V : EquivariantEtaleSite X}
    (f : V ⟶ U) : etale (GSpace.forget.map f.left) := by
  apply h2.2.of_postcomp _ (GSpace.forget.map U.hom) U.prop
  rw [← Functor.map_comp, MorphismProperty.Over.w f]
  exact V.prop

/-- The inclusion `Ét(X(G)) → Qét(X(G))` is continuous. -/
theorem isContinuous_ofEquivariantEtaleSite (X : GSpace.{u, v, v} K G) :
    (EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X).IsContinuous
      (equivariantEtaleTopology X) (equivariantQuasiEtaleTopology X) := by
  have := representablyFlat_ofEquivariantEtaleSite h1 h2 h3 X
  apply isContinuous_of_flat _ (equivariantEtalePrecoverage X)
  intro U R hR
  rw [← Sieve.generate_map_eq_functorPushforward]
  apply generate_mem_equivariantQuasiEtaleTopology
  rw [mem_equivariantQuasiEtalePrecoverage_iff, mem_quasiEtalePrecoverage_iff]
  intro x
  obtain ⟨V, f, hf, y, rfl⟩ := mem_equivariantEtalePrecoverage_iff.1 hR x
  obtain ⟨σ, hσ, hn, hT⟩ :=
    exists_chartImages (GSpace.forget.map f.left) (etale_forget_map_left h2 f) y
  refine ⟨σ, hσ, hn, fun T hTσ => ?_⟩
  obtain ⟨i, rfl⟩ := hT T hTσ
  exact ⟨(EquivariantQuasiEtaleSite.toQuasiEtaleSite X).obj
      ((EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X).obj V),
    (EquivariantQuasiEtaleSite.toQuasiEtaleSite X).map
      ((EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X).map f), i,
    Presieve.map.of (Presieve.map.of hf), rfl⟩

end Equivariant

end QuasiEtaleToEtale

open QuasiEtaleToEtale in
/-- `QuasiEtaleToEtaleStatement` follows from étale base change in the localized category
(`LocalizedEtalePullbackStatement`), stability of étale morphisms under composition and right
cancellation (`LocalizedEtaleStabilityStatement`), and the `G`-space structure of fibre products
along étale morphisms of `G`-spaces (`EtalePullbackGSpaceStatement`). -/
theorem quasiEtaleToEtale_of_inputs
    (h1 : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      LocalizedEtalePullbackStatement.{u, v} K)
    (h2 : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      LocalizedEtaleStabilityStatement.{u, v} K)
    (h3 : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      EtalePullbackGSpaceStatement.{u, v, z} K) :
    QuasiEtaleToEtaleStatement.{u, v, z} := by
  intro K _ _ _
  exact ⟨fun X => ⟨representablyFlat_toQuasiEtaleSite (h1 K) (h2 K) X,
      isContinuous_toQuasiEtaleSite (h1 K) (h2 K) X⟩,
    fun G _ _ X => ⟨representablyFlat_ofEquivariantEtaleSite (h1 K) (h2 K) (h3 K) X,
      isContinuous_ofEquivariantEtaleSite (h1 K) (h2 K) (h3 K) X⟩⟩

end Langlands.Analytic.SaturatedAtlasPresentation
