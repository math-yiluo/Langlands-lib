import Langlands.AlgebraicGeometry.Picard.LocalTwoAxisTrivialityStatement
import Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityProof
import Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingProof
import Langlands.AlgebraicGeometry.Modules.ProperLineBundleMorphismSpreadProof

/-! # Local two-axis triviality for smooth proper families

The two section axes detect degree-one cohomology on the scheme-theoretic fibre.
The published frame-lifting theorem gives a section near that fibre, and properness
spreads its invertibility. Flattening the two open restrictions gives the target.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

private lemma product_geometry {S : Scheme.{u}} (X Y : Over S)
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] :
    Smooth (X ⨯ Y).hom ∧ IsProper (X ⨯ Y).hom ∧
      GeometricallyConnected (X ⨯ Y).hom := by
  have hP : IsPullback (prod.fst (X := X) (Y := Y)).left
      (prod.snd (X := X) (Y := Y)).left X.hom Y.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst (X := X) (Y := Y)) (prod.snd (X := X) (Y := Y)))
      (prodIsProd X Y)
  have : Smooth (prod.fst (X := X) (Y := Y)).left :=
    MorphismProperty.of_isPullback hP.flip inferInstance
  have : IsProper (prod.fst (X := X) (Y := Y)).left :=
    MorphismProperty.of_isPullback hP.flip inferInstance
  have : GeometricallyConnected (prod.fst (X := X) (Y := Y)).left :=
    MorphismProperty.of_isPullback hP.flip inferInstance
  rw [← (prod.fst (X := X) (Y := Y)).w]
  exact ⟨inferInstance, inferInstance, GeometricallyConnected.comp _ _⟩

private lemma first_axis_closed {S : Scheme.{u}} (X Y : Over S)
    [IsProper Y.hom] (y₀ : Over.mk (𝟙 S) ⟶ Y) :
    IsClosedImmersion
      (prod.lift (𝟙 X) (Over.mkIdTerminal.from X ≫ y₀)).left := by
  have hP : IsPullback (prod.fst (X := X) (Y := Y)).left
      (prod.snd (X := X) (Y := Y)).left X.hom Y.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst (X := X) (Y := Y)) (prod.snd (X := X) (Y := Y)))
      (prodIsProd X Y)
  have : IsSeparated (prod.fst (X := X) (Y := Y)).left :=
    MorphismProperty.of_isPullback hP.flip inferInstance
  have h :
      (prod.lift (𝟙 X) (Over.mkIdTerminal.from X ≫ y₀)).left ≫
        (prod.fst (X := X) (Y := Y)).left = 𝟙 X.left := by
    rw [← Over.comp_left, prod.lift_fst]
    rfl
  have : IsClosedImmersion
      ((prod.lift (𝟙 X) (Over.mkIdTerminal.from X ≫ y₀)).left ≫
        (prod.fst (X := X) (Y := Y)).left) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ (prod.fst (X := X) (Y := Y)).left

private lemma second_axis_closed {S : Scheme.{u}} (X Y : Over S)
    [IsProper X.hom] (x₀ : Over.mk (𝟙 S) ⟶ X) :
    IsClosedImmersion
      (prod.lift (Over.mkIdTerminal.from Y ≫ x₀) (𝟙 Y)).left := by
  have hP : IsPullback (prod.fst (X := X) (Y := Y)).left
      (prod.snd (X := X) (Y := Y)).left X.hom Y.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst (X := X) (Y := Y)) (prod.snd (X := X) (Y := Y)))
      (prodIsProd X Y)
  have : IsSeparated (prod.snd (X := X) (Y := Y)).left :=
    MorphismProperty.of_isPullback hP inferInstance
  have h :
      (prod.lift (Over.mkIdTerminal.from Y ≫ x₀) (𝟙 Y)).left ≫
        (prod.snd (X := X) (Y := Y)).left = 𝟙 Y.left := by
    rw [← Over.comp_left, prod.lift_snd]
    rfl
  have : IsClosedImmersion
      ((prod.lift (Over.mkIdTerminal.from Y ≫ x₀) (𝟙 Y)).left ≫
        (prod.snd (X := X) (Y := Y)).left) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ (prod.snd (X := X) (Y := Y)).left

private def fibre_map {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y) (s : S) :
    X.hom.fiber s ⟶ Y.hom.fiber s :=
  pullback.lift (X.hom.fiberι s ≫ i.left) (X.hom.fiberToSpecResidueField s) (by
    rw [Category.assoc, Over.w i]
    exact X.hom.fiber_fac s)

@[reassoc (attr := simp)]
private lemma fibre_map_ι {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y) (s : S) :
    fibre_map i s ≫ Y.hom.fiberι s = X.hom.fiberι s ≫ i.left :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
private lemma fibre_map_base {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y) (s : S) :
    fibre_map i s ≫ Y.hom.fiberToSpecResidueField s =
      X.hom.fiberToSpecResidueField s :=
  pullback.lift_snd ..

private lemma product_fibre_isPullback {S : Scheme.{u}} (X Y : Over S) (s : S) :
    IsPullback (fibre_map (prod.fst (X := X) (Y := Y)) s)
      (fibre_map (prod.snd (X := X) (Y := Y)) s)
      (X.hom.fiberToSpecResidueField s) (Y.hom.fiberToSpecResidueField s) := by
  have hP : IsPullback (prod.fst (X := X) (Y := Y)).left
      (prod.snd (X := X) (Y := Y)).left X.hom Y.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst (X := X) (Y := Y)) (prod.snd (X := X) (Y := Y)))
      (prodIsProd X Y)
  apply IsPullback.mk'
  · simp only [fibre_map_base]
  · intro T a b h₁ h₂
    apply pullback.hom_ext
    · apply hP.hom_ext
      · simpa only [Category.assoc, fibre_map, Scheme.Hom.fiberι, pullback.lift_fst] using
          congrArg (fun t => t ≫ X.hom.fiberι s) h₁
      · simpa only [Category.assoc, fibre_map, Scheme.Hom.fiberι, pullback.lift_fst] using
          congrArg (fun t => t ≫ Y.hom.fiberι s) h₂
    · simpa only [Category.assoc, fibre_map, Scheme.Hom.fiberToSpecResidueField, pullback.lift_snd] using
        congrArg (fun t => t ≫ X.hom.fiberToSpecResidueField s) h₁
  · intro T a b hab
    let m : T ⟶ (X ⨯ Y).left := hP.lift
      (a ≫ X.hom.fiberι s) (b ≫ Y.hom.fiberι s) (by
        simp only [Category.assoc, Scheme.Hom.fiber_fac]
        rw [← Category.assoc, hab, Category.assoc])
    let l : T ⟶ (X ⨯ Y).hom.fiber s := pullback.lift m
      (a ≫ X.hom.fiberToSpecResidueField s) (by
        rw [← (prod.fst (X := X) (Y := Y)).w]
        simp only [m, IsPullback.lift_fst_assoc, Category.assoc, Scheme.Hom.fiber_fac])
    refine ⟨l, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp [l, m, fibre_map, Scheme.Hom.fiberι, Category.assoc]
      · simp [l, fibre_map, Scheme.Hom.fiberToSpecResidueField, Category.assoc]
    · apply pullback.hom_ext
      · simp [l, m, fibre_map, Scheme.Hom.fiberι, Category.assoc]
      · simpa [l, fibre_map, Scheme.Hom.fiberToSpecResidueField, Category.assoc] using hab

@[simp]
private lemma fibre_map_id {S : Scheme.{u}} (X : Over S) (s : S) :
    fibre_map (𝟙 X) s = 𝟙 (X.hom.fiber s) := by
  apply pullback.hom_ext
  · change fibre_map (𝟙 X) s ≫ X.hom.fiberι s = 𝟙 _ ≫ X.hom.fiberι s
    rw [fibre_map_ι, Over.id_left, Category.comp_id, Category.id_comp]
  · change fibre_map (𝟙 X) s ≫ X.hom.fiberToSpecResidueField s =
      𝟙 _ ≫ X.hom.fiberToSpecResidueField s
    rw [fibre_map_base, Category.id_comp]

@[simp]
private lemma fibre_map_comp {S : Scheme.{u}} {X Y Z : Over S}
    (i : X ⟶ Y) (j : Y ⟶ Z) (s : S) :
    fibre_map (i ≫ j) s = fibre_map i s ≫ fibre_map j s := by
  apply pullback.hom_ext <;>
    simp [fibre_map, Scheme.Hom.fiberι, Scheme.Hom.fiberToSpecResidueField,
      Category.assoc]

private def fibre_section {S : Scheme.{u}} {X : Over S}
    (x₀ : Over.mk (𝟙 S) ⟶ X) (s : S) :
    Over.mk (𝟙 (Spec (S.residueField s))) ⟶
      Over.mk (X.hom.fiberToSpecResidueField s) :=
  Over.homMk (pullback.lift (S.fromSpecResidueField s ≫ x₀.left)
    (𝟙 (Spec (S.residueField s))) (by simp)) (by
      simp [Scheme.Hom.fiberToSpecResidueField])

@[reassoc (attr := simp)]
private lemma fibre_section_ι {S : Scheme.{u}} {X : Over S}
    (x₀ : Over.mk (𝟙 S) ⟶ X) (s : S) :
    (fibre_section x₀ s).left ≫ X.hom.fiberι s =
      S.fromSpecResidueField s ≫ x₀.left :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
private lemma fibre_section_base {S : Scheme.{u}} {X : Over S}
    (x₀ : Over.mk (𝟙 S) ⟶ X) (s : S) :
    (fibre_section x₀ s).left ≫ X.hom.fiberToSpecResidueField s =
      𝟙 (Spec (S.residueField s)) :=
  pullback.lift_snd ..

private lemma fibre_map_to_section {S : Scheme.{u}} (X Y : Over S)
    (y₀ : Over.mk (𝟙 S) ⟶ Y) (s : S) :
    fibre_map (Over.mkIdTerminal.from X ≫ y₀) s =
      X.hom.fiberToSpecResidueField s ≫ (fibre_section y₀ s).left := by
  apply pullback.hom_ext
  · change fibre_map _ s ≫ Y.hom.fiberι s =
      (X.hom.fiberToSpecResidueField s ≫ (fibre_section y₀ s).left) ≫ Y.hom.fiberι s
    rw [fibre_map_ι, Category.assoc, fibre_section_ι]
    simp only [Over.comp_left, Over.mkIdTerminal_from_left]
    rw [← Category.assoc, ← Category.assoc, Scheme.Hom.fiber_fac]
    rfl
  · change fibre_map _ s ≫ Y.hom.fiberToSpecResidueField s =
      (X.hom.fiberToSpecResidueField s ≫ (fibre_section y₀ s).left) ≫
        Y.hom.fiberToSpecResidueField s
    rw [fibre_map_base, Category.assoc, fibre_section_base, Category.comp_id]

private lemma first_axis_fibre {S : Scheme.{u}} (X Y : Over S)
    (y₀ : Over.mk (𝟙 S) ⟶ Y) (s : S) :
    fibre_map (prod.lift (𝟙 X) (Over.mkIdTerminal.from X ≫ y₀)) s =
      (product_fibre_isPullback X Y s).lift (𝟙 (X.hom.fiber s))
        (X.hom.fiberToSpecResidueField s ≫ (fibre_section y₀ s).left) (by simp) := by
  apply (product_fibre_isPullback X Y s).hom_ext
  · rw [IsPullback.lift_fst, ← fibre_map_comp, prod.lift_fst, fibre_map_id]
  · rw [IsPullback.lift_snd, ← fibre_map_comp, prod.lift_snd, fibre_map_to_section]

private lemma second_axis_fibre {S : Scheme.{u}} (X Y : Over S)
    (x₀ : Over.mk (𝟙 S) ⟶ X) (s : S) :
    fibre_map (prod.lift (Over.mkIdTerminal.from Y ≫ x₀) (𝟙 Y)) s =
      (product_fibre_isPullback X Y s).lift
        (Y.hom.fiberToSpecResidueField s ≫ (fibre_section x₀ s).left)
        (𝟙 (Y.hom.fiber s)) (by simp) := by
  apply (product_fibre_isPullback X Y s).hom_ext
  · rw [IsPullback.lift_fst, ← fibre_map_comp, prod.lift_fst, fibre_map_to_section]
  · rw [IsPullback.lift_snd, ← fibre_map_comp, prod.lift_snd, fibre_map_id]

private lemma product_fibre_H1_detection
    {S : Scheme.{u}} (X Y : Over S)
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
    (x₀ : Over.mk (𝟙 S) ⟶ X) (y₀ : Over.mk (𝟙 S) ⟶ Y) (s : S) :
    let j₁ := fibre_map (prod.lift (𝟙 X) (Over.mkIdTerminal.from X ≫ y₀)) s
    let j₂ := fibre_map (prod.lift (Over.mkIdTerminal.from Y ≫ x₀) (𝟙 Y)) s
    let O := Langlands.Scheme.Modules.structureSheaf ((X ⨯ Y).hom.fiber s)
    let H := Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology
      ((X ⨯ Y).hom.fiberToSpecResidueField s) 1
    ∀ c : H.obj O,
      (H.map ((Scheme.Modules.pullbackPushforwardAdjunction j₁).unit.app O)).hom c = 0 →
      (H.map ((Scheme.Modules.pullbackPushforwardAdjunction j₂).unit.app O)).hom c = 0 →
      c = 0 := by
  have h := fieldTwoAxisH1Injectivity (S.residueField s) (Field.toIsField _)
    (Over.mk (X.hom.fiberToSpecResidueField s))
    (Over.mk (Y.hom.fiberToSpecResidueField s))
    (by change Smooth (pullback.snd X.hom (S.fromSpecResidueField s)); infer_instance)
    (by change IsProper (pullback.snd X.hom (S.fromSpecResidueField s)); infer_instance)
    (by change GeometricallyConnected
          (pullback.snd X.hom (S.fromSpecResidueField s)); infer_instance)
    (by change Smooth (pullback.snd Y.hom (S.fromSpecResidueField s)); infer_instance)
    (by change IsProper (pullback.snd Y.hom (S.fromSpecResidueField s)); infer_instance)
    (by change GeometricallyConnected
          (pullback.snd Y.hom (S.fromSpecResidueField s)); infer_instance)
    (fibre_section x₀ s) (fibre_section y₀ s) ((X ⨯ Y).hom.fiber s)
    (fibre_map (prod.fst (X := X) (Y := Y)) s)
    (fibre_map (prod.snd (X := X) (Y := Y)) s) (product_fibre_isPullback X Y s)
  dsimp only [Over.mk_hom, Over.mk_left] at h
  rw [fibre_map_base, ← first_axis_fibre, ← second_axis_fibre] at h
  exact h

private lemma nested_open_triviality
    {P S : Scheme.{u}} (f : P ⟶ S) (M : P.Modules) (s : S)
    (U : S.Opens) (hs : s ∈ U) (V : U.toScheme.Opens)
    (hsV : (⟨s, hs⟩ : U) ∈ V)
    (hM : Nonempty
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd f U.ι) V.ι)).obj
        ((Scheme.Modules.pullback (pullback.fst f U.ι)).obj M) ≅
          Langlands.Scheme.Modules.structureSheaf
            (pullback (pullback.snd f U.ι) V.ι))) :
    ∃ W : S.Opens, s ∈ W ∧ Nonempty
      ((Scheme.Modules.pullback (pullback.fst f W.ι)).obj M ≅
        Langlands.Scheme.Modules.structureSheaf (pullback f W.ι)) := by
  let g : V.toScheme ⟶ S := V.ι ≫ U.ι
  let W : S.Opens := g.opensRange
  let e₀ : V.toScheme ≅ W.toScheme := g.isoOpensRange
  let e₁ := pullbackLeftPullbackSndIso f U.ι V.ι
  let e₂ : pullback f g ≅ pullback f W.ι :=
    asIso (pullback.map f g f W.ι (𝟙 P) e₀.hom (𝟙 S)
      (by simp) (by simp [e₀, W]))
  let e : pullback (pullback.snd f U.ι) V.ι ≅ pullback f W.ι := e₁ ≪≫ e₂
  let q := pullback.fst (pullback.snd f U.ι) V.ι ≫ pullback.fst f U.ι
  have he : e.hom ≫ pullback.fst f W.ι = q := by
    simp [e, e₂, q, Category.assoc, e₁, g]
  have hi : e.inv ≫ q = pullback.fst f W.ι := by
    rw [← he, Iso.inv_hom_id_assoc]
  obtain ⟨t⟩ := hM
  let t' : (Scheme.Modules.pullback q).obj M ≅
      Langlands.Scheme.Modules.structureSheaf
        (pullback (pullback.snd f U.ι) V.ι) :=
    ((Scheme.Modules.pullbackComp
      (pullback.fst (pullback.snd f U.ι) V.ι) (pullback.fst f U.ι)).app M).symm ≪≫ t
  refine ⟨W, ?_, ⟨?_⟩⟩
  · exact ⟨⟨⟨s, hs⟩, hsV⟩, rfl⟩
  · exact (Scheme.Modules.pullbackCongr hi.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp e.inv q).app M).symm ≪≫
      (Scheme.Modules.pullback e.inv).mapIso t' ≪≫
      Langlands.Scheme.Modules.pullbackUnitIso e.inv

/-- A line bundle on a product of smooth proper geometrically connected families, trivial
on both section axes and on a scheme-theoretic fibre, is trivial over an open neighbourhood
of that base point. -/
theorem localTwoAxisTriviality : LocalTwoAxisTrivialityStatement.{u} := by
  intro S X Y hXsm hXpr hXgc hYsm hYpr hYgc x₀ y₀ L s hL₁ hL₂ hLs
  have := hXsm
  have := hXpr
  have := hXgc
  have := hYsm
  have := hYpr
  have := hYgc
  obtain ⟨hPsm, hPpr, hPgc⟩ := product_geometry X Y
  have := hPsm
  have := hPpr
  have := hPgc
  obtain ⟨U, hs, σ, hσ⟩ := fibreFrameLifting S (X ⨯ Y) X Y
    hPsm hPpr hPgc hXsm hXpr hXgc hYsm hYpr hYgc
    (prod.lift (𝟙 X) (Over.mkIdTerminal.from X ≫ y₀))
    (prod.lift (Over.mkIdTerminal.from Y ≫ x₀) (𝟙 Y))
    (first_axis_closed X Y y₀) (second_axis_closed X Y x₀)
    L s hL₁ hL₂ hLs (product_fibre_H1_detection X Y x₀ y₀ s)
  let Lᵤ : LineBundle (pullback (X ⨯ Y).hom U.ι) :=
    (LineBundle.pullback (pullback.fst (X ⨯ Y).hom U.ι)).obj L
  obtain ⟨V, hsV, hV⟩ :=
    Langlands.AlgebraicGeometry.Modules.properLineBundleMorphismSpread
      (pullback (X ⨯ Y).hom U.ι) U.toScheme
    (pullback.snd (X ⨯ Y).hom U.ι) (by infer_instance) Lᵤ σ ⟨s, hs⟩ hσ
  have := hV
  apply nested_open_triviality (X ⨯ Y).hom L.obj s U hs V hsV
  exact ⟨(asIso ((Scheme.Modules.pullback
      (pullback.fst (pullback.snd (X ⨯ Y).hom U.ι) V.ι)).map σ)).symm ≪≫
    Langlands.Scheme.Modules.pullbackUnitIso
      (pullback.fst (pullback.snd (X ⨯ Y).hom U.ι) V.ι)⟩

end Langlands.AlgebraicGeometry.Picard
