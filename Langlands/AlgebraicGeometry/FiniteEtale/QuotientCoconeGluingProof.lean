import Langlands.AlgebraicGeometry.FiniteEtale.QuotientGluingConstruction

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

namespace QuotientGluing

/-! ### Points in the range of an open immersion from a spectrum -/

section Points

variable {A K : CommRingCat.{u}} {Z : Scheme.{u}} (j : Spec A ⟶ Z) [IsOpenImmersion j]
  (x : Spec K ⟶ Z) (h : Set.range x ⊆ Set.range j)

/-- The ring map of a point lying in the range of an open immersion from a spectrum. -/
def pointRing : A ⟶ K :=
  Spec.preimage (IsOpenImmersion.lift j x h)

theorem SpecMap_pointRing_comp : Spec.map (pointRing j x h) ≫ j = x := by
  rw [pointRing, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem pointRing_eq {φ : A ⟶ K} (hφ : Spec.map φ ≫ j = x) : pointRing j x h = φ := by
  apply Spec.map_injective
  rw [← cancel_mono j, SpecMap_pointRing_comp, hφ]

end Points

section Construction

variable {S : Scheme.{u}} {G : Type u} [Group G] (D : SingleObj G ⥤ Cover S)

/-! ### Descending invariant maps -/

section Desc

variable {Z : Scheme.{u}} {t : Z ⟶ S} (ψ : coverScheme D ⟶ Z) (hψ : ψ ≫ t = coverHom D)
  (hinv : ∀ g : G, coverMap D g ≫ ψ = ψ)

include hψ in
theorem preimage_coverHom_le_of_comp (U : S.Opens) : coverHom D ⁻¹ᵁ U ≤ ψ ⁻¹ᵁ t ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, hψ]

/-- An invariant map over the base pulls sections over preimages of `U` back into the
invariant sections. -/
def descRing (U : S.Opens) : Γ(Z, t ⁻¹ᵁ U) ⟶ CommRingCat.of (invariantRing D U) :=
  CommRingCat.ofHom (RingHom.codRestrict
    (toSectionRing D U (ψ.appLE (t ⁻¹ᵁ U) (coverHom D ⁻¹ᵁ U)
      (preimage_coverHom_le_of_comp D ψ hψ U)))
    (invariantRing D U) fun z => (mem_invariantRing_iff D U _).mpr fun g => by
      change (ψ.appLE _ _ _ ≫ sectionAction D U g).hom z = (ψ.appLE _ _ _).hom z
      rw [sectionAction, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq (hinv g)])

theorem descRing_comp_invariantInclusion (U : S.Opens) :
    descRing D ψ hψ hinv U ≫ invariantInclusion D U =
      ψ.appLE (t ⁻¹ᵁ U) (coverHom D ⁻¹ᵁ U) (preimage_coverHom_le_of_comp D ψ hψ U) := by
  ext z
  rfl

theorem appLE_comp_descRing (U : S.Opens) :
    t.appLE U (t ⁻¹ᵁ U) le_rfl ≫ descRing D ψ hψ hinv U = (invariantDiagramMap D).app (op U) := by
  ext r
  change (ψ.appLE _ _ _).hom ((t.appLE _ _ _).hom r) = ((coverHom D).app U).hom r
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE,
    appLE_eq_of_eq hψ]

variable [Finite G] [IsAffineHom t]

/-- The map out of the glued quotient induced by an invariant map over the base, glued from
the spectra of `descRing`. -/
def gluedDesc : gluedQuotient D ⟶ Z :=
  colimit.desc (quotientGlueData D).functor
    { pt := Z
      ι :=
        { app := fun U => Spec.map (descRing D ψ hψ hinv U.1) ≫ (U.2.preimage t).fromSpec
          naturality := fun U V i => by
            dsimp [quotientGlueData, Scheme.AffineZariskiSite.relativeGluingData]
            rw [Category.comp_id, ← Spec.map_comp_assoc,
              ← (V.2.preimage t).map_fromSpec (U.2.preimage t)
                (homOfLE (t.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.le))).op,
              ← Spec.map_comp_assoc]
            congr 2
            ext z
            apply Subtype.ext
            change (sectionRes D _).hom ((ψ.appLE _ _ _).hom z) =
              (ψ.appLE _ _ _).hom ((Z.presheaf.map _).hom z)
            simp only [← CommRingCat.comp_apply, sectionRes, Scheme.Hom.appLE_map,
              Scheme.Hom.map_appLE] } }

theorem gluedCover_f_gluedDesc (U : S.AffineZariskiSite) :
    (gluedCover D).f U ≫ gluedDesc D ψ hψ hinv =
      Spec.map (descRing D ψ hψ hinv U.1) ≫ (U.2.preimage t).fromSpec := by
  rw [gluedCover_f]
  exact colimit.ι_desc _ _

theorem gluedMap_gluedDesc : gluedMap D ≫ gluedDesc D ψ hψ hinv = ψ := by
  refine coverScheme_hom_ext D fun U => ?_
  rw [reassoc_of% fromSpec_gluedMap, gluedCover_f_gluedDesc, ← Spec.map_comp_assoc,
    descRing_comp_invariantInclusion, IsAffineOpen.SpecMap_appLE_fromSpec]

theorem gluedDesc_comp : gluedDesc D ψ hψ hinv ≫ t = gluedStructure D := by
  refine Scheme.Cover.hom_ext (gluedCover D) _ _ fun U => ?_
  rw [reassoc_of% gluedCover_f_gluedDesc, gluedCover_f_gluedStructure,
    ← IsAffineOpen.SpecMap_appLE_fromSpec t U.2 (U.2.preimage t) le_rfl, ← Spec.map_comp_assoc,
    appLE_comp_descRing]

/-- Maps out of the glued quotient over an affine morphism are determined by their
composites with the quotient map. -/
theorem gluedQuotient_hom_ext {m₁ m₂ : gluedQuotient D ⟶ Z} (h₁ : m₁ ≫ t = gluedStructure D)
    (h₂ : m₂ ≫ t = gluedStructure D) (H : gluedMap D ≫ m₁ = gluedMap D ≫ m₂) : m₁ = m₂ := by
  refine Scheme.Cover.hom_ext (gluedCover D) _ _ fun U => ?_
  have hpre (m : gluedQuotient D ⟶ Z) (hm : m ≫ t = gluedStructure D) :
      ((gluedCover D).f U ≫ m) ⁻¹ᵁ (t ⁻¹ᵁ U.1) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, Category.assoc, hm, gluedCover_f_gluedStructure,
      Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self, Scheme.Hom.preimage_top]
  refine eq_of_SpecMap_comp_eq_of_isAffineOpen (invariantInclusion D U.1)
    (invariantInclusion_injective D U.1) _ (U.2.preimage t) (hpre m₁ h₁) (hpre m₂ h₂) ?_
  rw [← Category.assoc, ← Category.assoc, ← fromSpec_gluedMap, Category.assoc, Category.assoc, H]

end Desc

/-! ### The glued quotient cocone -/

section Cocone

variable [IsLocallyNoetherian S] [Finite G]

/-- The glued quotient as a finite étale cover. -/
def gluedQuotientCover : Cover S := cover (gluedStructure D)

/-- The leg of the glued quotient cocone. -/
def gluedCoconeMap : D.obj (SingleObj.star G) ⟶ gluedQuotientCover D :=
  ObjectProperty.homMk (Over.homMk (gluedMap D) (gluedMap_gluedStructure D))

/-- The glued quotient cocone. -/
def gluedCocone : Cocone D where
  pt := gluedQuotientCover D
  ι :=
    { app := fun _ => gluedCoconeMap D
      naturality := fun _ _ g => by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        change (D.map g).hom.left ≫ gluedMap D = gluedMap D ≫ 𝟙 _
        rw [Category.comp_id]
        exact coverMap_gluedMap D g }

/-- The glued quotient cocone is a colimit in finite étale covers. -/
def gluedCoconeIsColimit : IsColimit (gluedCocone D) where
  desc s := ObjectProperty.homMk (Over.homMk
    (gluedDesc D (s.ι.app (SingleObj.star G)).hom.left (Over.w (s.ι.app (SingleObj.star G)).hom)
      (cocone_leg_invariant D s))
    (gluedDesc_comp D _ _ _))
  fac s _ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact gluedMap_gluedDesc D _ _ _
  uniq s m hm := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    refine gluedQuotient_hom_ext D (Over.w m.hom)
      (gluedDesc_comp D (s.ι.app (SingleObj.star G)).hom.left
        (Over.w (s.ι.app (SingleObj.star G)).hom) (cocone_leg_invariant D s)) ?_
    exact (congrArg (fun f => f.hom.left) (hm (SingleObj.star G))).trans
      (gluedMap_gluedDesc D (s.ι.app (SingleObj.star G)).hom.left
        (Over.w (s.ι.app (SingleObj.star G)).hom) (cocone_leg_invariant D s)).symm

end Cocone

/-! ### Geometric points -/

section GeometricPoints

variable {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S) (U : S.AffineZariskiSite)
  (hs : ∀ p, s p ∈ U.1)

include hs in
theorem range_subset_fromSpec_preimage {Y : Scheme.{u}} {h : Y ⟶ S} [IsAffineHom h]
    (y : Spec (.of Ω) ⟶ Y) (hy : y ≫ h = s) :
    Set.range y ⊆ Set.range (U.2.preimage h).fromSpec := by
  rw [IsAffineOpen.range_fromSpec]
  rintro _ ⟨p, rfl⟩
  show h (y p) ∈ U.1
  rw [← Scheme.Hom.comp_apply, hy]
  exact hs p

include hs in
theorem range_subset_fromSpec : Set.range s ⊆ Set.range U.2.fromSpec := by
  rw [IsAffineOpen.range_fromSpec]
  rintro _ ⟨p, rfl⟩
  exact hs p

/-- The ring map of the geometric point `s` on sections over `U`. -/
def baseRing : Γ(S, U.1) ⟶ CommRingCat.of Ω :=
  pointRing U.2.fromSpec s (range_subset_fromSpec s U hs)

/-- The ring map of a geometric point of the cover on sections over the preimage of `U`. -/
def coverPointRing (x : Fiber s (D.obj (SingleObj.star G))) :
    Γ(coverScheme D, coverHom D ⁻¹ᵁ U.1) ⟶ CommRingCat.of Ω :=
  pointRing (U.2.preimage (coverHom D)).fromSpec x.left
    (range_subset_fromSpec_preimage s U hs x.left (Over.w x))

theorem SpecMap_coverPointRing (x : Fiber s (D.obj (SingleObj.star G))) :
    Spec.map (coverPointRing D s U hs x) ≫ (U.2.preimage (coverHom D)).fromSpec = x.left :=
  SpecMap_pointRing_comp _ _ _

theorem coverPointRing_injective : Function.Injective (coverPointRing D s U hs) := by
  intro x y h
  apply Over.OverMorphism.ext
  rw [← SpecMap_coverPointRing D s U hs x, ← SpecMap_coverPointRing D s U hs y, h]

theorem app_comp_coverPointRing (x : Fiber s (D.obj (SingleObj.star G))) :
    (coverHom D).app U.1 ≫ coverPointRing D s U hs x = baseRing s U hs := by
  rw [baseRing]
  symm
  apply pointRing_eq
  rw [Spec.map_comp, Category.assoc, Scheme.Hom.app_eq_appLE,
    IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 (U.2.preimage _) le_rfl, ← Category.assoc,
    SpecMap_coverPointRing]
  exact Over.w x

theorem exists_coverPointRing (φ : Γ(coverScheme D, coverHom D ⁻¹ᵁ U.1) ⟶ CommRingCat.of Ω)
    (hφ : (coverHom D).app U.1 ≫ φ = baseRing s U hs) :
    ∃ x, coverPointRing D s U hs x = φ := by
  refine ⟨Over.homMk (Spec.map φ ≫ (U.2.preimage (coverHom D)).fromSpec) ?_, ?_⟩
  · change (Spec.map φ ≫ (U.2.preimage (coverHom D)).fromSpec) ≫ coverHom D = s
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 _ le_rfl,
      ← Scheme.Hom.app_eq_appLE, ← Spec.map_comp_assoc, hφ, baseRing, SpecMap_pointRing_comp]
  · exact pointRing_eq _ _ _ rfl

theorem coverPointRing_map (g : G) (x : Fiber s (D.obj (SingleObj.star G))) :
    coverPointRing D s U hs ((pointFunctor s).map (D.map (SingleObj.toEnd G g)) x) =
      sectionAction D U.1 g ≫ coverPointRing D s U hs x := by
  apply pointRing_eq
  rw [Spec.map_comp, Category.assoc, ← fromSpec_coverMap, ← Category.assoc,
    SpecMap_coverPointRing]
  rfl

variable [IsLocallyNoetherian S] [Finite G]

omit [IsLocallyNoetherian S] in
include hs in
theorem range_subset_gluedCover (y : Spec (.of Ω) ⟶ gluedQuotient D)
    (hy : y ≫ gluedStructure D = s) : Set.range y ⊆ Set.range ((gluedCover D).f U) := by
  rintro _ ⟨p, rfl⟩
  have hp : y p ∈ gluedStructure D ⁻¹ᵁ U.1 := by
    show gluedStructure D (y p) ∈ U.1
    rw [← Scheme.Hom.comp_apply, hy]
    exact hs p
  rw [gluedStructure_preimage] at hp
  exact hp

/-- The ring map of a geometric point of the glued quotient on invariant sections over `U`. -/
def quotientPointRing (y : Fiber s (gluedQuotientCover D)) :
    CommRingCat.of (invariantRing D U.1) ⟶ CommRingCat.of Ω :=
  pointRing (A := CommRingCat.of (invariantRing D U.1)) ((gluedCover D).f U) y.left
    (range_subset_gluedCover D s U hs y.left (Over.w y))

theorem SpecMap_quotientPointRing (y : Fiber s (gluedQuotientCover D)) :
    Spec.map (quotientPointRing D s U hs y) ≫ (gluedCover D).f U = y.left :=
  SpecMap_pointRing_comp _ _ _

theorem quotientPointRing_injective : Function.Injective (quotientPointRing D s U hs) := by
  intro y z h
  apply Over.OverMorphism.ext
  rw [← SpecMap_quotientPointRing D s U hs y, ← SpecMap_quotientPointRing D s U hs z, h]

theorem quotientPointRing_map (x : Fiber s (D.obj (SingleObj.star G))) :
    quotientPointRing D s U hs
        ((pointFunctor s).map ((gluedCocone D).ι.app (SingleObj.star G)) x) =
      invariantInclusion D U.1 ≫ coverPointRing D s U hs x := by
  apply pointRing_eq
  rw [Spec.map_comp, Category.assoc, ← fromSpec_gluedMap, ← Category.assoc,
    SpecMap_coverPointRing]
  rfl

theorem algebraMap_comp_quotientPointRing (y : Fiber s (gluedQuotientCover D)) :
    (invariantDiagramMap D).app (op U.1) ≫ quotientPointRing D s U hs y = baseRing s U hs := by
  rw [baseRing]
  symm
  apply pointRing_eq
  rw [Spec.map_comp, Category.assoc, ← gluedCover_f_gluedStructure, ← Category.assoc,
    SpecMap_quotientPointRing]
  exact Over.w y

variable [IsAlgClosed Ω]

include hs in
/-- Every geometric point of the glued quotient lifts to the cover. -/
theorem gluedCocone_surjective :
    Function.Surjective ((pointFunctor s).map ((gluedCocone D).ι.app (SingleObj.star G))) := by
  intro y
  let _ : Algebra Γ(S, U.1) Ω := (baseRing s U hs).hom.toAlgebra
  have : IsNoetherianRing Γ(S, U.1) := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  have := sectionRing_finite D U
  have := sectionRing_etale D U
  obtain ⟨hsurj, -⟩ := invariantAlgebraGeometricPoints Γ(S, U.1) (sectionRing D U.1) G Ω
  let f : invariantRing D U.1 →ₐ[Γ(S, U.1)] Ω :=
    { toRingHom := (quotientPointRing D s U hs y).hom
      commutes' := fun r =>
        congrArg (fun φ => CommRingCat.Hom.hom φ r) (algebraMap_comp_quotientPointRing D s U hs y) }
  obtain ⟨x', hx'⟩ := hsurj f
  obtain ⟨x, hx⟩ := exists_coverPointRing D s U hs (CommRingCat.ofHom x'.toRingHom) (by
    ext r
    exact x'.commutes r)
  refine ⟨x, quotientPointRing_injective D s U hs ?_⟩
  rw [quotientPointRing_map, hx]
  ext c
  exact DFunLike.congr_fun hx' c

include hs in
/-- Two geometric points of the cover have the same image in the glued quotient exactly when
they lie in one group orbit. -/
theorem gluedCocone_orbit (x y : Fiber s (D.obj (SingleObj.star G))) :
    (pointFunctor s).map ((gluedCocone D).ι.app (SingleObj.star G)) x =
        (pointFunctor s).map ((gluedCocone D).ι.app (SingleObj.star G)) y ↔
      ∃ g : G, y = (pointFunctor s).map (D.map (SingleObj.toEnd G g)) x := by
  let _ : Algebra Γ(S, U.1) Ω := (baseRing s U hs).hom.toAlgebra
  have : IsNoetherianRing Γ(S, U.1) := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  have := sectionRing_finite D U
  have := sectionRing_etale D U
  obtain ⟨-, horbit⟩ := invariantAlgebraGeometricPoints Γ(S, U.1) (sectionRing D U.1) G Ω
  let F : Fiber s (D.obj (SingleObj.star G)) → (sectionRing D U.1 →ₐ[Γ(S, U.1)] Ω) := fun z =>
    { toRingHom := (coverPointRing D s U hs z).hom
      commutes' := fun r =>
        congrArg (fun φ => CommRingCat.Hom.hom φ r) (app_comp_coverPointRing D s U hs z) }
  constructor
  · intro h
    have h' := congrArg (quotientPointRing D s U hs) h
    rw [quotientPointRing_map, quotientPointRing_map] at h'
    have hcomp : (F x).comp (invariantRing D U.1).val = (F y).comp (invariantRing D U.1).val := by
      ext c
      exact congrArg (fun φ => CommRingCat.Hom.hom φ c) h'
    obtain ⟨g, hg⟩ := (horbit (F x) (F y)).mp hcomp
    refine ⟨g⁻¹, coverPointRing_injective D s U hs ?_⟩
    rw [coverPointRing_map]
    ext a
    exact DFunLike.congr_fun hg a
  · rintro ⟨g, rfl⟩
    apply quotientPointRing_injective D s U hs
    rw [quotientPointRing_map, quotientPointRing_map, coverPointRing_map, ← Category.assoc,
      invariantInclusion_comp_sectionAction]

end GeometricPoints

end Construction

/-- Every geometric point of a scheme factors through an affine open. -/
theorem exists_affine_mem {S : Scheme.{u}} {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S) :
    ∃ U : S.AffineZariskiSite, ∀ p, s p ∈ U.1 := by
  have hmem : s default ∈ ⨆ U : S.affineOpens, (U : S.Opens) := by
    rw [iSup_affineOpens_eq_top]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  exact ⟨⟨U.1, U.2⟩, fun p => Subsingleton.elim default p ▸ hU⟩

end QuotientGluing

/-- Over an arbitrary locally noetherian base, the scheme glued from the spectra of invariant
sections over affine opens is a quotient cocone with the geometric orbit property. -/
theorem finiteGroupQuotientCocones : FiniteGroupQuotientCocones.{u} := by
  intro S _ G _ _ D
  refine ⟨QuotientGluing.gluedCocone D, ⟨QuotientGluing.gluedCoconeIsColimit D⟩,
    fun Ω _ _ s => ?_⟩
  obtain ⟨U, hs⟩ := QuotientGluing.exists_affine_mem s
  exact ⟨QuotientGluing.gluedCocone_surjective D s U hs,
    QuotientGluing.gluedCocone_orbit D s U hs⟩

end Langlands.AlgebraicGeometry.FiniteEtale
