import Langlands.Geometry.Analytic.SetInducedSiteStatement
import Langlands.Geometry.Analytic.CopiesOverHom
import Langlands.CategoryTheory.Sites.FlatPrecoverageCoverPreserving

/-! # Berkovich's functor `Σ ↦ X_Σ(G)` is representably flat and continuous -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ## Points of the spaces `X_S` -/

section Copies

variable {G : Type z} [Group G] (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G)

theorem mapHom_apply {S T : Type z} [MulAction G S] [MulAction G T] (f : S →[G] T) (s : S)
    (x : localizedSpaceFunctor.obj X.V) :
    localizedSpaceFunctor.map (mapHom X f)
        (⟨s, x⟩ : (_ : S) × (presentationOf X.V).presentation.space) =
      (⟨f s, x⟩ : (_ : T) × (presentationOf X.V).presentation.space) := by
  refine (sigma_map_apply (fun _ : S => X.V) (mapHom X f) s x).trans ?_
  rw [copy_mapHom]
  exact localizedSpaceFunctor_map_localizedSigmaCofan_inj (fun _ : T => X.V) (f s) x

theorem actionMap_apply {S : Type z} [MulAction G S] (g : G) (s : S)
    (x : localizedSpaceFunctor.obj X.V) :
    localizedSpaceFunctor.map (actionMap X S g)
        (⟨s, x⟩ : (_ : S) × (presentationOf X.V).presentation.space) =
      (⟨g • s, localizedSpaceFunctor.map (X.ρ g).asHom x⟩ :
        (_ : S) × (presentationOf X.V).presentation.space) := by
  refine (sigma_map_apply (fun _ : S => X.V) (actionMap X S g) s x).trans ?_
  rw [copy_actionMap, Functor.map_comp]
  exact localizedSpaceFunctor_map_localizedSigmaCofan_inj (fun _ : S => X.V) (g • s) _

variable {X}

theorem index_comp_mapHom {S T : Type z} [MulAction G S] [MulAction G T]
    {U : LocalizedCategory.{u, max z v, max z v} (K := K)} (φ : U ⟶ (copies X S).pt)
    (f : S →[G] T) (x : localizedSpaceFunctor.obj U) :
    index (fun _ : T => X.V) (φ ≫ mapHom X f) x = f (index (fun _ : S => X.V) φ x) := by
  unfold index
  rw [Functor.map_comp]
  change (localizedSpaceFunctor.map (mapHom X f) (localizedSpaceFunctor.map φ x)).1 =
    f (localizedSpaceFunctor.map φ x).1
  generalize localizedSpaceFunctor.map φ x = y
  obtain ⟨s, y⟩ := y
  exact congrArg Sigma.fst (mapHom_apply X f s y)

theorem index_comp_actionMap {S : Type z} [MulAction G S]
    {U : LocalizedCategory.{u, max z v, max z v} (K := K)} (φ : U ⟶ (copies X S).pt)
    (g : G) (x : localizedSpaceFunctor.obj U) :
    index (fun _ : S => X.V) (φ ≫ actionMap X S g) x = g • index (fun _ : S => X.V) φ x := by
  unfold index
  rw [Functor.map_comp]
  change (localizedSpaceFunctor.map (actionMap X S g) (localizedSpaceFunctor.map φ x)).1 =
    g • (localizedSpaceFunctor.map φ x).1
  generalize localizedSpaceFunctor.map φ x = y
  obtain ⟨s, y⟩ := y
  exact congrArg Sigma.fst (actionMap_apply X g s y)

end Copies

/-! ## Discrete `G`-sets -/

namespace DiscreteGSetConstructions

variable {G : Type z} [Group G] [TopologicalSpace G]

/-- The morphism of `P(G)` given by a `G`-map. -/
def homOfGMap {S T : DiscreteGSet G} (f : S.obj.V →[G] T.obj.V) : S ⟶ T :=
  ObjectProperty.homMk
    { hom := TypeCat.ofHom f
      comm := fun g => by
        ext x
        exact f.map_smul g x }

@[simp]
theorem homOfGMap_apply {S T : DiscreteGSet G} (f : S.obj.V →[G] T.obj.V) (s : S.obj.V) :
    (homOfGMap f).hom.hom s = f s := rfl

theorem hom_ext {S T : DiscreteGSet G} {f f' : S ⟶ T} (h : ∀ s, f.hom.hom s = f'.hom.hom s) :
    f = f' :=
  ObjectProperty.hom_ext _ (Action.hom_ext _ _ (by ext s; exact h s))

/-- The one-point discrete `G`-set. -/
def point : DiscreteGSet G :=
  DiscreteGSet.of G PUnit fun _ => by
    have h : (MulAction.stabilizer G PUnit.unit : Set G) = Set.univ :=
      Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
    rw [h]
    exact isOpen_univ

/-- The product of two discrete `G`-sets. -/
def prod (S T : DiscreteGSet G) : DiscreteGSet G :=
  DiscreteGSet.of G (S.obj.V × T.obj.V) fun p => by
    have h : (MulAction.stabilizer G p : Set G) =
        (MulAction.stabilizer G p.1 : Set G) ∩ MulAction.stabilizer G p.2 := by
      ext g
      simp [MulAction.mem_stabilizer_iff, Prod.ext_iff]
    rw [h]
    exact (S.property p.1).inter (T.property p.2)

/-- The sub-`G`-set where two morphisms of `P(G)` agree. -/
def eqLocus {S T : DiscreteGSet G} (f f' : S ⟶ T) : SubMulAction G S.obj.V where
  carrier := {s | f.hom.hom s = f'.hom.hom s}
  smul_mem' g s hs := by
    change Action.gMap f.hom (g • s) = Action.gMap f'.hom (g • s)
    rw [map_smul, map_smul]
    exact congrArg (g • ·) hs

/-- The equalizer of two morphisms of `P(G)`. -/
def equalizer {S T : DiscreteGSet G} (f f' : S ⟶ T) : DiscreteGSet G :=
  DiscreteGSet.of G (eqLocus f f') fun s => by
    have h : (MulAction.stabilizer G s : Set G) = MulAction.stabilizer G (s : S.obj.V) := by
      ext g
      simp [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    rw [h]
    exact S.property _

end DiscreteGSetConstructions

/-! ## Morphisms over `X` into the disjoint unions of copies -/

section CopiesOverHom

variable {G : Type z} [Group G] {X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G}

theorem copiesHom_ext {S : Type z} {U : LocalizedCategory.{u, max z v, max z v} (K := K)}
    {p : U ⟶ X.V} {φ ψ : U ⟶ (copies X S).pt} (hφ : φ ≫ projectionHom X S = p)
    (hψ : ψ ≫ projectionHom X S = p)
    (h : ∀ x, index (fun _ : S => X.V) φ x = index (fun _ : S => X.V) ψ x) : φ = ψ :=
  copiesOverHom_ext hφ hψ h

theorem exists_copiesHom (S : Type z) {U : LocalizedCategory.{u, max z v, max z v} (K := K)}
    (p : U ⟶ X.V) (c : localizedSpaceFunctor.obj U → S) (hc : IsLocallyConstant c) :
    ∃ φ : U ⟶ (copies X S).pt,
      φ ≫ projectionHom X S = p ∧ ∀ x, index (fun _ : S => X.V) φ x = c x :=
  exists_copiesOverHom p c hc

end CopiesOverHom

/-! ## Morphisms over a `G`-space `X` into the `G`-spaces `X_S` -/

section GSpace

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (hC : ContinuityStatement.{u, v, z}) {X : GSpace.{u, max z v, max z v} K G}

/-- The index map of a morphism over `X` into `X_S`. -/
def gIndex {Y : Over X} {S : DiscreteGSet G} (φ : Y ⟶ (gSpaceOverFunctor hC X).obj S) :
    localizedSpaceFunctor.obj Y.left.obj.V → S.obj.V :=
  index (fun _ : S.obj.V => X.obj.V) φ.left.hom.hom

theorem gHom_w {Y : Over X} {S : DiscreteGSet G} (φ : Y ⟶ (gSpaceOverFunctor hC X).obj S) :
    φ.left.hom.hom ≫ projectionHom X.obj S.obj.V = Y.hom.hom.hom :=
  congrArg (fun f => f.hom.hom) (Over.w φ)

theorem isLocallyConstant_gIndex {Y : Over X} {S : DiscreteGSet G}
    (φ : Y ⟶ (gSpaceOverFunctor hC X).obj S) : IsLocallyConstant (gIndex hC φ) :=
  isLocallyConstant_index _ _

theorem gIndex_comp_map {Y : Over X} {S T : DiscreteGSet G}
    (φ : Y ⟶ (gSpaceOverFunctor hC X).obj S) (f : S ⟶ T)
    (y : localizedSpaceFunctor.obj Y.left.obj.V) :
    gIndex hC (φ ≫ (gSpaceOverFunctor hC X).map f) y = f.hom.hom (gIndex hC φ y) :=
  index_comp_mapHom φ.left.hom.hom (Action.gMap f.hom) y

theorem gIndex_smul {Y : Over X} {S : DiscreteGSet G} (φ : Y ⟶ (gSpaceOverFunctor hC X).obj S)
    (g : G) (y : localizedSpaceFunctor.obj Y.left.obj.V) :
    gIndex hC φ (localizedSpaceFunctor.map (Y.left.obj.ρ g).asHom y) = g • gIndex hC φ y := by
  have e : ((Y.left.obj.ρ g).asHom ≫ φ.left.hom.hom : Y.left.obj.V ⟶ (copies X.obj S.obj.V).pt) =
      φ.left.hom.hom ≫ actionMap X.obj S.obj.V g :=
    φ.left.hom.comm g
  have h1 := index_comp _ (Y.left.obj.ρ g).asHom
    (φ.left.hom.hom : Y.left.obj.V ⟶ (copies X.obj S.obj.V).pt) y
  have h2 := index_comp_actionMap
    (φ.left.hom.hom : Y.left.obj.V ⟶ (copies X.obj S.obj.V).pt) g y
  rw [e] at h1
  exact h1.symm.trans h2

theorem gHom_ext {Y : Over X} {S : DiscreteGSet G} {φ ψ : Y ⟶ (gSpaceOverFunctor hC X).obj S}
    (h : ∀ y, gIndex hC φ y = gIndex hC ψ y) : φ = ψ :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Action.hom_ext _ _
    (copiesHom_ext (gHom_w hC φ) (gHom_w hC ψ) h)))

theorem exists_gHom (Y : Over X) (S : DiscreteGSet G)
    (c : localizedSpaceFunctor.obj Y.left.obj.V → S.obj.V) (hc : IsLocallyConstant c)
    (hcg : ∀ (g : G) y, c (localizedSpaceFunctor.map (Y.left.obj.ρ g).asHom y) = g • c y) :
    ∃ φ : Y ⟶ (gSpaceOverFunctor hC X).obj S, ∀ y, gIndex hC φ y = c y := by
  obtain ⟨m, hm, hmc⟩ := exists_copiesHom (X := X.obj) S.obj.V Y.hom.hom.hom c hc
  have hp : ∀ g : G, (Y.left.obj.ρ g).asHom ≫ Y.hom.hom.hom = Y.hom.hom.hom ≫ (X.obj.ρ g).asHom :=
    fun g => Y.hom.hom.comm g
  have comm : ∀ g : G, (Y.left.obj.ρ g).asHom ≫ m = m ≫ actionMap X.obj S.obj.V g := fun g =>
    copiesHom_ext (p := (Y.left.obj.ρ g).asHom ≫ Y.hom.hom.hom)
      (by rw [Category.assoc, hm])
      (by rw [Category.assoc, actionMap_projectionHom, ← Category.assoc, hm, hp])
      (fun y => by rw [index_comp, index_comp_actionMap, hmc, hmc, hcg])
  exact ⟨Over.homMk (ObjectProperty.homMk ⟨m, comm⟩)
    (ObjectProperty.hom_ext _ (Action.hom_ext _ _ hm)), hmc⟩

/-- The category of morphisms from an object `Y` of `G-𝒜n/X` to the objects `X_S` is
cofiltered. -/
theorem isCofiltered_structuredArrow (Y : Over X) :
    IsCofiltered (StructuredArrow Y (gSpaceOverFunctor hC X)) where
  nonempty := by
    obtain ⟨φ, -⟩ := exists_gHom hC Y DiscreteGSetConstructions.point
      (fun _ => PUnit.unit) (IsLocallyConstant.const _) (fun _ _ => rfl)
    exact ⟨StructuredArrow.mk φ⟩
  cone_objs A B := by
    obtain ⟨φ, hφ⟩ := exists_gHom hC Y (DiscreteGSetConstructions.prod A.right B.right)
      (fun y => (gIndex hC A.hom y, gIndex hC B.hom y))
      ((isLocallyConstant_gIndex hC A.hom).prodMk (isLocallyConstant_gIndex hC B.hom))
      (fun g y => by rw [gIndex_smul, gIndex_smul]; rfl)
    refine ⟨StructuredArrow.mk φ,
      StructuredArrow.homMk (DiscreteGSetConstructions.homOfGMap ⟨Prod.fst, fun _ _ => rfl⟩)
        (gHom_ext hC fun y => (gIndex_comp_map hC φ _ y).trans (congrArg Prod.fst (hφ y))),
      StructuredArrow.homMk (DiscreteGSetConstructions.homOfGMap ⟨Prod.snd, fun _ _ => rfl⟩)
        (gHom_ext hC fun y => (gIndex_comp_map hC φ _ y).trans (congrArg Prod.snd (hφ y))),
      trivial⟩
  cone_maps A B f f' := by
    have hA : ∀ y, gIndex hC A.hom y ∈ DiscreteGSetConstructions.eqLocus f.right f'.right :=
      fun y => by
        change f.right.hom.hom (gIndex hC A.hom y) = f'.right.hom.hom (gIndex hC A.hom y)
        rw [← gIndex_comp_map, ← gIndex_comp_map, StructuredArrow.w f, StructuredArrow.w f']
    obtain ⟨φ, hφ⟩ := exists_gHom hC Y
      (DiscreteGSetConstructions.equalizer f.right f'.right)
      (fun y => ⟨gIndex hC A.hom y, hA y⟩)
      (IsLocallyConstant.desc _ Subtype.val (isLocallyConstant_gIndex hC A.hom)
        Subtype.val_injective)
      (fun g y => Subtype.ext (gIndex_smul hC A.hom g y))
    let ι : DiscreteGSetConstructions.equalizer f.right f'.right ⟶ A.right :=
      DiscreteGSetConstructions.homOfGMap ⟨Subtype.val, fun _ _ => rfl⟩
    refine ⟨StructuredArrow.mk φ, StructuredArrow.homMk ι
      (gHom_ext hC fun y => (gIndex_comp_map hC φ ι y).trans (congrArg Subtype.val (hφ y))),
      ?_⟩
    apply StructuredArrow.hom_ext
    rw [StructuredArrow.comp_right, StructuredArrow.comp_right]
    exact DiscreteGSetConstructions.hom_ext fun s => s.2

theorem representablyFlat_gSpaceOverFunctor : RepresentablyFlat (gSpaceOverFunctor hC X) :=
  ⟨fun Y => isCofiltered_structuredArrow hC Y⟩

end GSpace

/-! ## Flatness and continuity of `γ` -/

/-- A functor whose composite with a fully faithful functor is representably flat is
representably flat. -/
theorem representablyFlat_of_comp_fullyFaithful {C D E : Type*} [Category C] [Category D]
    [Category E] (F : C ⥤ D) (i : D ⥤ E) [i.Full] [i.Faithful] [RepresentablyFlat (F ⋙ i)] :
    RepresentablyFlat F :=
  ⟨fun Y => IsCofiltered.of_equivalence (StructuredArrow.post Y F i).asEquivalence.symm⟩

section Site

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (hC : ContinuityStatement.{u, v, z}) {X : GSpace.{u, max z v, max z v} K G}
  (hD : SigmaDescStatement.{u, v, z})

theorem representablyFlat_quasiEtaleSiteFunctor :
    RepresentablyFlat (quasiEtaleSiteFunctor hC X hD) := by
  have : RepresentablyFlat
      (quasiEtaleSiteFunctor hC X hD ⋙ MorphismProperty.Over.forget _ ⊤ X) :=
    representablyFlat_gSpaceOverFunctor hC
  exact representablyFlat_of_comp_fullyFaithful _ (MorphismProperty.Over.forget _ ⊤ X)

theorem representablyFlat_etaleSiteFunctor : RepresentablyFlat (etaleSiteFunctor hC X hD) := by
  have : RepresentablyFlat
      (etaleSiteFunctor hC X hD ⋙ MorphismProperty.Over.forget _ ⊤ X) :=
    representablyFlat_gSpaceOverFunctor hC
  exact representablyFlat_of_comp_fullyFaithful _ (MorphismProperty.Over.forget _ ⊤ X)

/-- The point map of `X_T → X_S` for a morphism `f : T → S` of `P(G)` is `Sigma.map f id`. -/
theorem gSpaceFunctor_map_apply {S T : DiscreteGSet G} (f : T ⟶ S) (t : T.obj.V)
    (y : (presentationOf X.obj.V).presentation.space) :
    localizedSpaceFunctor.map ((gSpaceFunctor hC X).map f).hom.hom
        (⟨t, y⟩ : (_ : T.obj.V) × (presentationOf X.obj.V).presentation.space) =
      (⟨f.hom.hom t, y⟩ : (_ : S.obj.V) × (presentationOf X.obj.V).presentation.space) :=
  mapHom_apply X.obj (Action.gMap f.hom) t y

theorem isOpenMap_gSpaceFunctor_map {S T : DiscreteGSet G} (f : T ⟶ S) :
    IsOpenMap (localizedSpaceFunctor.map ((gSpaceFunctor hC X).map f).hom.hom) := by
  have e : (fun p : (_ : T.obj.V) × (presentationOf X.obj.V).presentation.space =>
      (localizedSpaceFunctor.map ((gSpaceFunctor hC X).map f).hom.hom p :
        (_ : S.obj.V) × (presentationOf X.obj.V).presentation.space)) =
      Sigma.map (β₁ := fun _ : T.obj.V => (presentationOf X.obj.V).presentation.space)
        (β₂ := fun _ : S.obj.V => (presentationOf X.obj.V).presentation.space) f.hom.hom
        fun _ => id :=
    funext fun ⟨t, y⟩ => gSpaceFunctor_map_apply hC f t y
  have h : IsOpenMap (Sigma.map (β₁ := fun _ : T.obj.V => (presentationOf X.obj.V).presentation.space)
      (β₂ := fun _ : S.obj.V => (presentationOf X.obj.V).presentation.space) f.hom.hom
      fun _ => id) :=
    isOpenMap_sigma_map.2 fun _ => IsOpenMap.id
  rw [← e] at h
  exact h

theorem image_mem_nhds_gSpaceFunctor_map {S T : DiscreteGSet G} (f : T ⟶ S) (t : T.obj.V)
    (y : (presentationOf X.obj.V).presentation.space)
    {W : Set (localizedSpaceFunctor.obj ((gSpaceFunctor hC X).obj T).obj.V)}
    (hW : W ∈ 𝓝 (⟨t, y⟩ : (_ : T.obj.V) × (presentationOf X.obj.V).presentation.space)) :
    localizedSpaceFunctor.map ((gSpaceFunctor hC X).map f).hom.hom '' W ∈
      𝓝 (⟨f.hom.hom t, y⟩ : (_ : S.obj.V) × (presentationOf X.obj.V).presentation.space) := by
  have h := (isOpenMap_gSpaceFunctor_map hC f).image_mem_nhds hW
  rwa [gSpaceFunctor_map_apply hC f t y] at h

theorem isContinuous_quasiEtaleSiteFunctor :
    (quasiEtaleSiteFunctor hC X hD).IsContinuous (DiscreteGSet.topology G)
      (equivariantQuasiEtaleTopology X) := by
  have := representablyFlat_quasiEtaleSiteFunctor hC (X := X) hD
  refine Langlands.CategoryTheory.isContinuous_toGrothendieck
    (P := DiscreteGSet.precoverage G) (Q := equivariantQuasiEtalePrecoverage X) ?_
  intro S R hR
  rw [mem_equivariantQuasiEtalePrecoverage_iff, mem_quasiEtalePrecoverage_iff]
  rintro ⟨s, y⟩
  obtain ⟨T, f, hf, t, rfl⟩ := DiscreteGSet.mem_precoverage_iff.1 hR s
  let V := (EquivariantQuasiEtaleSite.toQuasiEtaleSite X).obj ((quasiEtaleSiteFunctor hC X hD).obj T)
  let φ := (EquivariantQuasiEtaleSite.toQuasiEtaleSite X).map ((quasiEtaleSiteFunctor hC X hD).map f)
  obtain ⟨σ, hσ, hστ, -, hnhds⟩ :=
    (localizedObjectEquiv.symm V.left).presentation.atlas.isNet_chartFamily.1 ⟨t, y⟩
  refine ⟨(fun W => localizedSpaceFunctor.map φ.left '' W) '' σ, hσ.image _, ?_, ?_⟩
  · exact Filter.mem_of_superset (image_mem_nhds_gSpaceFunctor_map hC f t y hnhds)
      Set.image_sUnion.subset
  · rintro _ ⟨W, hW, rfl⟩
    obtain ⟨i, rfl⟩ := hστ hW
    exact ⟨V, φ, i, Presieve.map_map (Presieve.map_map hf), rfl⟩

theorem isContinuous_etaleSiteFunctor :
    (etaleSiteFunctor hC X hD).IsContinuous (DiscreteGSet.topology G)
      (equivariantEtaleTopology X) := by
  have := representablyFlat_etaleSiteFunctor hC (X := X) hD
  refine Langlands.CategoryTheory.isContinuous_toGrothendieck
    (P := DiscreteGSet.precoverage G) (Q := equivariantEtalePrecoverage X) ?_
  intro S R hR
  rw [mem_equivariantEtalePrecoverage_iff]
  rintro ⟨s, y⟩
  obtain ⟨T, f, hf, t, rfl⟩ := DiscreteGSet.mem_precoverage_iff.1 hR s
  exact ⟨(etaleSiteFunctor hC X hD).obj T, (etaleSiteFunctor hC X hD).map f,
    Presieve.map_map hf, ⟨t, y⟩, mapHom_apply X.obj (Action.gMap f.hom) t y⟩

end Site

/-- **Berkovich's functor `γ : Σ ↦ X_Σ(G)` is representably flat and continuous**, for the
quasi-étale and for the étale topology. -/
theorem morphismOfSitesStatement : MorphismOfSitesStatement.{u, v, z} := by
  intro K _ _ _ G _ _ _ hC hD X
  exact ⟨⟨representablyFlat_quasiEtaleSiteFunctor hC hD, isContinuous_quasiEtaleSiteFunctor hC hD⟩,
    ⟨representablyFlat_etaleSiteFunctor hC hD, isContinuous_etaleSiteFunctor hC hD⟩⟩

end Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace
