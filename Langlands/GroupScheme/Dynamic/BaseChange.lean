import Langlands.GroupScheme.Dynamic.Basic

/-! # Base change of cocharacters and of the dynamic test schemes

For a morphism of base schemes `b : S' ⟶ S`, a group scheme `G` over `S` and a cocharacter
`χ : 𝔾_{m,S} ⟶ G`, this module defines the base-changed cocharacter
`𝔾_{m,S'} ⟶ G_{S'}` and the comparisons of the test schemes `T' ×_{S'} 𝔾_{m,S'}` and
`T' ×_{S'} 𝔸¹_{S'}` with `T' ×_S 𝔾_{m,S}` and `T' ×_S 𝔸¹_S`, for every scheme `T'` over `S'`.
Along these comparisons, orbit maps, orbit extensions, values at zero and limits of the
base-changed cocharacter correspond to those of `χ`. Consequently `P_G(χ)`, `Z_G(χ)` and
`U_G(χ)` commute with base change.
-/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S)

namespace Dynamic

/-- For `f : T ⟶ S'`, `b : S' ⟶ S` and `x : X ⟶ S`, the canonical isomorphism
`T ×_{S'} (X ×_S S') ≅ T ×_S X`. -/
def pullbackPullbackSndIso {C : Type w} [Category.{v} C] [HasPullbacks C] {T S' S X : C}
    (f : T ⟶ S') (b : S' ⟶ S) (x : X ⟶ S) :
    pullback f (pullback.snd x b) ≅ pullback (f ≫ b) x where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _) (by
    rw [pullback.condition_assoc, Category.assoc, pullback.condition])
  inv := pullback.lift (pullback.fst _ _)
    (pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ f) (by
      rw [Category.assoc, ← pullback.condition]))
    (pullback.lift_snd _ _ _).symm
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst]
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd]
      · simp only [Category.assoc, Category.id_comp, pullback.lift_snd, pullback.lift_fst_assoc]
        exact pullback.condition
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst]
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc]

@[reassoc (attr := simp)]
theorem pullbackPullbackSndIso_hom_fst {C : Type w} [Category.{v} C] [HasPullbacks C]
    {T S' S X : C} (f : T ⟶ S') (b : S' ⟶ S) (x : X ⟶ S) :
    (pullbackPullbackSndIso f b x).hom ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackPullbackSndIso_hom_snd {C : Type w} [Category.{v} C] [HasPullbacks C]
    {T S' S X : C} (f : T ⟶ S') (b : S' ⟶ S) (x : X ⟶ S) :
    (pullbackPullbackSndIso f b x).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ :=
  pullback.lift_snd _ _ _

/-- The projection-formula isomorphism `T' ×_{S'} (S' ×_S X) ≅ T' ×_S X` of schemes over `S`,
for a scheme `T'` over `S'` and a scheme `X` over `S`. -/
def mapTensorPullbackIso (T' : Over S') (X : Over S) :
    (Over.map b).obj (T' ⊗ (Over.pullback b).obj X) ≅ (Over.map b).obj T' ⊗ X :=
  Over.isoMk (pullbackPullbackSndIso T'.hom b X.hom) (by
    change (pullbackPullbackSndIso T'.hom b X.hom).hom ≫ pullback.fst _ _ ≫ T'.hom ≫ b =
      pullback.fst _ _ ≫ T'.hom ≫ b
    rw [pullbackPullbackSndIso_hom_fst_assoc])

@[reassoc (attr := simp)]
theorem mapTensorPullbackIso_hom_fst (T' : Over S') (X : Over S) :
    (mapTensorPullbackIso b T' X).hom ≫ fst _ X = (Over.map b).map (fst T' _) := by
  apply Over.OverMorphism.ext
  simp [mapTensorPullbackIso]

theorem mapTensorPullbackIso_hom_snd_left (T' : Over S') (X : Over S) :
    ((mapTensorPullbackIso b T' X).hom ≫ snd _ X).left =
      (snd T' ((Over.pullback b).obj X)).left ≫ pullback.fst X.hom b := by
  simp [mapTensorPullbackIso]

/-- For `X'` over `S'` identified with the base change of `X`, the comparison
`T' ×_{S'} X' ≅ T' ×_S X` of schemes over `S`. -/
def mapTensorIso (T' : Over S') {X' : Over S'} {X : Over S}
    (i : X' ≅ (Over.pullback b).obj X) :
    (Over.map b).obj (T' ⊗ X') ≅ (Over.map b).obj T' ⊗ X :=
  (Over.map b).mapIso (whiskerLeftIso T' i) ≪≫ mapTensorPullbackIso b T' X

@[reassoc (attr := simp)]
theorem mapTensorIso_hom_fst (T' : Over S') {X' : Over S'} {X : Over S}
    (i : X' ≅ (Over.pullback b).obj X) :
    (mapTensorIso b T' i).hom ≫ fst _ X = (Over.map b).map (fst T' X') := by
  simp only [mapTensorIso, Iso.trans_hom, Functor.mapIso_hom, whiskerLeftIso_hom, Category.assoc,
    mapTensorPullbackIso_hom_fst, ← Functor.map_comp, whiskerLeft_fst]

theorem mapTensorIso_hom_snd_left (T' : Over S') {X' : Over S'} {X : Over S}
    (i : X' ≅ (Over.pullback b).obj X) :
    ((mapTensorIso b T' i).hom ≫ snd _ X).left =
      (snd T' X').left ≫ i.hom.left ≫ pullback.fst X.hom b := by
  rw [mapTensorIso, Iso.trans_hom, Category.assoc, Over.comp_left,
    mapTensorPullbackIso_hom_snd_left, Functor.mapIso_hom, Over.map_map_left,
    whiskerLeftIso_hom, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left,
    Category.assoc]

end Dynamic

namespace AffineLine

/-- The affine line over `S'` is the base change of the affine line over `S`. -/
def baseChangeIso : scheme S' ≅ (Over.pullback b).obj (scheme S) :=
  Over.isoMk (AffineSpace.isPullback_map (n := PUnit.{u + 1}) b).isoPullback (by simp [scheme])

/-- The comparison with the base change preserves the coordinate function. -/
theorem baseChangeIso_appTop_coord :
    ((baseChangeIso b).hom.left ≫ pullback.fst (scheme S).hom b).appTop (coord S) = coord S' := by
  have h : (baseChangeIso b).hom.left ≫ pullback.fst (scheme S).hom b =
      AffineSpace.map PUnit.{u + 1} b :=
    (AffineSpace.isPullback_map (n := PUnit.{u + 1}) b).isoPullback_hom_fst
  exact (congrArg (fun f => f.appTop (coord S)) h).trans (AffineSpace.map_appTop_coord b _)

/-- The comparison `T' ×_{S'} 𝔸¹_{S'} ≅ T' ×_S 𝔸¹_S` of schemes over `S`. -/
def mapTensorIso (T' : Over S') :
    (Over.map b).obj (T' ⊗ scheme S') ≅ (Over.map b).obj T' ⊗ scheme S :=
  Dynamic.mapTensorIso b T' (baseChangeIso b)

/-- The comparison preserves the coordinate function of the affine line. -/
theorem homEquiv_mapTensorIso_hom_snd (T' : Over S') :
    homEquiv _ ((mapTensorIso b T').hom ≫ snd _ (scheme S)) =
      homEquiv (T' ⊗ scheme S') (snd T' (scheme S')) := by
  rw [homEquiv_apply, homEquiv_apply, mapTensorIso, Dynamic.mapTensorIso_hom_snd_left,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, baseChangeIso_appTop_coord]

end AffineLine

namespace Gm

/-- `𝔾_{m,S'}` is the base change of `𝔾_{m,S}`, as schemes over `S'`. -/
def overBaseChangeIso : (Gm S').X ≅ (Over.pullback b).obj (Gm S).X :=
  (Grp.forget _).mapIso (baseChangeIso b).symm

/-- The comparison `T' ×_{S'} 𝔾_{m,S'} ≅ T' ×_S 𝔾_{m,S}` of schemes over `S`. -/
def mapTensorIso (T' : Over S') :
    (Over.map b).obj (T' ⊗ (Gm S').X) ≅ (Over.map b).obj T' ⊗ (Gm S).X :=
  Dynamic.mapTensorIso b T' (overBaseChangeIso b)

/-- The second projection of the comparison corresponds to the unit coordinate under the
pullback point equivalence. -/
theorem mapTensorIso_hom_snd (T' : Over S') :
    (mapTensorIso b T').hom ≫ snd _ (Gm S).X =
      baseChangePointsEquiv b (Gm S).toGrp _
        (snd T' (Gm S').X ≫ (baseChangeIso b).inv.hom.hom) := by
  apply Over.OverMorphism.ext
  rw [mapTensorIso, Dynamic.mapTensorIso_hom_snd_left, baseChangePointsEquiv_left, Over.comp_left]
  rfl

/-- The comparison preserves the unit coordinate. -/
theorem pointsEquiv_mapTensorIso_hom_snd (T' : Over S') :
    pointsEquiv S _ ((mapTensorIso b T').hom ≫ snd _ (Gm S).X) =
      pointsEquiv S' (T' ⊗ (Gm S').X) (snd T' (Gm S').X) := by
  rw [mapTensorIso_hom_snd, ← baseChangeUnitsEquiv_apply, baseChangeUnitsEquiv_baseChangeIso_inv]

end Gm

namespace Dynamic

/-- The comparisons of `T' ×_{S'} 𝔾_{m,S'}` and `T' ×_{S'} 𝔸¹_{S'}` are compatible with the
inclusions of `𝔾_m` in `𝔸¹`. -/
@[reassoc]
theorem mapTensorIso_unitInclusion (T' : Over S') :
    (Over.map b).map (T' ◁ AffineLine.unitInclusion S') ≫ (AffineLine.mapTensorIso b T').hom =
      (Gm.mapTensorIso b T').hom ≫ (Over.map b).obj T' ◁ AffineLine.unitInclusion S := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, AffineLine.mapTensorIso, mapTensorIso_hom_fst,
      whiskerLeft_fst, Gm.mapTensorIso, mapTensorIso_hom_fst, ← Functor.map_comp, whiskerLeft_fst]
  · apply AffineLine.hom_ext
    simp only [Category.assoc, whiskerLeft_snd]
    conv_rhs => rw [← Category.assoc, AffineLine.homEquiv_comp_unitInclusion,
      Gm.pointsEquiv_mapTensorIso_hom_snd]
    rw [AffineLine.homEquiv_comp, AffineLine.homEquiv_mapTensorIso_hom_snd, Over.map_map_left,
      ← AffineLine.homEquiv_comp, whiskerLeft_snd, AffineLine.homEquiv_comp_unitInclusion]

/-- The comparison of `T' ×_{S'} 𝔸¹_{S'}` with `T' ×_S 𝔸¹_S` is compatible with the zero
sections. -/
@[reassoc]
theorem mapTensorIso_zeroSection (T' : Over S') :
    (Over.map b).map (lift (𝟙 T') (toUnit T' ≫ AffineLine.zeroSection S')) ≫
        (AffineLine.mapTensorIso b T').hom =
      lift (𝟙 _) (toUnit _ ≫ AffineLine.zeroSection S) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, AffineLine.mapTensorIso, mapTensorIso_hom_fst, ← Functor.map_comp,
      lift_fst, lift_fst, (Over.map b).map_id]
  · apply AffineLine.hom_ext
    rw [lift_snd, AffineLine.homEquiv_comp_zeroSection, Category.assoc, AffineLine.homEquiv_comp,
      AffineLine.homEquiv_mapTensorIso_hom_snd, Over.map_map_left, ← AffineLine.homEquiv_comp,
      lift_snd, AffineLine.homEquiv_comp_zeroSection]

variable {G : GroupScheme S}

/-- The base change `𝔾_{m,S'} ≅ (𝔾_{m,S})_{S'} ⟶ G_{S'}` of a cocharacter `χ` of `G`. -/
def baseChangeCocharacter (χ : (Gm S).toGrp ⟶ G) :
    (Gm S').toGrp ⟶ (GroupScheme.baseChange b).obj G :=
  (Gm.baseChangeIso b).inv ≫ (GroupScheme.baseChange b).map χ

/-- On points, the base-changed cocharacter is `χ` on the same unit. -/
theorem baseChangePointsEquiv_baseChangeCocharacter (χ : (Gm S).toGrp ⟶ G) (T' : Over S')
    (t : T' ⟶ (Gm S').X) :
    baseChangePointsEquiv b G T' (t ≫ (baseChangeCocharacter b χ).hom.hom) =
      baseChangePointsEquiv b (Gm S).toGrp T' (t ≫ (Gm.baseChangeIso b).inv.hom.hom) ≫
        χ.hom.hom := by
  rw [← baseChangePointsEquiv_comp]
  rfl

/-- The orbit map of the base-changed cocharacter corresponds to the orbit map of `χ`, along
the comparison of `T' ×_{S'} 𝔾_{m,S'}` with `T' ×_S 𝔾_{m,S}`. -/
theorem baseChangePointsEquiv_orbit (χ : (Gm S).toGrp ⟶ G) {T' : Over S'}
    (x : T' ⟶ ((GroupScheme.baseChange b).obj G).X) :
    baseChangePointsEquiv b G _ (orbit (baseChangeCocharacter b χ) x) =
      (Gm.mapTensorIso b T').hom ≫ orbit χ (baseChangePointsEquiv b G T' x) := by
  have hχ : baseChangePointsEquiv b G _ (snd T' (Gm S').X ≫
      (baseChangeCocharacter b χ).hom.hom) =
        (Gm.mapTensorIso b T').hom ≫ snd _ (Gm S).X ≫ χ.hom.hom := by
    rw [baseChangePointsEquiv_baseChangeCocharacter, ← Gm.mapTensorIso_hom_snd, Category.assoc]
  have hx : baseChangePointsEquiv b G _ (fst T' (Gm S').X ≫ x) =
      (Gm.mapTensorIso b T').hom ≫ fst _ (Gm S).X ≫ baseChangePointsEquiv b G T' x := by
    rw [baseChangePointsEquiv_naturality, Gm.mapTensorIso, ← mapTensorIso_hom_fst_assoc]
  simp only [orbit, map_mul, map_inv, hχ, hx, MonObj.comp_mul, GrpObj.comp_inv]

/-- A morphism `T' ×_{S'} 𝔸¹_{S'} ⟶ G_{S'}` extends the orbit map of the base-changed
cocharacter exactly when the corresponding morphism `T' ×_S 𝔸¹_S ⟶ G` extends the orbit map
of `χ`. -/
theorem isOrbitExtension_baseChange_iff (χ : (Gm S).toGrp ⟶ G) {T' : Over S'}
    (x : T' ⟶ ((GroupScheme.baseChange b).obj G).X)
    (e : T' ⊗ AffineLine.scheme S' ⟶ ((GroupScheme.baseChange b).obj G).X) :
    IsOrbitExtension (baseChangeCocharacter b χ) x e ↔
      IsOrbitExtension χ (baseChangePointsEquiv b G T' x)
        ((AffineLine.mapTensorIso b T').inv ≫ baseChangePointsEquiv b G _ e) := by
  have hι : (Over.map b).map (T' ◁ AffineLine.unitInclusion S') =
      (Gm.mapTensorIso b T').hom ≫ (Over.map b).obj T' ◁ AffineLine.unitInclusion S ≫
        (AffineLine.mapTensorIso b T').inv := by
    rw [← mapTensorIso_unitInclusion_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [IsOrbitExtension, IsOrbitExtension, ← (baseChangePointsEquiv b G _).injective.eq_iff,
    baseChangePointsEquiv_naturality, baseChangePointsEquiv_orbit, hι, Category.assoc,
    Category.assoc, cancel_epi]

/-- Evaluation at zero commutes with the comparison of `T' ×_{S'} 𝔸¹_{S'}` and
`T' ×_S 𝔸¹_S`. -/
theorem baseChangePointsEquiv_evalZero {T' : Over S'}
    (e : T' ⊗ AffineLine.scheme S' ⟶ ((GroupScheme.baseChange b).obj G).X) :
    baseChangePointsEquiv b G T' (evalZero e) =
      evalZero ((AffineLine.mapTensorIso b T').inv ≫ baseChangePointsEquiv b G _ e) := by
  rw [evalZero, evalZero, baseChangePointsEquiv_naturality, ← mapTensorIso_zeroSection,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- A point of `G_{S'}` has limit `l` under the base-changed cocharacter exactly when the
corresponding point of `G` has the corresponding limit under `χ`. -/
theorem hasLimit_baseChange_iff (χ : (Gm S).toGrp ⟶ G) {T' : Over S'}
    (x l : T' ⟶ ((GroupScheme.baseChange b).obj G).X) :
    HasLimit (baseChangeCocharacter b χ) x l ↔
      HasLimit χ (baseChangePointsEquiv b G T' x) (baseChangePointsEquiv b G T' l) := by
  constructor
  · rintro ⟨e, he, he0⟩
    exact ⟨_, (isOrbitExtension_baseChange_iff b χ x e).mp he,
      by rw [← baseChangePointsEquiv_evalZero, he0]⟩
  · rintro ⟨e, he, he0⟩
    refine ⟨(baseChangePointsEquiv b G _).symm ((AffineLine.mapTensorIso b T').hom ≫ e),
      (isOrbitExtension_baseChange_iff b χ x _).mpr ?_, ?_⟩
    · rwa [MulEquiv.apply_symm_apply, Iso.inv_hom_id_assoc]
    · apply (baseChangePointsEquiv b G T').injective
      rwa [baseChangePointsEquiv_evalZero, MulEquiv.apply_symm_apply, Iso.inv_hom_id_assoc]

/-- The dynamic parabolic subgroup functor commutes with base change. -/
theorem parabolic_baseChange (χ : (Gm S).toGrp ⟶ G) :
    parabolic (baseChangeCocharacter b χ) = (parabolic χ).baseChange b := by
  ext T' x
  rw [SubgroupFunctor.mem_baseChange, mem_parabolic, mem_parabolic]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨_, (isOrbitExtension_baseChange_iff b χ x e).mp he⟩
  · rintro ⟨e, he⟩
    refine ⟨(baseChangePointsEquiv b G _).symm ((AffineLine.mapTensorIso b T').hom ≫ e),
      (isOrbitExtension_baseChange_iff b χ x _).mpr ?_⟩
    rwa [MulEquiv.apply_symm_apply, Iso.inv_hom_id_assoc]

/-- The centralizer subgroup functor of a cocharacter commutes with base change. -/
theorem centralizer_baseChange (χ : (Gm S).toGrp ⟶ G) :
    centralizer (baseChangeCocharacter b χ) = (centralizer χ).baseChange b := by
  ext T' x
  rw [SubgroupFunctor.mem_baseChange, mem_centralizer, mem_centralizer,
    ← (baseChangePointsEquiv b G _).injective.eq_iff, baseChangePointsEquiv_orbit,
    baseChangePointsEquiv_naturality, Gm.mapTensorIso, ← mapTensorIso_hom_fst_assoc,
    cancel_epi]

/-- The dynamic unipotent subgroup functor commutes with base change. -/
theorem unipotent_baseChange (χ : (Gm S).toGrp ⟶ G) :
    unipotent (baseChangeCocharacter b χ) = (unipotent χ).baseChange b := by
  ext T' x
  rw [SubgroupFunctor.mem_baseChange, mem_unipotent, mem_unipotent, hasLimit_baseChange_iff,
    map_one]

end Dynamic

end Langlands.GroupScheme
