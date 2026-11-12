import Langlands.GroupScheme.AffineWeilCounit
import Langlands.GroupScheme.Dynamic.Representability

/-! # Dynamic subgroups of actual affine Weil restrictions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

variable (A) in
/-- An extension-base affine-line test regarded as a ground-base affine-line test. -/
def lineSplit (Z : Over (Spec (CommRingCat.of B))) :
    groundTest A B (Z ⊗ AffineLine.scheme (Spec (CommRingCat.of B))) ⟶
      groundTest A B Z ⊗ AffineLine.scheme (Spec (CommRingCat.of A)) :=
  lift (groundMap A B (fst Z _)) (lineRestrict (snd Z _))

variable (A) in
/-- An extension-base multiplicative test regarded as a ground-base multiplicative test. -/
def gmSplit (Z : Over (Spec (CommRingCat.of B))) :
    groundTest A B (Z ⊗ (Gm (Spec (CommRingCat.of B))).X) ⟶
      groundTest A B Z ⊗ (Gm (Spec (CommRingCat.of A))).X :=
  lift (groundMap A B (fst Z _)) (gmRestrict (snd Z _))

/-- Splitting the affine line is compatible with the inclusion of the multiplicative group. -/
theorem groundMap_whiskerLeft_lineSplit (Z : Over (Spec (CommRingCat.of B))) :
    groundMap A B (Z ◁ AffineLine.unitInclusion _) ≫ lineSplit A Z =
      gmSplit A Z ≫ groundTest A B Z ◁ AffineLine.unitInclusion _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, lineSplit, gmSplit, lift_fst, whiskerLeft_fst, lift_fst,
      groundMap, groundMap, ← Functor.map_comp, whiskerLeft_fst]
  · rw [Category.assoc, Category.assoc, lineSplit, gmSplit, lift_snd, whiskerLeft_snd,
      lift_snd_assoc, ← lineRestrict_naturality, whiskerLeft_snd, lineRestrict_unitInclusion]

/-- Splitting the affine line is compatible with the zero sections. -/
theorem groundMap_lift_zeroSection_lineSplit (Z : Over (Spec (CommRingCat.of B))) :
    groundMap A B (lift (𝟙 Z) (toUnit Z ≫ AffineLine.zeroSection _)) ≫ lineSplit A Z =
      lift (𝟙 _) (toUnit _ ≫ AffineLine.zeroSection _) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lineSplit, lift_fst, lift_fst, groundMap, groundMap,
      ← Functor.map_comp, lift_fst, CategoryTheory.Functor.map_id]
  · rw [Category.assoc, lineSplit, lift_snd, lift_snd, ← lineRestrict_naturality, lift_snd,
      lineRestrict_zeroSection]

variable [Module.Finite A B] [Module.Projective A B]
  {G : GroupScheme (Spec (CommRingCat.of B))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

variable (A) in
/-- The original curve attached by the counit to a restricted affine-line curve. -/
def counitExtension {Z : Over (Spec (CommRingCat.of B))}
    (e : groundTest A B Z ⊗ AffineLine.scheme (Spec (CommRingCat.of A)) ⟶
      (groupScheme A B G).X) :
    Z ⊗ AffineLine.scheme (Spec (CommRingCat.of B)) ⟶ G.X :=
  counit A B _ ≫ testPointsEquiv A B G _ (lineSplit A Z ≫ e)

/-- The counit carries the restricted orbit map to the original orbit map. -/
theorem counit_testPointsEquiv_gmSplit_orbit
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G) {Z : Over (Spec (CommRingCat.of B))}
    (g : groundTest A B Z ⟶ (groupScheme A B G).X) :
    counit A B _ ≫ testPointsEquiv A B G _ (gmSplit A Z ≫ Dynamic.orbit (cocharacter A B χ) g) =
      Dynamic.orbit χ (counit A B Z ≫ testPointsEquiv A B G _ g) := by
  simp only [Dynamic.orbit, MonObj.comp_mul, GrpObj.comp_inv, map_mul, map_inv]
  rw [gmSplit, lift_snd_assoc, lift_fst_assoc, testPointsEquiv_cocharacter,
    testPointsEquiv_naturality, ← Category.assoc, counit_scalarGmPoints, ← Category.assoc,
    counit_naturality, Category.assoc]

/-- The counit curve of a restricted orbit extension is an original orbit extension. -/
theorem isOrbitExtension_counitExtension
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G) {Z : Over (Spec (CommRingCat.of B))}
    {g : groundTest A B Z ⟶ (groupScheme A B G).X}
    {e : groundTest A B Z ⊗ AffineLine.scheme (Spec (CommRingCat.of A)) ⟶
      (groupScheme A B G).X}
    (he : Dynamic.IsOrbitExtension (cocharacter A B χ) g e) :
    Dynamic.IsOrbitExtension χ (counit A B Z ≫ testPointsEquiv A B G _ g)
      (counitExtension A e) := by
  rw [Dynamic.IsOrbitExtension, counitExtension, ← Category.assoc, ← counit_naturality,
    Category.assoc, ← testPointsEquiv_naturality, ← Category.assoc,
    groundMap_whiskerLeft_lineSplit, Category.assoc, he]
  exact counit_testPointsEquiv_gmSplit_orbit χ g

/-- The zero value of the counit curve is the counit of the restricted zero value. -/
theorem evalZero_counitExtension {Z : Over (Spec (CommRingCat.of B))}
    (e : groundTest A B Z ⊗ AffineLine.scheme (Spec (CommRingCat.of A)) ⟶
      (groupScheme A B G).X) :
    Dynamic.evalZero (counitExtension A e) =
      counit A B Z ≫ testPointsEquiv A B G _ (Dynamic.evalZero e) := by
  rw [Dynamic.evalZero, counitExtension, ← Category.assoc, ← counit_naturality,
    Category.assoc, ← testPointsEquiv_naturality, ← Category.assoc,
    groundMap_lift_zeroSection_lineSplit]
  rfl

section Standard

variable (C : CommAlgCat.{u} (CommRingCat.of A))

/-- On a standard test, the counit after the restricted unit recovers every point. -/
theorem counit_testPointsEquiv_unit (x : standardTest A C ⟶ (groupScheme A B G).X) :
    counit A B _ ≫ testPointsEquiv A B G _ (testUnit A B C ≫ x) =
      testPointsEquiv A B G _ x := by
  rw [testPointsEquiv_naturality, ← Category.assoc, counit_tensorTestMap_testUnit,
    Category.id_comp]

/-- A restricted orbit extension on a standard test yields an original orbit extension. -/
theorem exists_isOrbitExtension_testPointsEquiv
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {g : standardTest A C ⟶ (groupScheme A B G).X}
    {e : standardTest A C ⊗ AffineLine.scheme (Spec (CommRingCat.of A)) ⟶
      (groupScheme A B G).X}
    (he : Dynamic.IsOrbitExtension (cocharacter A B χ) g e) :
    Dynamic.IsOrbitExtension χ (testPointsEquiv A B G _ g)
      (counitExtension A (testUnit A B C ▷ _ ≫ e)) := by
  have h := isOrbitExtension_counitExtension χ (he.whiskerRight _ (testUnit A B C))
  rwa [counit_testPointsEquiv_unit] at h

/-- Restricted limits on a standard test are original limits on its tensor test. -/
theorem hasLimit_testPointsEquiv_of_standard
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {g l : standardTest A C ⟶ (groupScheme A B G).X}
    (h : Dynamic.HasLimit (cocharacter A B χ) g l) :
    Dynamic.HasLimit χ (testPointsEquiv A B G _ g) (testPointsEquiv A B G _ l) := by
  obtain ⟨e, he, he0⟩ := h
  refine ⟨_, exists_isOrbitExtension_testPointsEquiv C χ he, ?_⟩
  rw [evalZero_counitExtension, Dynamic.evalZero_whiskerRight, he0,
    counit_testPointsEquiv_unit]

/-- Restricted dynamic-parabolic points on a standard test are original ones. -/
theorem testPointsEquiv_mem_parabolic_of_standard
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {g : standardTest A C ⟶ (groupScheme A B G).X}
    (hg : g ∈ (Dynamic.parabolic (cocharacter A B χ)).carrier _) :
    testPointsEquiv A B G _ g ∈ (Dynamic.parabolic χ).carrier (tensorTest A B _) := by
  obtain ⟨e, he⟩ := hg
  exact ⟨_, exists_isOrbitExtension_testPointsEquiv C χ he⟩

/-- Restricted identity-limit points on a standard test are original ones. -/
theorem testPointsEquiv_mem_unipotent_of_standard
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {g : standardTest A C ⟶ (groupScheme A B G).X}
    (hg : g ∈ (Dynamic.unipotent (cocharacter A B χ)).carrier _) :
    testPointsEquiv A B G _ g ∈ (Dynamic.unipotent χ).carrier (tensorTest A B _) := by
  have h := hasLimit_testPointsEquiv_of_standard C χ hg
  rwa [map_one] at h

end Standard

section Map

variable {P : GroupScheme (Spec (CommRingCat.of B))} [IsAffine P.X.left]
  [LocallyOfFiniteType P.X.hom]

variable (A) in
/-- Point comparison turns the restricted homomorphism into the original one. -/
theorem testPointsEquiv_comp_map (f : P ⟶ G) {T : Over (Spec (CommRingCat.of A))}
    (x : T ⟶ (groupScheme A B P).X) :
    testPointsEquiv A B G T (x ≫ (map A B f).hom.hom) =
      testPointsEquiv A B P T x ≫ f.hom.hom :=
  Corepresented.groupSchemeMap_points (corepresentableBy A B P) (corepresentableBy A B G)
    (pointTransformation A B f) x

/-- Restriction of a monomorphic homomorphism is monomorphic. -/
instance mono_map (f : P ⟶ G) [Mono f.hom.hom] : Mono (map A B f).hom.hom :=
  ⟨fun a b h => (testPointsEquiv A B P _).injective (by
    rw [← cancel_mono f.hom.hom, ← testPointsEquiv_comp_map, ← testPointsEquiv_comp_map, h])⟩

/-- The range of a restricted homomorphism is a restricted subgroup functor, provided the
latter is represented by a homomorphism whose universal point descends. -/
theorem range_map_eq {F : SubgroupFunctor G} {F' : SubgroupFunctor (groupScheme A B G)}
    (f : P ⟶ G) (hf : SubgroupFunctor.range f = F)
    (hle : ∀ (T : Over (Spec (CommRingCat.of A))) (x : T ⟶ (groupScheme A B G).X),
      testPointsEquiv A B G T x ∈ F.carrier (tensorTest A B T) → x ∈ F'.carrier T)
    {Q : GroupScheme (Spec (CommRingCat.of A))} (q : Q ⟶ groupScheme A B G)
    (hq : SubgroupFunctor.range q = F')
    (hQ : testPointsEquiv A B G Q.X q.hom.hom ∈ F.carrier (tensorTest A B Q.X)) :
    SubgroupFunctor.range (map A B f) = F' := by
  subst hf hq
  apply SubgroupFunctor.ext
  intro T
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    apply hle
    rw [testPointsEquiv_comp_map]
    exact SubgroupFunctor.mem_range.2 ⟨_, rfl⟩
  · intro x hx
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.1 hQ
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    refine SubgroupFunctor.mem_range.2 ⟨y ≫ (testPointsEquiv A B P Q.X).symm w, ?_⟩
    rw [Category.assoc]
    congr 1
    apply (testPointsEquiv A B G _).injective
    rw [testPointsEquiv_comp_map, MulEquiv.apply_symm_apply]
    exact hw

/-- Restriction carries a dynamic parabolic subgroup to the transferred one. -/
theorem range_map_eq_parabolic (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G) (f : P ⟶ G)
    (hf : SubgroupFunctor.range f = Dynamic.parabolic χ) :
    SubgroupFunctor.range (map A B f) = Dynamic.parabolic (cocharacter A B χ) :=
  range_map_eq f hf (fun _ x hx => mem_dynamicParabolic_of_testPointsEquiv A B χ x hx)
    (Corepresented.parabolicHom (cocharacter A B χ))
    (Corepresented.isRepresentedBy_parabolicHom _).2
    (testPointsEquiv_mem_parabolic_of_standard _ χ (by
      rw [← (Corepresented.isRepresentedBy_parabolicHom (cocharacter A B χ)).2]
      exact SubgroupFunctor.mem_range.2 ⟨𝟙 _, Category.id_comp _⟩))

/-- Restriction carries a dynamic unipotent subgroup to the transferred one. -/
theorem range_map_eq_unipotent (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G) (f : P ⟶ G)
    (hf : SubgroupFunctor.range f = Dynamic.unipotent χ) :
    SubgroupFunctor.range (map A B f) = Dynamic.unipotent (cocharacter A B χ) :=
  range_map_eq f hf (fun _ x hx => mem_dynamicUnipotent_of_testPointsEquiv A B χ x hx)
    (Corepresented.unipotentHom (cocharacter A B χ))
    (Corepresented.isRepresentedBy_unipotentHom _).2
    (testPointsEquiv_mem_unipotent_of_standard _ χ (by
      rw [← (Corepresented.isRepresentedBy_unipotentHom (cocharacter A B χ)).2]
      exact SubgroupFunctor.mem_range.2 ⟨𝟙 _, Category.id_comp _⟩))

/-- Restriction of a representing homomorphism represents the transferred parabolic. -/
theorem isRepresentedBy_map_parabolic (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {f : P ⟶ G} (hf : (Dynamic.parabolic χ).IsRepresentedBy f) :
    (Dynamic.parabolic (cocharacter A B χ)).IsRepresentedBy (map A B f) :=
  haveI := hf.1
  ⟨inferInstance, range_map_eq_parabolic χ f hf.2⟩

/-- Restriction of a representing homomorphism represents the transferred unipotent. -/
theorem isRepresentedBy_map_unipotent (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {f : P ⟶ G} (hf : (Dynamic.unipotent χ).IsRepresentedBy f) :
    (Dynamic.unipotent (cocharacter A B χ)).IsRepresentedBy (map A B f) :=
  haveI := hf.1
  ⟨inferInstance, range_map_eq_unipotent χ f hf.2⟩

end Map

section Descent

variable (A) in
/-- The original points attached to a ground-base cocharacter of the restricted group. -/
def descendPoints (ν : (Gm (Spec (CommRingCat.of A))).toGrp ⟶ groupScheme A B G)
    (Z : Over (Spec (CommRingCat.of B))) :
    (Z ⟶ (Gm (Spec (CommRingCat.of B))).X) →* (Z ⟶ G.X) where
  toFun y := counit A B Z ≫ testPointsEquiv A B G _ (gmRestrict y ≫ ν.hom.hom)
  map_one' := by
    rw [gmRestrict_one, MonObj.one_comp, map_one, MonObj.comp_one]
  map_mul' y y' := by
    rw [gmRestrict_mul, MonObj.mul_comp, map_mul, MonObj.comp_mul]

theorem descendPoints_naturality
    (ν : (Gm (Spec (CommRingCat.of A))).toGrp ⟶ groupScheme A B G)
    {Z Z' : Over (Spec (CommRingCat.of B))} (a : Z' ⟶ Z)
    (y : Z ⟶ (Gm (Spec (CommRingCat.of B))).X) :
    descendPoints A ν Z' (a ≫ y) = a ≫ descendPoints A ν Z y := by
  change counit A B Z' ≫ testPointsEquiv A B G _ (gmRestrict (a ≫ y) ≫ ν.hom.hom) =
    a ≫ counit A B Z ≫ testPointsEquiv A B G _ (gmRestrict y ≫ ν.hom.hom)
  rw [gmRestrict_naturality, Category.assoc, testPointsEquiv_naturality, ← Category.assoc,
    counit_naturality, Category.assoc]

variable (A) in
/-- The extension-base cocharacter corresponding to a ground-base cocharacter of the
restricted group. -/
def descendCocharacter (ν : (Gm (Spec (CommRingCat.of A))).toGrp ⟶ groupScheme A B G) :
    (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G :=
  homOfPoints (descendPoints A ν) (descendPoints_naturality ν)

/-- Every ground-base cocharacter of the restricted group is a transferred cocharacter. -/
theorem cocharacter_descendCocharacter
    (ν : (Gm (Spec (CommRingCat.of A))).toGrp ⟶ groupScheme A B G) :
    cocharacter A B (descendCocharacter A ν) = ν := by
  have key : ∀ (C : CommAlgCat.{u} (CommRingCat.of A))
      (x : standardTest A C ⟶ (Gm (Spec (CommRingCat.of A))).X),
      x ≫ (cocharacter A B (descendCocharacter A ν)).hom.hom = x ≫ ν.hom.hom := by
    intro C x
    apply (testPointsEquiv A B G _).injective
    rw [testPointsEquiv_cocharacter, descendCocharacter, comp_homOfPoints]
    change counit A B _ ≫
      testPointsEquiv A B G _ (gmRestrict (scalarGmPoints A B _ x) ≫ ν.hom.hom) = _
    rw [gmRestrict_scalarGmPoints, Category.assoc, counit_testPointsEquiv_unit]
  apply hom_ext_points
  intro T x
  rw [← affinization_gmAffine x, Category.assoc, Category.assoc,
    key ((algΓ (CommRingCat.of A)).obj T).unop (gmAffine x)]

end Descent

end Langlands.GroupScheme.AffineWeil
