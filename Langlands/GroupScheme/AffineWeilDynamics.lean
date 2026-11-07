import Langlands.GroupScheme.AffineWeilRestrictionMaps
import Langlands.GroupScheme.Dynamic.Basic

/-! # Cocharacters and identity limits under actual affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The actual algebra of relative global sections of a ground-base test scheme. -/
abbrev sectionAlgebra (T : Over (Spec (CommRingCat.of A))) :
    CommAlgCat.{u} (CommRingCat.of A) :=
  ((algΓ (CommRingCat.of A)).obj T).unop

/-- Tensor extension of the actual relative global sections. -/
abbrev tensorAlgebra (T : Over (Spec (CommRingCat.of A))) :
    CommAlgCat.{u} (CommRingCat.of B) :=
  (tensorFunctor A B).obj (sectionAlgebra A T)

/-- The actual affine extension-base test supplied by the restricted point functor. -/
abbrev tensorTest (T : Over (Spec (CommRingCat.of A))) :
    Over (Spec (CommRingCat.of B)) :=
  (algSpec (CommRingCat.of B)).obj (op (tensorAlgebra A B T))

/-- Change of relative test scheme on the actual tensor spectra. -/
def tensorTestMap {T T' : Over (Spec (CommRingCat.of A))} (a : T' ⟶ T) :
    tensorTest A B T' ⟶ tensorTest A B T :=
  (algSpec (CommRingCat.of B)).map
    ((tensorFunctor A B).map ((algΓ (CommRingCat.of A)).map a).unop).op

/-- Tensor-spectrum change of test preserves identities. -/
@[simp] theorem tensorTestMap_id (T : Over (Spec (CommRingCat.of A))) :
    tensorTestMap A B (𝟙 T) = 𝟙 (tensorTest A B T) := by
  unfold tensorTestMap
  rw [(algΓ (CommRingCat.of A)).map_id, unop_id, (tensorFunctor A B).map_id,
    op_id, (algSpec (CommRingCat.of B)).map_id]

/-- Tensor-spectrum change of test preserves composition. -/
@[simp] theorem tensorTestMap_comp {T T' T'' : Over (Spec (CommRingCat.of A))}
    (a : T'' ⟶ T') (b : T' ⟶ T) :
    tensorTestMap A B (a ≫ b) = tensorTestMap A B a ≫ tensorTestMap A B b := by
  simp only [tensorTestMap, Functor.map_comp, unop_comp, op_comp]

/-- A ground-base function enters tensor coefficients through the right factor. -/
def includeSection (T : Over (Spec (CommRingCat.of A))) :
    Γ(T.left, ⊤) →+* Γ((tensorTest A B T).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (tensorAlgebra A B T))).inv.hom.comp
    (Algebra.TensorProduct.includeRight :
      sectionAlgebra A T →ₐ[A] B ⊗[A] sectionAlgebra A T).toRingHom

/-- Spectrum pullback preserves the right-factor scalar inclusion. -/
theorem includeSection_naturality {T T' : Over (Spec (CommRingCat.of A))}
    (a : T' ⟶ T) (r : Γ(T.left, ⊤)) :
    (tensorTestMap A B a).left.appTop (includeSection A B T r) =
      includeSection A B T' (a.left.appTop r) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of (tensorAlgebra A B T))).inv ≫
    (Spec.map (CommRingCat.ofHom
      (((tensorFunctor A B).map ((algΓ (CommRingCat.of A)).map a).unop).hom.toRingHom))).appTop)
      (Algebra.TensorProduct.includeRight r) = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Scalar multiplicative points on the actual tensor test. -/
def scalarGmPoints (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ (Gm (Spec (CommRingCat.of A))).X) →*
      (tensorTest A B T ⟶ (Gm (Spec (CommRingCat.of B))).X) :=
  (Gm.pointsEquiv (Spec (CommRingCat.of B)) (tensorTest A B T)).symm.toMonoidHom.comp
    ((Units.map (includeSection A B T).toMonoidHom).comp
      (Gm.pointsEquiv (Spec (CommRingCat.of A)) T).toMonoidHom)

/-- Scalar multiplicative points commute with every test-scheme pullback. -/
theorem scalarGmPoints_naturality {T T' : Over (Spec (CommRingCat.of A))}
    (a : T' ⟶ T) (x : T ⟶ (Gm (Spec (CommRingCat.of A))).X) :
    scalarGmPoints A B T' (a ≫ x) =
      tensorTestMap A B a ≫ scalarGmPoints A B T x := by
  apply (Gm.pointsEquiv (Spec (CommRingCat.of B)) (tensorTest A B T')).injective
  simp only [scalarGmPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, Gm.pointsEquiv_naturality]
  apply Units.ext
  exact (includeSection_naturality A B a _).symm

/-- A scalar affine-line point on the actual tensor test. -/
def scalarLinePoint {T : Over (Spec (CommRingCat.of A))}
    (x : T ⟶ AffineLine.scheme (Spec (CommRingCat.of A))) :
    tensorTest A B T ⟶ AffineLine.scheme (Spec (CommRingCat.of B)) :=
  (AffineLine.homEquiv (tensorTest A B T)).symm
    (includeSection A B T (AffineLine.homEquiv T x))

/-- Scalar affine-line points commute with every test-scheme pullback. -/
theorem scalarLinePoint_naturality {T T' : Over (Spec (CommRingCat.of A))}
    (a : T' ⟶ T) (x : T ⟶ AffineLine.scheme (Spec (CommRingCat.of A))) :
    scalarLinePoint A B (a ≫ x) =
      tensorTestMap A B a ≫ scalarLinePoint A B x := by
  apply AffineLine.hom_ext
  simp only [scalarLinePoint, Equiv.apply_symm_apply, AffineLine.homEquiv_comp]
  exact (includeSection_naturality A B a _).symm

/-- Forgetting the unit commutes with the actual scalar point maps. -/
theorem scalarLinePoint_unitInclusion {T : Over (Spec (CommRingCat.of A))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of A))).X) :
    scalarLinePoint A B (x ≫ AffineLine.unitInclusion _) =
      scalarGmPoints A B T x ≫ AffineLine.unitInclusion _ := by
  apply AffineLine.hom_ext
  simp only [scalarLinePoint, Equiv.apply_symm_apply,
    AffineLine.homEquiv_comp_unitInclusion, scalarGmPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rfl

/-- A zero scalar point remains zero on the actual tensor test. -/
theorem scalarLinePoint_zeroSection {T : Over (Spec (CommRingCat.of A))}
    (x : T ⟶ 𝟙_ (Over (Spec (CommRingCat.of A)))) :
    scalarLinePoint A B (x ≫ AffineLine.zeroSection _) =
      toUnit (tensorTest A B T) ≫ AffineLine.zeroSection _ := by
  apply AffineLine.hom_ext
  simp only [scalarLinePoint, Equiv.apply_symm_apply,
    AffineLine.homEquiv_comp_zeroSection, map_zero]

/-- Compare multiplicative orbit tests by tensor extension and scalar inclusion. -/
def gmComparison (T : Over (Spec (CommRingCat.of A))) :
    tensorTest A B (T ⊗ (Gm (Spec (CommRingCat.of A))).X) ⟶
      tensorTest A B T ⊗ (Gm (Spec (CommRingCat.of B))).X :=
  lift (tensorTestMap A B (fst T (Gm (Spec (CommRingCat.of A))).X))
    (scalarGmPoints A B _ (snd T (Gm (Spec (CommRingCat.of A))).X))

/-- Compare affine-line orbit tests by tensor extension and scalar inclusion. -/
def lineComparison (T : Over (Spec (CommRingCat.of A))) :
    tensorTest A B (T ⊗ AffineLine.scheme (Spec (CommRingCat.of A))) ⟶
      tensorTest A B T ⊗ AffineLine.scheme (Spec (CommRingCat.of B)) :=
  lift (tensorTestMap A B (fst T (AffineLine.scheme (Spec (CommRingCat.of A)))))
    (scalarLinePoint A B (snd T (AffineLine.scheme (Spec (CommRingCat.of A)))))

/-- The orbit-test comparisons preserve the inclusion of multiplicative parameters. -/
theorem lineComparison_unitInclusion (T : Over (Spec (CommRingCat.of A))) :
    tensorTestMap A B (T ◁ AffineLine.unitInclusion _) ≫ lineComparison A B T =
      gmComparison A B T ≫ tensorTest A B T ◁ AffineLine.unitInclusion _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [lineComparison, gmComparison, Category.assoc, lift_fst,
      whiskerLeft_fst, ← tensorTestMap_comp]
  · simp only [lineComparison, gmComparison, Category.assoc, lift_snd,
      whiskerLeft_snd, ← scalarLinePoint_naturality]
    rw [scalarLinePoint_unitInclusion, ← Category.assoc, lift_snd]

/-- The affine-line comparison preserves the zero section of each test. -/
theorem lineComparison_zeroSection (T : Over (Spec (CommRingCat.of A))) :
    tensorTestMap A B (lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection _)) ≫
        lineComparison A B T =
      lift (𝟙 (tensorTest A B T))
        (toUnit (tensorTest A B T) ≫ AffineLine.zeroSection _) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [lineComparison, Category.assoc, lift_fst, ← tensorTestMap_comp,
      tensorTestMap_id]
  · simp only [lineComparison, Category.assoc, lift_snd, ← scalarLinePoint_naturality]
    exact scalarLinePoint_zeroSection A B _

variable [Module.Finite A B] [Module.Projective A B]
  (G : GroupScheme (Spec (CommRingCat.of B)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Actual restricted points on any test are original points on its tensor spectrum. -/
abbrev testPointsEquiv (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ (groupScheme A B G).X) ≃* (tensorTest A B T ⟶ G.X) :=
  Corepresented.pointsEquiv (pointFunctor A B G) (corepresentableBy A B G) T

/-- The actual tensor-spectrum point comparison respects all test pullbacks. -/
theorem testPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of A))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme A B G).X) :
    testPointsEquiv A B G T' (a ≫ x) =
      tensorTestMap A B a ≫ testPointsEquiv A B G T x :=
  Corepresented.pointsEquiv_naturality
    (pointFunctor A B G) (corepresentableBy A B G) a x

variable {G}

/-- The point homomorphisms of the transferred ground-base cocharacter. -/
def cocharacterPoints (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ (Gm (Spec (CommRingCat.of A))).X) →*
      (T ⟶ (groupScheme A B G).X) :=
  (testPointsEquiv A B G T).symm.toMonoidHom.comp
    ((((pointsMap χ).app (op (tensorTest A B T))).hom).comp (scalarGmPoints A B T))

/-- Point comparison evaluates the transferred point map on the original scalar unit. -/
theorem testPointsEquiv_cocharacterPoints
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {T : Over (Spec (CommRingCat.of A))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of A))).X) :
    testPointsEquiv A B G T (cocharacterPoints A B χ T x) =
      scalarGmPoints A B T x ≫ χ.hom.hom := by
  exact (testPointsEquiv A B G T).apply_symm_apply _

/-- Transferred cocharacter points are natural in every actual relative test. -/
theorem cocharacterPoints_naturality
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {T T' : Over (Spec (CommRingCat.of A))} (a : T' ⟶ T)
    (x : T ⟶ (Gm (Spec (CommRingCat.of A))).X) :
    cocharacterPoints A B χ T' (a ≫ x) = a ≫ cocharacterPoints A B χ T x := by
  apply (testPointsEquiv A B G T').injective
  rw [testPointsEquiv_naturality, testPointsEquiv_cocharacterPoints,
    testPointsEquiv_cocharacterPoints]
  rw [scalarGmPoints_naturality, Category.assoc]

/-- The actual ground-base cocharacter induced by an extension-base cocharacter. -/
def cocharacter (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G) :
    (Gm (Spec (CommRingCat.of A))).toGrp ⟶ groupScheme A B G :=
  homOfPoints (cocharacterPoints A B χ) (cocharacterPoints_naturality A B χ)

/-- The transferred cocharacter retains its original value on the included scalar unit. -/
theorem testPointsEquiv_cocharacter
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {T : Over (Spec (CommRingCat.of A))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of A))).X) :
    testPointsEquiv A B G T (x ≫ (cocharacter A B χ).hom.hom) =
      scalarGmPoints A B T x ≫ χ.hom.hom := by
  rw [cocharacter, comp_homOfPoints]
  exact (testPointsEquiv A B G T).apply_symm_apply _

/-- The actual orbit of a restricted point is the pullback of its original orbit. -/
theorem testPointsEquiv_orbit
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {T : Over (Spec (CommRingCat.of A))} (g : T ⟶ (groupScheme A B G).X) :
    testPointsEquiv A B G _ (Dynamic.orbit (cocharacter A B χ) g) =
      gmComparison A B T ≫ Dynamic.orbit χ (testPointsEquiv A B G T g) := by
  rw [Dynamic.orbit, map_mul, map_mul, map_inv, testPointsEquiv_cocharacter,
    testPointsEquiv_naturality]
  simp only [Dynamic.orbit, MonObj.comp_mul, GrpObj.comp_inv,
    gmComparison, ← Category.assoc, lift_fst, lift_snd]

/-- Pull an original affine-line curve back to the actual restricted group. -/
def transferExtension {T : Over (Spec (CommRingCat.of A))}
    (e : tensorTest A B T ⊗ AffineLine.scheme (Spec (CommRingCat.of B)) ⟶ G.X) :
    T ⊗ AffineLine.scheme (Spec (CommRingCat.of A)) ⟶ (groupScheme A B G).X :=
  (testPointsEquiv A B G _).symm (lineComparison A B T ≫ e)

/-- Point comparison retains the original pulled-back curve. -/
theorem testPointsEquiv_transferExtension {T : Over (Spec (CommRingCat.of A))}
    (e : tensorTest A B T ⊗ AffineLine.scheme (Spec (CommRingCat.of B)) ⟶ G.X) :
    testPointsEquiv A B G _ (transferExtension A B e) = lineComparison A B T ≫ e :=
  (testPointsEquiv A B G _).apply_symm_apply _

/-- Transferring a curve preserves the orbit-extension equation on every test scheme. -/
theorem transferExtension_isOrbitExtension
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {T : Over (Spec (CommRingCat.of A))} (g : T ⟶ (groupScheme A B G).X)
    {e : tensorTest A B T ⊗ AffineLine.scheme (Spec (CommRingCat.of B)) ⟶ G.X}
    (he : Dynamic.IsOrbitExtension χ (testPointsEquiv A B G T g) e) :
    Dynamic.IsOrbitExtension (cocharacter A B χ) g (transferExtension A B e) := by
  apply (testPointsEquiv A B G _).injective
  rw [testPointsEquiv_naturality, testPointsEquiv_transferExtension,
    testPointsEquiv_orbit, ← Category.assoc, lineComparison_unitInclusion,
    Category.assoc, he]

/-- Evaluation at zero of the transferred curve retains the original zero value. -/
theorem testPointsEquiv_evalZero_transferExtension
    {T : Over (Spec (CommRingCat.of A))}
    (e : tensorTest A B T ⊗ AffineLine.scheme (Spec (CommRingCat.of B)) ⟶ G.X) :
    testPointsEquiv A B G T (Dynamic.evalZero (transferExtension A B e)) =
      Dynamic.evalZero e := by
  rw [Dynamic.evalZero, testPointsEquiv_naturality,
    testPointsEquiv_transferExtension, ← Category.assoc, lineComparison_zeroSection]
  rfl

/-- A limit of the original tensor-spectrum point is also a limit of the restricted point. -/
theorem hasLimit_of_testPointsEquiv
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {T : Over (Spec (CommRingCat.of A))} (g l : T ⟶ (groupScheme A B G).X)
    (h : Dynamic.HasLimit χ (testPointsEquiv A B G T g) (testPointsEquiv A B G T l)) :
    Dynamic.HasLimit (cocharacter A B χ) g l := by
  obtain ⟨e, he, he0⟩ := h
  refine ⟨transferExtension A B e, transferExtension_isOrbitExtension A B χ g he, ?_⟩
  apply (testPointsEquiv A B G T).injective
  rw [testPointsEquiv_evalZero_transferExtension, he0]

/-- Original identity-limit membership transfers to the actual restricted point. -/
theorem mem_dynamicUnipotent_of_testPointsEquiv
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {T : Over (Spec (CommRingCat.of A))} (g : T ⟶ (groupScheme A B G).X)
    (hg : testPointsEquiv A B G T g ∈ (Dynamic.unipotent χ).carrier (tensorTest A B T)) :
    g ∈ (Dynamic.unipotent (cocharacter A B χ)).carrier T := by
  change Dynamic.HasLimit χ (testPointsEquiv A B G T g) 1 at hg
  apply hasLimit_of_testPointsEquiv A B χ g 1
  simpa only [map_one] using hg

/-- Original orbit-extension membership transfers to the actual restricted point. -/
theorem mem_dynamicParabolic_of_testPointsEquiv
    (χ : (Gm (Spec (CommRingCat.of B))).toGrp ⟶ G)
    {T : Over (Spec (CommRingCat.of A))} (g : T ⟶ (groupScheme A B G).X)
    (hg : testPointsEquiv A B G T g ∈ (Dynamic.parabolic χ).carrier (tensorTest A B T)) :
    g ∈ (Dynamic.parabolic (cocharacter A B χ)).carrier T := by
  obtain ⟨e, he⟩ := hg
  exact ⟨transferExtension A B e, transferExtension_isOrbitExtension A B χ g he⟩

end Langlands.GroupScheme.AffineWeil
