import Langlands.GroupScheme.AffineWeilDynamics
import Langlands.GroupScheme.AffineWeilTorusAdjunction
import Langlands.AlgebraicGeometry.PolynomialSpecPoints

/-! # The counit of actual affine Weil restriction on test schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

section Affinization

variable {R : CommRingCat.{u}}

/-- Maps into a relative spectrum are determined by pullback of global functions. -/
theorem algSpec_hom_ext {T : Over (Spec R)} {C : CommAlgCat.{u} R}
    {x y : T ⟶ (algSpec R).obj (op C)}
    (h : ∀ c : C, x.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c) =
      y.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c)) : x = y := by
  apply ((algΓAlgSpecAdjunction R).homEquiv T (op C)).symm.injective
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro c
  rw [Langlands.AlgebraicGeometry.PolynomialSpecPoints.adjunction_homEquiv_symm_apply,
    Langlands.AlgebraicGeometry.PolynomialSpecPoints.adjunction_homEquiv_symm_apply]
  exact h c

/-- The canonical map from a relative test scheme to the spectrum of its global sections. -/
def affinization (T : Over (Spec R)) :
    T ⟶ (algSpec R).obj ((algΓ R).obj T) :=
  (algΓAlgSpecAdjunction R).unit.app T

/-- Global functions of a test scheme as spectrum coordinates on its affinization. -/
def affinizationCoord (T : Over (Spec R)) :
    Γ(T.left, ⊤) →+* Γ(((algSpec R).obj ((algΓ R).obj T)).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ((algΓ R).obj T).unop)).inv.hom

/-- The affinization map pulls the spectrum coordinates back to the original functions. -/
theorem affinization_appTop (T : Over (Spec R)) (s : Γ(T.left, ⊤)) :
    (affinization T).left.appTop (affinizationCoord T s) = s := by
  have h : ((algΓAlgSpecAdjunction R).homEquiv T ((algΓ R).obj T)).symm (affinization T) =
      𝟙 _ := by
    rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  have h2 := congrArg (fun φ => φ.unop.hom s) h
  exact (Langlands.AlgebraicGeometry.PolynomialSpecPoints.adjunction_homEquiv_symm_apply
    T _ (affinization T) s).symm.trans h2

/-- A multiplicative point on the spectrum of the global sections of a test scheme. -/
def gmAffine {T : Over (Spec R)} (x : T ⟶ (Gm (Spec R)).X) :
    (algSpec R).obj ((algΓ R).obj T) ⟶ (Gm (Spec R)).X :=
  (Gm.pointsEquiv _ _).symm
    (Units.map (affinizationCoord T).toMonoidHom (Gm.pointsEquiv _ T x))

/-- Every multiplicative point factors through the affinization of its test scheme. -/
theorem affinization_gmAffine {T : Over (Spec R)} (x : T ⟶ (Gm (Spec R)).X) :
    affinization T ≫ gmAffine x = x := by
  apply (Gm.pointsEquiv _ T).injective
  rw [Gm.pointsEquiv_naturality, gmAffine, MulEquiv.apply_symm_apply]
  apply Units.ext
  exact affinization_appTop T _

/-- The structure map of a relative spectrum is its algebra map on spectrum coordinates. -/
theorem algebraMap_algSpec (D : CommAlgCat.{u} R) (r : R) :
    algebraMap R ((algΓ R).obj ((algSpec R).obj (op D))).unop r =
      (Scheme.ΓSpecIso (CommRingCat.of D)).inv (algebraMap R D r) := by
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R D))).appTop) r = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

end Affinization

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The structure morphism `Spec B → Spec A`. -/
abbrev baseMap : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- An extension-base test scheme regarded over the ground base. -/
abbrev groundTest (Z : Over (Spec (CommRingCat.of B))) : Over (Spec (CommRingCat.of A)) :=
  (Over.map (baseMap A B)).obj Z

/-- An extension-base map of test schemes regarded over the ground base. -/
abbrev groundMap {Z Z' : Over (Spec (CommRingCat.of B))} (a : Z' ⟶ Z) :
    groundTest A B Z' ⟶ groundTest A B Z :=
  (Over.map (baseMap A B)).map a

/-- The ground-base structure of an extension-base test factors through the extension. -/
theorem algebraMap_groundTest (Z : Over (Spec (CommRingCat.of B))) (a : A) :
    algebraMap A (sectionAlgebra A (groundTest A B Z)) a =
      algebraMap B (sectionAlgebra B Z) (algebraMap A B a) := by
  change ((Scheme.ΓSpecIso _).inv ≫ (Z.hom ≫ baseMap A B).appTop) a =
    ((Scheme.ΓSpecIso _).inv ≫ Z.hom.appTop) (algebraMap A B a)
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

variable {B} in
/-- Ground-base relative sections of an extension-base test are its extension-base
relative sections with restricted scalars. -/
def sectionRestrict (Z : Over (Spec (CommRingCat.of B))) :
    sectionAlgebra A (groundTest A B Z) ⟶ (restrictScalars A B).obj (sectionAlgebra B Z) :=
  ConcreteCategory.ofHom (C := CommAlgCat (CommRingCat.of A))
    (show sectionAlgebra A (groundTest A B Z) →ₐ[CommRingCat.of A]
        (restrictScalars A B).obj (sectionAlgebra B Z) from
      { toRingHom := RingHom.id _
        commutes' := algebraMap_groundTest A B Z })

/-- The multiplication `B ⊗[A] Γ(Z) → Γ(Z)` of an extension-base test scheme. -/
def counitAlgebraMap (Z : Over (Spec (CommRingCat.of B))) :
    tensorAlgebra A B (groundTest A B Z) ⟶ sectionAlgebra B Z :=
  (tensorFunctor A B).map (sectionRestrict A Z) ≫ multiplication A (sectionAlgebra B Z)

theorem counitAlgebraMap_tmul (Z : Over (Spec (CommRingCat.of B))) (b : B)
    (s : sectionAlgebra A (groundTest A B Z)) :
    (counitAlgebraMap A B Z).hom (b ⊗ₜ[A] s) =
      algebraMap B (sectionAlgebra B Z) b * (sectionRestrict A Z).hom s :=
  multiplication_tensorMap_tmul A (sectionRestrict A Z) b s

/-- The counit `Z → Spec (B ⊗[A] Γ(Z))` of Weil restriction on an extension-base test. -/
def counit (Z : Over (Spec (CommRingCat.of B))) : Z ⟶ tensorTest A B (groundTest A B Z) :=
  (algΓAlgSpecAdjunction (CommRingCat.of B)).homEquiv _ _ (counitAlgebraMap A B Z).op

/-- The counit pulls back spectrum coordinates by the multiplication map. -/
theorem counit_appTop (Z : Over (Spec (CommRingCat.of B)))
    (c : tensorAlgebra A B (groundTest A B Z)) :
    (counit A B Z).left.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (tensorAlgebra A B (groundTest A B Z)))).inv c) =
        (counitAlgebraMap A B Z).hom c := by
  rw [← Langlands.AlgebraicGeometry.PolynomialSpecPoints.adjunction_homEquiv_symm_apply,
    counit, Equiv.symm_apply_apply]
  rfl

/-- The counit pulls each included ground function back to itself. -/
theorem counit_appTop_includeSection (Z : Over (Spec (CommRingCat.of B)))
    (r : Γ(Z.left, ⊤)) :
    (counit A B Z).left.appTop (includeSection A B (groundTest A B Z) r) = r := by
  refine (counit_appTop A B Z (Algebra.TensorProduct.includeRight r)).trans ?_
  refine (counitAlgebraMap_tmul A B Z 1 r).trans ?_
  rw [map_one, one_mul]
  rfl

/-- The multiplication maps are natural in the extension-base test scheme. -/
theorem counitAlgebraMap_naturality {Z Z' : Over (Spec (CommRingCat.of B))} (a : Z' ⟶ Z) :
    (tensorFunctor A B).map ((algΓ (CommRingCat.of A)).map (groundMap A B a)).unop ≫
        counitAlgebraMap A B Z' =
      counitAlgebraMap A B Z ≫ ((algΓ (CommRingCat.of B)).map a).unop := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp only [CommAlgCat.hom_comp, AlgHom.coe_comp, Function.comp_apply]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul b s =>
    change (counitAlgebraMap A B Z').hom
        (b ⊗ₜ[A] ((algΓ (CommRingCat.of A)).map (groundMap A B a)).unop.hom s) =
      ((algΓ (CommRingCat.of B)).map a).unop.hom ((counitAlgebraMap A B Z).hom (b ⊗ₜ[A] s))
    rw [counitAlgebraMap_tmul, counitAlgebraMap_tmul, map_mul, AlgHom.commutes]
    rfl

/-- The counit is natural in the extension-base test scheme. -/
theorem counit_naturality {Z Z' : Over (Spec (CommRingCat.of B))} (a : Z' ⟶ Z) :
    counit A B Z' ≫ tensorTestMap A B (groundMap A B a) = a ≫ counit A B Z := by
  rw [counit, counit, tensorTestMap, ← Adjunction.homEquiv_naturality_right,
    ← Adjunction.homEquiv_naturality_left]
  congr 1
  apply Quiver.Hom.unop_inj
  exact counitAlgebraMap_naturality A B a

section Unit

variable (C : CommAlgCat.{u} (CommRingCat.of A))

/-- The standard affine ground-base test scheme `Spec C`. -/
abbrev standardTest : Over (Spec (CommRingCat.of A)) :=
  (algSpec (CommRingCat.of A)).obj (op C)

/-- The coordinate map `C → B ⊗[A] Γ(Spec C)` of the unit on a standard test. -/
def testUnitAlgebraMap :
    C ⟶ sectionAlgebra A (groundTest A B (tensorTest A B (standardTest A C))) :=
  ConcreteCategory.ofHom (C := CommAlgCat (CommRingCat.of A))
    (show C →ₐ[CommRingCat.of A]
        sectionAlgebra A (groundTest A B (tensorTest A B (standardTest A C))) from
      { toRingHom := (includeSection A B (standardTest A C)).comp
          (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
        commutes' := fun a => by
          refine (congrArg (includeSection A B (standardTest A C))
            (algebraMap_algSpec C a).symm).trans ?_
          refine Eq.trans ?_
            (algebraMap_groundTest A B (tensorTest A B (standardTest A C)) a).symm
          refine Eq.trans ?_ (algebraMap_algSpec (tensorAlgebra A B (standardTest A C))
            (algebraMap A B a)).symm
          change (Scheme.ΓSpecIso (CommRingCat.of (tensorAlgebra A B (standardTest A C)))).inv
              (1 ⊗ₜ[A] algebraMap A (sectionAlgebra A (standardTest A C)) a) =
            (Scheme.ΓSpecIso (CommRingCat.of (tensorAlgebra A B (standardTest A C)))).inv
              (algebraMap A B a ⊗ₜ[A] 1)
          rw [← Algebra.TensorProduct.algebraMap_apply',
            Algebra.TensorProduct.algebraMap_apply] })

/-- The unit `Spec (B ⊗[A] Γ(Spec C)) → Spec C` of Weil restriction on a standard test. -/
def testUnit : groundTest A B (tensorTest A B (standardTest A C)) ⟶ standardTest A C :=
  (algΓAlgSpecAdjunction (CommRingCat.of A)).homEquiv _ _ (testUnitAlgebraMap A B C).op

/-- The unit pulls each function back to its right-factor inclusion. -/
theorem testUnit_appTop (s : Γ((standardTest A C).left, ⊤)) :
    (testUnit A B C).left.appTop s = includeSection A B (standardTest A C) s := by
  obtain ⟨c, rfl⟩ : ∃ c : C, (Scheme.ΓSpecIso (CommRingCat.of C)).inv c = s :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of C)).hom s, Iso.hom_inv_id_apply _ _⟩
  rw [← Langlands.AlgebraicGeometry.PolynomialSpecPoints.adjunction_homEquiv_symm_apply,
    testUnit, Equiv.symm_apply_apply]
  rfl

/-- The counit followed by the restricted unit is the identity of the tensor test. -/
theorem counit_tensorTestMap_testUnit :
    counit A B (tensorTest A B (standardTest A C)) ≫ tensorTestMap A B (testUnit A B C) = 𝟙 _ := by
  rw [counit, tensorTestMap, ← Adjunction.homEquiv_naturality_right,
    ← Equiv.eq_symm_apply]
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro c
  rw [Langlands.AlgebraicGeometry.PolynomialSpecPoints.adjunction_homEquiv_symm_apply]
  change (counitAlgebraMap A B _).hom (((tensorFunctor A B).map
    ((algΓ (CommRingCat.of A)).map (testUnit A B C)).unop).hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (tensorAlgebra A B (standardTest A C)))).inv c
  induction c using TensorProduct.inductionOn with
  | add x y hx hy =>
    erw [map_add, map_add, map_add, hx, hy]
    rfl
  | tmul b s =>
    change (counitAlgebraMap A B _).hom
      (b ⊗ₜ[A] ((algΓ (CommRingCat.of A)).map (testUnit A B C)).unop.hom s) = _
    erw [counitAlgebraMap_tmul, algebraMap_algSpec]
    change (Scheme.ΓSpecIso (CommRingCat.of (tensorAlgebra A B (standardTest A C)))).inv
        (b ⊗ₜ[A] 1) * (show Γ(Spec (CommRingCat.of (tensorAlgebra A B (standardTest A C))), ⊤)
          from (testUnit A B C).left.appTop s) = _
    erw [testUnit_appTop]
    change (Scheme.ΓSpecIso (CommRingCat.of (tensorAlgebra A B (standardTest A C)))).inv
        (b ⊗ₜ[A] 1) *
      (Scheme.ΓSpecIso (CommRingCat.of (tensorAlgebra A B (standardTest A C)))).inv
        (1 ⊗ₜ[A] s) = _
    have h : (b ⊗ₜ[A] (1 : sectionAlgebra A (standardTest A C))) * (1 ⊗ₜ[A] s) =
        b ⊗ₜ[A] s := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact (map_mul (Scheme.ΓSpecIso
      (CommRingCat.of (tensorAlgebra A B (standardTest A C)))).inv.hom _ _).symm.trans
        (congrArg _ h)

end Unit

variable {A B}

/-- An extension-base affine-line point regarded over the ground base. -/
def lineRestrict {Z : Over (Spec (CommRingCat.of B))}
    (y : Z ⟶ AffineLine.scheme (Spec (CommRingCat.of B))) :
    groundTest A B Z ⟶ AffineLine.scheme (Spec (CommRingCat.of A)) :=
  (AffineLine.homEquiv (groundTest A B Z)).symm (AffineLine.homEquiv Z y)

theorem homEquiv_lineRestrict {Z : Over (Spec (CommRingCat.of B))}
    (y : Z ⟶ AffineLine.scheme (Spec (CommRingCat.of B))) :
    AffineLine.homEquiv (groundTest A B Z) (lineRestrict (A := A) y) =
      AffineLine.homEquiv Z y :=
  Equiv.apply_symm_apply _ _

theorem lineRestrict_naturality {Z Z' : Over (Spec (CommRingCat.of B))} (a : Z' ⟶ Z)
    (y : Z ⟶ AffineLine.scheme (Spec (CommRingCat.of B))) :
    lineRestrict (A := A) (a ≫ y) = groundMap A B a ≫ lineRestrict y := by
  apply AffineLine.hom_ext
  rw [AffineLine.homEquiv_comp, homEquiv_lineRestrict, homEquiv_lineRestrict,
    AffineLine.homEquiv_comp]
  rfl

theorem lineRestrict_zeroSection {Z : Over (Spec (CommRingCat.of B))}
    (x : Z ⟶ 𝟙_ (Over (Spec (CommRingCat.of B)))) :
    lineRestrict (A := A) (x ≫ AffineLine.zeroSection _) =
      toUnit (groundTest A B Z) ≫ AffineLine.zeroSection _ := by
  apply AffineLine.hom_ext
  rw [homEquiv_lineRestrict, AffineLine.homEquiv_comp_zeroSection,
    AffineLine.homEquiv_comp_zeroSection]

/-- An extension-base multiplicative point regarded over the ground base. -/
def gmRestrict {Z : Over (Spec (CommRingCat.of B))}
    (y : Z ⟶ (Gm (Spec (CommRingCat.of B))).X) :
    groundTest A B Z ⟶ (Gm (Spec (CommRingCat.of A))).X :=
  (Gm.pointsEquiv _ (groundTest A B Z)).symm (Gm.pointsEquiv _ Z y)

theorem pointsEquiv_gmRestrict {Z : Over (Spec (CommRingCat.of B))}
    (y : Z ⟶ (Gm (Spec (CommRingCat.of B))).X) :
    Gm.pointsEquiv _ (groundTest A B Z) (gmRestrict (A := A) y) = Gm.pointsEquiv _ Z y :=
  MulEquiv.apply_symm_apply _ _

theorem gmRestrict_mul {Z : Over (Spec (CommRingCat.of B))}
    (y y' : Z ⟶ (Gm (Spec (CommRingCat.of B))).X) :
    gmRestrict (A := A) (y * y') = gmRestrict y * gmRestrict y' := by
  apply (Gm.pointsEquiv _ (groundTest A B Z)).injective
  rw [map_mul, pointsEquiv_gmRestrict, pointsEquiv_gmRestrict, pointsEquiv_gmRestrict,
    map_mul]

theorem gmRestrict_one {Z : Over (Spec (CommRingCat.of B))} :
    gmRestrict (A := A) (1 : Z ⟶ (Gm (Spec (CommRingCat.of B))).X) = 1 := by
  apply (Gm.pointsEquiv _ (groundTest A B Z)).injective
  rw [map_one, pointsEquiv_gmRestrict, map_one]

theorem gmRestrict_naturality {Z Z' : Over (Spec (CommRingCat.of B))} (a : Z' ⟶ Z)
    (y : Z ⟶ (Gm (Spec (CommRingCat.of B))).X) :
    gmRestrict (A := A) (a ≫ y) = groundMap A B a ≫ gmRestrict y := by
  apply (Gm.pointsEquiv _ (groundTest A B Z')).injective
  rw [Gm.pointsEquiv_naturality, pointsEquiv_gmRestrict, pointsEquiv_gmRestrict,
    Gm.pointsEquiv_naturality]
  rfl

theorem lineRestrict_unitInclusion {Z : Over (Spec (CommRingCat.of B))}
    (y : Z ⟶ (Gm (Spec (CommRingCat.of B))).X) :
    lineRestrict (A := A) (y ≫ AffineLine.unitInclusion _) =
      gmRestrict y ≫ AffineLine.unitInclusion _ := by
  apply AffineLine.hom_ext
  rw [homEquiv_lineRestrict, AffineLine.homEquiv_comp_unitInclusion,
    AffineLine.homEquiv_comp_unitInclusion, pointsEquiv_gmRestrict]

variable (A) in
/-- The counit recovers an affine-line point from its scalar point. -/
theorem counit_scalarLinePoint {Z : Over (Spec (CommRingCat.of B))}
    (y : Z ⟶ AffineLine.scheme (Spec (CommRingCat.of B))) :
    counit A B Z ≫ scalarLinePoint A B (lineRestrict y) = y := by
  apply AffineLine.hom_ext
  rw [AffineLine.homEquiv_comp, scalarLinePoint, Equiv.apply_symm_apply,
    homEquiv_lineRestrict, counit_appTop_includeSection]

variable (A) in
/-- The counit recovers a multiplicative point from its scalar point. -/
theorem counit_scalarGmPoints {Z : Over (Spec (CommRingCat.of B))}
    (y : Z ⟶ (Gm (Spec (CommRingCat.of B))).X) :
    counit A B Z ≫ scalarGmPoints A B _ (gmRestrict y) = y := by
  apply (Gm.pointsEquiv _ Z).injective
  rw [Gm.pointsEquiv_naturality]
  apply Units.ext
  simp only [scalarGmPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, pointsEquiv_gmRestrict]
  exact counit_appTop_includeSection A B Z _

/-- On a standard test, restricting a scalar point recovers the unit of the original point. -/
theorem gmRestrict_scalarGmPoints (C : CommAlgCat.{u} (CommRingCat.of A))
    (x : standardTest A C ⟶ (Gm (Spec (CommRingCat.of A))).X) :
    gmRestrict (scalarGmPoints A B _ x) = testUnit A B C ≫ x := by
  apply (Gm.pointsEquiv _ _).injective
  rw [pointsEquiv_gmRestrict, Gm.pointsEquiv_naturality]
  apply Units.ext
  simp only [scalarGmPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  exact (testUnit_appTop A B C _).symm

end Langlands.GroupScheme.AffineWeil
