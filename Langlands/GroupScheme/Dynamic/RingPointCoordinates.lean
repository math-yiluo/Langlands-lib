import Langlands.GroupScheme.Dynamic.Representability
import Langlands.GroupScheme.Dynamic.BaseChange
import Langlands.GroupScheme.Dynamic.DominantCombinationInclusions

/-! # Points of a corepresented group over algebras, and over base changes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Corepresented.RingCoordinates

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

theorem pointRing_comp {A A' : CommRingCat.{u}} {f : Spec A ⟶ Spec R} {f' : Spec A' ⟶ Spec R}
    (y : Over.mk f' ⟶ Over.mk f) (x : Over.mk f ⟶ (groupScheme F e).X) :
    pointRing (y ≫ x) = pointRing x ≫ Spec.preimage y.left := by
  apply Spec.map_injective
  rw [specMap_pointRing, Spec.map_comp, Spec.map_preimage, specMap_pointRing, Over.comp_left]
  rfl

section AlgPoints

variable (R) (D : Type u) [CommRing D] [Algebra R D]

/-- `Spec D` as a scheme over `Spec R`, for an `R`-algebra `D`. -/
abbrev specOver : Over (Spec R) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R D)))

variable {R D}

/-- The `R`-algebra map `B → D` classifying a point over `Spec D`. -/
def algHom (x : specOver R D ⟶ (groupScheme F e).X) : B →ₐ[R] D where
  __ := (pointRing x).hom
  commutes' r := by
    have h := algebraMap_comp_pointRing x
    rw [Spec.preimage_map] at h
    exact congrArg (fun φ => φ.hom r) h

theorem algHom_apply (x : specOver R D ⟶ (groupScheme F e).X) (b : B) :
    algHom x b = pointRing x b := rfl

variable (F e) in
/-- The point over `Spec D` classified by an `R`-algebra map `B → D`. -/
def ofAlgHom (φ : B →ₐ[R] D) : specOver R D ⟶ (groupScheme F e).X :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext φ.commutes)

theorem algHom_ofAlgHom (φ : B →ₐ[R] D) : algHom (ofAlgHom F e φ) = φ := by
  ext b
  rw [algHom_apply]
  change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))) b = φ b
  rw [Spec.preimage_map]
  rfl

theorem ofAlgHom_algHom (x : specOver R D ⟶ (groupScheme F e).X) :
    ofAlgHom F e (algHom x) = x := by
  apply hom_ext_of_pointRing
  ext b
  exact congrArg (fun φ : B →ₐ[R] D => φ b) (algHom_ofAlgHom (algHom x))

variable (F e D) in
/-- Points over `Spec D` are the `R`-algebra maps `B → D`. -/
def algHomEquiv : (specOver R D ⟶ (groupScheme F e).X) ≃ (B →ₐ[R] D) where
  toFun := algHom
  invFun := ofAlgHom F e
  left_inv := ofAlgHom_algHom
  right_inv := algHom_ofAlgHom

variable {D' : Type u} [CommRing D'] [Algebra R D']

/-- The morphism `Spec D' ⟶ Spec D` over `Spec R` given by an `R`-algebra map `D → D'`. -/
def specMapOver (g : D →ₐ[R] D') : specOver R D' ⟶ specOver R D :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    change _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext g.commutes)

theorem algHom_comp (g : D →ₐ[R] D') (x : specOver R D ⟶ (groupScheme F e).X) :
    algHom (specMapOver g ≫ x) = g.comp (algHom x) := by
  ext b
  rw [algHom_apply, pointRing_comp, AlgHom.comp_apply, algHom_apply]
  change (Spec.preimage (Spec.map (CommRingCat.ofHom g.toRingHom))) (pointRing x b) = _
  rw [Spec.preimage_map]
  rfl

end AlgPoints

section BaseChange

variable (R) (K : Type u) [CommRing K] [Algebra R K]

/-- The base morphism `Spec K ⟶ Spec R`. -/
abbrev baseMap : Spec (CommRingCat.of K) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R K))

variable (D : Type u) [CommRing D] [Algebra R D] [Algebra K D] [IsScalarTower R K D]

/-- `Spec D` as a scheme over `Spec K`. -/
abbrev testOver : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K D)))

theorem specMap_algebraMap_comp_baseMap :
    Spec.map (CommRingCat.ofHom (algebraMap K D)) ≫ baseMap R K =
      Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- `Spec D` over `Spec R`, compared with `Spec D` over `Spec K` regarded over `Spec R`. -/
def testOverHom : specOver R D ⟶ (Over.map (baseMap R K)).obj (testOver K D) :=
  Over.homMk (𝟙 _) (by
    rw [Category.id_comp]
    exact specMap_algebraMap_comp_baseMap R K D)

/-- The inverse comparison of `testOverHom`. -/
def testOverInv : (Over.map (baseMap R K)).obj (testOver K D) ⟶ specOver R D :=
  Over.homMk (𝟙 _) (by
    rw [Category.id_comp]
    exact (specMap_algebraMap_comp_baseMap R K D).symm)

theorem testOverHom_comp_testOverInv : testOverHom R K D ≫ testOverInv R K D = 𝟙 _ :=
  Over.OverMorphism.ext (Category.id_comp _)

theorem testOverInv_comp_testOverHom : testOverInv R K D ≫ testOverHom R K D = 𝟙 _ :=
  Over.OverMorphism.ext (Category.id_comp _)

variable {R K D}

/-- The `R`-algebra map `B → D` classifying the underlying point of a point of the base change
over `Spec D`. -/
def baseAlgHom
    (z : testOver K D ⟶ ((GroupScheme.baseChange (baseMap R K)).obj (groupScheme F e)).X) :
    B →ₐ[R] D :=
  algHom (testOverHom R K D ≫ baseChangePointsEquiv (baseMap R K) (groupScheme F e) _ z)

theorem baseAlgHom_bijective :
    Function.Bijective (baseAlgHom (F := F) (e := e) (K := K) (D := D)) := by
  refine (algHomEquiv F e D).bijective.comp ?_
  refine Function.Bijective.comp ?_ (baseChangePointsEquiv _ _ _).bijective
  refine ⟨fun x y h => ?_, fun y => ⟨testOverInv R K D ≫ y, ?_⟩⟩
  · have := congrArg (fun z => testOverInv R K D ≫ z) h
    simpa only [← Category.assoc, testOverInv_comp_testOverHom, Category.id_comp] using this
  · simp only [← Category.assoc, testOverHom_comp_testOverInv, Category.id_comp]

variable {D' : Type u} [CommRing D'] [Algebra R D'] [Algebra K D'] [IsScalarTower R K D']

/-- The morphism `Spec D' ⟶ Spec D` over `Spec K` given by a `K`-algebra map `D → D'`. -/
def specMapK (g : D →ₐ[K] D') : testOver K D' ⟶ testOver K D :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    change _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext g.commutes)

theorem baseAlgHom_comp (g : D →ₐ[K] D')
    (z : testOver K D ⟶ ((GroupScheme.baseChange (baseMap R K)).obj (groupScheme F e)).X) :
    baseAlgHom (specMapK g ≫ z) = (g.restrictScalars R).comp (baseAlgHom z) := by
  rw [baseAlgHom, baseAlgHom, GroupScheme.baseChangePointsEquiv_naturality, ← algHom_comp,
    ← Category.assoc, ← Category.assoc]
  congr 1

section Conjugation

open AffineLine

/-- The unit point `u` of `𝔾_{m,K}` over `Spec D`, regarded over `Spec R`, is the unit point
`u` of `𝔾_{m,R}`. -/
theorem testOverHom_comp_unitPoint (u : Dˣ) :
    testOverHom R K D ≫ baseChangePointsEquiv (baseMap R K) (Gm (Spec R)).toGrp (testOver K D)
        (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap K D))) u ≫
          (Gm.baseChangeIso (baseMap R K)).inv.hom.hom) =
      unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R D))) u := by
  apply (Gm.pointsEquiv _ _).injective
  rw [Gm.pointsEquiv_naturality, ← Gm.baseChangeUnitsEquiv_apply,
    Gm.baseChangeUnitsEquiv_baseChangeIso_inv, unitPoint, unitPoint, MulEquiv.apply_symm_apply]
  erw [MulEquiv.apply_symm_apply]
  ext
  change (𝟙 (Spec (CommRingCat.of D)) : _ ⟶ _).appTop _ = _
  rw [Scheme.Hom.id_appTop]
  rfl

/-- Conjugation by a base-changed cocharacter corresponds to conjugation by the cocharacter. -/
theorem testOverHom_comp_conj {G : GroupScheme (Spec R)} (ν : (Gm (Spec R)).toGrp ⟶ G)
    (z : testOver K D ⟶ ((GroupScheme.baseChange (baseMap R K)).obj G).X) (u : Dˣ) :
    testOverHom R K D ≫ baseChangePointsEquiv (baseMap R K) G (testOver K D)
        ((unitPoint (Spec.map (CommRingCat.ofHom (algebraMap K D))) u ≫
          (Dynamic.baseChangeCocharacter (baseMap R K) ν).hom.hom) * z *
        (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap K D))) u ≫
          (Dynamic.baseChangeCocharacter (baseMap R K) ν).hom.hom)⁻¹) =
      (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R D))) u ≫ ν.hom.hom) *
        (testOverHom R K D ≫ baseChangePointsEquiv (baseMap R K) G (testOver K D) z) *
        (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R D))) u ≫ ν.hom.hom)⁻¹ := by
  rw [map_mul, map_mul, map_inv, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
    Dynamic.baseChangePointsEquiv_baseChangeCocharacter, ← Category.assoc,
    testOverHom_comp_unitPoint]

end Conjugation

/-- Restricting a base-changed point along a map of `K`-algebras restricts its underlying
point. -/
theorem specMapOver_comp_testOverHom {G : GroupScheme (Spec R)} (g : D →ₐ[K] D')
    (z : testOver K D ⟶ ((GroupScheme.baseChange (baseMap R K)).obj G).X) :
    specMapOver (g.restrictScalars R) ≫ testOverHom R K D ≫
        baseChangePointsEquiv (baseMap R K) G _ z =
      testOverHom R K D' ≫ baseChangePointsEquiv (baseMap R K) G _ (specMapK g ≫ z) := by
  rw [GroupScheme.baseChangePointsEquiv_naturality, ← Category.assoc, ← Category.assoc]
  congr 1

end BaseChange

end Langlands.GroupScheme.Corepresented.RingCoordinates
