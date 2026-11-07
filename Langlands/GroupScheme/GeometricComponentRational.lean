import Langlands.GroupScheme.GeometricComponents

/-! # Rational classes in the chosen geometric component group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

variable (k : Type u) [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- The actual geometric components fixed by the whole absolute Galois group. -/
def geometricComponentFixedSubgroup : Subgroup (GeometricComponents k H) :=
  allComponentFixedSubgroup k (AlgebraicClosure k) H

@[simp]
theorem mem_geometricComponentFixedSubgroup (c : GeometricComponents k H) :
    c ∈ geometricComponentFixedSubgroup k H ↔
      ∀ σ : Field.absoluteGaloisGroup k, σ • c = c :=
  Iff.rfl

/-- Extend a rational identity-component class to the chosen algebraic closure
and identify its class with an actual geometric component. -/
def rationalGeometricComponentHom :
    RationalComponentQuotient H →* GeometricComponents k H :=
  (allComponentQuotientEquiv (baseChanged k (AlgebraicClosure k) H)).toMonoidHom.comp
    (rationalComponentBaseChange H (algebraMap k (AlgebraicClosure k)))

@[simp]
theorem rationalGeometricComponentHom_projection (x : rationalPoints H) :
    rationalGeometricComponentHom k H (rationalComponentProjection H x) =
      geometricComponentOfPoint k H
        (baseChangeSectionHom (baseMap k (AlgebraicClosure k)) H x) :=
  rfl

/-- Distinct rational identity-component classes have distinct geometric components. -/
theorem rationalGeometricComponentHom_injective :
    Function.Injective (rationalGeometricComponentHom k H) :=
  (allComponentQuotientEquiv (baseChanged k (AlgebraicClosure k) H)).injective.comp
    (rationalComponentBaseChange_injective H (algebraMap k (AlgebraicClosure k)))

set_option backward.isDefEq.respectTransparency false in
/-- Every component represented by a base-field section is Galois fixed. -/
theorem rationalGeometricComponentHom_smul (σ : Field.absoluteGaloisGroup k)
    (c : RationalComponentQuotient H) :
    σ • rationalGeometricComponentHom k H c = rationalGeometricComponentHom k H c := by
  obtain ⟨x, rfl⟩ := rationalComponentProjection_surjective H c
  rw [rationalGeometricComponentHom_projection, geometricComponent_smul_ofPoint,
    rationalConjugate_baseChangeSectionHom]

/-- The canonical injection of rational classes into the fixed geometric subgroup. -/
def rationalGeometricComponentToFixed :
    RationalComponentQuotient H →* geometricComponentFixedSubgroup k H where
  toFun c := ⟨rationalGeometricComponentHom k H c,
    fun σ => rationalGeometricComponentHom_smul k H σ c⟩
  map_one' := Subtype.ext (map_one (rationalGeometricComponentHom k H))
  map_mul' c d := Subtype.ext (map_mul (rationalGeometricComponentHom k H) c d)

@[simp]
theorem rationalGeometricComponentToFixed_val (c : RationalComponentQuotient H) :
    (rationalGeometricComponentToFixed k H c).val = rationalGeometricComponentHom k H c :=
  rfl

theorem rationalGeometricComponentToFixed_injective :
    Function.Injective (rationalGeometricComponentToFixed k H) := by
  intro c d h
  apply rationalGeometricComponentHom_injective k H
  exact congrArg
    (fun z : geometricComponentFixedSubgroup k H => (z : GeometricComponents k H)) h

/-- A base-field section maps to the geometric component of its actual pullback. -/
def geometricComponentOfRationalPoint : rationalPoints H →* GeometricComponents k H :=
  (rationalGeometricComponentHom k H).comp (rationalComponentProjection H)

@[simp]
theorem geometricComponentOfRationalPoint_apply (x : rationalPoints H) :
    geometricComponentOfRationalPoint k H x =
      geometricComponentOfPoint k H
        (baseChangeSectionHom (baseMap k (AlgebraicClosure k)) H x) :=
  rfl

/-- The kernel consists exactly of the actual identity-component sections. -/
theorem ker_geometricComponentOfRationalPoint :
    (geometricComponentOfRationalPoint k H).ker = rationalIdentitySubgroup H := by
  ext x
  change rationalGeometricComponentHom k H (rationalComponentProjection H x) = 1 ↔
    x ∈ rationalIdentitySubgroup H
  rw [← map_one (rationalGeometricComponentHom k H),
    (rationalGeometricComponentHom_injective k H).eq_iff]
  change x ∈ (rationalComponentProjection H).ker ↔ x ∈ rationalIdentitySubgroup H
  rw [ker_rationalComponentProjection]

@[simp]
theorem geometricComponentOfRationalPoint_eq_one_iff (x : rationalPoints H) :
    geometricComponentOfRationalPoint k H x = 1 ↔ x ∈ rationalIdentitySubgroup H := by
  change x ∈ (geometricComponentOfRationalPoint k H).ker ↔ _
  rw [ker_geometricComponentOfRationalPoint]

/-- The image consists precisely of components containing a pulled-back
base-field section. Fixedness alone is not used as a rationality criterion. -/
theorem mem_range_rationalGeometricComponentHom (c : GeometricComponents k H) :
    c ∈ (rationalGeometricComponentHom k H).range ↔
      ∃ x : rationalPoints H,
        geometricComponentOfPoint k H
          (baseChangeSectionHom (baseMap k (AlgebraicClosure k)) H x) = c := by
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := rationalComponentProjection_surjective H q
    exact ⟨x, (rationalGeometricComponentHom_projection k H x).symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨rationalComponentProjection H x,
      (rationalGeometricComponentHom_projection k H x).trans hx⟩

variable {H}
  {H' H'' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]
  [Smooth H''.X.hom] [IsAffineHom H''.X.hom]

/-- The chosen geometric-component map agrees with the actual map on sections. -/
@[simp]
theorem geometricComponentMap_ofPoint (f : H ⟶ H')
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    geometricComponentMap k f (geometricComponentOfPoint k H x) =
      geometricComponentOfPoint k H'
        (rationalPoints.map
          ((GroupScheme.baseChange (baseMap k (AlgebraicClosure k))).map f) x) := by
  change allComponentMap _ (allComponentOfPoint _ x) = allComponentOfPoint _ _
  rw [allComponentMap_apply]
  rfl

/-- A homomorphism over the base field induces a map on Galois-fixed components. -/
def geometricComponentFixedMap (f : H ⟶ H') :
    geometricComponentFixedSubgroup k H →* geometricComponentFixedSubgroup k H' where
  toFun c := ⟨geometricComponentMap k f c.val, by
    change ∀ σ : Field.absoluteGaloisGroup k,
      σ • geometricComponentMap k f c.val = geometricComponentMap k f c.val
    intro σ
    rw [← geometricComponentMap_smul]
    exact congrArg (geometricComponentMap k f)
      ((mem_geometricComponentFixedSubgroup k H c.val).mp c.property σ)⟩
  map_one' := Subtype.ext (map_one (geometricComponentMap k f))
  map_mul' c d := Subtype.ext (map_mul (geometricComponentMap k f) c.val d.val)

@[simp]
theorem geometricComponentFixedMap_val (f : H ⟶ H')
    (c : geometricComponentFixedSubgroup k H) :
    (geometricComponentFixedMap k f c).val = geometricComponentMap k f c.val :=
  rfl

@[simp]
theorem geometricComponentFixedMap_id :
    geometricComponentFixedMap k (𝟙 H) =
      MonoidHom.id (geometricComponentFixedSubgroup k H) := by
  ext c
  exact congrArg (fun m : GeometricComponents k H →* GeometricComponents k H => m c.val)
    (geometricComponentMap_id k (H := H))

@[simp]
theorem geometricComponentFixedMap_comp (f : H ⟶ H') (g : H' ⟶ H'') :
    geometricComponentFixedMap k (f ≫ g) =
      (geometricComponentFixedMap k g).comp (geometricComponentFixedMap k f) := by
  ext c
  exact congrArg (fun m => m c.val) (geometricComponentMap_comp k f g)

/-- The rational-class injection is natural for actual base-field homomorphisms. -/
theorem rationalGeometricComponentHom_naturality (f : H ⟶ H')
    (c : RationalComponentQuotient H) :
    geometricComponentMap k f (rationalGeometricComponentHom k H c) =
      rationalGeometricComponentHom k H' (rationalComponentMap f c) := by
  obtain ⟨x, rfl⟩ := rationalComponentProjection_surjective H c
  rw [rationalComponentMap_projection, rationalGeometricComponentHom_projection,
    rationalGeometricComponentHom_projection, geometricComponentMap_ofPoint]
  exact congrArg (geometricComponentOfPoint k H')
    (baseChangeSectionHom_naturality (baseMap k (AlgebraicClosure k)) f x).symm

/-- The factorization through the fixed subgroup is natural as well. -/
theorem rationalGeometricComponentToFixed_naturality (f : H ⟶ H')
    (c : RationalComponentQuotient H) :
    geometricComponentFixedMap k f (rationalGeometricComponentToFixed k H c) =
      rationalGeometricComponentToFixed k H' (rationalComponentMap f c) := by
  apply Subtype.ext
  exact rationalGeometricComponentHom_naturality k f c

end Langlands.GroupScheme.IdentityComponent
