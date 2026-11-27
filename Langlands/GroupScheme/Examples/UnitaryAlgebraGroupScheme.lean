import Langlands.GroupScheme.Examples.UnitaryAlgebraPresentation
import Langlands.GroupScheme.Quaternionic.IsometryCut
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.Torus.Split

/-!
# The special unitary group scheme of a central simple algebra with involution

Let `F ⊆ E` be fields with `E/F` finite, `B` a finite-dimensional central simple `E`-algebra
that is an `F`-algebra through `E`, and `τ` an `F`-linear involution of `B`. This module builds
the affine group scheme `SU(B, τ)` over `F` whose points with coefficients in a commutative
`F`-algebra `R` are `UnitaryPoints.specialUnitaryPoints E τ R`, the units `u` of `R ⊗_F B` with
`u τ_R(u) = 1` and relative reduced norm one. It is the closed subgroup scheme of the unit group
scheme of `B` cut out by the coordinates of `u τ(u) - 1` and of `Nrd(u) - 1`. An isomorphism
of `SU(B, τ)` with a group scheme `G` gives a presentation `UnitaryAlgebra.Presentation E τ G`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.UnitaryAlgebra

open Langlands.CentralSimple.UnitaryPoints Langlands.GroupScheme.Quaternionic

variable {F : Type u} (E : Type u) {B : Type u} [Field F] [Field E] [Algebra F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B] [FiniteDimensional F E]
  [FiniteDimensional F B] (τ : FirstKindInvolution F B)

/-- The special unitary points, as subgroups of the values of the unit functor of `B`. -/
def family : ∀ R : CommAlgCat.{u} (CommRingCat.of F),
    Subgroup ((FiniteAlgebraUnits.functor F B).obj R) :=
  fun R => specialUnitaryPoints E τ R

/-- The `j`-th coordinate over `F` of an element of `E ⊗_F R`. -/
def normCoord (R : Type u) [CommRing R] [Algebra F R]
    (j : Fin (Module.finrank F (E ⧸ (⊥ : Submodule F E)))) (z : E ⊗[F] R) : R :=
  IsometryCut.coord (⊥ : Submodule F E) R j (TensorProduct.comm F E R z)

/-- The coordinates commute with every change of coefficients. -/
theorem normCoord_map {R S : Type u} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
    (φ : R →ₐ[F] S) (j : Fin (Module.finrank F (E ⧸ (⊥ : Submodule F E)))) (z : E ⊗[F] R) :
    normCoord E S j (Algebra.TensorProduct.map (AlgHom.id F E) φ z) = φ (normCoord E R j z) := by
  have h : TensorProduct.comm F E S (Algebra.TensorProduct.map (AlgHom.id F E) φ z) =
      Algebra.TensorProduct.map φ (AlgHom.id F E) (TensorProduct.comm F E R z) := by
    induction z using TensorProduct.inductionOn with
    | tmul e r => rfl
    | add z z' hz hz' => rw [map_add, LinearEquiv.map_add, hz, hz', LinearEquiv.map_add, map_add]
  rw [normCoord, normCoord, h, IsometryCut.coord_map]

/-- An element of `E ⊗_F R` vanishes exactly when all its coordinates vanish. -/
theorem eq_zero_iff_normCoord {R : Type u} [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    z = 0 ↔ ∀ j, normCoord E R j z = 0 := by
  have h := IsometryCut.mem_baseChange_iff (⊥ : Submodule F E) (TensorProduct.comm F E R z)
  rw [Submodule.baseChange_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at h
  exact h

/-- The defining coordinates of `Nrd(u) - 1` at the universal unit. -/
def normGenerator (j : Fin (Module.finrank F (E ⧸ (⊥ : Submodule F E)))) :
    FiniteAlgebraUnits.candidateRing (IsometryCut.unitsBasis F B) :=
  normCoord E _ j ((relativeNorm F E B _
    (FiniteAlgebraUnits.algebraicUniversalUnit (IsometryCut.unitsBasis F B)) :
      E ⊗[F] FiniteAlgebraUnits.candidateRing (IsometryCut.unitsBasis F B)) - 1)

/-- The ideal cutting out the special unitary group. -/
def ideal : Ideal (FiniteAlgebraUnits.coordinateAlgebra (IsometryCut.unitsBasis F B)) :=
  IsometryCut.ideal τ ⊥ 1 ⊔ Ideal.span (Set.range (normGenerator (B := B) E))

omit [IsSimpleRing B] [FiniteDimensional F B] in
/-- The isometry defect for `Q = 1` is `y τ_R(y) - 1`. -/
theorem defect_one_eq (R : Type u) [CommRing R] [Algebra F R] (y : R ⊗[F] B) :
    IsometryCut.defect τ 1 y = y * τ.baseChange R y - 1 := by
  rw [IsometryCut.defect, ← Algebra.TensorProduct.one_def, mul_one]

/-- The special unitary points are cut out by `ideal`. -/
theorem isCutOutBy :
    Corepresented.IsCutOutBy (FiniteAlgebraUnits.corepresentableBy (IsometryCut.unitsBasis F B))
      (family E τ) (ideal E τ) := by
  intro R x
  change x ∈ family E τ R ↔
    ∀ c ∈ ideal E τ, FiniteAlgebraUnits.unitCoefficientMap (IsometryCut.unitsBasis F B) x c = 0
  set φ := FiniteAlgebraUnits.unitCoefficientMap (IsometryCut.unitsBasis F B) x
  have h1 := IsometryCut.isCutOutBy (τ := τ) IsometryCut.isStable_bot (1 : B) R x
  change x ∈ IsometryCut.isometryFamily (IsometryCut.isStable_bot (τ := τ)) 1 R ↔
    ∀ c ∈ IsometryCut.ideal τ ⊥ 1, φ c = 0 at h1
  have hx : x = Units.map (Algebra.TensorProduct.map φ (AlgHom.id F B)).toMonoidHom
      (FiniteAlgebraUnits.algebraicUniversalUnit (IsometryCut.unitsBasis F B)) :=
    (FiniteAlgebraUnits.algebraicPoint_unitCoefficientMap (IsometryCut.unitsBasis F B) x).symm
  have key : ∀ j, φ (normGenerator E j) =
      normCoord E R j ((relativeNorm F E B R x : E ⊗[F] R) - 1) := by
    intro j
    rw [normGenerator, ← normCoord_map, map_sub, map_one, hx, relativeNorm_naturality]
    rfl
  have h2 : relativeNorm F E B R x = 1 ↔ ∀ c ∈ Ideal.span (Set.range (normGenerator (B := B) E)),
      φ c = 0 := by
    rw [← Units.val_eq_one, ← sub_eq_zero, eq_zero_iff_normCoord]
    constructor
    · intro h c hc
      have hle : Ideal.span (Set.range (normGenerator (B := B) E)) ≤ RingHom.ker φ := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, key]
        exact h j
      exact hle hc
    · intro h j
      rw [← key]
      exact h _ (Ideal.subset_span ⟨j, rfl⟩)
  have hfam : x ∈ family E τ R ↔ x ∈ IsometryCut.isometryFamily (IsometryCut.isStable_bot (τ := τ)) 1 R ∧
      relativeNorm F E B R x = 1 := by
    rw [IsometryCut.mem_isometryFamily, Submodule.baseChange_bot, Submodule.mem_bot,
      defect_one_eq, sub_eq_zero]
    exact mem_specialUnitaryPoints τ x
  rw [hfam, h1, h2]
  constructor
  · rintro ⟨ha, hb⟩ c hc
    have hle : ideal E τ ≤ RingHom.ker φ := by
      refine sup_le (fun d hd => ?_) (fun d hd => ?_)
      · exact (RingHom.mem_ker).mpr (ha d hd)
      · exact (RingHom.mem_ker).mpr (hb d hd)
    exact hle hc
  · intro h
    exact ⟨fun c hc => h c (Ideal.mem_sup_left hc), fun c hc => h c (Ideal.mem_sup_right hc)⟩

/-- The special unitary group scheme `SU(B, τ)` over `F`. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of F)) :=
  Corepresented.cutGroupScheme (isCutOutBy E τ)

/-- `SU(B, τ)` is affine over `F`. -/
instance : IsAffineHom (groupScheme E τ).X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap F _)))
  infer_instance

/-- The points of `SU(B, τ)` on every test scheme are the special unitary points over its
global sections. -/
def pointsEquiv (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (groupScheme E τ).X) ≃* specialUnitaryPoints E τ ((algΓ (CommRingCat.of F)).obj T).unop :=
  Corepresented.pointsEquiv (Corepresented.cutFunctor (isCutOutBy E τ))
    (Corepresented.cutCorepresentableBy (isCutOutBy E τ)) T

/-- The points comparison is natural in the test scheme. -/
theorem pointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of F))} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme E τ).X) :
    pointsEquiv E τ T' (a ≫ x) =
      specialUnitaryMap E τ ((algΓ (CommRingCat.of F)).map a).unop.hom (pointsEquiv E τ T x) :=
  Corepresented.pointsEquiv_naturality (Corepresented.cutFunctor (isCutOutBy E τ))
    (Corepresented.cutCorepresentableBy (isCutOutBy E τ)) a x

/-- The points of `SU(B, τ)` with coefficients in a commutative algebra. -/
def affinePointsEquiv (R : CommAlgCat.{u} (CommRingCat.of F)) :
    (groupScheme E τ).affinePoints R ≃* specialUnitaryPoints E τ R :=
  Corepresented.affinePointsEquiv (Corepresented.cutFunctor (isCutOutBy E τ))
    (Corepresented.cutCorepresentableBy (isCutOutBy E τ)) R

/-- The coefficient points comparison is natural in the coefficient algebra. -/
theorem affinePointsEquiv_naturality {R S : CommAlgCat.{u} (CommRingCat.of F)} (f : R ⟶ S)
    (x : (groupScheme E τ).affinePoints R) :
    affinePointsEquiv E τ S ((groupScheme E τ).affinePointMap f x) =
      specialUnitaryMap E τ f.hom (affinePointsEquiv E τ R x) :=
  Corepresented.affinePointsEquiv_naturality (Corepresented.cutFunctor (isCutOutBy E τ))
    (Corepresented.cutCorepresentableBy (isCutOutBy E τ)) f x

/-- An isomorphism from `SU(B, τ)` gives a presentation by special unitary points. -/
def Presentation.ofIso {G : GroupScheme (Spec (CommRingCat.of F))} (φ : groupScheme E τ ≅ G) :
    Presentation E τ G where
  pointsEquiv R := (isoPointsEquiv φ.symm _).trans (affinePointsEquiv E τ R)
  naturality f x := by
    simp only [MulEquiv.trans_apply, isoPointsEquiv_apply]
    rw [← affinePointsEquiv_naturality]
    simp only [GroupScheme.affinePointMap_apply, Category.assoc]

end Langlands.GroupScheme.UnitaryAlgebra
