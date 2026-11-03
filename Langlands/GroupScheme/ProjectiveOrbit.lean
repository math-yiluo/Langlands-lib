import Langlands.GroupScheme.MatrixRepresentation
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.GlobalLinearAction
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure

/-! # Actual projective orbit maps of finite matrix representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme.ProjectiveOrbit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (n : ℕ)

/-- Convert an invertible coordinate matrix to its coordinate linear equivalence. -/
def coordinateEquiv {A : Type u} [CommRing A] :
    GL (Fin (n + 1)) A ≃* ((Fin (n + 1) → A) ≃ₗ[A] (Fin (n + 1) → A)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv A _)

@[simp] theorem coordinateEquiv_apply {A : Type u} [CommRing A]
    (M : GL (Fin (n + 1)) A) (v : Fin (n + 1) → A) :
    coordinateEquiv n M v = (M : Matrix _ _ A) *ᵥ v := rfl

/-- The actual relative projective coordinate action of an invertible matrix. -/
def matrixAction {T : Scheme.{u}} (M : GL (Fin (n + 1)) Γ(T, ⊤)) :
    RelativeProjectiveSpace T n ⟶ RelativeProjectiveSpace T n :=
  RelativeProjectiveSpace.globalLinearAction n (coordinateEquiv n M)

@[reassoc (attr := simp)]
theorem matrixAction_toBase {T : Scheme.{u}} (M : GL (Fin (n + 1)) Γ(T, ⊤)) :
    matrixAction n M ≫ RelativeProjectiveSpace.toBase T n =
      RelativeProjectiveSpace.toBase T n :=
  RelativeProjectiveSpace.globalLinearAction_toBase n _

@[simp] theorem matrixAction_one {T : Scheme.{u}} :
    matrixAction n (1 : GL (Fin (n + 1)) Γ(T, ⊤)) = 𝟙 _ := by
  unfold matrixAction
  rw [map_one]
  exact RelativeProjectiveSpace.globalLinearAction_refl n

/-- Matrix multiplication acts in the usual left-action order. -/
theorem matrixAction_mul {T : Scheme.{u}} (M N : GL (Fin (n + 1)) Γ(T, ⊤)) :
    matrixAction n (M * N) = matrixAction n N ≫ matrixAction n M := by
  unfold matrixAction
  rw [RelativeProjectiveSpace.globalLinearAction_comp]
  congr 1
  change coordinateEquiv n (M * N) = coordinateEquiv n M * coordinateEquiv n N
  exact map_mul _ _ _

@[simp, reassoc] theorem matrixAction_inv_hom {T : Scheme.{u}}
    (M : GL (Fin (n + 1)) Γ(T, ⊤)) :
    matrixAction n M⁻¹ ≫ matrixAction n M = 𝟙 _ := by
  rw [← matrixAction_mul, mul_inv_cancel, matrixAction_one]

@[simp, reassoc] theorem matrixAction_hom_inv {T : Scheme.{u}}
    (M : GL (Fin (n + 1)) Γ(T, ⊤)) :
    matrixAction n M ≫ matrixAction n M⁻¹ = 𝟙 _ := by
  rw [← matrixAction_mul, inv_mul_cancel, matrixAction_one]

/-- Restricting a matrix is precisely pulling back its global-function coefficients. -/
theorem coordinatePullback_coordinateEquiv {T U : Scheme.{u}} (f : T ⟶ U)
    (M : GL (Fin (n + 1)) Γ(U, ⊤)) :
    RelativeProjectiveSpace.coordinatePullback n f (coordinateEquiv n M) =
      coordinateEquiv n (Matrix.GeneralLinearGroup.map f.appTop.hom M) := by
  apply ProjectiveSpace.coordinateEquiv_ext n
  intro i j
  rw [RelativeProjectiveSpace.coordinatePullback_coeff]
  simp only [coordinateEquiv_apply, Matrix.mulVec_single_one]
  rfl

@[reassoc]
theorem map_matrixAction {T U : Scheme.{u}} (f : T ⟶ U)
    (M : GL (Fin (n + 1)) Γ(U, ⊤)) :
    RelativeProjectiveSpace.map n f ≫ matrixAction n M =
      matrixAction n (Matrix.GeneralLinearGroup.map f.appTop.hom M) ≫
        RelativeProjectiveSpace.map n f := by
  unfold matrixAction
  rw [RelativeProjectiveSpace.map_globalLinearAction, coordinatePullback_coordinateEquiv]

variable {S T U : Scheme.{u}}

/-- Pull back an actual projective section along an arbitrary scheme morphism. -/
def pullbackPoint (p : S ⟶ RelativeProjectiveSpace S n) (f : T ⟶ S) :
    T ⟶ RelativeProjectiveSpace T n :=
  RelativeProjectiveSpace.lift n (𝟙 T) (f ≫ p ≫ RelativeProjectiveSpace.toIntegral S n)

@[reassoc (attr := simp)] theorem pullbackPoint_toBase
    (p : S ⟶ RelativeProjectiveSpace S n) (f : T ⟶ S) :
    pullbackPoint n p f ≫ RelativeProjectiveSpace.toBase T n = 𝟙 T := by
  simp [pullbackPoint]

@[reassoc (attr := simp)] theorem pullbackPoint_toIntegral
    (p : S ⟶ RelativeProjectiveSpace S n) (f : T ⟶ S) :
    pullbackPoint n p f ≫ RelativeProjectiveSpace.toIntegral T n =
      f ≫ p ≫ RelativeProjectiveSpace.toIntegral S n := by
  simp [pullbackPoint]

/-- Pullback of the chosen projective point commutes with all test morphisms. -/
theorem pullbackPoint_naturality (p : S ⟶ RelativeProjectiveSpace S n)
    (f : U ⟶ S) (a : T ⟶ U) :
    a ≫ pullbackPoint n p f =
      pullbackPoint n p (a ≫ f) ≫ RelativeProjectiveSpace.map n a := by
  apply RelativeProjectiveSpace.hom_ext <;> simp

/-- Maps of projective sections are determined after mapping to the base's projective space. -/
theorem section_ext_of_map (f : T ⟶ S)
    {a b : T ⟶ RelativeProjectiveSpace T n}
    (hbase : a ≫ RelativeProjectiveSpace.toBase T n =
      b ≫ RelativeProjectiveSpace.toBase T n)
    (h : a ≫ RelativeProjectiveSpace.map n f = b ≫ RelativeProjectiveSpace.map n f) : a = b := by
  apply RelativeProjectiveSpace.hom_ext hbase
  simpa only [Category.assoc, RelativeProjectiveSpace.map_toIntegral] using
    congrArg (fun q => q ≫ RelativeProjectiveSpace.toIntegral S n) h

/-- Equality of two matrix translates is the fixed-point test for their right difference. -/
theorem translates_eq_iff (v : T ⟶ RelativeProjectiveSpace T n)
    (M N : GL (Fin (n + 1)) Γ(T, ⊤)) :
    v ≫ matrixAction n M = v ≫ matrixAction n N ↔
      v ≫ matrixAction n (M⁻¹ * N) = v := by
  constructor
  · intro h
    have h' := congrArg (fun q => q ≫ matrixAction n M⁻¹) h
    simpa only [matrixAction_mul, Category.assoc, matrixAction_hom_inv,
      Category.comp_id] using h'.symm
  · intro h
    have h' := congrArg (fun q => q ≫ matrixAction n M) h
    simpa only [matrixAction_mul, Category.assoc, matrixAction_inv_hom,
      Category.comp_id] using h'.symm

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}

/-- The projective section obtained by translating the base point by a test point of the group. -/
def orbitSection (ρ : MatrixRepresentation G (Fin (n + 1)))
    (p : Spec R ⟶ RelativeProjectiveSpace (Spec R) n) (T : Over (Spec R))
    (g : T ⟶ G.X) : T.left ⟶ RelativeProjectiveSpace T.left n :=
  pullbackPoint n p T.hom ≫ matrixAction n (ρ.pointMatrix T g)

@[reassoc (attr := simp)] theorem orbitSection_toBase
    (ρ : MatrixRepresentation G (Fin (n + 1)))
    (p : Spec R ⟶ RelativeProjectiveSpace (Spec R) n) (T : Over (Spec R))
    (g : T ⟶ G.X) :
    orbitSection n ρ p T g ≫ RelativeProjectiveSpace.toBase T.left n = 𝟙 _ := by
  simp [orbitSection]

/-- Naturality retains the full actual projective morphisms on arbitrary schemes. -/
theorem orbitSection_naturality (ρ : MatrixRepresentation G (Fin (n + 1)))
    (p : Spec R ⟶ RelativeProjectiveSpace (Spec R) n)
    {T U : Over (Spec R)} (a : T ⟶ U) (g : U ⟶ G.X) :
    a.left ≫ orbitSection n ρ p U g =
      orbitSection n ρ p T (a ≫ g) ≫ RelativeProjectiveSpace.map n a.left := by
  unfold orbitSection
  rw [← Category.assoc, pullbackPoint_naturality, Category.assoc,
    map_matrixAction, ← Category.assoc,
    ← MatrixRepresentation.pointMatrix_naturality]
  rw [Over.w a]

/-- The actual separated ambient projective scheme over the coefficient spectrum. -/
def ambient (R : CommRingCat.{u}) : Over (Spec R) :=
  Over.mk (RelativeProjectiveSpace.toBase (Spec R) n)

instance ambient_isSeparated (R : CommRingCat.{u}) : IsSeparated (ambient n R).hom := by
  change IsSeparated (RelativeProjectiveSpace.toBase (Spec (CommRingCat.of R)) n)
  rw [← RelativeProjectiveSpace.affineComparisonIso_inv_toSpec R n]
  infer_instance

/-- The actual orbit morphism is the universal matrix translate of the chosen section. -/
def orbitMap (ρ : MatrixRepresentation G (Fin (n + 1)))
    (p : Spec R ⟶ RelativeProjectiveSpace (Spec R) n) : G.X ⟶ ambient n R :=
  Over.homMk (orbitSection n ρ p G.X (𝟙 _) ≫ RelativeProjectiveSpace.map n G.X.hom)
    (by simp [ambient])

/-- On every scheme test the actual orbit map equals the pointwise matrix translate. -/
theorem comp_orbitMap (ρ : MatrixRepresentation G (Fin (n + 1)))
    (p : Spec R ⟶ RelativeProjectiveSpace (Spec R) n) (T : Over (Spec R))
    (g : T ⟶ G.X) :
    (g ≫ orbitMap n ρ p).left =
      orbitSection n ρ p T g ≫ RelativeProjectiveSpace.map n T.hom := by
  change g.left ≫ (orbitSection n ρ p G.X (𝟙 _) ≫ _) = _
  rw [← Category.assoc, orbitSection_naturality, Category.assoc,
    ← RelativeProjectiveSpace.map_comp, Over.w g, Category.comp_id]

/-- The all-test fibers of the actual orbit map are precisely projective stabilizer tests. -/
theorem orbitMap_fibers (ρ : MatrixRepresentation G (Fin (n + 1)))
    (p : Spec R ⟶ RelativeProjectiveSpace (Spec R) n) (T : Over (Spec R))
    (g h : T ⟶ G.X) :
    g ≫ orbitMap n ρ p = h ≫ orbitMap n ρ p ↔
      pullbackPoint n p T.hom ≫ matrixAction n (ρ.pointMatrix T (g⁻¹ * h)) =
        pullbackPoint n p T.hom := by
  have heq : g ≫ orbitMap n ρ p = h ≫ orbitMap n ρ p ↔
      orbitSection n ρ p T g = orbitSection n ρ p T h := by
    constructor
    · intro hgh
      apply section_ext_of_map n T.hom (by simp)
      simpa only [comp_orbitMap] using congrArg Over.Hom.left hgh
    · intro hgh
      apply Over.OverMorphism.ext
      simp only [comp_orbitMap, hgh]
  rw [heq]
  unfold orbitSection
  rw [translates_eq_iff, map_mul, map_inv]

end Langlands.GroupScheme.ProjectiveOrbit
