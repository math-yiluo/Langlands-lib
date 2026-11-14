import Langlands.GroupScheme.SplitUnipotentTorsor.VectorRetract
import Langlands.GroupScheme.VectorGroupQuotient
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # Finite projective tensor coordinates and actual vector-group retracts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.TensorCoordinates

variable {R : CommRingCat.{u}}
variable {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The tensor module of relative global sections with the fixed coefficient module. -/
abbrev Points (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M] [Module R M]
    (T : Over (Spec R)) :=
  ((algΓ R).obj T).unop ⊗[R] M

/-- Restriction on the global-section factor of tensor coordinates. -/
def pullback {T W : Over (Spec R)} (a : W ⟶ T) :
    Points R M T →ₗ[R] Points R M W :=
  TensorProduct.map (((algΓ R).map a).unop.hom.toLinearMap) LinearMap.id

/-- Extension of a coefficient-module map to relative global sections. -/
def moduleMap (f : M →ₗ[R] N) (T : Over (Spec R)) :
    Points R M T →ₗ[R] Points R N T :=
  TensorProduct.map LinearMap.id f

theorem pullback_moduleMap (f : M →ₗ[R] N) {T W : Over (Spec R)}
    (a : W ⟶ T) (x : Points R M T) :
    pullback a (moduleMap f T x) = moduleMap f W (pullback a x) := by
  simp only [pullback, moduleMap, TensorProduct.map_map, LinearMap.id_comp,
    LinearMap.comp_id]

/-- Naturality uses the actual algebra maps on relative global sections. -/
def IsNatural {V : GroupScheme (Spec R)}
    (e : ∀ T : Over (Spec R), (T ⟶ V.X) ≃* Multiplicative (Points R M T)) : Prop :=
  ∀ {T W : Over (Spec R)} (a : W ⟶ T) (x : T ⟶ V.X),
    (e W (a ≫ x)).toAdd = pullback a (e T x).toAdd

variable {V W : GroupScheme (Spec R)}
    (e : ∀ T : Over (Spec R), (T ⟶ V.X) ≃* Multiplicative (Points R M T))
    (d : ∀ T : Over (Spec R), (T ⟶ W.X) ≃* Multiplicative (Points R N T))

/-- A linear coefficient map gives a homomorphism on each group of points. -/
def pointMap (f : M →ₗ[R] N) (T : Over (Spec R)) : (T ⟶ V.X) →* (T ⟶ W.X) :=
  (d T).symm.toMonoidHom.comp
    ((AddMonoidHom.toMultiplicative (moduleMap f T).toAddMonoidHom).comp
      (e T).toMonoidHom)

@[simp]
theorem pointMap_coordinates (f : M →ₗ[R] N) (T : Over (Spec R)) (x : T ⟶ V.X) :
    (d T (pointMap e d f T x)).toAdd = moduleMap f T (e T x).toAdd :=
  congrArg Multiplicative.toAdd ((d T).apply_symm_apply _)

theorem pointMap_naturality (he : IsNatural e) (hd : IsNatural d)
    (f : M →ₗ[R] N) {T T' : Over (Spec R)} (a : T' ⟶ T) (x : T ⟶ V.X) :
    pointMap e d f T' (a ≫ x) = a ≫ pointMap e d f T x := by
  apply (d T').injective
  apply Multiplicative.toAdd.injective
  rw [pointMap_coordinates, he a x, hd, pointMap_coordinates, pullback_moduleMap]

/-- The actual group-scheme morphism induced by a linear coefficient map. -/
def hom (he : IsNatural e) (hd : IsNatural d) (f : M →ₗ[R] N) : V ⟶ W :=
  homOfPoints (pointMap e d f) (pointMap_naturality e d he hd f)

@[simp]
theorem hom_coordinates (he : IsNatural e) (hd : IsNatural d) (f : M →ₗ[R] N)
    (T : Over (Spec R)) (x : T ⟶ V.X) :
    (d T (x ≫ (hom e d he hd f).hom.hom)).toAdd =
      moduleMap f T (e T x).toAdd := by
  change (d T (x ≫ (homOfPoints (pointMap e d f)
    (pointMap_naturality e d he hd f)).hom.hom)).toAdd = _
  rw [comp_homOfPoints, pointMap_coordinates]

theorem hom_retract (he : IsNatural e) (hd : IsNatural d)
    (j : M →ₗ[R] N) (p : N →ₗ[R] M) (hjp : p ∘ₗ j = LinearMap.id) :
    hom e d he hd j ≫ hom d e hd he p = 𝟙 V := by
  apply hom_ext_points
  intro T x
  apply (e T).injective
  apply Multiplicative.toAdd.injective
  rw [Grp.comp_hom_hom, ← Category.assoc, hom_coordinates, hom_coordinates]
  simp only [moduleMap, TensorProduct.map_map, hjp, LinearMap.id_comp,
    TensorProduct.map_id, LinearMap.id_apply, Grp.id_hom_hom, Category.comp_id]

section Free

variable (R) (n : ℕ)

/-- Free tensor coordinates on the standard polynomial vector group. -/
def free :
    ∀ T : Over (Spec R),
      (T ⟶ (VectorGroup.groupScheme R n).X) ≃*
        Multiplicative (Points R (Fin n → R) T) :=
  fun T => (VectorGroup.coordinates R n T).trans
    (AddEquiv.toMultiplicative
      (TensorProduct.piScalarRight R R ((algΓ R).obj T).unop (Fin n)).symm.toAddEquiv)

@[simp]
theorem pi_free (T : Over (Spec R)) (x : T ⟶ (VectorGroup.groupScheme R n).X) :
    TensorProduct.piScalarRight R R ((algΓ R).obj T).unop (Fin n)
      (free R n T x).toAdd = (VectorGroup.coordinates R n T x).toAdd := by
  exact (TensorProduct.piScalarRight R R ((algΓ R).obj T).unop (Fin n)).apply_symm_apply _

theorem free_natural : IsNatural (free R n) := by
  intro T W a x
  apply (TensorProduct.piScalarRight R R ((algΓ R).obj W).unop (Fin n)).injective
  have hpi : ∀ z : Points R (Fin n → R) T,
      TensorProduct.piScalarRight R R ((algΓ R).obj W).unop (Fin n) (pullback a z) =
        fun i => a.left.appTop
          (TensorProduct.piScalarRight R R ((algΓ R).obj T).unop (Fin n) z i) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c m =>
      funext i
      simp only [pullback, TensorProduct.map_tmul, LinearMap.id_apply,
        TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
      exact ((((algΓ R).map a).unop.hom.toLinearMap).map_smul (m i) c).symm
    | add z z' hz hz' =>
      simp only [map_add, hz, hz', Pi.add_apply]
      funext i
      exact (map_add a.left.appTop.hom _ _).symm
  rw [hpi, pi_free, pi_free]
  exact VectorGroup.coordinates_comp a x

end Free

/-- A natural tensor-coordinate model of a finite projective module is an actual
group-scheme retract of a finite vector group. -/
theorem isFiniteVectorGroupRetract [Module.Finite R M] [Module.Projective R M]
    (he : IsNatural e) : IsFiniteVectorGroupRetract V := by
  obtain ⟨n, p, j, _, _, hjp⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  refine ⟨n, VectorGroup.groupScheme R n,
    hom e (free R n) he (free_natural R n) j,
    hom (free R n) e (free_natural R n) he p, ?_, ?_⟩
  · exact ⟨VectorGroup.coordinates R n, fun _ _ a x => VectorGroup.coordinates_comp a x⟩
  · exact hom_retract e (free R n) he (free_natural R n) j p hjp

/-- Finite projective tensor coordinates trivialize cocycles after every affine test. -/
theorem cocycle_isTrivial [Module.Finite R M] [Module.Projective R M]
    (he : IsNatural e) (T : Over (Spec R)) [IsAffine T.left]
    (U : Over T.left) [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (ξ : Cocycle ((GroupScheme.baseChange T.hom).obj V) U) : ξ.IsTrivial :=
  Cocycle.isTrivial_of_isFiniteVectorGroupRetract (isFiniteVectorGroupRetract e he) T U ξ

/-- An actual fpqc torsor under a finite projective tensor-coordinate group has a
section on every affine test scheme. -/
theorem exists_section [Module.Finite R M] [Module.Projective R M]
    (he : IsNatural e) (T : Over (Spec R)) [IsAffine T.left] (X : Over T.left)
    [ModObj ((GroupScheme.baseChange T.hom).obj V).X X] (hflat : Flat X.hom)
    (hsurj : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hX : IsIso (ModObj.leftSMul ((GroupScheme.baseChange T.hom).obj V).X X)) :
    ∃ s : T.left ⟶ X.left, s ≫ X.hom = 𝟙 T.left :=
  exists_section_of_isFiniteVectorGroupRetract (isFiniteVectorGroupRetract e he)
    T X hflat hsurj hqc hX

end Langlands.GroupScheme.TensorCoordinates
