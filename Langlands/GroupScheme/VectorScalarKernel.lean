import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.KernelSquareTransport
import Langlands.GroupScheme.KernelIsoGeometry
import Langlands.GroupScheme.Reductive.TrivialUnipotentRadical
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.IntegralModelReduction

/-! # Scalar transitions on vector groups and their residue kernels -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace VectorGroup

variable {R : CommRingCat.{u}} {n : ℕ}

theorem coefficientMap_comp {T W : Over (Spec R)} (f : W ⟶ T) :
    f.left.appTop.hom.comp (scalarMap T) = scalarMap W := by
  rw [scalarMap, scalarMap, ← CommRingCat.hom_comp, Category.assoc,
    ← Scheme.Hom.comp_appTop, Over.w]

/-- Multiplication by one scalar on every coordinate of every test. -/
def scalarPoints (c : R) (T : Over (Spec R)) :
    (T ⟶ (groupScheme R n).X) →* (T ⟶ (groupScheme R n).X) where
  toFun x := (coordinates R n T).symm
    (Multiplicative.ofAdd fun j => scalarMap T c * (coordinates R n T x).toAdd j)
  map_one' := by
    apply (coordinates R n T).injective
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MulEquiv.apply_symm_apply, map_one]
    change scalarMap T c * 0 = 0
    exact mul_zero _
  map_mul' x y := by
    apply (coordinates R n T).injective
    apply Multiplicative.toAdd.injective
    funext j
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact mul_add _ _ _

@[simp]
theorem scalarPoints_coord (c : R) (T : Over (Spec R))
    (x : T ⟶ (groupScheme R n).X) (j : Fin n) :
    (coordinates R n T (scalarPoints c T x)).toAdd j =
      scalarMap T c * (coordinates R n T x).toAdd j :=
  congrArg (fun y => y.toAdd j) ((coordinates R n T).apply_symm_apply _)

theorem scalarPoints_natural (c : R) {T W : Over (Spec R)} (f : W ⟶ T)
    (x : T ⟶ (groupScheme R n).X) :
    scalarPoints c W (f ≫ x) = f ≫ scalarPoints c T x := by
  apply points_ext
  intro j
  rw [scalarPoints_coord, coordinates_comp, coordinates_comp]
  dsimp only
  rw [scalarPoints_coord, map_mul]
  exact congrArg (fun a => a * f.left.appTop.hom ((coordinates R n T x).toAdd j))
    (congrArg (fun g : R →+* Γ(W.left, ⊤) => g c) (coefficientMap_comp f)).symm

/-- The actual group-scheme scalar endomorphism. -/
def scalar (c : R) : groupScheme R n ⟶ groupScheme R n :=
  homOfPoints (scalarPoints c) (scalarPoints_natural c)

@[simp]
theorem coordinates_scalar (c : R) (T : Over (Spec R))
    (x : T ⟶ (groupScheme R n).X) (j : Fin n) :
    (coordinates R n T (x ≫ (scalar c).hom.hom)).toAdd j =
      scalarMap T c * (coordinates R n T x).toAdd j := by
  rw [scalar, comp_homOfPoints, scalarPoints_coord]

@[simp]
theorem scalar_zero : scalar (n := n) (0 : R) = 0 := by
  apply hom_ext_points
  intro T x
  apply points_ext
  intro j
  rw [coordinates_scalar]
  rw [Grp.zero_hom, Mon.zero_hom, ← Hom.one_def, MonObj.comp_one, map_one]
  rw [map_zero]
  exact zero_mul _

@[simp]
theorem scalar_one : scalar (n := n) (1 : R) = 𝟙 _ := by
  apply hom_ext_points
  intro T x
  apply points_ext
  intro j
  rw [coordinates_scalar, Grp.id_hom_hom, Category.comp_id, map_one, one_mul]

theorem scalar_comp (c d : R) :
    scalar (n := n) c ≫ scalar d = scalar (c * d) := by
  apply hom_ext_points
  intro T x
  apply points_ext
  intro j
  rw [Grp.comp_hom_hom, ← Category.assoc, coordinates_scalar,
    coordinates_scalar, coordinates_scalar, map_mul]
  ring

/-- Scaling by a unit is an actual group-scheme isomorphism. -/
def scalarIso (c : Rˣ) : groupScheme R n ≅ groupScheme R n where
  hom := scalar (c : R)
  inv := scalar ((c⁻¹ : Rˣ) : R)
  hom_inv_id := by rw [scalar_comp, Units.mul_inv, scalar_one]
  inv_hom_id := by rw [scalar_comp, Units.inv_mul, scalar_one]

section BaseChange

variable {A : CommRingCat.{u}} (ρ : R ⟶ A)

/-- All-test coordinates for base change of the polynomial vector group. -/
def baseChangeCoordinates (T : Over (Spec A)) :
    (T ⟶ ((GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R n)).X) ≃*
      Multiplicative (Fin n → Γ(T.left, ⊤)) :=
  (baseChangePointsEquiv (Spec.map ρ) (groupScheme R n) T).trans
    (coordinates R n ((Over.map (Spec.map ρ)).obj T))

theorem baseChangeCoordinates_natural {T W : Over (Spec A)} (f : W ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R n)).X) :
    (baseChangeCoordinates ρ W (f ≫ x)).toAdd =
      fun j => f.left.appTop.hom ((baseChangeCoordinates ρ T x).toAdd j) := by
  simp only [baseChangeCoordinates, MulEquiv.trans_apply,
    baseChangePointsEquiv_naturality]
  rfl

private def baseChangePointEquiv (T : Over (Spec A)) :
    (T ⟶ ((GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R n)).X) ≃*
      (T ⟶ (groupScheme A n).X) :=
  (baseChangeCoordinates ρ T).trans (coordinates A n T).symm

private theorem baseChangePointEquiv_natural {T W : Over (Spec A)} (f : W ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R n)).X) :
    baseChangePointEquiv ρ W (f ≫ x) = f ≫ baseChangePointEquiv ρ T x := by
  apply points_ext
  intro j
  simp only [baseChangePointEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    coordinates_comp]
  exact congrFun (baseChangeCoordinates_natural ρ f x) j

/-- Base change of a vector group is canonically the vector group over the new ring. -/
def baseChangeIso :
    (GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R n) ≅ groupScheme A n :=
  isoOfPoints (baseChangePointEquiv ρ) (baseChangePointEquiv_natural ρ)

@[simp]
theorem coordinates_baseChangeIso_hom (T : Over (Spec A))
    (x : T ⟶ ((GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R n)).X) :
    coordinates A n T (x ≫ (baseChangeIso ρ).hom.hom.hom) =
      baseChangeCoordinates ρ T x := by
  rw [baseChangeIso, comp_isoOfPoints_hom]
  exact (coordinates A n T).apply_symm_apply _

theorem coefficientMap_map (T : Over (Spec A)) :
    scalarMap ((Over.map (Spec.map ρ)).obj T) =
      (scalarMap T).comp ρ.hom := by
  change ((Scheme.ΓSpecIso R).inv ≫ (T.hom ≫ Spec.map ρ).appTop).hom = _
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Scalar endomorphisms commute with base change with the actual coefficient map. -/
theorem scalar_baseChange (c : R) :
    (baseChangeIso (n := n) ρ).hom ≫ scalar (ρ.hom c) =
      (GroupScheme.baseChange (Spec.map ρ)).map (scalar c) ≫
        (baseChangeIso ρ).hom := by
  apply hom_ext_points
  intro T x
  apply points_ext
  intro j
  simp only [Grp.comp_hom_hom, ← Category.assoc, coordinates_scalar,
    coordinates_baseChangeIso_hom]
  change scalarMap T (ρ.hom c) *
      (baseChangeCoordinates ρ T x).toAdd j =
    (coordinates R n ((Over.map (Spec.map ρ)).obj T)
      (baseChangePointsEquiv (Spec.map ρ) (groupScheme R n) T
        (x ≫ ((GroupScheme.baseChange (Spec.map ρ)).map (scalar c)).hom.hom))).toAdd j
  rw [baseChangePointsEquiv_comp, coordinates_scalar, coefficientMap_map]
  rfl

end BaseChange
end VectorGroup

/-- The actual scheme kernel of the zero homomorphism is its source group. -/
def zeroKernelIso {S : Scheme.{u}} (G H : GroupScheme S) :
    kernel (0 : G ⟶ H) ≅ G where
  hom := kernelι 0
  inv := pullback.lift (𝟙 G) 0 (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · change (pullback.fst _ _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _ =
        𝟙 _ ≫ pullback.fst _ _
      rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · apply Subsingleton.elim
  inv_hom_id := pullback.lift_fst _ _ _

namespace VectorGroup

variable {k : Type u} [Field k] (n : ℕ)

/-- A scalar transition over a field has a smooth connected unipotent actual kernel. -/
theorem scalar_kernel_properties (c : k) :
    Smooth (kernel (scalar (R := CommRingCat.of k) (n := n) c)).X.hom ∧
      ConnectedSpace (kernel (scalar (R := CommRingCat.of k) (n := n) c)).X.left ∧
        IsUnipotent (kernel (scalar (R := CommRingCat.of k) (n := n) c)) := by
  by_cases hc : c = 0
  · subst c
    rw [scalar_zero]
    let hv : RelativeRoot.IsVectorGroupOfDimension
        (groupScheme (CommRingCat.of k) n) n :=
      ⟨coordinates (CommRingCat.of k) n, isNaturalVectorCoordinates⟩
    exact smooth_connected_unipotent_of_groupIso (zeroKernelIso _ _)
      ⟨hv.smooth, hv.connectedSpace, isUnipotent k n⟩
  · have he : (scalarIso (n := n) (Units.mk0 c hc)).hom =
        scalar (R := CommRingCat.of k) (n := n) c := rfl
    have : IsIso (scalar (R := CommRingCat.of k) (n := n) c) := by
      rw [← he]
      infer_instance
    have : IsIso (pullback.snd
        (scalar (R := CommRingCat.of k) (n := n) c) (kernelUnit _)) :=
      pullback_snd_iso_of_left_iso _ _
    exact ⟨(smooth_isAffineHom_kernel_of_isIso _).1,
      connectedSpace_kernel_of_isIso _,
      isUnipotent_trivial.of_iso (asIso
        (pullback.snd (scalar (R := CommRingCat.of k) (n := n) c) (kernelUnit _)))⟩

/-- The same kernel calculation after any ring-to-field specialization. -/
theorem scalar_baseChange_kernel_properties {R : CommRingCat.{u}}
    (ρ : R ⟶ CommRingCat.of k) (c : R) :
    Smooth (kernel ((GroupScheme.baseChange (Spec.map ρ)).map
      (scalar (n := n) c))).X.hom ∧
      ConnectedSpace (kernel ((GroupScheme.baseChange (Spec.map ρ)).map
        (scalar (n := n) c))).X.left ∧
      IsUnipotent (kernel ((GroupScheme.baseChange (Spec.map ρ)).map
        (scalar (n := n) c))) := by
  exact smooth_connected_unipotent_of_groupIso
    (kernelSquareIso _ _ (baseChangeIso ρ) (baseChangeIso ρ)
      (scalar_baseChange ρ c)) (scalar_kernel_properties n (ρ.hom c))

end VectorGroup
end Langlands.GroupScheme
