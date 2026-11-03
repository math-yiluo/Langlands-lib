import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Torus.UniversalPoint
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.Weights
import Langlands.GroupScheme.Lie.GroupAlgebraCoordinates
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # A finite bound for the ranks of actual split subtori -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace Lie

section TargetMaps

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
variable (f : G ⟶ H) (A : Type u) [CommRing A] [Algebra R A]

/-- Postcomposition restricts to the actual dual-number identity kernels. -/
def targetMap : lieKernel G A →* lieKernel H A where
  toFun x := ⟨x.val ≫ f.hom.hom, by
    change reduction H (x.val ≫ f.hom.hom) = 1
    change (affineMap G (TrivSqZeroExt.fstHom R A A) x.val) ≫ f.hom.hom = 1
    change reduction G x.val ≫ f.hom.hom = 1
    rw [x.property, MonObj.one_comp]⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp _ _ _)

/-- The map of identity kernels is linear for the actual epsilon-scaling actions. -/
def targetMapLinear [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] :
    Additive (lieKernel G A) →ₗ[A] Additive (lieKernel H A) where
  toFun x := Additive.ofMul (targetMap f A x.toMul)
  map_add' x y := congrArg Additive.ofMul ((targetMap f A).map_mul x.toMul y.toMul)
  map_smul' c x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- A monomorphism on underlying schemes is injective on the actual Lie kernels. -/
theorem targetMapLinear_injective [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Mono f.hom.hom] : Function.Injective (targetMapLinear f A) := by
  intro x y h
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (cancel_mono f.hom.hom).mp (congrArg (fun z => z.toMul.val) h)

end TargetMaps

section FiniteDimension

attribute [local instance] coordinateOriginAlgebra

variable (k : Type u) [Field k]
variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

/-- The Lie kernel of an affine finite-type group over a field is finite dimensional. -/
theorem finiteDimensional_lieKernel : FiniteDimensional k (Additive (lieKernel G k)) := by
  classical
  let : Algebra.FiniteType k (coordinateAlgebra G) := coordinateAlgebraFiniteType G
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out
    (R := k) (A := coordinateAlgebra G)
  let ev : Additive (lieKernel G k) →ₗ[k] (s → k) :=
    { toFun := fun x c => kernelDerivationLinearEquiv G x c
      map_add' := fun x y => by ext c; simp
      map_smul' := fun c x => by ext d; simp }
  apply FiniteDimensional.of_injective ev
  intro x y h
  apply (kernelDerivationLinearEquiv G).injective
  apply Derivation.ext_of_adjoin_eq_top (s : Set (coordinateAlgebra G)) hs
  intro c hc
  exact congrFun h ⟨c, hc⟩

end FiniteDimension

end Lie

namespace splitTorus

variable {R : CommRingCat.{u}} (I : Type u) [Finite I]
variable (A : Type u) [CommRing A] [Algebra R A]

local instance : IsAffineHom (splitTorus (Spec R) I).X.hom :=
  isAffineHom_splitTorus_spec R I

/-- The dual-number unit with constant coefficient one and infinitesimal coefficient `a`. -/
def infinitesimalUnit (a : A) : (DualNumber A)ˣ where
  val := ⟨1, a⟩
  inv := ⟨1, -a⟩
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

@[simp] theorem infinitesimalUnit_mul (a b : A) :
    infinitesimalUnit A (a + b) = infinitesimalUnit A a * infinitesimalUnit A b := by
  apply Units.ext
  ext <;> simp [infinitesimalUnit, add_comm]

/-- Independent infinitesimal unit coordinates define a point of the actual identity kernel. -/
def infinitesimalPoint (v : I → A) : lieKernel (splitTorus (Spec R) I) A :=
  ⟨(algebraPointsEquiv I (DualNumber A)).symm (fun i => infinitesimalUnit A (v i)), by
    apply (algebraPointsEquiv I A).injective
    rw [Lie.reduction, algebraPointsEquiv_naturality, MulEquiv.apply_symm_apply, map_one]
    funext i
    apply Units.ext
    rfl⟩

/-- Coordinate tangent vectors map linearly into the actual Lie kernel of a split torus. -/
def infinitesimalLinear : (I → A) →ₗ[A]
    Additive (lieKernel (splitTorus (Spec R) I) A) where
  toFun v := Additive.ofMul (infinitesimalPoint (R := R) I A v)
  map_add' v w := by
    apply Additive.toMul.injective
    change infinitesimalPoint (R := R) I A (v + w) =
      infinitesimalPoint (R := R) I A v * infinitesimalPoint (R := R) I A w
    apply Subtype.ext
    change (algebraPointsEquiv I (DualNumber A)).symm _ =
      (algebraPointsEquiv I (DualNumber A)).symm _ *
        (algebraPointsEquiv I (DualNumber A)).symm _
    apply (algebraPointsEquiv I (DualNumber A)).injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    funext i
    exact infinitesimalUnit_mul A _ _
  map_smul' c v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply (algebraPointsEquiv I (DualNumber A)).injective
    change _ = algebraPointsEquiv I (DualNumber A)
      (Lie.affineMap _ (GeneralLinear.DualNumber.epsilonScaleAlg c) _)
    rw [algebraPointsEquiv_naturality]
    simp only [infinitesimalPoint]
    funext i
    apply Units.ext
    ext <;> simp [infinitesimalUnit, GeneralLinear.DualNumber.epsilonScaleAlg,
      GeneralLinear.DualNumber.epsilonScale]

/-- Independent infinitesimal coordinates remain distinct on actual points. -/
theorem infinitesimalLinear_injective :
    Function.Injective (infinitesimalLinear (R := R) I A) := by
  intro v w h
  have h' := congrArg
    (fun z => algebraPointsEquiv I (DualNumber A) z.toMul.val) h
  change (algebraPointsEquiv I (DualNumber A))
      ((algebraPointsEquiv I (DualNumber A)).symm (fun i => infinitesimalUnit A (v i))) =
    (algebraPointsEquiv I (DualNumber A))
      ((algebraPointsEquiv I (DualNumber A)).symm (fun i => infinitesimalUnit A (w i))) at h'
  simp only [MulEquiv.apply_symm_apply] at h'
  funext i
  exact congrArg (fun x : (DualNumber A)ˣ => x.val.snd) (congrFun h' i)

variable {k : Type u} [Field k]
variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A closed split torus has rank at most the dimension of the actual ambient Lie kernel. -/
theorem card_le_finrank_lieKernel
    [FiniteDimensional k (Additive (lieKernel G k))]
    (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (hi : IsClosedSubgroup i) :
    Nat.card I ≤ Module.finrank k (Additive (lieKernel G k)) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let f := (Lie.targetMapLinear i k).comp
    (infinitesimalLinear (R := CommRingCat.of k) I k)
  have hf : Function.Injective f :=
    (Lie.targetMapLinear_injective i k).comp (infinitesimalLinear_injective I k)
  let := Fintype.ofFinite I
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
    LinearMap.finrank_le_finrank_of_injective hf

end splitTorus

/-- The split rank of an affine finite-type group over a field has a finite bound. -/
theorem splitRank_le_finrank_lieKernel
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    splitRank G ≤ (Module.finrank k (Additive (lieKernel G k)) : ℕ∞) := by
  let := Lie.finiteDimensional_lieKernel k G
  refine iSup_le fun I => iSup_le fun _ => iSup_le fun i => iSup_le fun hi => ?_
  exact_mod_cast splitTorus.card_le_finrank_lieKernel I i hi

end Langlands.GroupScheme
