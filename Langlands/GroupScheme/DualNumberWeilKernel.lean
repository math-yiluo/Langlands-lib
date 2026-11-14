import Langlands.GroupScheme.AffineWeilRestrictionMaps
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.KernelSquareTransport
import Langlands.AlgebraicGeometry.Picard.DualNumberBaseChange

/-! # The epsilon kernel in the Weil restriction of the additive group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.DualNumberWeil

variable (k : Type u) [Field k]

local instance dualNumber_finite : Module.Finite k (DualNumber k) := by
  change Module.Finite k (k × k)
  infer_instance

local instance dualNumber_projective : Module.Projective k (DualNumber k) := by
  change Module.Projective k (k × k)
  infer_instance

local instance additive_isAffine :
    IsAffine (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1).X.left := by
  change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin 1) (DualNumber k))))
  infer_instance

local instance additive_locallyOfFiniteType :
    LocallyOfFiniteType (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1).X.hom := by
  have : Smooth (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1).X.hom :=
    Corepresented.smooth_groupScheme_iff.mpr inferInstance
  infer_instance

/-- The actual affine Weil restriction of the additive group over `k[ε]`. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  AffineWeil.groupScheme k (DualNumber k)
    (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1)

variable (T : Type u) [CommRing T] [Algebra k T]

/-- Tensor extension of the dual numbers, with epsilon retained. -/
def tensorEquiv : DualNumber k ⊗[k] T ≃ₐ[k] DualNumber T :=
  (Algebra.TensorProduct.comm k (DualNumber k) T).trans
    ((Langlands.AlgebraicGeometry.Picard.DualNumberBaseChange.tensorEquiv k T).restrictScalars k)

@[simp]
theorem tensorEquiv_tmul (z : DualNumber k) (t : T) :
    tensorEquiv k T (z ⊗ₜ[k] t) =
      TrivSqZeroExt.inl t *
        GeneralLinear.DualNumber.coefficientMap (algebraMap k T) z := by
  exact Langlands.AlgebraicGeometry.Picard.DualNumberBaseChange.tensorTo_tmul k T t z

variable {T} {T' : Type u} [CommRing T'] [Algebra k T']

/-- The tensor comparison is natural for every coefficient algebra. -/
theorem tensorEquiv_naturality (f : T →ₐ[k] T') (z : DualNumber k ⊗[k] T) :
    tensorEquiv k T'
        (Algebra.TensorProduct.lTensor (S := DualNumber k) (DualNumber k) f z) =
      GeneralLinear.DualNumber.coefficientMap f.toRingHom (tensorEquiv k T z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tensorEquiv_tmul, map_mul]
    apply TrivSqZeroExt.ext <;>
      simp [GeneralLinear.DualNumber.coefficientMap_fst,
        GeneralLinear.DualNumber.coefficientMap_snd, f.commutes]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- A single coordinate can be read as its coefficient. -/
def singletonEquiv (A : Type u) [AddCommGroup A] :
    Multiplicative (Fin 1 → A) ≃* Multiplicative A where
  toFun x := Multiplicative.ofAdd (x.toAdd 0)
  invFun x := Multiplicative.ofAdd (fun _ => x.toAdd)
  left_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg x.toAdd (Subsingleton.elim 0 i)
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (T)

/-- Affine Weil-restriction points are actual dual numbers over the test algebra. -/
def affineCoordinates :
    (AffineWeil.pointFunctor k (DualNumber k)
      (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1)).obj
        (CommAlgCat.of (CommRingCat.of k) T) ≃* Multiplicative (DualNumber T) :=
  (Corepresented.affinePointsEquiv
    (VectorGroup.functor (CommRingCat.of (DualNumber k)) 1)
    (VectorGroup.corepresentableBy (CommRingCat.of (DualNumber k)) 1)
    (CommAlgCat.of (CommRingCat.of (DualNumber k)) (DualNumber k ⊗[k] T))).trans
      ((singletonEquiv _).trans (tensorEquiv k T).toAddEquiv.toMultiplicative)

variable {T}

/-- The explicit affine coordinates respect maps of the actual test algebra. -/
theorem affineCoordinates_naturality (f : T →ₐ[k] T')
    (p : (AffineWeil.pointFunctor k (DualNumber k)
      (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1)).obj
        (CommAlgCat.of (CommRingCat.of k) T)) :
    affineCoordinates k T'
      ((AffineWeil.pointFunctor k (DualNumber k)
        (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1)).map
          (CommAlgCat.ofHom f) p) =
      Multiplicative.ofAdd (GeneralLinear.DualNumber.coefficientMap f.toRingHom
        (affineCoordinates k T p).toAdd) := by
  let a : CommAlgCat.of (CommRingCat.of (DualNumber k)) (DualNumber k ⊗[k] T) ⟶
      CommAlgCat.of (CommRingCat.of (DualNumber k)) (DualNumber k ⊗[k] T') :=
    CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := DualNumber k) (DualNumber k) f)
  change Multiplicative.ofAdd (tensorEquiv k T'
    ((Corepresented.affinePointsEquiv
      (VectorGroup.functor (CommRingCat.of (DualNumber k)) 1)
      (VectorGroup.corepresentableBy (CommRingCat.of (DualNumber k)) 1)
      (CommAlgCat.of (CommRingCat.of (DualNumber k)) (DualNumber k ⊗[k] T'))
      ((algSpec (CommRingCat.of (DualNumber k))).map a.op ≫ p)).toAdd 0)) =
    Multiplicative.ofAdd (GeneralLinear.DualNumber.coefficientMap f.toRingHom
      (tensorEquiv k T ((Corepresented.affinePointsEquiv
        (VectorGroup.functor (CommRingCat.of (DualNumber k)) 1)
        (VectorGroup.corepresentableBy (CommRingCat.of (DualNumber k)) 1)
        (CommAlgCat.of (CommRingCat.of (DualNumber k)) (DualNumber k ⊗[k] T)) p).toAdd 0)))
  rw [Corepresented.affinePointsEquiv_naturality]
  exact congrArg Multiplicative.ofAdd
    (tensorEquiv_naturality k f _)

variable (S : Over (Spec (CommRingCat.of k)))

/-- Coordinates on every scheme test, including nonaffine and nonreduced tests. -/
def coordinates :
    (S ⟶ (groupScheme k).X) ≃* Multiplicative (DualNumber Γ(S.left, ⊤)) :=
  (Corepresented.pointsEquiv
    (AffineWeil.pointFunctor k (DualNumber k)
      (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1))
    (AffineWeil.corepresentableBy k (DualNumber k)
      (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1)) S).trans
    (affineCoordinates k (((algΓ (CommRingCat.of k)).obj S).unop))

variable {S}

/-- All-test dual-number coordinates commute with pullback of global functions. -/
theorem coordinates_comp {S' : Over (Spec (CommRingCat.of k))}
    (a : S' ⟶ S) (p : S ⟶ (groupScheme k).X) :
    coordinates k S' (a ≫ p) =
      Multiplicative.ofAdd (GeneralLinear.DualNumber.coefficientMap a.left.appTop.hom
        (coordinates k S p).toAdd) := by
  dsimp only [coordinates, MulEquiv.trans_apply]
  rw [Corepresented.pointsEquiv_naturality]
  exact affineCoordinates_naturality k (((algΓ (CommRingCat.of k)).map a).unop.hom) _

/-- Multiplication by epsilon on the additive dual-number group. -/
def epsilonHom (A : Type u) [CommRing A] :
    Multiplicative (DualNumber A) →* Multiplicative (DualNumber A) :=
  MonoidHom.mk' (fun z => Multiplicative.ofAdd (DualNumber.eps * z.toAdd))
    (fun x y => congrArg Multiplicative.ofAdd (mul_add _ x.toAdd y.toAdd))

variable (S)

/-- Multiplication by epsilon on actual points of the Weil restriction. -/
def epsilonPoints : (S ⟶ (groupScheme k).X) →* (S ⟶ (groupScheme k).X) :=
  (coordinates k S).symm.toMonoidHom.comp
    ((epsilonHom Γ(S.left, ⊤)).comp (coordinates k S).toMonoidHom)

@[simp]
theorem coordinates_epsilonPoints (p : S ⟶ (groupScheme k).X) :
    coordinates k S (epsilonPoints k S p) =
      Multiplicative.ofAdd (DualNumber.eps * (coordinates k S p).toAdd) :=
  (coordinates k S).apply_symm_apply _

variable {S}

theorem epsilonPoints_naturality {S' : Over (Spec (CommRingCat.of k))}
    (a : S' ⟶ S) (p : S ⟶ (groupScheme k).X) :
    epsilonPoints k S' (a ≫ p) = a ≫ epsilonPoints k S p := by
  apply (coordinates k S').injective
  rw [coordinates_epsilonPoints, coordinates_comp, coordinates_comp, coordinates_epsilonPoints]
  simp only [toAdd_ofAdd, map_mul,
    GeneralLinear.DualNumber.coefficientMap_eps]

/-- The actual scheme homomorphism which multiplies the dual-number coordinate by epsilon. -/
def epsilonMap : groupScheme k ⟶ groupScheme k :=
  homOfPoints (epsilonPoints k) (epsilonPoints_naturality k)

@[simp]
theorem coordinates_epsilonMap (p : S ⟶ (groupScheme k).X) :
    coordinates k S (p ≫ (epsilonMap k).hom.hom) =
      Multiplicative.ofAdd (DualNumber.eps * (coordinates k S p).toAdd) := by
  rw [epsilonMap, comp_homOfPoints]
  exact coordinates_epsilonPoints k S p

/-- The epsilon-annihilator consists exactly of dual numbers with zero constant term. -/
theorem epsilon_mul_eq_zero_iff {A : Type u} [CommRing A] (z : DualNumber A) :
    DualNumber.eps * z = 0 ↔ z.fst = 0 := by
  constructor
  · intro h
    have h' := congrArg TrivSqZeroExt.snd h
    simpa only [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps,
      zero_mul, one_mul, zero_add, TrivSqZeroExt.snd_zero] using h'
  · intro h
    apply TrivSqZeroExt.ext
    · simp
    · simp [h]

/-- The scheme map vanishes on a point exactly when its constant coordinate vanishes. -/
theorem epsilonMap_eq_one_iff (p : S ⟶ (groupScheme k).X) :
    p ≫ (epsilonMap k).hom.hom = 1 ↔ (coordinates k S p).toAdd.fst = 0 := by
  constructor
  · intro h
    apply (epsilon_mul_eq_zero_iff _).mp
    have h' := congrArg (fun q => (coordinates k S q).toAdd) h
    simpa only [coordinates_epsilonMap, map_one, toAdd_ofAdd, toAdd_one] using h'
  · intro h
    apply (coordinates k S).injective
    rw [coordinates_epsilonMap, map_one]
    exact congrArg Multiplicative.ofAdd ((epsilon_mul_eq_zero_iff _).mpr h)

variable (S)

/-- The pointwise kernel of the actual scheme map is the epsilon coefficient. -/
def epsilonKernelPointEquiv :
    (((yonedaGrp.map (epsilonMap k)).app (op S)).hom.ker) ≃*
      Multiplicative Γ(S.left, ⊤) where
  toFun x := Multiplicative.ofAdd (coordinates k S x.val).toAdd.snd
  invFun b := ⟨(coordinates k S).symm
    (Multiplicative.ofAdd (TrivSqZeroExt.inr b.toAdd)), by
      change (coordinates k S).symm _ ≫ (epsilonMap k).hom.hom = 1
      rw [epsilonMap_eq_one_iff, MulEquiv.apply_symm_apply]
      rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply (coordinates k S).injective
    rw [MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    apply TrivSqZeroExt.ext
    · exact ((epsilonMap_eq_one_iff k x.val).mp x.property).symm
    · rfl
  right_inv b := by
    change Multiplicative.ofAdd
      (coordinates k S ((coordinates k S).symm _)).toAdd.snd = b
    rw [MulEquiv.apply_symm_apply]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (coordinates k S (x.val * y.val)).toAdd.snd = _
    rw [map_mul]
    rfl

/-- Actual scheme-theoretic epsilon-kernel points are naturally one additive coordinate. -/
def kernelCoordinates :
    (S ⟶ (kernel (epsilonMap k)).X) ≃* Multiplicative Γ(S.left, ⊤) :=
  (kernelPointsEquiv (epsilonMap k) S).trans (epsilonKernelPointEquiv k S)

theorem kernelCoordinates_apply (p : S ⟶ (kernel (epsilonMap k)).X) :
    kernelCoordinates k S p =
      Multiplicative.ofAdd
        (coordinates k S (p ≫ (kernelι (epsilonMap k)).hom.hom)).toAdd.snd := rfl

variable {S}

/-- Epsilon coefficients commute with arbitrary scheme pullback. -/
theorem kernelCoordinates_comp {S' : Over (Spec (CommRingCat.of k))}
    (a : S' ⟶ S) (p : S ⟶ (kernel (epsilonMap k)).X) :
    kernelCoordinates k S' (a ≫ p) =
      Multiplicative.ofAdd (a.left.appTop (kernelCoordinates k S p).toAdd) := by
  rw [kernelCoordinates_apply, Category.assoc, coordinates_comp, kernelCoordinates_apply]
  rfl

variable (S)

/-- One vector coordinate on every scheme-theoretic kernel test. -/
def kernelVectorCoordinates :
    (S ⟶ (kernel (epsilonMap k)).X) ≃*
      Multiplicative (Fin 1 → Γ(S.left, ⊤)) :=
  (kernelCoordinates k S).trans (singletonEquiv _).symm

theorem kernel_isVectorGroup :
    RelativeRoot.IsVectorGroupOfDimension (kernel (epsilonMap k)) 1 := by
  refine ⟨kernelVectorCoordinates k, ?_⟩
  intro S S' a p
  funext i
  change (kernelCoordinates k S' (a ≫ p)).toAdd =
    a.left.appTop (kernelCoordinates k S p).toAdd
  rw [kernelCoordinates_comp]
  rfl

/-- The actual epsilon-kernel is isomorphic to the standard additive line. -/
def kernelIso : kernel (epsilonMap k) ≅ VectorGroup.groupScheme (CommRingCat.of k) 1 :=
  (kernel_isVectorGroup k).iso

theorem kernel_smooth : Smooth (kernel (epsilonMap k)).X.hom :=
  (kernel_isVectorGroup k).smooth

theorem kernel_connected : ConnectedSpace (kernel (epsilonMap k)).X.left :=
  (kernel_isVectorGroup k).connectedSpace

theorem kernel_unipotent : IsUnipotent (kernel (epsilonMap k)) :=
  (kernel_isVectorGroup k).isUnipotent

end Langlands.GroupScheme.DualNumberWeil
