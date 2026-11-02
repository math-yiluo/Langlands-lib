import Langlands.GroupScheme.Lie.DualNumberKernel

/-! # The module structure on the actual affine Lie kernel -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable {A B C : Type u} [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

/-- Algebra maps which jointly distinguish coefficients also distinguish points
of an affine target. -/
theorem affineMap_jointly_injective [IsAffineHom G.X.hom]
    (f : A →ₐ[R] B) (g : A →ₐ[R] C)
    (hfg : Function.Injective (fun a : A => (f a, g a)))
    {x y : AffinePoints G A}
    (hf : affineMap G f x = affineMap G f y)
    (hg : affineMap G g x = affineMap G g y) : x = y := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨D, ⟨e⟩⟩ := (essImage_algSpec (G := G.X)).mpr this
  let a := algSpec.fullyFaithful.preimage (x ≫ e.inv)
  let b := algSpec.fullyFaithful.preimage (y ≫ e.inv)
  have ha : (algSpec R).map a = x ≫ e.inv :=
    algSpec.fullyFaithful.map_preimage _
  have hb : (algSpec R).map b = y ≫ e.inv :=
    algSpec.fullyFaithful.map_preimage _
  have hf' : (CommAlgCat.ofHom f).op ≫ a = (CommAlgCat.ofHom f).op ≫ b := by
    apply (algSpec R).map_injective
    simpa only [Functor.map_comp, ha, hb, Category.assoc, affineMap_apply] using
      congrArg (fun z => z ≫ e.inv) hf
  have hg' : (CommAlgCat.ofHom g).op ≫ a = (CommAlgCat.ofHom g).op ≫ b := by
    apply (algSpec R).map_injective
    simpa only [Functor.map_comp, ha, hb, Category.assoc, affineMap_apply] using
      congrArg (fun z => z ≫ e.inv) hg
  have hab : a = b := by
    apply Quiver.Hom.unop_inj
    ext d
    apply hfg
    exact Prod.ext
      (ConcreteCategory.congr_hom (congrArg Quiver.Hom.unop hf') d)
      (ConcreteCategory.congr_hom (congrArg Quiver.Hom.unop hg') d)
  apply (cancel_mono e.inv).mp
  rw [← ha, ← hb, hab]

variable {M N P : Type u} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
  [Module R M] [Module Aᵐᵒᵖ M] [IsCentralScalar A M]
  [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]
  [Module R N] [Module Aᵐᵒᵖ N] [IsCentralScalar A N]
  [IsScalarTower R A N] [IsScalarTower R Aᵐᵒᵖ N]
  [Module R P] [Module Aᵐᵒᵖ P] [IsCentralScalar A P]
  [IsScalarTower R A P] [IsScalarTower R Aᵐᵒᵖ P]

/-- A linear map on the square-zero ideal gives an actual test-algebra map. -/
def squareMap (f : M →ₗ[A] N) :
    TrivSqZeroExt A M →ₐ[R] TrivSqZeroExt A N :=
  (TrivSqZeroExt.map f).restrictScalars R

@[simp] theorem squareMap_fst (f : M →ₗ[A] N) (z : TrivSqZeroExt A M) :
    (squareMap (R := R) f z).fst = z.fst := TrivSqZeroExt.fst_map f z

@[simp] theorem squareMap_snd (f : M →ₗ[A] N) (z : TrivSqZeroExt A M) :
    (squareMap (R := R) f z).snd = f z.snd := TrivSqZeroExt.snd_map f z

theorem squareMap_comp (f : M →ₗ[A] N) (g : N →ₗ[A] P) :
    squareMap (R := R) (g.comp f) = (squareMap g).comp (squareMap f) := by
  apply AlgHom.ext
  intro z
  apply TrivSqZeroExt.ext <;> simp

theorem squareMap_id :
    squareMap (R := R) (LinearMap.id : M →ₗ[A] M) =
      AlgHom.id R (TrivSqZeroExt A M) := by
  apply AlgHom.ext
  intro z
  apply TrivSqZeroExt.ext <;> simp

theorem squareMap_zero :
    squareMap (R := R) (0 : M →ₗ[A] N) =
      (TrivSqZeroExt.inlAlgHom R A N).comp (TrivSqZeroExt.fstHom R A M) := by
  apply AlgHom.ext
  intro z
  apply TrivSqZeroExt.ext <;> simp

/-- The point homomorphism induced by a linear map of square-zero ideals. -/
abbrev squarePointMap (f : M →ₗ[A] N) :
    AffinePoints G (TrivSqZeroExt A M) →*
      AffinePoints G (TrivSqZeroExt A N) :=
  affineMap G (squareMap f)

@[simp] theorem squarePointMap_id (x : AffinePoints G (TrivSqZeroExt A M)) :
    squarePointMap G (LinearMap.id : M →ₗ[A] M) x = x := by
  rw [squarePointMap, squareMap_id, affineMap_id]

theorem squarePointMap_comp (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (x : AffinePoints G (TrivSqZeroExt A M)) :
    squarePointMap G (g.comp f) x =
      squarePointMap G g (squarePointMap G f x) := by
  simp only [squarePointMap, squareMap_comp, affineMap_comp]

@[simp] theorem squarePointMap_zero (x : lieKernel G A) :
    squarePointMap G (0 : A →ₗ[A] N) x.val = 1 := by
  rw [squarePointMap, squareMap_zero, affineMap_comp]
  change affineMap G (TrivSqZeroExt.inlAlgHom R A N) (reduction G x.val) = 1
  rw [x.property, map_one]

/-- The projections from two independent infinitesimals jointly distinguish
actual points of an affine group scheme. -/
theorem squarePair_ext [IsAffineHom G.X.hom]
    {x y : AffinePoints G (TrivSqZeroExt A (A × A))}
    (h₁ : affineMap G (squareMap (LinearMap.fst A A A)) x =
      affineMap G (squareMap (LinearMap.fst A A A)) y)
    (h₂ : affineMap G (squareMap (LinearMap.snd A A A)) x =
      affineMap G (squareMap (LinearMap.snd A A A)) y) : x = y := by
  apply affineMap_jointly_injective G _ _ ?_ h₁ h₂
  intro z w h
  apply TrivSqZeroExt.ext
  · simpa using congrArg (fun p : DualNumber A × DualNumber A => p.1.fst) h
  · apply Prod.ext
    · simpa using congrArg (fun p : DualNumber A × DualNumber A => p.1.snd) h
    · simpa using congrArg (fun p : DualNumber A × DualNumber A => p.2.snd) h

/-- Independent infinitesimal directions commute. -/
theorem squarePointMap_inl_inr_comm [IsAffineHom G.X.hom] (x y : lieKernel G A) :
    squarePointMap G (LinearMap.inl A A A) x.val *
        squarePointMap G (LinearMap.inr A A A) y.val =
      squarePointMap G (LinearMap.inr A A A) y.val *
        squarePointMap G (LinearMap.inl A A A) x.val := by
  apply squarePair_ext G
  all_goals
    simp only [map_mul, ← squarePointMap_comp, LinearMap.fst_comp_inl,
      LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr,
      squarePointMap_id, squarePointMap_zero, one_mul, mul_one]

/-- A repeated tangent vector is the product of its two independent inclusions. -/
theorem squarePointMap_diagonal [IsAffineHom G.X.hom] (x : lieKernel G A) :
    squarePointMap G (LinearMap.id.prod LinearMap.id : A →ₗ[A] A × A) x.val =
      squarePointMap G (LinearMap.inl A A A) x.val *
        squarePointMap G (LinearMap.inr A A A) x.val := by
  apply squarePair_ext G
  all_goals
    simp only [map_mul, ← squarePointMap_comp, LinearMap.fst_prod,
      LinearMap.snd_prod, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, squarePointMap_id,
      squarePointMap_zero, one_mul, mul_one]

/-- Addition of linear maps of the square-zero ideal is the group law on
infinitesimal points. -/
theorem squarePointMap_add [IsAffineHom G.X.hom]
    (f g : A →ₗ[A] N) (x : lieKernel G A) :
    squarePointMap G (f + g) x.val =
      squarePointMap G f x.val * squarePointMap G g x.val := by
  have h := congrArg (squarePointMap G (f.coprod g)) (squarePointMap_diagonal G x)
  simpa only [map_mul, ← squarePointMap_comp, LinearMap.coprod_comp_prod,
    LinearMap.comp_id, LinearMap.coprod_inl, LinearMap.coprod_inr] using h

end Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable {A : Type u} [CommRing A] [Algebra R A]

/-- The actual group law on an affine identity kernel is commutative. -/
theorem lieKernel_mul_comm [IsAffineHom G.X.hom] (x y : lieKernel G A) :
    x * y = y * x := by
  apply Subtype.ext
  change x.val * y.val = y.val * x.val
  have h := congrArg
    (Lie.squarePointMap G ((LinearMap.id : A →ₗ[A] A).coprod LinearMap.id))
    (Lie.squarePointMap_inl_inr_comm G x y)
  simpa only [map_mul, ← Lie.squarePointMap_comp, LinearMap.coprod_inl,
    LinearMap.coprod_inr, Lie.squarePointMap_id] using h

/-- The commutative group structure retains exactly the original kernel operations. -/
instance lieKernelCommGroup [IsAffineHom G.X.hom] : CommGroup (lieKernel G A) :=
  { (inferInstance : Group (lieKernel G A)) with mul_comm := lieKernel_mul_comm G }

@[simp] theorem lieKernelScale_one (x : lieKernel G A) :
    lieKernelScale G 1 x = x := by
  apply Subtype.ext
  change Lie.squarePointMap G (1 • (LinearMap.id : A →ₗ[A] A)) x.val = x.val
  simp only [one_smul, Lie.squarePointMap_id]

theorem lieKernelScale_mul (c d : A) (x : lieKernel G A) :
    lieKernelScale G (c * d) x = lieKernelScale G c (lieKernelScale G d x) := by
  apply Subtype.ext
  change Lie.squarePointMap G ((c * d) • (LinearMap.id : A →ₗ[A] A)) x.val =
    Lie.squarePointMap G (c • (LinearMap.id : A →ₗ[A] A))
      (Lie.squarePointMap G (d • (LinearMap.id : A →ₗ[A] A)) x.val)
  have hlin : (c • (LinearMap.id : A →ₗ[A] A)).comp (d • LinearMap.id) =
      (c * d) • LinearMap.id := by
    apply LinearMap.ext
    intro a
    simp [mul_assoc]
  rw [← Lie.squarePointMap_comp, hlin]

@[simp] theorem lieKernelScale_zero (x : lieKernel G A) :
    lieKernelScale G 0 x = 1 := by
  apply Subtype.ext
  change Lie.squarePointMap G (0 • (LinearMap.id : A →ₗ[A] A)) x.val = 1
  simp only [zero_smul, Lie.squarePointMap_zero]

theorem lieKernelScale_add [IsAffineHom G.X.hom] (c d : A) (x : lieKernel G A) :
    lieKernelScale G (c + d) x = lieKernelScale G c x * lieKernelScale G d x := by
  apply Subtype.ext
  change Lie.squarePointMap G ((c + d) • (LinearMap.id : A →ₗ[A] A)) x.val =
    Lie.squarePointMap G (c • (LinearMap.id : A →ₗ[A] A)) x.val *
      Lie.squarePointMap G (d • (LinearMap.id : A →ₗ[A] A)) x.val
  rw [add_smul, Lie.squarePointMap_add]

/-- Scalar multiplication is induced by the actual epsilon-scaling algebra map. -/
instance lieKernelSMul : SMul A (Additive (lieKernel G A)) where
  smul c x := Additive.ofMul (lieKernelScale G c x.toMul)

@[simp] theorem lieKernel_smul_toMul (c : A) (x : Additive (lieKernel G A)) :
    (c • x).toMul = lieKernelScale G c x.toMul := rfl

/-- The actual affine dual-number kernel is a module, with its existing group law
as addition and epsilon scaling as scalar multiplication. -/
instance lieKernelModule [IsAffineHom G.X.hom] :
    Module A (Additive (lieKernel G A)) where
  one_smul x := congrArg Additive.ofMul (lieKernelScale_one G x.toMul)
  mul_smul c d x := congrArg Additive.ofMul (lieKernelScale_mul G c d x.toMul)
  smul_zero c := congrArg Additive.ofMul ((lieKernelScale G c).map_one)
  smul_add c x y :=
    congrArg Additive.ofMul ((lieKernelScale G c).map_mul x.toMul y.toMul)
  add_smul c d x := congrArg Additive.ofMul (lieKernelScale_add G c d x.toMul)
  zero_smul x := congrArg Additive.ofMul (lieKernelScale_zero G x.toMul)

variable {B : Type u} [CommRing B] [Algebra R B]

/-- Epsilon scaling commutes with coefficient change, including nonunit scalars. -/
theorem lieKernelMap_scale (f : A →ₐ[R] B) (c : A) (x : lieKernel G A) :
    lieKernelMap G f (lieKernelScale G c x) =
      lieKernelScale G (f c) (lieKernelMap G f x) := by
  apply Subtype.ext
  simp only [lieKernelMap_val, lieKernelScale_val, ← Lie.affineMap_comp]
  have he : (GeneralLinear.DualNumber.coefficientAlgMap f).comp
      (GeneralLinear.DualNumber.epsilonScaleAlg c) =
      (GeneralLinear.DualNumber.epsilonScaleAlg (f c)).comp
        (GeneralLinear.DualNumber.coefficientAlgMap f) := by
    apply AlgHom.ext
    intro z
    apply TrivSqZeroExt.ext <;>
      simp [GeneralLinear.DualNumber.coefficientAlgMap,
        GeneralLinear.DualNumber.epsilonScaleAlg]
  rw [he]

/-- Coefficient change on the actual kernels is semilinear. -/
def lieKernelMapLinear [IsAffineHom G.X.hom] (f : A →ₐ[R] B) :
    Additive (lieKernel G A) →ₛₗ[f.toRingHom] Additive (lieKernel G B) where
  toFun x := Additive.ofMul (lieKernelMap G f x.toMul)
  map_add' x y := congrArg Additive.ofMul ((lieKernelMap G f).map_mul x.toMul y.toMul)
  map_smul' c x := congrArg Additive.ofMul (lieKernelMap_scale G f c x.toMul)

@[simp] theorem lieKernelMapLinear_toMul [IsAffineHom G.X.hom] (f : A →ₐ[R] B)
    (x : Additive (lieKernel G A)) :
    (lieKernelMapLinear G f x).toMul = lieKernelMap G f x.toMul := rfl

end Langlands.GroupScheme
