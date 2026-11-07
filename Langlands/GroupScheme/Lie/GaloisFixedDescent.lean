import Langlands.GroupScheme.Lie.WeightLineGaloisCoordinates
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Mathlib.FieldTheory.Galois.Infinite

/-! # Effective Galois descent of actual Lie-kernel vectors -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

/-- The actual coefficient Lie vectors fixed by every coefficient automorphism. -/
def coefficientFixedLie : AddSubgroup (Additive (lieKernel G L)) where
  carrier := {x | ∀ σ : L ≃ₐ[k] L, lieKernelMapLinear G σ.toAlgHom x = x}
  zero_mem' := fun σ => map_zero _
  add_mem' := by
    intro x y hx hy σ
    rw [map_add, hx σ, hy σ]
  neg_mem' := by
    intro x hx σ
    rw [map_neg, hx σ]

/-- Coefficient extension of every original Lie vector is Galois fixed. -/
theorem lieKernelMapLinear_base_fixed (x : Additive (lieKernel G k)) (σ : L ≃ₐ[k] L) :
    lieKernelMapLinear G σ.toAlgHom (lieKernelMapLinear G (Algebra.ofId k L) x) =
      lieKernelMapLinear G (Algebra.ofId k L) x :=
  lieKernelMapLinear_base G σ.toAlgHom x

variable [LocallyOfFiniteType G.X.hom]

/-- Extension of actual Lie vectors is injective, as seen in natural finite coordinates. -/
theorem lieKernelMapLinear_base_injective :
    Function.Injective (lieKernelMapLinear G (Algebra.ofId k L)) := by
  let c := finiteCoordinates G
  intro x y h
  apply (c.equiv (CommAlgCat.of k k)).injective
  funext j
  apply (algebraMap k L).injective
  have hc := congrArg (fun z => c.equiv (CommAlgCat.of k L) z j) h
  have hn (z : Additive (lieKernel G k)) :
      c.equiv (CommAlgCat.of k L) (lieKernelMapLinear G (Algebra.ofId k L) z) =
        fun j => algebraMap k L (c.equiv (CommAlgCat.of k k) z j) :=
    c.naturality (CommAlgCat.ofHom (Algebra.ofId k L)) z
  exact (congrFun (hn x) j).symm.trans (hc.trans (congrFun (hn y) j))

variable [IsGalois k L]

/-- Every fixed actual coefficient Lie vector comes from a unique original-field
Lie vector. No finite-degree restriction on the Galois extension is needed. -/
theorem exists_lieKernelMapLinear_eq_of_fixed
    (x : coefficientFixedLie k L G) :
    ∃ y : Additive (lieKernel G k), lieKernelMapLinear G (Algebra.ofId k L) y = x.val := by
  let c := finiteCoordinates G
  have hc (j) : c.equiv (CommAlgCat.of k L) x.val j ∈ Set.range (algebraMap k L) := by
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro σ
    have hn :
        c.equiv (CommAlgCat.of k L) (lieKernelMapLinear G σ.toAlgHom x.val) =
          fun j => σ (c.equiv (CommAlgCat.of k L) x.val j) :=
      c.naturality (CommAlgCat.ofHom σ.toAlgHom) x.val
    rw [x.property σ] at hn
    exact congrFun hn.symm j
  let f : Fin (Module.finrank k (Additive (lieKernel G k))) → k :=
    fun j => (hc j).choose
  refine ⟨(c.equiv (CommAlgCat.of k k)).symm f, ?_⟩
  apply (c.equiv (CommAlgCat.of k L)).injective
  have hn :
      c.equiv (CommAlgCat.of k L)
          (lieKernelMapLinear G (Algebra.ofId k L) ((c.equiv (CommAlgCat.of k k)).symm f)) =
        fun j => algebraMap k L (c.equiv (CommAlgCat.of k k)
          ((c.equiv (CommAlgCat.of k k)).symm f) j) :=
    c.naturality (CommAlgCat.ofHom (Algebra.ofId k L)) _
  exact hn.trans (by
    rw [LinearEquiv.apply_symm_apply]
    funext j
    exact (hc j).choose_spec)

/-- Original actual Lie vectors are additively equivalent to all fixed
coefficient Lie vectors. The forward map is the original coefficient extension. -/
def coefficientFixedLieEquiv :
    Additive (lieKernel G k) ≃+ coefficientFixedLie k L G :=
  AddEquiv.ofBijective
    ({ toFun := fun x => ⟨lieKernelMapLinear G (Algebra.ofId k L) x,
         lieKernelMapLinear_base_fixed k L G x⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' := fun x y => Subtype.ext (map_add _ x y) } :
        Additive (lieKernel G k) →+ coefficientFixedLie k L G)
    ⟨fun x y h => lieKernelMapLinear_base_injective k L G (congrArg Subtype.val h),
      fun x => by
        obtain ⟨y, hy⟩ := exists_lieKernelMapLinear_eq_of_fixed k L G x
        exact ⟨y, Subtype.ext hy⟩⟩

@[simp]
theorem coefficientFixedLieEquiv_val (x : Additive (lieKernel G k)) :
    (coefficientFixedLieEquiv k L G x).val =
      lieKernelMapLinear G (Algebra.ofId k L) x := rfl

local notation "G_L" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

omit [LocallyOfFiniteType G.X.hom] [IsGalois k L] in
/-- Fixed vectors for the canonical semilinear action on the actual scheme
base change. -/
def baseChangeFixedLie : AddSubgroup (Additive (lieKernel G_L L)) where
  carrier := {x | ∀ σ : L ≃ₐ[k] L, baseChangeGaloisEquiv k L G σ x = x}
  zero_mem' := fun σ => (baseChangeGaloisEquiv k L G σ).map_zero
  add_mem' := by
    intro x y hx hy σ
    rw [(baseChangeGaloisEquiv k L G σ).map_add, hx σ, hy σ]
  neg_mem' := by
    intro x hx σ
    exact ((baseChangeGaloisEquiv k L G σ).map_neg x).trans (congrArg Neg.neg (hx σ))

omit [LocallyOfFiniteType G.X.hom] [IsGalois k L] in
/-- The actual pullback comparison identifies the two fixed-vector carriers. -/
def fixedLieBaseChangeEquiv :
    coefficientFixedLie k L G ≃+ baseChangeFixedLie k L G where
  toFun x := ⟨(kernelBaseChangeLinearEquiv k L G L).symm x.val, by
    intro σ
    rw [baseChangeGaloisEquiv_apply, LinearEquiv.apply_symm_apply, x.property σ]⟩
  invFun x := ⟨kernelBaseChangeLinearEquiv k L G L x.val, by
    intro σ
    have h := congrArg (kernelBaseChangeLinearEquiv k L G L) (x.property σ)
    simpa only [baseChangeGaloisEquiv_apply, LinearEquiv.apply_symm_apply] using h⟩
  left_inv x := Subtype.ext ((kernelBaseChangeLinearEquiv k L G L).apply_symm_apply x.val)
  right_inv x := Subtype.ext ((kernelBaseChangeLinearEquiv k L G L).symm_apply_apply x.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

/-- Effective Galois descent for the actual Lie kernel of the actual scheme
base change. Its forward map extends coefficients and applies the actual
pullback comparison. -/
def baseChangeFixedLieEquiv :
    Additive (lieKernel G k) ≃+ baseChangeFixedLie k L G :=
  (coefficientFixedLieEquiv k L G).trans (fixedLieBaseChangeEquiv k L G)

@[simp]
theorem baseChangeFixedLieEquiv_val (x : Additive (lieKernel G k)) :
    (baseChangeFixedLieEquiv k L G x).val =
      (kernelBaseChangeLinearEquiv k L G L).symm
        (lieKernelMapLinear G (Algebra.ofId k L) x) := rfl

end Langlands.GroupScheme.Lie
