import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

/-! # Unit kernels of ring maps with square-zero kernel -/

universe u v w u' v'

open CategoryTheory

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroUnitKernels

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- Every product of two elements of the actual ring-map kernel vanishes. -/
def SquareZeroKernel (f : R →+* S) : Prop :=
  ∀ a b : (RingHom.ker f), (a : R) * (b : R) = 0

lemma squareZeroKernel_iff_ker_sq_eq_bot (f : R →+* S) :
    SquareZeroKernel f ↔ (RingHom.ker f) ^ 2 = ⊥ := by
  rw [pow_two]
  constructor
  · intro h
    apply le_antisymm _ bot_le
    apply Ideal.mul_le.mpr
    intro a ha b hb
    exact Ideal.mem_bot.mpr (h ⟨a, ha⟩ ⟨b, hb⟩)
  · intro h a b
    have hab := Ideal.mul_mem_mul a.property b.property
    rw [h, Ideal.mem_bot] at hab
    exact hab

/-- The actual subgroup of units mapped to one. -/
abbrev UnitKernel (f : R →+* S) := (Units.map f.toMonoidHom).ker

lemma unitKernel_map_eq_one (f : R →+* S) (g : UnitKernel f) :
    f (g.val : R) = 1 :=
  congrArg (fun x : Sˣ ↦ (x : S)) g.property

/-- The unit `1 + a` has inverse `1 - a`, without a chosen splitting. -/
def oneAddUnit (f : R →+* S) (h : SquareZeroKernel f) (a : (RingHom.ker f)) : Rˣ where
  val := 1 + (a : R)
  inv := 1 - (a : R)
  val_inv := by
    calc
      (1 + (a : R)) * (1 - (a : R)) = 1 - (a : R) * (a : R) := by ring
      _ = 1 := by rw [h a a, sub_zero]
  inv_val := by
    calc
      (1 - (a : R)) * (1 + (a : R)) = 1 - (a : R) * (a : R) := by ring
      _ = 1 := by rw [h a a, sub_zero]

@[simp]
lemma oneAddUnit_val (f : R →+* S) (h : SquareZeroKernel f) (a : (RingHom.ker f)) :
    (oneAddUnit f h a : R) = 1 + (a : R) := rfl

lemma oneAddUnit_add (f : R →+* S) (h : SquareZeroKernel f) (a b : (RingHom.ker f)) :
    oneAddUnit f h (a + b) = oneAddUnit f h a * oneAddUnit f h b := by
  apply Units.ext
  change 1 + ((a : R) + (b : R)) = (1 + (a : R)) * (1 + (b : R))
  calc
    1 + ((a : R) + (b : R)) = 1 + (a : R) + (b : R) + (a : R) * (b : R) := by
      rw [h a b]
      ring
    _ = _ := by ring

/-- Additive kernel elements, written multiplicatively, are precisely the units
reducing to one. The inverse sends a unit to its value minus one. -/
def kernelEquiv (f : R →+* S) (h : SquareZeroKernel f) :
    Multiplicative (RingHom.ker f) ≃* UnitKernel f where
  toFun a := ⟨oneAddUnit f h a.toAdd, by
    apply Units.ext
    change f (1 + (a.toAdd : R)) = 1
    rw [map_add, map_one, RingHom.mem_ker.mp a.toAdd.property, add_zero]⟩
  invFun g := Multiplicative.ofAdd
    ⟨(g.val : R) - 1, by
      rw [RingHom.mem_ker, map_sub, unitKernel_map_eq_one, map_one, sub_self]⟩
  left_inv a := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change 1 + (a.toAdd : R) - 1 = (a.toAdd : R)
    ring
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    change 1 + ((g.val : R) - 1) = (g.val : R)
    ring
  map_mul' a b := Subtype.ext (oneAddUnit_add f h a.toAdd b.toAdd)

@[simp]
lemma kernelEquiv_val (f : R →+* S) (h : SquareZeroKernel f)
    (a : Multiplicative (RingHom.ker f)) :
    ((kernelEquiv f h a).val : R) = 1 + (a.toAdd : R) := rfl

@[simp]
lemma kernelEquiv_symm_val (f : R →+* S) (h : SquareZeroKernel f)
    (g : UnitKernel f) :
    ((kernelEquiv f h).symm g).toAdd.val = (g.val : R) - 1 := rfl

/-- The same equivalence in the additive notation used for abelian-group sheaves. -/
def kernelAddEquiv (f : R →+* S) (h : SquareZeroKernel f) :
    (RingHom.ker f) ≃+ Additive (UnitKernel f) where
  toFun a := Additive.ofMul (kernelEquiv f h (Multiplicative.ofAdd a))
  invFun g := ((kernelEquiv f h).symm g.toMul).toAdd
  left_inv a := congrArg Multiplicative.toAdd
    ((kernelEquiv f h).left_inv (Multiplicative.ofAdd a))
  right_inv g := congrArg Additive.ofMul ((kernelEquiv f h).right_inv g.toMul)
  map_add' a b := congrArg Additive.ofMul
    ((kernelEquiv f h).map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))

section CommutingSquare

variable {R' : Type u'} [CommRing R'] {S' : Type v'} [CommRing S']
  (f : R →+* S) (g : R' →+* S')
  (a : R →+* R') (b : S →+* S')
  (comm : g.comp a = b.comp f)

/-- A commuting ring-map square induces the restriction map on additive kernels. -/
def additiveKernelMap : (RingHom.ker f) →+ (RingHom.ker g) where
  toFun x := ⟨a x, by
    rw [RingHom.mem_ker]
    change (g.comp a) x = 0
    rw [comm]
    change b (f x) = 0
    rw [RingHom.mem_ker.mp x.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero a)
  map_add' x y := Subtype.ext (map_add a (x : R) (y : R))

/-- The same commuting square induces the actual map on unit kernels. -/
def unitKernelMap : UnitKernel f →* UnitKernel g where
  toFun x := ⟨Units.map a.toMonoidHom x.val, by
    apply Units.ext
    change g (a (x.val : R)) = 1
    change (g.comp a) (x.val : R) = 1
    rw [comm]
    change b (f (x.val : R)) = 1
    rw [unitKernel_map_eq_one, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

/-- The `1 + a` comparison commutes with every commuting square of ring maps. -/
lemma unitKernelMap_equiv (hf : SquareZeroKernel f) (hg : SquareZeroKernel g)
    (x : (RingHom.ker f)) :
    unitKernelMap f g a b comm (kernelEquiv f hf (Multiplicative.ofAdd x)) =
      kernelEquiv g hg (Multiplicative.ofAdd (additiveKernelMap f g a b comm x)) := by
  apply Subtype.ext
  apply Units.ext
  change a (1 + (x : R)) = 1 + a (x : R)
  rw [map_add, map_one]

end CommutingSquare

section Presheaves

variable {C : Type w} [Category.{v} C]
  {F G : Cᵒᵖ ⥤ CommRingCat.{u}} (η : F ⟶ G)

/-- Naturality of a ring-presheaf map, expressed as a commuting ring-map square. -/
lemma restriction_square {U V : Cᵒᵖ} (k : U ⟶ V) :
    (η.app V).hom.comp (F.map k).hom =
      (G.map k).hom.comp (η.app U).hom :=
  congrArg CommRingCat.Hom.hom (η.naturality k)

/-- The actual additive kernels of a map of ring presheaves. -/
def additiveKernelPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (RingHom.ker (η.app U).hom)
  map k := AddCommGrpCat.ofHom
    (additiveKernelMap _ _ (F.map k).hom (G.map k).hom (restriction_square η k))
  map_id U := by
    apply AddCommGrpCat.ext
    intro x
    apply Subtype.ext
    change (F.map (𝟙 U)).hom (x : F.obj U) = (x : F.obj U)
    simp
  map_comp {U V W} k l := by
    apply AddCommGrpCat.ext
    intro x
    apply Subtype.ext
    change (F.map (k ≫ l)).hom (x : F.obj U) =
      (F.map l).hom ((F.map k).hom (x : F.obj U))
    simp

/-- Units mapped to one on every object, with the actual restriction maps. -/
def unitKernelPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Additive (UnitKernel (η.app U).hom))
  map k := AddCommGrpCat.ofHom
    (unitKernelMap _ _ (F.map k).hom (G.map k).hom (restriction_square η k)).toAdditive
  map_id U := by
    apply AddCommGrpCat.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change (F.map (𝟙 U)).hom (x.toMul.val : F.obj U) = (x.toMul.val : F.obj U)
    simp
  map_comp {U V W} k l := by
    apply AddCommGrpCat.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change (F.map (k ≫ l)).hom (x.toMul.val : F.obj U) =
      (F.map l).hom ((F.map k).hom (x.toMul.val : F.obj U))
    simp

/-- The square-zero additive-kernel/unit-kernel comparison is an isomorphism
of presheaves of abelian groups on an arbitrary category. -/
def kernelPresheafIso (h : ∀ U, SquareZeroKernel (η.app U).hom) :
    additiveKernelPresheaf η ≅ unitKernelPresheaf η :=
  NatIso.ofComponents
    (fun U ↦ (kernelAddEquiv (η.app U).hom (h U)).toAddCommGrpIso) (by
      intro U V k
      apply AddCommGrpCat.ext
      intro x
      exact (congrArg Additive.ofMul
        (unitKernelMap_equiv (η.app U).hom (η.app V).hom
          (F.map k).hom (G.map k).hom (restriction_square η k) (h U) (h V) x)).symm)

end Presheaves

end Langlands.AlgebraicGeometry.Picard.SquareZeroUnitKernels
