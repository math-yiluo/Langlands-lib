import Langlands.AbelianScheme.Kernel
import Langlands.GroupScheme.Torus.Lattice

/-! # Homomorphisms and cocharacters of actual group-scheme kernels -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CommGroupScheme

open Langlands.GroupScheme

variable {S : Scheme.{u}} {P G H : CommGroupScheme S} (f : G ⟶ H)

/-- The actual scheme kernel, equipped with its inherited commutativity. -/
abbrev kernel : CommGroupScheme S where
  toGrp := GroupScheme.kernel (groupHom f)

/-- The inclusion of the actual scheme kernel in the commutative category. -/
def kernelι : kernel f ⟶ G := Additive.ofMul (GroupScheme.kernelι (groupHom f))

@[simp] theorem kernelι_comp : kernelι f ≫ f = 0 := by
  apply CommGroupScheme.hom_ext_points
  intro T x
  rw [comp_groupHom_comp, comp_groupHom_zero]
  exact (kernelPointsEquiv (groupHom f) T x).property

/-- Maps to the actual kernel are determined by their composites with inclusion. -/
theorem kernel_hom_ext {g h : P ⟶ kernel f} (w : g ≫ kernelι f = h ≫ kernelι f) :
    g = h := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply (cancel_mono (GroupScheme.kernelι (groupHom f)).hom.hom).mp
  exact congrArg (fun j => (groupHom j).hom.hom) w

private def kernelLiftPoints (g : P ⟶ G) (w : g ≫ f = 0) (T : Over S) :
    (T ⟶ P.X) →* (T ⟶ (kernel f).X) :=
  (kernelPointsEquiv (groupHom f) T).symm.toMonoidHom.comp
    { toFun x := ⟨x ≫ (groupHom g).hom.hom, by
        change (x ≫ (groupHom g).hom.hom) ≫ (groupHom f).hom.hom = 1
        rw [← comp_groupHom_comp, w, comp_groupHom_zero]⟩
      map_one' := Subtype.ext (CategoryTheory.MonObj.one_comp _)
      map_mul' x y := Subtype.ext (CategoryTheory.MonObj.mul_comp _ _ _) }

private theorem kernelLiftPoints_ι (g : P ⟶ G) (w : g ≫ f = 0)
    (T : Over S) (x : T ⟶ P.X) :
    kernelLiftPoints f g w T x ≫ (groupHom (kernelι f)).hom.hom =
      x ≫ (groupHom g).hom.hom :=
  congrArg Subtype.val ((kernelPointsEquiv (groupHom f) T).apply_symm_apply _)

private theorem kernelLiftPoints_naturality (g : P ⟶ G) (w : g ≫ f = 0)
    {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ P.X) :
    kernelLiftPoints f g w T' (a ≫ x) = a ≫ kernelLiftPoints f g w T x := by
  apply (cancel_mono (GroupScheme.kernelι (groupHom f)).hom.hom).mp
  change kernelLiftPoints f g w T' (a ≫ x) ≫ (groupHom (kernelι f)).hom.hom =
    (a ≫ kernelLiftPoints f g w T x) ≫ (groupHom (kernelι f)).hom.hom
  calc
    _ = (a ≫ x) ≫ (groupHom g).hom.hom := kernelLiftPoints_ι f g w T' (a ≫ x)
    _ = a ≫ (x ≫ (groupHom g).hom.hom) := Category.assoc _ _ _
    _ = a ≫ (kernelLiftPoints f g w T x ≫ (groupHom (kernelι f)).hom.hom) :=
      congrArg (fun y => a ≫ y) (kernelLiftPoints_ι f g w T x).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The unique actual group-scheme factor of a morphism whose composite is zero. -/
def kernelLift (g : P ⟶ G) (w : g ≫ f = 0) : P ⟶ kernel f :=
  Additive.ofMul (homOfPoints (kernelLiftPoints f g w)
    (fun a x => kernelLiftPoints_naturality f g w a x))

@[simp] theorem kernelLift_ι (g : P ⟶ G) (w : g ≫ f = 0) :
    kernelLift f g w ≫ kernelι f = g := by
  apply CommGroupScheme.hom_ext_points
  intro T x
  rw [comp_groupHom_comp]
  change (x ≫ (homOfPoints (kernelLiftPoints f g w) _).hom.hom) ≫ _ = _
  rw [comp_homOfPoints, kernelLiftPoints_ι]

/-- Postcomposition as an additive homomorphism of actual Hom groups. -/
def postcompose (P : CommGroupScheme S) : (P ⟶ G) →+ (P ⟶ H) where
  toFun g := g ≫ f
  map_zero' := zero_comp
  map_add' g h := Preadditive.add_comp _ _ _ g h _

/-- The universal property of the actual scheme kernel, with the additive Hom laws. -/
def kernelHomEquiv (P : CommGroupScheme S) :
    (P ⟶ kernel f) ≃+ (postcompose f P).ker where
  toFun g := ⟨g ≫ kernelι f, by
    change (g ≫ kernelι f) ≫ f = 0
    rw [Category.assoc, kernelι_comp, comp_zero]⟩
  invFun g := kernelLift f g.val g.property
  left_inv g := kernel_hom_ext f (kernelLift_ι f _ _)
  right_inv g := Subtype.ext (kernelLift_ι f _ _)
  map_add' g h := Subtype.ext (Preadditive.add_comp _ _ _ _ _ _)

@[simp] theorem kernelHomEquiv_val (P : CommGroupScheme S) (g : P ⟶ kernel f) :
    (kernelHomEquiv f P g).val = g ≫ kernelι f := rfl

end Langlands.CommGroupScheme

namespace Langlands.GroupScheme.cocharacterLattice

variable {S : Scheme.{u}} {G H : CommGroupScheme S} (f : G ⟶ H)

/-- Cocharacters of the actual kernel are precisely actual cocharacters killed by the map. -/
def kernelEquiv : cocharacterLattice (CommGroupScheme.kernel f) ≃+
    (CommGroupScheme.postcompose f (Gm S)).ker :=
  CommGroupScheme.kernelHomEquiv f (Gm S)

@[simp] theorem kernelEquiv_val (ν : cocharacterLattice (CommGroupScheme.kernel f)) :
    (kernelEquiv f ν).val = ν ≫ CommGroupScheme.kernelι f := rfl

end Langlands.GroupScheme.cocharacterLattice
