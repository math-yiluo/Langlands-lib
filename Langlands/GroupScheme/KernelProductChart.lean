import Langlands.AbelianScheme.Kernel
import Langlands.GroupScheme.Products

/-! # Full kernels in compatible product charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.KernelProductChart

variable {S : Scheme.{u}} {I : Type u} [Finite I]
  {G H : GroupScheme S} {A B : I → GroupScheme S}
  (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)

/-- The product of the actual factor kernels, as an actual group scheme. -/
abbrev factorKernels : GroupScheme S := pi (fun i => kernel (f i))

/-- The product of the inclusions of the factor kernels. -/
def inclusion : (factorKernels f).X ⟶ (pi A).X :=
  (CategoryTheory.Limits.Pi.map (fun i => kernelι (f i))).hom.hom

@[reassoc (attr := simp)]
theorem inclusion_π (i : I) :
    inclusion f ≫ (Pi.π A i).hom.hom =
      (Pi.π (fun i => kernel (f i)) i).hom.hom ≫ (kernelι (f i)).hom.hom :=
  congrArg (fun z => z.hom.hom) (CategoryTheory.Limits.Pi.map_π (fun i => kernelι (f i)) i)

@[reassoc (attr := simp)]
theorem factorMap_π (i : I) :
    (CategoryTheory.Limits.Pi.map f).hom.hom ≫ (Pi.π B i).hom.hom =
      (Pi.π A i).hom.hom ≫ (f i).hom.hom :=
  congrArg (fun z => z.hom.hom) (CategoryTheory.Limits.Pi.map_π f i)

/-- In every coordinate the product of kernels maps to the identity. -/
theorem inclusion_factorMap :
    inclusion f ≫ (CategoryTheory.Limits.Pi.map f).hom.hom = 1 := by
  apply Fan.IsLimit.hom_ext (piIsLimit B)
  intro i
  change (inclusion f ≫ (CategoryTheory.Limits.Pi.map f).hom.hom) ≫
      (Pi.π B i).hom.hom = (1 : (factorKernels f).X ⟶ (pi B).X) ≫
        (Pi.π B i).hom.hom
  rw [Category.assoc, factorMap_π, inclusion_π_assoc, MonObj.one_comp]
  have h := (kernelPointsEquiv (f i) (factorKernels f).X
    (Pi.π (fun i => kernel (f i)) i).hom.hom).property
  change ((Pi.π (fun i => kernel (f i)) i).hom.hom ≫
    (kernelι (f i)).hom.hom) ≫ (f i).hom.hom = 1 at h
  simpa only [Category.assoc] using h

variable (m : (pi A).X ⟶ G.X) (n : (pi B).X ⟶ H.X)
  (hc : m ≫ q.hom.hom = (CategoryTheory.Limits.Pi.map f).hom.hom ≫ n)
  (hn : η[(pi B).X] ≫ n = η[H.X])

include hn in
/-- A chart taking its distinguished unit to the ambient unit does so on
the identity point of every test scheme. No group-map assertion is used. -/
theorem one_comp {T : Over S} :
    (1 : T ⟶ (pi B).X) ≫ n = 1 := by
  change (toUnit T ≫ η[(pi B).X]) ≫ n = toUnit T ≫ η[H.X]
  rw [Category.assoc, hn]

/-- Multiplication of the factor kernels lands in the full ambient kernel. -/
def toKernel : (factorKernels f).X ⟶ (kernel q).X :=
  (kernel_isPullback q).lift (inclusion f ≫ m) (toUnit _) (by
    change (inclusion f ≫ m) ≫ q.hom.hom = 1
    calc
      (inclusion f ≫ m) ≫ q.hom.hom =
          inclusion f ≫ (CategoryTheory.Limits.Pi.map f).hom.hom ≫ n := by rw [Category.assoc, hc]
      _ = (inclusion f ≫ (CategoryTheory.Limits.Pi.map f).hom.hom) ≫ n := (Category.assoc _ _ _).symm
      _ = (1 : (factorKernels f).X ⟶ (pi B).X) ≫ n := by rw [inclusion_factorMap]
      _ = 1 := one_comp n hn)

@[reassoc (attr := simp)]
theorem toKernel_ι :
    toKernel q f m n hc hn ≫ (kernelι q).hom.hom = inclusion f ≫ m :=
  (kernel_isPullback q).lift_fst _ _ _

variable [Mono n]
  (l : (kernel q).X ⟶ (pi A).X)
  (hl : l ≫ m = (kernelι q).hom.hom)

include hc hn hl in
/-- Containment of the full kernel in the source chart forces every target
coordinate to be the identity, by monicity of the target chart. -/
theorem lift_factorMap :
    l ≫ (CategoryTheory.Limits.Pi.map f).hom.hom = 1 := by
  apply (cancel_mono n).mp
  calc
    (l ≫ (CategoryTheory.Limits.Pi.map f).hom.hom) ≫ n = (l ≫ m) ≫ q.hom.hom := by
      rw [Category.assoc, ← hc, ← Category.assoc]
    _ = (kernelι q).hom.hom ≫ q.hom.hom := by rw [hl]
    _ = 1 := (kernel_isPullback q).w
    _ = (1 : (kernel q).X ⟶ (pi B).X) ≫ n := (one_comp n hn).symm

include hc hn hl in
theorem lift_coordinate (i : I) :
    (l ≫ (Pi.π A i).hom.hom) ≫ (f i).hom.hom = 1 := by
  have h := congrArg (fun z => z ≫ (Pi.π B i).hom.hom)
    (lift_factorMap q f m n hc hn l hl)
  simpa only [Category.assoc, factorMap_π, MonObj.one_comp] using h

/-- The full kernel recovers one point of each actual factor kernel. -/
def fromKernel : (kernel q).X ⟶ (factorKernels f).X :=
  Fan.IsLimit.lift (piIsLimit (fun i => kernel (f i))) fun i =>
    (kernel_isPullback (f i)).lift (l ≫ (Pi.π A i).hom.hom) (toUnit _)
      (lift_coordinate q f m n hc hn l hl i)

@[reassoc (attr := simp)]
theorem fromKernel_π (i : I) :
    fromKernel q f m n hc hn l hl ≫
        (Pi.π (fun i => kernel (f i)) i).hom.hom =
      (kernel_isPullback (f i)).lift (l ≫ (Pi.π A i).hom.hom) (toUnit _)
        (lift_coordinate q f m n hc hn l hl i) :=
  Fan.IsLimit.fac (piIsLimit (fun i => kernel (f i))) _ i

@[reassoc (attr := simp)]
theorem fromKernel_inclusion :
    fromKernel q f m n hc hn l hl ≫ inclusion f = l := by
  apply Fan.IsLimit.hom_ext (piIsLimit A)
  intro i
  change (fromKernel q f m n hc hn l hl ≫ inclusion f) ≫ (Pi.π A i).hom.hom =
    l ≫ (Pi.π A i).hom.hom
  rw [Category.assoc, inclusion_π, ← Category.assoc, fromKernel_π]
  exact (kernel_isPullback (f i)).lift_fst _ _ _

variable [Mono m]

/-- Compatible monomorphic product charts identify the full ambient kernel
with the product of the actual factor kernels, provided the full kernel
factors through the source chart. This is an isomorphism of schemes over S. -/
def iso : (factorKernels f).X ≅ (kernel q).X where
  hom := toKernel q f m n hc hn
  inv := fromKernel q f m n hc hn l hl
  hom_inv_id := by
    apply Fan.IsLimit.hom_ext (piIsLimit (fun i => kernel (f i)))
    intro i
    apply (cancel_mono (kernelι (f i)).hom.hom).mp
    have h : toKernel q f m n hc hn ≫ l = inclusion f := by
      apply (cancel_mono m).mp
      rw [Category.assoc, hl, toKernel_ι]
    calc
      ((toKernel q f m n hc hn ≫ fromKernel q f m n hc hn l hl) ≫
          (Pi.π (fun i => kernel (f i)) i).hom.hom) ≫ (kernelι (f i)).hom.hom =
          (toKernel q f m n hc hn ≫
            (fromKernel q f m n hc hn l hl ≫ inclusion f)) ≫
              (Pi.π A i).hom.hom := by
        simp only [Category.assoc, inclusion_π]
      _ = inclusion f ≫ (Pi.π A i).hom.hom := by rw [fromKernel_inclusion, h]
      _ = ((𝟙 (factorKernels f).X) ≫
          (Pi.π (fun i => kernel (f i)) i).hom.hom) ≫ (kernelι (f i)).hom.hom := by
        rw [Category.id_comp, inclusion_π]
  inv_hom_id := by
    apply (cancel_mono (kernelι q).hom.hom).mp
    rw [Category.assoc, toKernel_ι, ← Category.assoc, fromKernel_inclusion, hl,
      Category.id_comp]

end Langlands.GroupScheme.KernelProductChart
