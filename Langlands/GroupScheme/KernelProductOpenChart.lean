import Langlands.GroupScheme.KernelProductChartGeometry
import Langlands.GroupScheme.Lie.SmoothOpenSubgroup

/-! # Local product charts for full scheme-theoretic kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.KernelProductChart

variable {S : Scheme.{u}} {I : Type u} [Finite I]
  {G H : GroupScheme S} {A B : I → GroupScheme S}
  (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
  (m : (pi A).X ⟶ G.X) (n : (pi B).X ⟶ H.X)
  (hc : m ≫ q.hom.hom = (CategoryTheory.Limits.Pi.map f).hom.hom ≫ n)
  (hn : η[(pi B).X] ≫ n = η[H.X]) [Mono n]

include hc hn in
/-- A point in the source chart killed by the ambient map has unit target
coordinates, by monicity of the target chart. -/
theorem chart_factorMap_eq_one {T : Over S} (a : T ⟶ (pi A).X)
    (ha : (a ≫ m) ≫ q.hom.hom = 1) :
    a ≫ (CategoryTheory.Limits.Pi.map f).hom.hom = 1 := by
  apply (cancel_mono n).mp
  calc
    (a ≫ (CategoryTheory.Limits.Pi.map f).hom.hom) ≫ n =
        (a ≫ m) ≫ q.hom.hom := by rw [Category.assoc, ← hc, ← Category.assoc]
    _ = 1 := ha
    _ = (1 : T ⟶ (pi B).X) ≫ n := (one_comp n hn).symm

include hc hn in
theorem chart_coordinate_eq_one {T : Over S} (a : T ⟶ (pi A).X)
    (ha : (a ≫ m) ≫ q.hom.hom = 1) (i : I) :
    (a ≫ (Pi.π A i).hom.hom) ≫ (f i).hom.hom = 1 := by
  have h := congrArg (fun z => z ≫ (Pi.π B i).hom.hom)
    (chart_factorMap_eq_one q f m n hc hn a ha)
  simpa only [Category.assoc, factorMap_π, MonObj.one_comp] using h

/-- A chart point killed by the ambient map lifts to the product of the
full factor kernels. -/
def chartKernelLift {T : Over S} (a : T ⟶ (pi A).X)
    (ha : (a ≫ m) ≫ q.hom.hom = 1) : T ⟶ (factorKernels f).X :=
  Fan.IsLimit.lift (piIsLimit (fun i => kernel (f i))) fun i =>
    (kernel_isPullback (f i)).lift (a ≫ (Pi.π A i).hom.hom) (toUnit _)
      (chart_coordinate_eq_one q f m n hc hn a ha i)

@[reassoc (attr := simp)]
theorem chartKernelLift_π {T : Over S} (a : T ⟶ (pi A).X)
    (ha : (a ≫ m) ≫ q.hom.hom = 1) (i : I) :
    chartKernelLift q f m n hc hn a ha ≫
        (Pi.π (fun i => kernel (f i)) i).hom.hom =
      (kernel_isPullback (f i)).lift (a ≫ (Pi.π A i).hom.hom) (toUnit _)
        (chart_coordinate_eq_one q f m n hc hn a ha i) :=
  Fan.IsLimit.fac (piIsLimit (fun i => kernel (f i))) _ i

@[reassoc (attr := simp)]
theorem chartKernelLift_inclusion {T : Over S} (a : T ⟶ (pi A).X)
    (ha : (a ≫ m) ≫ q.hom.hom = 1) :
    chartKernelLift q f m n hc hn a ha ≫ inclusion f = a := by
  apply Fan.IsLimit.hom_ext (piIsLimit A)
  intro i
  change (chartKernelLift q f m n hc hn a ha ≫ inclusion f) ≫
    (Pi.π A i).hom.hom = a ≫ (Pi.π A i).hom.hom
  rw [Category.assoc, inclusion_π, ← Category.assoc, chartKernelLift_π]
  exact (kernel_isPullback (f i)).lift_fst _ _ _

/-- The product of the full factor kernels is the inverse image of the
ambient kernel in the source chart. No containment of the whole ambient
kernel in that chart is assumed. -/
theorem isPullback_toKernel :
    IsPullback (inclusion f) (toKernel q f m n hc hn)
      m (kernelι q).hom.hom := by
  have hk (c : PullbackCone m (kernelι q).hom.hom) :
      (c.fst ≫ m) ≫ q.hom.hom = 1 := by
    rw [c.condition, Category.assoc, (kernel_isPullback q).w]
    exact MonObj.comp_one _
  let l := fun c : PullbackCone m (kernelι q).hom.hom =>
    chartKernelLift q f m n hc hn c.fst (hk c)
  have hl (c : PullbackCone m (kernelι q).hom.hom) :
      l c ≫ inclusion f = c.fst :=
    chartKernelLift_inclusion q f m n hc hn c.fst (hk c)
  refine ⟨⟨(toKernel_ι q f m n hc hn).symm⟩,
    ⟨PullbackCone.IsLimit.mk _ l hl ?_ ?_⟩⟩
  · intro c
    apply (cancel_mono (kernelι q).hom.hom).mp
    rw [Category.assoc, toKernel_ι, ← Category.assoc, hl, c.condition]
  · intro c z hz _hw
    apply Fan.IsLimit.hom_ext (piIsLimit (fun i => kernel (f i)))
    intro i
    change z ≫ (Pi.π (fun i => kernel (f i)) i).hom.hom =
      l c ≫ (Pi.π (fun i => kernel (f i)) i).hom.hom
    apply (cancel_mono (kernelι (f i)).hom.hom).mp
    have h := congrArg (fun a => a ≫ (Pi.π A i).hom.hom)
      (hz.trans (hl c).symm)
    simpa only [Category.assoc, inclusion_π] using h

/-- Restricting an open source chart to the full ambient kernel gives an
open chart whose source is the product of the full factor kernels. -/
theorem isOpenImmersion_toKernel [IsOpenImmersion m.left] :
    IsOpenImmersion (toKernel q f m n hc hn).left :=
  MorphismProperty.of_isPullback
    ((isPullback_toKernel q f m n hc hn).map (Over.forget S))
    (inferInstance : IsOpenImmersion m.left)

section Field

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {A B : I → GroupScheme (Spec (CommRingCat.of k))}

/-- Over an algebraically closed field, compatible product charts with an
open source chart and monic target chart imply smoothness of the full
ambient kernel whenever all full factor kernels are smooth. -/
theorem smooth_kernel_of_openChart
    (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
    (m : (pi A).X ⟶ G.X) (n : (pi B).X ⟶ H.X)
    (hc : m ≫ q.hom.hom = (CategoryTheory.Limits.Pi.map f).hom.hom ≫ n)
    (hn : η[(pi B).X] ≫ n = η[H.X])
    [Mono n] [IsOpenImmersion m.left]
    [LocallyOfFiniteType (kernel q).X.hom]
    (hfactor : ∀ i, Smooth (kernel (f i)).X.hom) :
    Smooth (kernel q).X.hom := by
  let p := toKernel q f m n hc hn
  let : IsOpenImmersion p.left := isOpenImmersion_toKernel q f m n hc hn
  let : Smooth (factorKernels f).X.hom :=
    smooth_pi (fun i => kernel (f i)) hfactor
  have : Smooth (p.left ≫ (kernel q).X.hom) := by
    simpa only [Over.w] using (inferInstance : Smooth (factorKernels f).X.hom)
  have hne : ((kernel q).X.hom.smoothLocus : Set (kernel q).X.left).Nonempty := by
    let x : (factorKernels f).X.left :=
      η[(factorKernels f).X].left (IsLocalRing.closedPoint k)
    refine ⟨p.left x, ?_⟩
    change x ∈ p.left ⁻¹ᵁ (kernel q).X.hom.smoothLocus
    rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    trivial
  let : GrpObj (Over.mk (kernel q).X.hom) := (kernel q).grp
  exact smooth_of_nonempty_smoothLocus (kernel q).X.hom hne

end Field

end Langlands.GroupScheme.KernelProductChart
