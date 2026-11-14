import Langlands.GroupScheme.KernelOrderedProductChart
import Langlands.GroupScheme.KernelProductOpenChart

/-! # Open ordered charts for full scheme-theoretic kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeRoot

variable {S : Scheme.{u}} {n : ℕ} {G H : GroupScheme S}
  {A B : Fin n → GroupScheme S}

private theorem finiteProductUniverseIso_naturality (f : ∀ i, A i ⟶ B i) :
    (finiteProductUniverseIso A).hom ≫ (CategoryTheory.Limits.Pi.map f).hom.hom =
      (CategoryTheory.Limits.Pi.map (fun i : ULift.{u} (Fin n) => f i.down)).hom.hom ≫
        (finiteProductUniverseIso B).hom := by
  have h : (Pi.reindex (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n) A).hom ≫
      CategoryTheory.Limits.Pi.map f =
    CategoryTheory.Limits.Pi.map (fun i : ULift.{u} (Fin n) => f i.down) ≫
      (Pi.reindex Equiv.ulift B).hom := by
    apply Pi.hom_ext
    intro i
    have hA := Pi.reindex_hom_π
      (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n) A (ULift.up i)
    have hB := Pi.reindex_hom_π
      (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n) B (ULift.up i)
    calc
      ((Pi.reindex Equiv.ulift A).hom ≫ CategoryTheory.Limits.Pi.map f) ≫
          Pi.π B i =
        ((Pi.reindex Equiv.ulift A).hom ≫ Pi.π A i) ≫ f i := by
          rw [Category.assoc, Pi.map_π, ← Category.assoc]
      _ = Pi.π (fun i : ULift.{u} (Fin n) => A i.down) (ULift.up i) ≫ f i :=
        congrArg (fun z => z ≫ f i) hA
      _ = CategoryTheory.Limits.Pi.map (fun i : ULift.{u} (Fin n) => f i.down) ≫
          Pi.π (fun i : ULift.{u} (Fin n) => B i.down) (ULift.up i) :=
        (Pi.map_π (fun i : ULift.{u} (Fin n) => f i.down) (ULift.up i)).symm
      _ = (CategoryTheory.Limits.Pi.map (fun i : ULift.{u} (Fin n) => f i.down) ≫
          (Pi.reindex Equiv.ulift B).hom) ≫ Pi.π B i := by
        rw [Category.assoc]
        exact congrArg
          (fun z => CategoryTheory.Limits.Pi.map
            (fun i : ULift.{u} (Fin n) => f i.down) ≫ z) hB.symm
  exact congrArg (fun z => z.hom.hom) h

private theorem orderedProductKernelChart_compatibility
    (j : ∀ i, A i ⟶ G) (k : ∀ i, B i ⟶ H)
    (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
    (h : ∀ i, j i ≫ q = f i ≫ k i) :
    orderedProductKernelChart j ≫ q.hom.hom =
      (CategoryTheory.Limits.Pi.map (fun i : ULift.{u} (Fin n) => f i.down)).hom.hom ≫
        orderedProductKernelChart k := by
  unfold orderedProductKernelChart
  rw [Category.assoc, ← orderedMultiplication_map j k q f h]
  unfold productFactorMap
  rw [← Category.assoc, finiteProductUniverseIso_naturality, Category.assoc]

private theorem orderedProductKernelChart_unit (k : ∀ i, B i ⟶ H) :
    η[(pi (fun i : ULift.{u} (Fin n) => B i.down)).X] ≫
      orderedProductKernelChart k = η[H.X] := by
  unfold orderedProductKernelChart finiteProductUniverseIso
  change η[(pi (fun i : ULift.{u} (Fin n) => B i.down)).X] ≫
    ((Pi.reindex Equiv.ulift B).hom.hom.hom ≫ orderedMultiplication k) = _
  rw [← Category.assoc, IsMonHom.one_hom, unit_orderedMultiplication]

/-- The local chart of the full ambient kernel induced by the actual ordered
multiplication charts, indexed by the universe-raised finite factor list. -/
def orderedMultiplicationKernelOpenMap
    (j : ∀ i, A i ⟶ G) (k : ∀ i, B i ⟶ H)
    (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
    (h : ∀ i, j i ≫ q = f i ≫ k i)
    [Mono (orderedMultiplication k)] :
    (pi (fun i : ULift.{u} (Fin n) => kernel (f i.down))).X ⟶ (kernel q).X :=
  KernelProductChart.toKernel q (fun i : ULift.{u} (Fin n) => f i.down)
    (orderedProductKernelChart j) (orderedProductKernelChart k)
    (orderedProductKernelChart_compatibility j k q f h)
    (orderedProductKernelChart_unit k)

/-- This kernel chart is open whenever the original source chart is open. -/
theorem isOpenImmersion_orderedMultiplicationKernelOpenMap
    (j : ∀ i, A i ⟶ G) (k : ∀ i, B i ⟶ H)
    (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
    (h : ∀ i, j i ≫ q = f i ≫ k i)
    [Mono (orderedMultiplication k)]
    [IsOpenImmersion (orderedMultiplication j).left] :
    IsOpenImmersion (orderedMultiplicationKernelOpenMap j k q f h).left := by
  let : IsOpenImmersion (orderedProductKernelChart j).left := by
    unfold orderedProductKernelChart
    have : IsIso (finiteProductUniverseIso A).hom.left :=
      (Over.forget S).map_isIso (finiteProductUniverseIso A).hom
    simp only [Over.comp_left]
    infer_instance
  exact KernelProductChart.isOpenImmersion_toKernel q
    (fun i : ULift.{u} (Fin n) => f i.down)
    (orderedProductKernelChart j) (orderedProductKernelChart k)
    (orderedProductKernelChart_compatibility j k q f h)
    (orderedProductKernelChart_unit k)

/-- Compatible actual ordered multiplication charts, open on the source
and monic on the target, give smoothness of the full ambient kernel over
an algebraically closed field when all full factor kernels are smooth. -/
theorem smooth_kernel_of_orderedOpenCharts
    {F : Type u} [Field F] [IsAlgClosed F]
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    {A B : Fin n → GroupScheme (Spec (CommRingCat.of F))}
    (j : ∀ i, A i ⟶ G) (k : ∀ i, B i ⟶ H)
    (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
    (h : ∀ i, j i ≫ q = f i ≫ k i)
    [Mono (orderedMultiplication k)]
    [IsOpenImmersion (orderedMultiplication j).left]
    [LocallyOfFiniteType (kernel q).X.hom]
    (hfactor : ∀ i, Smooth (kernel (f i)).X.hom) :
    Smooth (kernel q).X.hom := by
  let : IsOpenImmersion (orderedProductKernelChart j).left := by
    unfold orderedProductKernelChart
    have : IsIso (finiteProductUniverseIso A).hom.left :=
      (Over.forget _).map_isIso (finiteProductUniverseIso A).hom
    simp only [Over.comp_left]
    infer_instance
  exact KernelProductChart.smooth_kernel_of_openChart q
    (fun i : ULift.{u} (Fin n) => f i.down)
    (orderedProductKernelChart j) (orderedProductKernelChart k)
    (orderedProductKernelChart_compatibility j k q f h)
    (orderedProductKernelChart_unit k) (fun i => hfactor i.down)

end Langlands.GroupScheme.RelativeRoot
