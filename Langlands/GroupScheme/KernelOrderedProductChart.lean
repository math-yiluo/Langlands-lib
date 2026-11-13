import Langlands.GroupScheme.KernelProductChartBaseChange
import Langlands.GroupScheme.Rational.OrderedProductMaps

/-! # Kernel comparisons for actual ordered multiplication charts -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {S : Scheme.{u}} {n : ℕ} {G H : GroupScheme S}
  {A B : Fin n → GroupScheme S}

/-- Ordered multiplication sends the identity point to the identity point
on every test scheme, without being a group homomorphism. -/
@[simp]
theorem one_comp_orderedMultiplication (j : ∀ i, A i ⟶ G) {T : Over S} :
    (1 : T ⟶ (∏ᶜ A).X) ≫ orderedMultiplication j = 1 := by
  rw [comp_orderedMultiplication, map_one]
  simp [orderedPoints]

/-- The actual ordered multiplication chart preserves the unit section. -/
@[reassoc (attr := simp)]
theorem unit_orderedMultiplication (j : ∀ i, A i ⟶ G) :
    η[(∏ᶜ A).X] ≫ orderedMultiplication j = η[G.X] := by
  have h := congrArg (fun z => η[(∏ᶜ A).X] ≫ z)
    (one_comp_orderedMultiplication j (T := (∏ᶜ A).X))
  simpa only [Hom.one_def, ← Category.assoc,
    CategoryTheory.CartesianMonoidalCategory.comp_toUnit,
    CategoryTheory.CartesianMonoidalCategory.toUnit_unit, Category.id_comp] using h

/-- Reindex a finite product by its universe-raised finite index. -/
def finiteProductUniverseIso (A : Fin n → GroupScheme S) :
    (pi (fun i : ULift.{u} (Fin n) => A i.down)).X ≅ (∏ᶜ A).X :=
  (Grp.forget (Over S)).mapIso (Pi.reindex Equiv.ulift A)

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

/-- Express an actual ordered multiplication chart with a universe-raised
finite source index for the general kernel-product API. -/
def orderedProductKernelChart (j : ∀ i, A i ⟶ G) :
    (pi (fun i : ULift.{u} (Fin n) => A i.down)).X ⟶ G.X :=
  (finiteProductUniverseIso A).hom ≫ orderedMultiplication j

instance mono_orderedProductKernelChart (j : ∀ i, A i ⟶ G)
    [Mono (orderedMultiplication j)] : Mono (orderedProductKernelChart j) := by
  unfold orderedProductKernelChart
  infer_instance

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

/-- Compatible monomorphic ordered multiplication charts identify the actual
ambient kernel with the product of the actual factor kernels, given a lift
of the entire ambient kernel through the source chart. -/
def orderedMultiplicationKernelIso
    (j : ∀ i, A i ⟶ G) (k : ∀ i, B i ⟶ H)
    (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
    (h : ∀ i, j i ≫ q = f i ≫ k i)
    [Mono (orderedMultiplication j)] [Mono (orderedMultiplication k)]
    (l : (kernel q).X ⟶ (∏ᶜ A).X)
    (hl : l ≫ orderedMultiplication j = (kernelι q).hom.hom) :
    (∏ᶜ fun i => kernel (f i)).X ≅ (kernel q).X :=
  (finiteProductUniverseIso (fun i => kernel (f i))).symm ≪≫
    KernelProductChart.iso q (fun i : ULift.{u} (Fin n) => f i.down)
      (orderedProductKernelChart j) (orderedProductKernelChart k)
      (orderedProductKernelChart_compatibility j k q f h)
      (orderedProductKernelChart_unit k)
      (l ≫ (finiteProductUniverseIso A).inv) (by
        unfold orderedProductKernelChart
        rw [Category.assoc, Iso.inv_hom_id_assoc, hl])

private theorem orderedProductKernelChart_baseChange_lift
    {T : Scheme.{u}} (b : T ⟶ S) (j : ∀ i, A i ⟶ G) {P : Over T}
    (l : P ⟶ (Over.pullback b).obj (∏ᶜ A).X) :
    (l ≫ (Over.pullback b).map (finiteProductUniverseIso A).inv) ≫
        (Over.pullback b).map (orderedProductKernelChart j) =
      l ≫ (Over.pullback b).map (orderedMultiplication j) := by
  unfold orderedProductKernelChart
  rw [Functor.map_comp, Category.assoc, ← Category.assoc
    ((Over.pullback b).map (finiteProductUniverseIso A).inv),
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- A full-kernel lift into the pullback of an actual ordered chart supplies
the actual product-of-kernels comparison after arbitrary base change. -/
def orderedMultiplicationKernelIso_baseChange
    {T : Scheme.{u}} (b : T ⟶ S)
    (j : ∀ i, A i ⟶ G) (k : ∀ i, B i ⟶ H)
    (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
    (h : ∀ i, j i ≫ q = f i ≫ k i)
    [Mono (orderedMultiplication j)] [Mono (orderedMultiplication k)]
    (l : (kernel ((GroupScheme.baseChange b).map q)).X ⟶
      (Over.pullback b).obj (∏ᶜ A).X)
    (hl : l ≫ (Over.pullback b).map (orderedMultiplication j) =
      (kernelι ((GroupScheme.baseChange b).map q)).hom.hom) :
    (∏ᶜ fun i => kernel ((GroupScheme.baseChange b).map (f i))).X ≅
      (kernel ((GroupScheme.baseChange b).map q)).X :=
  (finiteProductUniverseIso
    (fun i => kernel ((GroupScheme.baseChange b).map (f i)))).symm ≪≫
    KernelProductChart.iso_baseChange b q (fun i : ULift.{u} (Fin n) => f i.down)
      (orderedProductKernelChart j) (orderedProductKernelChart k)
      (orderedProductKernelChart_compatibility j k q f h)
      (orderedProductKernelChart_unit k)
      (l ≫ (Over.pullback b).map (finiteProductUniverseIso A).inv) (by
        rw [orderedProductKernelChart_baseChange_lift, hl])

/-- Over a field, smooth connected affine factor kernels give smoothness
and connectedness of the ambient kernel contained in an ordered chart. -/
theorem smooth_connected_orderedMultiplicationKernel_baseChange
    {F : Type u} [Field F] (c : Spec (CommRingCat.of F) ⟶ S)
    (j : ∀ i, A i ⟶ G) (k : ∀ i, B i ⟶ H)
    (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
    (h : ∀ i, j i ≫ q = f i ≫ k i)
    [Mono (orderedMultiplication j)] [Mono (orderedMultiplication k)]
    (l : (kernel ((GroupScheme.baseChange c).map q)).X ⟶
      (Over.pullback c).obj (∏ᶜ A).X)
    (hl : l ≫ (Over.pullback c).map (orderedMultiplication j) =
      (kernelι ((GroupScheme.baseChange c).map q)).hom.hom)
    (hfactor : ∀ i, Smooth (kernel ((GroupScheme.baseChange c).map (f i))).X.hom ∧
      IsAffineHom (kernel ((GroupScheme.baseChange c).map (f i))).X.hom ∧
      ConnectedSpace (kernel ((GroupScheme.baseChange c).map (f i))).X.left) :
    Smooth (kernel ((GroupScheme.baseChange c).map q)).X.hom ∧
      ConnectedSpace (kernel ((GroupScheme.baseChange c).map q)).X.left :=
  KernelProductChart.smooth_connected_baseChange c q
    (fun i : ULift.{u} (Fin n) => f i.down)
    (orderedProductKernelChart j) (orderedProductKernelChart k)
    (orderedProductKernelChart_compatibility j k q f h)
    (orderedProductKernelChart_unit k)
    (l ≫ (Over.pullback c).map (finiteProductUniverseIso A).inv)
    (by rw [orderedProductKernelChart_baseChange_lift, hl])
    (fun i => hfactor i.down)

end Langlands.GroupScheme.RelativeRoot
