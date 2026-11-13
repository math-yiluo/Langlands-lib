import Langlands.GroupScheme.KernelProductChartGeometry

/-! # Base change of compatible product charts -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.KernelProductChart

variable {S T : Scheme.{u}} (b : T ⟶ S) {I : Type u} [Finite I]
  {A B : I → GroupScheme S} {G H : GroupScheme S}

/-- Pull back a product chart and express its source as the product of the
actual pulled-back factors, using the categorical product comparison. -/
def baseChangeChart (m : (pi A).X ⟶ G.X) :
    (pi (fun i => (GroupScheme.baseChange b).obj (A i))).X ⟶
      ((GroupScheme.baseChange b).obj G).X :=
  (PreservesProduct.iso (GroupScheme.baseChange b) A).inv.hom.hom ≫
    (Over.pullback b).map m

/-- Convert a lift to the pullback of the original product into a lift to
the product of the actual pulled-back factors. -/
def baseChangeLift {P : Over T}
    (l : P ⟶ (Over.pullback b).obj (pi A).X) :
    P ⟶ (pi (fun i => (GroupScheme.baseChange b).obj (A i))).X :=
  l ≫ (PreservesProduct.iso (GroupScheme.baseChange b) A).hom.hom.hom

@[reassoc (attr := simp)]
theorem baseChangeLift_chart {P : Over T}
    (l : P ⟶ (Over.pullback b).obj (pi A).X) (m : (pi A).X ⟶ G.X) :
    baseChangeLift b l ≫ baseChangeChart b m = l ≫ (Over.pullback b).map m := by
  let e := (Grp.forget (Over T)).mapIso
    (PreservesProduct.iso (GroupScheme.baseChange b) A)
  change (l ≫ e.hom) ≫ (e.inv ≫ (Over.pullback b).map m) =
    l ≫ (Over.pullback b).map m
  rw [Category.assoc, e.hom_inv_id_assoc]

private theorem productComparison_naturality (f : ∀ i, A i ⟶ B i) :
    (GroupScheme.baseChange b).map (CategoryTheory.Limits.Pi.map f) ≫
        (PreservesProduct.iso (GroupScheme.baseChange b) B).hom =
      (PreservesProduct.iso (GroupScheme.baseChange b) A).hom ≫
        CategoryTheory.Limits.Pi.map (fun i => (GroupScheme.baseChange b).map (f i)) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
    Pi.map_π, piComparison_comp_π_assoc, ← Functor.map_comp]

private theorem productComparison_inv_naturality (f : ∀ i, A i ⟶ B i) :
    (PreservesProduct.iso (GroupScheme.baseChange b) A).inv ≫
        (GroupScheme.baseChange b).map (CategoryTheory.Limits.Pi.map f) =
      CategoryTheory.Limits.Pi.map (fun i => (GroupScheme.baseChange b).map (f i)) ≫
        (PreservesProduct.iso (GroupScheme.baseChange b) B).inv := by
  apply (cancel_mono (PreservesProduct.iso (GroupScheme.baseChange b) B).hom).mp
  rw [Category.assoc, productComparison_naturality, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Compatibility of product charts is preserved by arbitrary base change. -/
theorem baseChangeChart_compatibility (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
    (m : (pi A).X ⟶ G.X) (n : (pi B).X ⟶ H.X)
    (hc : m ≫ q.hom.hom = (CategoryTheory.Limits.Pi.map f).hom.hom ≫ n) :
    baseChangeChart b m ≫ ((GroupScheme.baseChange b).map q).hom.hom =
      (CategoryTheory.Limits.Pi.map
        (fun i => (GroupScheme.baseChange b).map (f i))).hom.hom ≫
          baseChangeChart b n := by
  have h := congrArg (fun z => z.hom.hom) (productComparison_inv_naturality b f)
  change (PreservesProduct.iso (GroupScheme.baseChange b) A).inv.hom.hom ≫
      (Over.pullback b).map (CategoryTheory.Limits.Pi.map f).hom.hom =
    (CategoryTheory.Limits.Pi.map
      (fun i => (GroupScheme.baseChange b).map (f i))).hom.hom ≫
        (PreservesProduct.iso (GroupScheme.baseChange b) B).inv.hom.hom at h
  unfold baseChangeChart
  change _ ≫ (Over.pullback b).map m ≫ (Over.pullback b).map q.hom.hom = _
  rw [← Functor.map_comp, hc, Functor.map_comp]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ (Over.pullback b).map n) h

/-- A product chart taking the distinguished unit to the ambient unit
retains this property after arbitrary base change. -/
theorem baseChangeChart_unit (n : (pi B).X ⟶ H.X)
    (hn : η[(pi B).X] ≫ n = η[H.X]) :
    η[(pi (fun i => (GroupScheme.baseChange b).obj (B i))).X] ≫
        baseChangeChart b n = η[((GroupScheme.baseChange b).obj H).X] := by
  have hunit : (1 : (pi B).X ⟶ (pi B).X) ≫ n = 1 := one_comp n hn
  have hm : (1 : ((GroupScheme.baseChange b).obj (pi B)).X ⟶
      ((GroupScheme.baseChange b).obj (pi B)).X) ≫ (Over.pullback b).map n =
        (1 : ((GroupScheme.baseChange b).obj (pi B)).X ⟶
          ((GroupScheme.baseChange b).obj H).X) := by
    simpa only [Functor.map_comp, Functor.map_one] using
      congrArg ((Over.pullback b).map) hunit
  have hη := congrArg (fun z =>
    η[((GroupScheme.baseChange b).obj (pi B)).X] ≫ z) hm
  have hη' : η[((GroupScheme.baseChange b).obj (pi B)).X] ≫
      (Over.pullback b).map n = η[((GroupScheme.baseChange b).obj H).X] := by
    simpa only [Hom.one_def, ← Category.assoc,
      CategoryTheory.CartesianMonoidalCategory.comp_toUnit,
      CategoryTheory.CartesianMonoidalCategory.toUnit_unit, Category.id_comp] using hη
  unfold baseChangeChart
  rw [← Category.assoc, IsMonHom.one_hom]
  exact hη'

/-- Monomorphic product charts stay monomorphic after arbitrary base change. -/
instance mono_baseChangeChart (m : (pi A).X ⟶ G.X) [Mono m] :
    Mono (baseChangeChart b m) := by
  let e := (Grp.forget (Over T)).mapIso
    (PreservesProduct.iso (GroupScheme.baseChange b) A)
  change Mono (e.inv ≫ (Over.pullback b).map m)
  infer_instance

/-- Open product charts stay open after arbitrary base change. -/
theorem isOpenImmersion_baseChangeChart (m : (pi A).X ⟶ G.X)
    [IsOpenImmersion m.left] : IsOpenImmersion (baseChangeChart b m).left := by
  have hp : IsOpenImmersion ((Over.pullback b).map m).left := by
    have h := Scheme.pullback_map_isOpenImmersion
      (pi A).X.hom b G.X.hom b m.left (𝟙 T) (𝟙 S)
      (show (pi A).X.hom ≫ (𝟙 S) = m.left ≫ G.X.hom by simp)
      (show b ≫ (𝟙 S) = (𝟙 T) ≫ b by simp)
    simpa only [Over.pullback_map_left, pullback.map, Category.comp_id] using h
  let e := (Grp.forget (Over T)).mapIso
    (PreservesProduct.iso (GroupScheme.baseChange b) A)
  have : IsIso e.inv.left := (Over.forget T).map_isIso e.inv
  change IsOpenImmersion (e.inv.left ≫ ((Over.pullback b).map m).left)
  infer_instance

/-- Compatible integral product charts give the kernel comparison after base
change, from an actual lift of the full base-changed kernel into the pullback
of the source chart. -/
def iso_baseChange (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
    (m : (pi A).X ⟶ G.X) (n : (pi B).X ⟶ H.X) [Mono m] [Mono n]
    (hc : m ≫ q.hom.hom = (CategoryTheory.Limits.Pi.map f).hom.hom ≫ n)
    (hn : η[(pi B).X] ≫ n = η[H.X])
    (l : (kernel ((GroupScheme.baseChange b).map q)).X ⟶
      (Over.pullback b).obj (pi A).X)
    (hl : l ≫ (Over.pullback b).map m =
      (kernelι ((GroupScheme.baseChange b).map q)).hom.hom) :
    (factorKernels (fun i => (GroupScheme.baseChange b).map (f i))).X ≅
      (kernel ((GroupScheme.baseChange b).map q)).X :=
  iso ((GroupScheme.baseChange b).map q)
    (fun i => (GroupScheme.baseChange b).map (f i))
    (baseChangeChart b m) (baseChangeChart b n)
    (baseChangeChart_compatibility b q f m n hc) (baseChangeChart_unit b n hn)
    (baseChangeLift b l) (by rw [baseChangeLift_chart, hl])

section Field

variable {k : Type u} [Field k]

/-- After base change to a field, the chart comparison transfers smoothness
and connectedness of all affine factor kernels to the full ambient kernel. -/
theorem smooth_connected_baseChange
    (c : Spec (CommRingCat.of k) ⟶ S)
    (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
    (m : (pi A).X ⟶ G.X) (n : (pi B).X ⟶ H.X) [Mono m] [Mono n]
    (hc : m ≫ q.hom.hom = (CategoryTheory.Limits.Pi.map f).hom.hom ≫ n)
    (hn : η[(pi B).X] ≫ n = η[H.X])
    (l : (kernel ((GroupScheme.baseChange c).map q)).X ⟶
      (Over.pullback c).obj (pi A).X)
    (hl : l ≫ (Over.pullback c).map m =
      (kernelι ((GroupScheme.baseChange c).map q)).hom.hom)
    (hfactor : ∀ i, Smooth (kernel ((GroupScheme.baseChange c).map (f i))).X.hom ∧
      IsAffineHom (kernel ((GroupScheme.baseChange c).map (f i))).X.hom ∧
      ConnectedSpace (kernel ((GroupScheme.baseChange c).map (f i))).X.left) :
    Smooth (kernel ((GroupScheme.baseChange c).map q)).X.hom ∧
      ConnectedSpace (kernel ((GroupScheme.baseChange c).map q)).X.left :=
  smooth_connected ((GroupScheme.baseChange c).map q)
    (fun i => (GroupScheme.baseChange c).map (f i))
    (baseChangeChart c m) (baseChangeChart c n)
    (baseChangeChart_compatibility c q f m n hc) (baseChangeChart_unit c n hn)
    (baseChangeLift c l) (by rw [baseChangeLift_chart, hl]) hfactor

end Field

end Langlands.GroupScheme.KernelProductChart
