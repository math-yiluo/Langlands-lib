import Mathlib.Algebra.Group.End
import Langlands.AlgebraicGeometry.FiniteEtale.Definitions
import Langlands.AlgebraicGeometry.FiniteEtale.Statements
import Langlands.AbelianScheme.Tate.Integral
import Langlands.AbelianScheme.Tate.AbelianScheme
import Langlands.AbelianScheme.Tate.PrimeAdic
import Langlands.AbelianScheme.TorsionFiniteEtaleStatement

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj PreGaloisCategory
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u
namespace Langlands.AlgebraicGeometry.FiniteEtale
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))

/-- The cover associated with an actual object of the slice. -/
def ofOver (Y : Over S) [IsFinite Y.hom] [Etale Y.hom] : Cover S :=
  ⟨Y, inferInstance, inferInstance⟩

/-- Evaluation on the actual points of a finite étale object of the slice. -/
def act (Y : Over S) [IsFinite Y.hom] [Etale Y.hom]
    (g : FundamentalGroup s hfin) (x : Over.mk s ⟶ Y) : Over.mk s ⟶ Y :=
  g.hom.app (ofOver Y) x

theorem act_naturality {Y Z : Over S} [IsFinite Y.hom] [Etale Y.hom]
    [IsFinite Z.hom] [Etale Z.hom] (f : Y ⟶ Z)
    (g : FundamentalGroup s hfin) (x : Over.mk s ⟶ Y) :
    act s hfin Z g (x ≫ f) = act s hfin Y g x ≫ f :=
  smul_naturality s hfin (Y := ofOver Y) (Z := ofOver Z) (ObjectProperty.homMk f) g x

instance tensor_isFinite (Y Z : Over S) [IsFinite Y.hom] [IsFinite Z.hom] :
    IsFinite (Y ⊗ Z).hom := by
  change IsFinite (pullback.fst Y.hom Z.hom ≫ Y.hom)
  infer_instance
instance tensor_etale (Y Z : Over S) [Etale Y.hom] [Etale Z.hom] :
    Etale (Y ⊗ Z).hom := by
  change Etale (pullback.fst Y.hom Z.hom ≫ Y.hom)
  infer_instance

/-- Product preservation follows from naturality with both projections. -/
theorem act_lift (Y Z : Over S) [IsFinite Y.hom] [Etale Y.hom]
    [IsFinite Z.hom] [Etale Z.hom] (g : FundamentalGroup s hfin)
    (x : Over.mk s ⟶ Y) (y : Over.mk s ⟶ Z) :
    act s hfin (Y ⊗ Z) g (lift x y) = lift (act s hfin Y g x) (act s hfin Z g y) := by
  apply hom_ext
  · rw [← act_naturality, lift_fst, lift_fst]
  · rw [← act_naturality, lift_snd, lift_snd]

instance unit_isFinite : IsFinite (𝟙_ (Over S)).hom := by
  change IsFinite (𝟙 S)
  infer_instance
instance unit_etale : Etale (𝟙_ (Over S)).hom := by
  change Etale (𝟙 S)
  infer_instance

variable (G : Grp (Over S)) [IsFinite G.X.hom] [Etale G.X.hom]

/-- Naturality with the unit fixes the identity point. -/
theorem act_one (g : FundamentalGroup s hfin) :
    act s hfin G.X g (1 : Over.mk s ⟶ G.X) = 1 := by
  change act s hfin G.X g (toUnit _ ≫ η[G.X]) = toUnit _ ≫ η[G.X]
  rw [act_naturality]
  congr 1
  exact toUnit_unique _ _

/-- Naturality with multiplication preserves the actual group law on points. -/
theorem act_mul (g : FundamentalGroup s hfin) (x y : Over.mk s ⟶ G.X) :
    act s hfin G.X g (x * y) = act s hfin G.X g x * act s hfin G.X g y := by
  change act s hfin G.X g (lift x y ≫ μ[G.X]) = _
  rw [act_naturality, act_lift]
  rfl

/-- Evaluation, now bundled as additive automorphisms of actual group-scheme points. -/
def groupMonodromy (g : FundamentalGroup s hfin) : AddAut (Additive (Over.mk s ⟶ G.X)) :=
    { toFun := fun x => Additive.ofMul (act s hfin G.X g x.toMul)
      invFun := fun x => Additive.ofMul (act s hfin G.X g⁻¹ x.toMul)
      left_inv := fun x => by
        change g.inv.app (ofOver G.X) (g.hom.app (ofOver G.X) x) = x
        exact ConcreteCategory.congr_hom (g.hom_inv_id_app (ofOver G.X)) x
      right_inv := fun x => by
        change g.hom.app (ofOver G.X) (g.inv.app (ofOver G.X) x) = x
        exact ConcreteCategory.congr_hom (g.inv_hom_id_app (ofOver G.X)) x
      map_add' := fun x y => act_mul s hfin G g x.toMul y.toMul }

theorem groupMonodromy_one (x : Additive (Over.mk s ⟶ G.X)) :
    groupMonodromy s hfin G 1 x = x := rfl

theorem groupMonodromy_mul (g h : FundamentalGroup s hfin)
    (x : Additive (Over.mk s ⟶ G.X)) :
    groupMonodromy s hfin G (g * h) x =
      groupMonodromy s hfin G g (groupMonodromy s hfin G h x) := rfl

/-- The evaluation action, in additive notation. Install locally when needed. -/
@[instance_reducible] def groupAction :
    DistribMulAction (FundamentalGroup s hfin) (Additive (Over.mk s ⟶ G.X)) where
  smul := fun g x => groupMonodromy s hfin G g x
  one_smul := groupMonodromy_one s hfin G
  mul_smul := groupMonodromy_mul s hfin G
  smul_zero g := map_zero (groupMonodromy s hfin G g)
  smul_add g := map_add (groupMonodromy s hfin G g)

@[simp] theorem groupMonodromy_apply (g : FundamentalGroup s hfin)
    (x : Additive (Over.mk s ⟶ G.X)) :
    (groupMonodromy s hfin G g x).toMul = act s hfin G.X g x.toMul := rfl

/-- The topology here is precisely the existing discrete geometric-fibre topology. -/
theorem continuous_groupMonodromy :
    @Continuous (FundamentalGroup s hfin × Additive (Over.mk s ⟶ G.X))
      (Additive (Over.mk s ⟶ G.X))
      (inferInstance : TopologicalSpace (FundamentalGroup s hfin × Fiber s (ofOver G.X)))
      (fiberTopology s (ofOver G.X))
      (fun z => groupMonodromy s hfin G z.1 z.2) :=
  (fiberContinuousSMul s hfin (ofOver G.X)).continuous_smul

/-- Actual finite étale group-scheme homomorphisms intertwine the action. -/
theorem groupMonodromy_naturality {H : Grp (Over S)}
    [IsFinite H.X.hom] [Etale H.X.hom] (f : G ⟶ H)
    (g : FundamentalGroup s hfin) (x : Additive (Over.mk s ⟶ G.X)) :
    (groupMonodromy s hfin H g (Additive.ofMul (x.toMul ≫ f.hom.hom))).toMul =
      (groupMonodromy s hfin G g x).toMul ≫ f.hom.hom :=
  act_naturality s hfin f.hom.hom g x.toMul

end Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.GroupScheme.Tate
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]

/-- A morphism into the existing torsion kernel, constructed by its point equivalence. -/
def kernelLift (T : Over S) (n : ℕ) (x : Level G T n) :
    T ⟶ (kernel (multiplication G n)).X :=
  ((kernelLevelEquiv G T n).symm x).toMul

@[simp] theorem kernelLift_ι (T : Over S) (n : ℕ) (x : Level G T n) :
    kernelLift G T n x ≫ (kernelι (multiplication G n)).hom.hom = x.toMul.val :=
  congrArg (fun z : Level G T n => z.toMul.val)
    ((kernelLevelEquiv G T n).apply_symm_apply x)

/-- The universal kernel point, viewed as a torsion section of the original scheme. -/
def kernelSection (n : ℕ) : Level G (kernel (multiplication G n)).X n :=
  kernelLevelEquiv G _ n (Additive.ofMul (𝟙 _))

@[simp] theorem kernelSection_val (n : ℕ) :
    (kernelSection G n).toMul.val = (kernelι (multiplication G n)).hom.hom := by
  change (𝟙 _) ≫ _ = _
  simp

/-- The actual `[m/n]` map between multiplication kernels. -/
def kernelTransition {n m : ℕ} (h : n ∣ m) :
    (kernel (multiplication G m)).X ⟶ (kernel (multiplication G n)).X :=
  kernelLift G _ n (transition G _ h (kernelSection G m))

/-- Its composite with the kernel inclusion is the published multiplication morphism. -/
theorem kernelTransition_ι {n m : ℕ} (h : n ∣ m) :
    kernelTransition G h ≫ (kernelι (multiplication G n)).hom.hom =
      (kernelι (multiplication G m)).hom.hom ≫ (multiplication G (m / n : ℕ)).hom.hom := by
  rw [kernelTransition, kernelLift_ι]
  change (kernelSection G m).toMul.val ^ (m / n) = _
  rw [kernelSection_val, points_multiplication]
  exact (zpow_natCast _ _).symm

/-- On all test-scheme points this is exactly the existing Tate transition. -/
theorem kernelLevelEquiv_transition (T : Over S) {n m : ℕ} (h : n ∣ m)
    (x : Additive (T ⟶ (kernel (multiplication G m)).X)) :
    kernelLevelEquiv G T n (Additive.ofMul (x.toMul ≫ kernelTransition G h)) =
      transition G T h (kernelLevelEquiv G T m x) := by
  apply toSection_injective G T n
  change (x.toMul ≫ kernelTransition G h) ≫ (kernelι (multiplication G n)).hom.hom =
    (x.toMul ≫ (kernelι (multiplication G m)).hom.hom) ^ (m / n)
  rw [Category.assoc, kernelTransition_ι, ← Category.assoc, points_multiplication]
  exact zpow_natCast _ _

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]
/-- The map between actual torsion kernels induced by a group-scheme homomorphism. -/
def kernelLevelMap (f : G ⟶ H) (n : ℕ) :
    (kernel (multiplication G n)).X ⟶ (kernel (multiplication H n)).X :=
  kernelLift H _ n (levelMap _ f n (kernelSection G n))

@[simp] theorem kernelLevelMap_ι (f : G ⟶ H) (n : ℕ) :
    kernelLevelMap f n ≫ (kernelι (multiplication H n)).hom.hom =
      (kernelι (multiplication G n)).hom.hom ≫ f.hom.hom := by
  rw [kernelLevelMap, kernelLift_ι]
  change (kernelSection G n).toMul.val ≫ f.hom.hom = _
  rw [kernelSection_val]

theorem kernelLevelEquiv_map (T : Over S) (f : G ⟶ H) (n : ℕ)
    (x : Additive (T ⟶ (kernel (multiplication G n)).X)) :
    kernelLevelEquiv H T n (Additive.ofMul (x.toMul ≫ kernelLevelMap f n)) =
      levelMap T f n (kernelLevelEquiv G T n x) := by
  apply toSection_injective H T n
  change (x.toMul ≫ kernelLevelMap f n) ≫ (kernelι (multiplication H n)).hom.hom =
    (x.toMul ≫ (kernelι (multiplication G n)).hom.hom) ≫ f.hom.hom
  rw [Category.assoc, kernelLevelMap_ι, Category.assoc]

section Monodromy
open Langlands.AlgebraicGeometry.FiniteEtale
variable {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
variable (G) (n : ℕ)
  [IsFinite (kernel (multiplication G n)).X.hom]
  [Etale (kernel (multiplication G n)).X.hom]

/-- Transport of actual kernel-fibre evaluation through the published equivalence. -/
def finiteLevelMonodromy (g : FundamentalGroup s hfin) : AddAut (Level G (Over.mk s) n) :=
  ((kernelLevelEquiv G (Over.mk s) n).symm.trans
    (groupMonodromy s hfin (kernel (multiplication G n)) g)).trans
      (kernelLevelEquiv G (Over.mk s) n)

/-- Explicit compatibility with the evaluation action on underlying kernel points. -/
@[simp] theorem finiteLevelMonodromy_kernel (g : FundamentalGroup s hfin)
    (x : Additive (Over.mk s ⟶ (kernel (multiplication G n)).X)) :
    finiteLevelMonodromy G s hfin n g (kernelLevelEquiv G (Over.mk s) n x) =
      kernelLevelEquiv G (Over.mk s) n
        (Additive.ofMul (act s hfin (kernel (multiplication G n)).X g x.toMul)) := by
  simp [finiteLevelMonodromy, groupMonodromy]

theorem finiteLevelMonodromy_one (x : Level G (Over.mk s) n) :
    finiteLevelMonodromy G s hfin n 1 x = x := by
  change kernelLevelEquiv G (Over.mk s) n ((kernelLevelEquiv G (Over.mk s) n).symm x) = x
  exact AddEquiv.apply_symm_apply _ x

theorem finiteLevelMonodromy_mul (g h : FundamentalGroup s hfin)
    (x : Level G (Over.mk s) n) :
    finiteLevelMonodromy G s hfin n (g * h) x =
      finiteLevelMonodromy G s hfin n g (finiteLevelMonodromy G s hfin n h x) := by
  simp only [finiteLevelMonodromy, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  rfl

include hfin in
/-- Finiteness is deduced from `hfin`, not imposed on the level. -/
theorem finiteLevel_finite : Finite (Level G (Over.mk s) n) := by
  have : Finite (Additive (Over.mk s ⟶ (kernel (multiplication G n)).X)) :=
    hfin (ofOver (kernel (multiplication G n)).X)
  exact Finite.of_injective (kernelLevelEquiv G (Over.mk s) n).symm
    (kernelLevelEquiv G (Over.mk s) n).symm.injective

/-- Joint continuity with the published discrete level topology. -/
theorem continuous_finiteLevelMonodromy :
    Continuous (fun z : FundamentalGroup s hfin × Level G (Over.mk s) n =>
      finiteLevelMonodromy G s hfin n z.1 z.2) := by
  let K := kernel (multiplication G n)
  let : TopologicalSpace (Additive (Over.mk s ⟶ K.X)) := fiberTopology s (ofOver K.X)
  let : DiscreteTopology (Additive (Over.mk s ⟶ K.X)) := ⟨rfl⟩
  have he : Continuous (kernelLevelEquiv G (Over.mk s) n) := continuous_of_discreteTopology
  have hi : Continuous (kernelLevelEquiv G (Over.mk s) n).symm := continuous_of_discreteTopology
  exact he.comp ((continuous_groupMonodromy s hfin K).comp
    (continuous_fst.prodMk (hi.comp continuous_snd)))

/-- Additive evaluation commutes with the already published residue scalar action. -/
theorem finiteLevelMonodromy_zmod_smul (g : FundamentalGroup s hfin)
    (a : ZMod n) (x : Level G (Over.mk s) n) :
    finiteLevelMonodromy G s hfin n g (a • x) =
      a • finiteLevelMonodromy G s hfin n g x := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  simp only [Int.cast_smul_eq_zsmul, map_zsmul]

variable {n}
/-- The existing divisibility transition is equivariant. -/
theorem finiteLevelMonodromy_transition {m : ℕ}
    [IsFinite (kernel (multiplication G m)).X.hom]
    [Etale (kernel (multiplication G m)).X.hom]
    (h : n ∣ m) (g : FundamentalGroup s hfin) (x : Level G (Over.mk s) m) :
    finiteLevelMonodromy G s hfin n g (transition G (Over.mk s) h x) =
      transition G (Over.mk s) h (finiteLevelMonodromy G s hfin m g x) := by
  obtain ⟨y, rfl⟩ := (kernelLevelEquiv G (Over.mk s) m).surjective x
  rw [← kernelLevelEquiv_transition, finiteLevelMonodromy_kernel,
    finiteLevelMonodromy_kernel, ← kernelLevelEquiv_transition]
  congr 1
  exact act_naturality s hfin (kernelTransition G h) g y.toMul

/-- The existing map of torsion levels is equivariant for actual group-scheme maps. -/
theorem finiteLevelMonodromy_map
    [IsFinite (kernel (multiplication H n)).X.hom]
    [Etale (kernel (multiplication H n)).X.hom]
    (f : G ⟶ H) (g : FundamentalGroup s hfin) (x : Level G (Over.mk s) n) :
    finiteLevelMonodromy H s hfin n g (levelMap (Over.mk s) f n x) =
      levelMap (Over.mk s) f n (finiteLevelMonodromy G s hfin n g x) := by
  obtain ⟨y, rfl⟩ := (kernelLevelEquiv G (Over.mk s) n).surjective x
  rw [← kernelLevelEquiv_map, finiteLevelMonodromy_kernel,
    finiteLevelMonodromy_kernel, ← kernelLevelEquiv_map]
  congr 1
  exact act_naturality s hfin (kernelLevelMap f n) g y.toMul

end Monodromy
end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤)))

/-- The actual multiplication kernel, packaged using the named geometric theorem hypothesis. -/
def torsionCover : Cover S :=
  ⟨(GroupScheme.kernel (GroupScheme.multiplication A.toGrp n)).X,
    (htor S A n hn hu).1, (htor S A n hn hu).2⟩

include htor hn hu in
/-- The finite part of the explicit theorem dependency for this actual kernel. -/
theorem torsionKernel_isFinite :
    IsFinite (GroupScheme.kernel (GroupScheme.multiplication A.toGrp n)).X.hom :=
  (htor S A n hn hu).1

include htor hn hu in
/-- The étale part of the explicit theorem dependency for this actual kernel. -/
theorem torsionKernel_etale :
    Etale (GroupScheme.kernel (GroupScheme.multiplication A.toGrp n)).X.hom :=
  (htor S A n hn hu).2

/-- Geometric monodromy on the existing positive, invertible torsion level. -/
def levelMonodromy (g : FundamentalGroup s hfin) : AddAut (Level A (Over.mk s) n) := by
  letI := torsionKernel_isFinite htor A n hn hu
  letI := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevelMonodromy A.toGrp s hfin n g

/-- Forward transport is exactly evaluation at the actual torsion cover. -/
theorem levelMonodromy_kernel (g : FundamentalGroup s hfin)
    (x : Additive (Over.mk s ⟶ (GroupScheme.kernel
      (GroupScheme.multiplication A.toGrp n)).X)) :
    levelMonodromy s hfin htor A n hn hu g (kernelLevelEquiv A (Over.mk s) n x) =
      kernelLevelEquiv A (Over.mk s) n
        (Additive.ofMul (g.hom.app (torsionCover htor A n hn hu) x.toMul)) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevelMonodromy_kernel A.toGrp s hfin n g x

/-- The explicit formula on underlying kernel points, in the reverse direction. -/
theorem kernelPoint_levelMonodromy (g : FundamentalGroup s hfin)
    (x : Level A (Over.mk s) n) :
    ((kernelLevelEquiv A (Over.mk s) n).symm
      (levelMonodromy s hfin htor A n hn hu g x)).toMul =
        g.hom.app (torsionCover htor A n hn hu)
          ((kernelLevelEquiv A (Over.mk s) n).symm x).toMul := by
  obtain ⟨y, rfl⟩ := (kernelLevelEquiv A (Over.mk s) n).surjective x
  rw [levelMonodromy_kernel, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  rfl

@[simp] theorem levelMonodromy_one (x : Level A (Over.mk s) n) :
    levelMonodromy s hfin htor A n hn hu 1 x = x := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevelMonodromy_one A.toGrp s hfin n x

theorem levelMonodromy_mul (g h : FundamentalGroup s hfin) (x : Level A (Over.mk s) n) :
    levelMonodromy s hfin htor A n hn hu (g * h) x =
      levelMonodromy s hfin htor A n hn hu g (levelMonodromy s hfin htor A n hn hu h x) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevelMonodromy_mul A.toGrp s hfin n g h x

@[simp] theorem levelMonodromy_zero (g : FundamentalGroup s hfin) :
    levelMonodromy s hfin htor A n hn hu g 0 = 0 :=
  map_zero _

theorem levelMonodromy_add (g : FundamentalGroup s hfin) (x y : Level A (Over.mk s) n) :
    levelMonodromy s hfin htor A n hn hu g (x + y) =
      levelMonodromy s hfin htor A n hn hu g x + levelMonodromy s hfin htor A n hn hu g y :=
  _root_.map_add _ x y

theorem levelMonodromy_zmod_smul (g : FundamentalGroup s hfin)
    (a : ZMod n) (x : Level A (Over.mk s) n) :
    levelMonodromy s hfin htor A n hn hu g (a • x) =
      a • levelMonodromy s hfin htor A n hn hu g x := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  simp only [Int.cast_smul_eq_zsmul, map_zsmul]

/-- A locally installable action; no geometric theorem is hidden in an instance. -/
@[instance_reducible] def levelAction :
    DistribMulAction (FundamentalGroup s hfin) (Level A (Over.mk s) n) where
  smul := fun g x => levelMonodromy s hfin htor A n hn hu g x
  one_smul := levelMonodromy_one s hfin htor A n hn hu
  mul_smul := levelMonodromy_mul s hfin htor A n hn hu
  smul_zero := levelMonodromy_zero s hfin htor A n hn hu
  smul_add := levelMonodromy_add s hfin htor A n hn hu

include htor hn hu hfin in
/-- The finite level is finite by the actual fibre equivalence and `hfin`. -/
theorem level_finite : Finite (Level A (Over.mk s) n) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.finiteLevel_finite A.toGrp s hfin n

/-- Joint continuity uses the existing discrete level topology. -/
theorem continuous_levelMonodromy :
    Continuous (fun z : FundamentalGroup s hfin × Level A (Over.mk s) n =>
      levelMonodromy s hfin htor A n hn hu z.1 z.2) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  exact GroupScheme.Tate.continuous_finiteLevelMonodromy A.toGrp s hfin n

/-- Continuity packaged for the locally installed action. -/
theorem levelAction_continuousSMul :
    letI := levelAction s hfin htor A n hn hu
    ContinuousSMul (FundamentalGroup s hfin) (Level A (Over.mk s) n) := by
  let := levelAction s hfin htor A n hn hu
  exact ⟨continuous_levelMonodromy s hfin htor A n hn hu⟩

/-- Equivariance of the published divisor transition, at two positive invertible levels. -/
theorem levelMonodromy_transition (m : ℕ) (hm : 0 < m)
    (hu_m : IsUnit (m : Γ(S, ⊤))) (h : n ∣ m)
    (g : FundamentalGroup s hfin) (x : Level A (Over.mk s) m) :
    levelMonodromy s hfin htor A n hn hu g (transition A (Over.mk s) h x) =
      transition A (Over.mk s) h (levelMonodromy s hfin htor A m hm hu_m g x) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  have := torsionKernel_isFinite htor A m hm hu_m
  have := torsionKernel_etale htor A m hm hu_m
  exact GroupScheme.Tate.finiteLevelMonodromy_transition A.toGrp s hfin h g x

/-- Equivariance of the published level map for an actual abelian-scheme homomorphism. -/
theorem levelMonodromy_map {B : AbelianScheme S} (f : A ⟶ B)
    (g : FundamentalGroup s hfin) (x : Level A (Over.mk s) n) :
    levelMonodromy s hfin htor B n hn hu g (levelMap (Over.mk s) f n x) =
      levelMap (Over.mk s) f n (levelMonodromy s hfin htor A n hn hu g x) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  have := torsionKernel_isFinite htor B n hn hu
  have := torsionKernel_etale htor B n hn hu
  exact GroupScheme.Tate.finiteLevelMonodromy_map A.toGrp s hfin (AbelianScheme.groupHom f) g x

end Langlands.AbelianScheme.Tate
