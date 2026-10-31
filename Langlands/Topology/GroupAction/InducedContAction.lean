import Langlands.Topology.GroupAction.InducedSpace
import Langlands.CategoryTheory.TopCatSelfForget
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Induction and restriction of actual continuous topological actions -/

noncomputable section

universe u v

namespace Langlands.TopologicalInduction

open CategoryTheory

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G)

private instance actionMulAction {K : Type u} [Monoid K] [TopologicalSpace K]
    (X : ContAction TopCat.{max u v} K) : MulAction K X.obj.V :=
  inferInstanceAs (MulAction K ((forget₂ (Action TopCat K) TopCat).obj X.obj))

private instance continuousAction {K : Type u} [Monoid K] [TopologicalSpace K]
    (X : ContAction TopCat.{max u v} K) : ContinuousSMul K X.obj.V :=
  X.property

/-- Restriction along the actual continuous subgroup inclusion. -/
abbrev restrictAction : ContAction TopCat.{max u v} G ⥤ ContAction TopCat.{max u v} H :=
  ContAction.res TopCat ⟨H.subtype, continuous_subtype_val⟩

/-- The balanced quotient with its actual jointly continuous full-group action. -/
def inducedAction (X : ContAction TopCat.{max u v} H) :
    ContAction TopCat.{max u v} G :=
  ⟨{ V := TopCat.of (Space H X.obj.V)
     ρ :=
       { toFun := fun g => TopCat.ofHom ⟨(g • ·), continuous_const_smul g⟩
         map_one' := by
           apply TopCat.ext
           intro z
           exact one_smul G z
         map_mul' := by
           intro g k
           apply TopCat.ext
           intro z
           exact mul_smul g k z } },
   (Action.isContinuous_def _).mpr (by
     change Continuous (fun p : G × Space H X.obj.V => p.1 • p.2)
     exact continuous_smul)⟩

private theorem hom_smul {K : Type u} [Monoid K] [TopologicalSpace K]
    {X Y : ContAction TopCat.{max u v} K} (f : X ⟶ Y) (k : K) (x : X.obj.V) :
    f.hom.hom (k • x) = k • f.hom.hom x :=
  congrArg (fun a : X.obj.V ⟶ Y.obj.V => a x) (f.hom.comm k)

omit [IsTopologicalGroup G] in
private theorem unit_hom_equivariant {X Y : ContAction TopCat.{max u v} H}
    (f : X ⟶ Y) (h : H) (x : X.obj.V) :
    unit H (f.hom.hom (h • x)) = (h : G) • unit H (f.hom.hom x) := by
  rw [hom_smul, unit_subgroup_smul]

/-- Induce a continuous equivariant map by quotient extension. -/
def inducedMap {X Y : ContAction TopCat.{max u v} H} (f : X ⟶ Y) :
    inducedAction H X ⟶ inducedAction H Y :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom
        ⟨lift (fun x => unit H (f.hom.hom x)) (unit_hom_equivariant H f),
          continuous_lift _ _ (continuous_unit.comp f.hom.hom.hom.continuous)⟩
      comm := fun g => by
        apply TopCat.ext
        intro z
        exact lift_smul (fun x => unit H (f.hom.hom x)) (unit_hom_equivariant H f) g z }

@[simp]
theorem inducedMap_mk {X Y : ContAction TopCat.{max u v} H} (f : X ⟶ Y)
    (g : G) (x : X.obj.V) :
    (inducedMap H f).hom.hom (mk H g x) = mk H g (f.hom.hom x) := by
  change g • unit H (f.hom.hom x) = _
  exact smul_unit g _

/-- Induction on the actual continuous-action categories. -/
def induction : ContAction TopCat.{max u v} H ⥤ ContAction TopCat.{max u v} G where
  obj := inducedAction H
  map := inducedMap H
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro z
    induction z using Quotient.inductionOn with
    | h p =>
      change (inducedMap H (𝟙 X)).hom.hom (mk H p.1 p.2) = mk H p.1 p.2
      simp only [inducedMap_mk]
      rfl
  map_comp f k := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro z
    induction z using Quotient.inductionOn with
    | h p =>
      change (inducedMap H (f ≫ k)).hom.hom (mk H p.1 p.2) =
        (inducedMap H k).hom.hom ((inducedMap H f).hom.hom (mk H p.1 p.2))
      simp only [inducedMap_mk]
      rfl

/-- Restrict an induced-space morphism to the original subgroup space. -/
def restrictHom {X : ContAction TopCat.{max u v} H}
    {Y : ContAction TopCat.{max u v} G} (f : inducedAction H X ⟶ Y) :
    X ⟶ (restrictAction H).obj Y :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom
        ⟨fun x => f.hom.hom (unit H x),
          f.hom.hom.hom.continuous.comp continuous_unit⟩
      comm := fun h => by
        apply TopCat.ext
        intro x
        change f.hom.hom (unit H (h • x)) = (h : G) • f.hom.hom (unit H x)
        rw [unit_subgroup_smul]
        exact hom_smul f (h : G) (unit H x) }

@[simp]
theorem restrictHom_apply {X : ContAction TopCat.{max u v} H}
    {Y : ContAction TopCat.{max u v} G} (f : inducedAction H X ⟶ Y) (x : X.obj.V) :
    (restrictHom H f).hom.hom x = f.hom.hom (unit H x) := rfl

omit [IsTopologicalGroup G] in
private theorem restricted_hom_equivariant {X : ContAction TopCat.{max u v} H}
    {Y : ContAction TopCat.{max u v} G} (f : X ⟶ (restrictAction H).obj Y)
    (h : H) (x : X.obj.V) :
    f.hom.hom (h • x) = @SMul.smul G Y.obj.V _ (h : G) (f.hom.hom x) :=
  hom_smul f h x

/-- Extend a continuous subgroup-equivariant map across the actual quotient. -/
def extendHom {X : ContAction TopCat.{max u v} H}
    {Y : ContAction TopCat.{max u v} G} (f : X ⟶ (restrictAction H).obj Y) :
    inducedAction H X ⟶ Y :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom
        ⟨lift (Y := Y.obj.V) (fun x => f.hom.hom x) (restricted_hom_equivariant H f),
          continuous_lift (Y := Y.obj.V) _ _ f.hom.hom.hom.continuous⟩
      comm := fun g => by
        apply TopCat.ext
        intro z
        exact lift_smul (Y := Y.obj.V) (fun x => f.hom.hom x)
          (restricted_hom_equivariant H f) g z }

@[simp]
theorem extendHom_mk {X : ContAction TopCat.{max u v} H}
    {Y : ContAction TopCat.{max u v} G} (f : X ⟶ (restrictAction H).obj Y)
    (g : G) (x : X.obj.V) :
    (extendHom H f).hom.hom (mk H g x) = @SMul.smul G Y.obj.V _ g (f.hom.hom x) := rfl

/-- The continuous equivariant universal property on the categorical hom sets. -/
def inductionHomEquiv (X : ContAction TopCat.{max u v} H)
    (Y : ContAction TopCat.{max u v} G) :
    ((induction H).obj X ⟶ Y) ≃ (X ⟶ (restrictAction H).obj Y) where
  toFun := restrictHom H
  invFun := extendHom H
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro z
    induction z using Quotient.inductionOn with
    | h p =>
      change p.1 • f.hom.hom (unit H p.2) = f.hom.hom (mk H p.1 p.2)
      have he := hom_smul f p.1 (unit H p.2)
      change f.hom.hom (p.1 • unit H p.2) = p.1 • f.hom.hom (unit H p.2) at he
      rw [smul_unit] at he
      exact he.symm
  right_inv f := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    change lift (Y := Y.obj.V) (fun x => f.hom.hom x) (restricted_hom_equivariant H f)
      (unit H x) = f.hom.hom x
    exact lift_unit _ _ x

theorem inductionHomEquiv_naturality_left_symm
    {X' X : ContAction TopCat.{max u v} H} {Y : ContAction TopCat.{max u v} G}
    (f : X' ⟶ X) (k : X ⟶ (restrictAction H).obj Y) :
    (inductionHomEquiv H X' Y).symm (f ≫ k) =
      (induction H).map f ≫ (inductionHomEquiv H X Y).symm k := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply TopCat.ext
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    change (extendHom H (f ≫ k)).hom.hom (mk H p.1 p.2) =
      (extendHom H k).hom.hom ((inducedMap H f).hom.hom (mk H p.1 p.2))
    rw [extendHom_mk, inducedMap_mk, extendHom_mk]
    rfl

theorem inductionHomEquiv_naturality_right
    {X : ContAction TopCat.{max u v} H} {Y Y' : ContAction TopCat.{max u v} G}
    (f : (induction H).obj X ⟶ Y) (k : Y ⟶ Y') :
    (inductionHomEquiv H X Y') (f ≫ k) =
      (inductionHomEquiv H X Y) f ≫ (restrictAction H).map k := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  rfl

/-- Induction is left adjoint to restriction on actual continuous actions. -/
def inductionAdjunction : induction H ⊣ restrictAction H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := inductionHomEquiv H
      homEquiv_naturality_left_symm := inductionHomEquiv_naturality_left_symm H
      homEquiv_naturality_right := inductionHomEquiv_naturality_right H }

@[simp]
theorem inductionAdjunction_homEquiv (X : ContAction TopCat.{max u v} H)
    (Y : ContAction TopCat.{max u v} G) :
    (inductionAdjunction H).homEquiv X Y = inductionHomEquiv H X Y := by
  simp only [inductionAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

@[simp]
theorem inductionAdjunction_unit_apply (X : ContAction TopCat.{max u v} H) (x : X.obj.V) :
    ((inductionAdjunction H).unit.app X).hom.hom x = unit H x := rfl

@[simp]
theorem inductionAdjunction_counit_mk (Y : ContAction TopCat.{max u v} G)
    (g : G) (x : ((restrictAction H).obj Y).obj.V) :
    ((inductionAdjunction H).counit.app Y).hom.hom (mk H g x) =
      @SMul.smul G Y.obj.V _ g x := rfl

end Langlands.TopologicalInduction
