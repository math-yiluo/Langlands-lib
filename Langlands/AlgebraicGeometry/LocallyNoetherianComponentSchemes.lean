import Langlands.AlgebraicGeometry.LocallyNoetherianConnectedComponentOpenProof
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Actual connected-component schemes and induced morphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Langlands.AlgebraicGeometry

/-- The map on actual topological connected components induced by a scheme map. -/
def componentMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ConnectedComponents X → ConnectedComponents Y :=
  f.continuous.connectedComponentsMap

@[simp] theorem componentMap_mk {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    componentMap f (.mk x) = .mk (f x) :=
  f.continuous.connectedComponentsMap_mk x

@[simp] theorem componentMap_id (X : Scheme.{u}) (c : ConnectedComponents X) :
    componentMap (𝟙 X) c = c := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simp

@[simp] theorem componentMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : ConnectedComponents X) :
    componentMap (f ≫ g) c = componentMap g (componentMap f c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simp

/-- The open subset underlying an actual connected component. -/
def componentOpen (X : Scheme.{u}) [IsLocallyNoetherian X]
    (c : ConnectedComponents X) : X.Opens where
  carrier := {x | ConnectedComponents.mk x = c}
  is_open' := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    convert locallyNoetherianConnectedComponentOpen_proof X x using 1
    ext y
    exact ConnectedComponents.coe_eq_coe'

@[simp] theorem mem_componentOpen {X : Scheme.{u}} [IsLocallyNoetherian X]
    (c : ConnectedComponents X) (x : X) :
    x ∈ componentOpen X c ↔ ConnectedComponents.mk x = c := Iff.rfl

theorem componentOpen_mk (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    (componentOpen X (.mk x) : Set X) = connectedComponent x := by
  ext y
  exact ConnectedComponents.coe_eq_coe'

/-- The actual open subscheme of a locally Noetherian scheme at a component. -/
abbrev componentScheme (X : Scheme.{u}) [IsLocallyNoetherian X]
    (c : ConnectedComponents X) : Scheme.{u} :=
  (componentOpen X c).toScheme

/-- Inclusion of the actual open component scheme. -/
abbrev componentι (X : Scheme.{u}) [IsLocallyNoetherian X]
    (c : ConnectedComponents X) : componentScheme X c ⟶ X :=
  (componentOpen X c).ι

instance componentSchemeConnected (X : Scheme.{u}) [IsLocallyNoetherian X]
    (c : ConnectedComponents X) : ConnectedSpace (componentScheme X c) := by
  apply Subtype.connectedSpace
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [componentOpen_mk]
  exact isConnected_connectedComponent

instance componentSchemeLocallyNoetherian (X : Scheme.{u}) [IsLocallyNoetherian X]
    (c : ConnectedComponents X) : IsLocallyNoetherian (componentScheme X c) :=
  inferInstanceAs (IsLocallyNoetherian (componentOpen X c).toScheme)

instance componentιOpenImmersion (X : Scheme.{u}) [IsLocallyNoetherian X]
    (c : ConnectedComponents X) : IsOpenImmersion (componentι X c) := inferInstance

theorem componentOpen_disjoint (X : Scheme.{u}) [IsLocallyNoetherian X]
    {c d : ConnectedComponents X} (h : c ≠ d) :
    Disjoint (componentOpen X c) (componentOpen X d) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  exact h (hx.1.symm.trans hx.2)

theorem componentOpen_iSup (X : Scheme.{u}) [IsLocallyNoetherian X] :
    ⨆ c, componentOpen X c = ⊤ := by
  apply Opens.ext
  simp only [Opens.coe_iSup, Opens.coe_top, Set.iUnion_eq_univ_iff]
  intro x
  exact ⟨ConnectedComponents.mk x, rfl⟩

/-- The open cover by all actual connected components, including the empty cover
when the original scheme is empty. -/
def componentOpenCover (X : Scheme.{u}) [IsLocallyNoetherian X] : X.OpenCover where
  I₀ := ConnectedComponents X
  X := componentScheme X
  f := componentι X
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    exact ⟨ConnectedComponents.mk x, ⟨x, rfl⟩, rfl⟩

section Morphisms

variable {X Y Z : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

/-- Restrict an actual morphism to a source component and its specified image
component. The equality only identifies the target index. -/
def componentHomTo (f : X ⟶ Y) (c : ConnectedComponents X)
    (d : ConnectedComponents Y) (e : componentMap f c = d) :
    componentScheme X c ⟶ componentScheme Y d :=
  f.resLE (componentOpen Y d) (componentOpen X c) (by
    intro x hx
    change ConnectedComponents.mk (f x) = d
    rw [← componentMap_mk, hx, e])

@[reassoc (attr := simp)]
theorem componentHomTo_ι (f : X ⟶ Y) (c : ConnectedComponents X)
    (d : ConnectedComponents Y) (e : componentMap f c = d) :
    componentHomTo f c d e ≫ componentι Y d = componentι X c ≫ f :=
  f.resLE_comp_ι _

/-- The component factorization is uniquely determined by its inclusion square. -/
theorem componentHomTo_unique (f : X ⟶ Y) (c : ConnectedComponents X)
    (d : ConnectedComponents Y) (e : componentMap f c = d)
    (k : componentScheme X c ⟶ componentScheme Y d)
    (hk : k ≫ componentι Y d = componentι X c ≫ f) :
    k = componentHomTo f c d e := by
  apply (cancel_mono (componentι Y d)).mp
  simpa using hk

@[simp] theorem componentHomTo_id (c : ConnectedComponents X) :
    componentHomTo (𝟙 X) c c (componentMap_id X c) = 𝟙 _ := by
  symm
  apply componentHomTo_unique
  simp

/-- Component restrictions compose for every actual scheme map. -/
theorem componentHomTo_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : ConnectedComponents X) (d : ConnectedComponents Y) (e : ConnectedComponents Z)
    (hcd : componentMap f c = d) (hde : componentMap g d = e) :
    componentHomTo f c d hcd ≫ componentHomTo g d e hde =
      componentHomTo (f ≫ g) c e
        ((componentMap_comp f g c).trans ((congrArg (componentMap g) hcd).trans hde)) := by
  apply componentHomTo_unique
  simp [Category.assoc]

/-- Canonical restriction to the component selected by the actual continuous map. -/
def componentHom (f : X ⟶ Y) (c : ConnectedComponents X) :
    componentScheme X c ⟶ componentScheme Y (componentMap f c) :=
  componentHomTo f c (componentMap f c) rfl

@[reassoc (attr := simp)]
theorem componentHom_ι (f : X ⟶ Y) (c : ConnectedComponents X) :
    componentHom f c ≫ componentι Y (componentMap f c) = componentι X c ≫ f :=
  componentHomTo_ι f c _ rfl

/-- Equality transport of the target agrees with the uniquely specified component
factorization. -/
theorem componentHomTo_eqToHom (f : X ⟶ Y) (c : ConnectedComponents X)
    {d e : ConnectedComponents Y} (hd : componentMap f c = d) (h : d = e) :
    componentHomTo f c d hd ≫
        eqToHom (congrArg (componentScheme Y) h) =
      componentHomTo f c e (hd.trans h) := by
  subst h
  simp

end Morphisms

theorem componentOpen_eq_top (X : Scheme.{u}) [IsLocallyNoetherian X]
    [PreconnectedSpace X] (c : ConnectedComponents X) :
    componentOpen X c = ⊤ := by
  ext x
  exact iff_true_intro (Subsingleton.elim _ _)

/-- On a connected scheme, its sole actual component scheme is canonically the
original scheme. -/
def componentInclusionIso (X : Scheme.{u}) [IsLocallyNoetherian X]
    [PreconnectedSpace X] (c : ConnectedComponents X) :
    componentScheme X c ≅ X :=
  X.isoOfEq (componentOpen_eq_top X c) ≪≫ X.topIso

@[simp] theorem componentInclusionIso_hom (X : Scheme.{u}) [IsLocallyNoetherian X]
    [PreconnectedSpace X] (c : ConnectedComponents X) :
    (componentInclusionIso X c).hom = componentι X c := by
  simp [componentInclusionIso]

theorem componentIndex_isEmpty (X : Scheme.{u}) [IsEmpty X] :
    IsEmpty (ConnectedComponents X) :=
  ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance

end Langlands.AlgebraicGeometry
