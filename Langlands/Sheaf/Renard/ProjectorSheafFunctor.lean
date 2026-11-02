import Langlands.Sheaf.Renard.ProjectorSheaf
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Functoriality of the original-action projector sheaf

The component maps retain independent source and target carrier universes.
Categorical natural transformations fix one carrier universe, independent of
the space universe.
-/

noncomputable section

open CategoryTheory Opposite
open Langlands.Algebra Langlands.HarmonicAnalysis

universe u v w z

namespace Langlands.Sheaf.Renard.ProjectorBasisSheaf

variable {X : Type u} [TopologicalSpace X]
  (hX : Langlands.Topology.IsLocallyProfinite X)

section Components

variable {M : Type v} {N : Type w} {P : Type z}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) N]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) P]

/-- Restrict the original additive map to the exact published fixed subgroup. -/
def valueMap (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    (U : CompactOpen hX) : Value hX M U →+ Value hX N U :=
  (NonUnitalModuleCorner.restrict (idempotent hX U) f).toAddMonoidHom

@[simp] theorem valueMap_val
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    (U : CompactOpen hX) (s : Value hX M U) :
    (valueMap hX f U s).val = f s.val := rfl

/-- The complete component function, including its fixed-subgroup proof. -/
theorem coe_valueMap
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    (U : CompactOpen hX) :
    ⇑(valueMap hX f U) =
      fun s => ⟨f s.val,
        NonUnitalModuleCorner.map_mem_fixedPart (idempotent hX U) f s.property⟩ := rfl

/-- Naturality as an equality of entire additive maps, at independent universes. -/
theorem valueMap_naturality
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    {U V : CompactOpen hX} (h : U.obj ≤ V.obj) :
    (valueMap hX f U).comp (restrict hX M h) =
      (restrict hX N h).comp (valueMap hX f V) := by
  ext s
  exact Subtype.ext (f.map_smul (test hX U) s.val)

theorem valueMap_naturality_apply
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    {U V : CompactOpen hX} (h : U.obj ≤ V.obj) (s : Value hX M V) :
    valueMap hX f U (restrict hX M h s) =
      restrict hX N h (valueMap hX f V s) :=
  DFunLike.congr_fun (valueMap_naturality hX f h) s

@[simp] theorem valueMap_id (U : CompactOpen hX) :
    valueMap hX (NonUnitalModuleHom.id (PointwiseTestAlgebra.Carrier X) M) U =
      AddMonoidHom.id (Value hX M U) := by
  ext s
  rfl

@[simp] theorem valueMap_comp
    (g : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) N P)
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    (U : CompactOpen hX) :
    valueMap hX (g.comp f) U =
      (valueMap hX g U).comp (valueMap hX f U) := by
  ext s
  rfl

@[simp] theorem valueMap_zero (U : CompactOpen hX) :
    valueMap hX (0 : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) U = 0 := by
  ext s
  rfl

@[simp] theorem valueMap_add
    (f g : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    (U : CompactOpen hX) :
    valueMap hX (f + g) U = valueMap hX f U + valueMap hX g U := by
  ext s
  rfl

/-- The component assignment is additive on original intertwiner groups. -/
def valueMapAddHom (U : CompactOpen hX) :
    NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N →+
      (Value hX M U →+ Value hX N U) where
  toFun f := valueMap hX f U
  map_zero' := valueMap_zero hX U
  map_add' f g := valueMap_add hX f g U

end Components

section NaturalTransformations

variable {M N P : Type v}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) N]
  [NonUnitalModule (PointwiseTestAlgebra.Carrier X) P]

/-- The actual natural transformation with original-map components. -/
def rawMap (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) :
    rawPresheaf hX M ⟶ rawPresheaf hX N where
  app U := AddCommGrpCat.ofHom (valueMap hX f U.unop)
  naturality U V h := by
    exact congrArg AddCommGrpCat.ofHom
      (valueMap_naturality hX f h.unop.hom.le)

@[simp] theorem rawMap_app_hom
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    (U : CompactOpen hX) :
    ((rawMap hX f).app (op U)).hom = valueMap hX f U := rfl

@[simp] theorem rawMap_app_val
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    (U : CompactOpen hX) (s : Value hX M U) :
    ((rawMap hX f).app (op U) s).val = f s.val := rfl

@[simp] theorem rawMap_id :
    rawMap hX (NonUnitalModuleHom.id (PointwiseTestAlgebra.Carrier X) M) =
      𝟙 (rawPresheaf hX M) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  rfl

@[simp] theorem rawMap_comp
    (g : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) N P)
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) :
    rawMap hX (g.comp f) = rawMap hX f ≫ rawMap hX g := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  rfl

@[simp] theorem rawMap_zero :
    rawMap hX (0 : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  rfl

@[simp] theorem rawMap_add
    (f g : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) :
    rawMap hX (f + g) = rawMap hX f + rawMap hX g := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  rfl

/-- The actual sheaf morphism, using the proved intrinsic sheaf condition. -/
def sheafMap (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) :
    basisSheaf hX M ⟶ basisSheaf hX N :=
  ObjectProperty.homMk (ObjectProperty.homMk (rawMap hX f))

@[simp] theorem sheafMap_app_hom
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    (U : CompactOpen hX) :
    ((sheafMap hX f).hom.hom.app (op U)).hom = valueMap hX f U := rfl

theorem coe_sheafMap_app
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    (U : CompactOpen hX) :
    ⇑((sheafMap hX f).hom.hom.app (op U)) =
      fun s => ⟨f s.val,
        NonUnitalModuleCorner.map_mem_fixedPart (idempotent hX U) f s.property⟩ := rfl

@[simp] theorem sheafMap_app_val
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    (U : CompactOpen hX) (s : Value hX M U) :
    ((sheafMap hX f).hom.hom.app (op U) s).val = f s.val := rfl

theorem sheafMap_naturality
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N)
    {U V : CompactOpen hX} (h : U.obj ≤ V.obj) :
    restriction (rawPresheaf hX M) h ≫ (sheafMap hX f).hom.hom.app (op U) =
      (sheafMap hX f).hom.hom.app (op V) ≫ restriction (rawPresheaf hX N) h :=
  restriction_naturality (rawMap hX f) h

@[simp] theorem sheafMap_id :
    sheafMap hX (NonUnitalModuleHom.id (PointwiseTestAlgebra.Carrier X) M) =
      𝟙 (basisSheaf hX M) := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact rawMap_id hX

@[simp] theorem sheafMap_comp
    (g : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) N P)
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) :
    sheafMap hX (g.comp f) = sheafMap hX f ≫ sheafMap hX g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact rawMap_comp hX g f

@[simp] theorem sheafMap_zero :
    sheafMap hX (0 : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) = 0 := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact rawMap_zero hX

@[simp] theorem sheafMap_add
    (f g : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) :
    sheafMap hX (f + g) = sheafMap hX f + sheafMap hX g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact rawMap_add hX f g

end NaturalTransformations

/-- The actual module-to-basis-sheaf functor at the unchanged carrier universe. -/
def functor :
    NonUnitalModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X) ⥤
      BasisSheaf.{u,v} (compactOpenBasis hX) where
  obj M := basisSheaf hX M
  map f := sheafMap hX f
  map_id _M := sheafMap_id hX
  map_comp f g := sheafMap_comp hX g f

@[simp] theorem functor_obj
    (M : NonUnitalModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X)) :
    (functor hX).obj M = basisSheaf hX M := rfl

@[simp] theorem functor_map
    {M N : NonUnitalModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X)} (f : M ⟶ N) :
    (functor hX).map f = sheafMap hX f := rfl

@[simp] theorem functor_map_app_val
    {M N : NonUnitalModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X)}
    (f : M ⟶ N) (U : CompactOpen hX) (s : Value hX M U) :
    (((functor hX).map f).hom.hom.app (op U) s).val =
      (NonUnitalModuleHom.toAddMonoidHom f) s.val := rfl

instance functor_additive : (functor.{u,v} hX).Additive where
  map_add := by
    intro M N f g
    exact sheafMap_add hX f g

@[simp] theorem functor_map_zero
    (M N : NonUnitalModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X)) :
    (functor hX).map (0 : M ⟶ N) = 0 := (functor hX).map_zero M N

@[simp] theorem functor_map_add
    {M N : NonUnitalModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X)}
    (f g : M ⟶ N) :
    (functor hX).map (f + g) = (functor hX).map f + (functor hX).map g :=
  (functor hX).map_add

/-- Renard's nondegenerate specialization is restriction along the published inclusion. -/
def nondegenerateFunctor :
    NondegenerateModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X) ⥤
      BasisSheaf.{u,v} (compactOpenBasis hX) :=
  nondegenerateInclusion (PointwiseTestAlgebra.Carrier X) ⋙ functor hX

theorem nondegenerateFunctor_eq :
    nondegenerateFunctor.{u,v} hX =
      nondegenerateInclusion (PointwiseTestAlgebra.Carrier X) ⋙ functor hX := rfl

instance nondegenerateFunctor_additive :
    (nondegenerateFunctor.{u,v} hX).Additive := by
  change (nondegenerateInclusion (PointwiseTestAlgebra.Carrier X) ⋙
    functor.{u,v} hX).Additive
  infer_instance

@[simp] theorem nondegenerateFunctor_obj
    (M : NondegenerateModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X)) :
    (nondegenerateFunctor hX).obj M = basisSheaf hX M.obj := rfl

@[simp] theorem nondegenerateFunctor_map
    {M N : NondegenerateModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X)} (f : M ⟶ N) :
    (nondegenerateFunctor hX).map f = sheafMap hX f.hom := rfl

@[simp] theorem nondegenerateFunctor_map_app_val
    {M N : NondegenerateModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X)}
    (f : M ⟶ N) (U : CompactOpen hX) (s : Value hX M.obj U) :
    (((nondegenerateFunctor hX).map f).hom.hom.app (op U) s).val =
      (NonUnitalModuleHom.toAddMonoidHom f.hom) s.val := rfl

@[simp] theorem nondegenerateFunctor_map_zero
    (M N : NondegenerateModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X)) :
    (nondegenerateFunctor hX).map (0 : M ⟶ N) = 0 :=
  (nondegenerateFunctor hX).map_zero M N

@[simp] theorem nondegenerateFunctor_map_add
    {M N : NondegenerateModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X)}
    (f g : M ⟶ N) :
    (nondegenerateFunctor hX).map (f + g) =
      (nondegenerateFunctor hX).map f + (nondegenerateFunctor hX).map g :=
  (nondegenerateFunctor hX).map_add

/-! Complete unapplied interfaces, including both unequal universe directions. -/

example : {X : Type u} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    {M : Type v} → {N : Type w} →
    [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M] →
    [NonUnitalModule (PointwiseTestAlgebra.Carrier X) N] →
    NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N →
    (U : CompactOpen hX) → (Value hX M U →+ Value hX N U) :=
  @valueMap.{u,v,w}

example : {X : Type u} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    {M : Type v} → {N : Type w} →
    [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M] →
    [NonUnitalModule (PointwiseTestAlgebra.Carrier X) N] →
    (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N) →
    {U V : CompactOpen hX} → (h : U.obj ≤ V.obj) →
    (valueMap hX f U).comp (restrict hX M h) =
      (restrict hX N h).comp (valueMap hX f V) :=
  @valueMap_naturality.{u,v,w}

example : {X : Type u} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    NonUnitalModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X) ⥤
      BasisSheaf.{u,v} (compactOpenBasis hX) :=
  @functor.{u,v}

example : {X : Type u} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    (functor.{u,v} hX).Additive :=
  @functor_additive.{u,v}

example : {X : Type u} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    NondegenerateModuleCat.{u,v} (PointwiseTestAlgebra.Carrier X) ⥤
      BasisSheaf.{u,v} (compactOpenBasis hX) :=
  @nondegenerateFunctor.{u,v}

example : {X : Type u} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    (nondegenerateFunctor.{u,v} hX).Additive :=
  @nondegenerateFunctor_additive.{u,v}

example : {X : Type} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    NonUnitalModuleCat.{0,1} (PointwiseTestAlgebra.Carrier X) ⥤
      BasisSheaf.{0,1} (compactOpenBasis hX) :=
  @functor.{0,1}

example : {X : Type 1} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    NonUnitalModuleCat.{1,0} (PointwiseTestAlgebra.Carrier X) ⥤
      BasisSheaf.{1,0} (compactOpenBasis hX) :=
  @functor.{1,0}

example : {X : Type} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    NondegenerateModuleCat.{0,1} (PointwiseTestAlgebra.Carrier X) ⥤
      BasisSheaf.{0,1} (compactOpenBasis hX) :=
  @nondegenerateFunctor.{0,1}

example : {X : Type 1} → [TopologicalSpace X] →
    (hX : Langlands.Topology.IsLocallyProfinite X) →
    NondegenerateModuleCat.{1,0} (PointwiseTestAlgebra.Carrier X) ⥤
      BasisSheaf.{1,0} (compactOpenBasis hX) :=
  @nondegenerateFunctor.{1,0}

end Langlands.Sheaf.Renard.ProjectorBasisSheaf
