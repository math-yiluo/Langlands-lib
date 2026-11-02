import Langlands.Sheaf.Equivariant.LocallyConstant
import Mathlib.Topology.Sheaves.Functors

/-! # Direct images along actual continuous equivariant maps -/

noncomputable section

universe u v a b r w

namespace Langlands.Sheaf.Equivariant.DirectImage

open CategoryTheory TopologicalSpace Opposite

variable {G : Type v} [Group G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Inverse images of opens, retaining every original group label. -/
def preimage : ActionOpens G Y ⥤ ActionOpens G X where
  obj U := ⟨(Opens.map (TopCat.ofHom f)).obj U.openSet⟩
  map {U V} k := ⟨k.label, fun x hx => by
    change f (k.label • x) ∈ V.openSet
    rw [hf]
    exact k.mapsTo (f x) hx⟩
  map_id _ := ActionOpens.Hom.ext rfl
  map_comp _ _ := ActionOpens.Hom.ext rfl

@[simp]
theorem preimage_mem (U : ActionOpens G Y) (x : X) :
    x ∈ ((preimage f hf).obj U).openSet ↔ f x ∈ U.openSet := Iff.rfl

@[simp]
theorem preimage_map_label {U V : ActionOpens G Y} (k : U ⟶ V) :
    ((preimage f hf).map k).label = k.label := rfl

variable (A : Type a) [Category.{b} A]

/-- The complete transport-presheaf direct image is precomposition. -/
def presheaf : ((ActionOpens G X)ᵒᵖ ⥤ A) ⥤ ((ActionOpens G Y)ᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft _ _ A).obj (preimage f hf).op

/-- Forgetting labels recovers the ordinary topological direct image literally. -/
def underlyingIso :
    presheaf f hf A ⋙ underlyingPresheaf G Y A ≅
      underlyingPresheaf G X A ⋙ TopCat.Presheaf.pushforward A (TopCat.ofHom f) :=
  Iso.refl _

/-- Arbitrary open covers glue after direct image. -/
theorem isSheaf (F : TopologicalSheaf G X A) :
    sheafProperty G Y A ((presheaf f hf A).obj F.obj) :=
  TopCat.Sheaf.pushforward_sheaf_of_sheaf (TopCat.ofHom f) F.property

/-- Direct image of the entire ordinary-open equivariant sheaf. -/
def sheaf : TopologicalSheaf G X A ⥤ TopologicalSheaf G Y A :=
  (sheafProperty G Y A).lift
    (toTransportPresheaf G X A ⋙ presheaf f hf A) (isSheaf f hf A)

@[simp]
theorem sheaf_obj_obj (F : TopologicalSheaf G X A) (U : ActionOpens G Y) :
    ((sheaf f hf A).obj F).obj.obj (op U) = F.obj.obj (op ((preimage f hf).obj U)) := rfl

@[simp]
theorem sheaf_obj_map (F : TopologicalSheaf G X A) {U V : ActionOpens G Y} (k : U ⟶ V) :
    ((sheaf f hf A).obj F).obj.map k.op = F.obj.map ((preimage f hf).map k).op := rfl

@[simp]
theorem sheaf_map_app {F F' : TopologicalSheaf G X A} (k : F ⟶ F') (U : ActionOpens G Y) :
    ((sheaf f hf A).map k).hom.app (op U) = k.hom.app (op ((preimage f hf).obj U)) := rfl

/-- Direct image commutes with forgetting equivariance. -/
def toSheafIso :
    sheaf f hf A ⋙ toSheaf G Y A ≅
      toSheaf G X A ⋙ TopCat.Sheaf.pushforward A (TopCat.ofHom f) := Iso.refl _

/-- Direct image along the identity retains the original sheaf and maps. -/
def idIso :
    sheaf (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) A ≅
      𝟭 (TopologicalSheaf G X A) := Iso.refl _

/-- Direct image along a composite is the composite of direct images. -/
def compIso (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y) :
    sheaf (g.comp f) (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) A ≅
      sheaf f hf A ⋙ sheaf g hg A := Iso.refl _

section Coefficients

variable [ContinuousConstSMul G X] [ContinuousConstSMul G Y]
  {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- The original continuous map restricted to an inverse-image open. -/
def pointMap (U : ActionOpens G Y) :
    C(((preimage f hf).obj U).openSet, U.openSet) where
  toFun x := ⟨f x.val, x.property⟩
  continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk _

/-- Precomposition of every locally constant coefficient section. -/
def coefficientMap (ρ : Representation R G M) :
    LocallyConstantSheaf.sheaf (X := Y) ρ ⟶
      (sheaf f hf (ModuleCat.{max u w} R)).obj (LocallyConstantSheaf.sheaf (X := X) ρ) :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom (LocallyConstant.comapₗ R (pointMap f hf U.unop))
      naturality U V k := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        apply LocallyConstant.ext
        intro x
        change ρ k.unop.label⁻¹ (LocallyConstant.toFun s
            (LocallyConstantSheaf.pointMap k.unop (pointMap f hf V.unop x))) =
          ρ k.unop.label⁻¹ (LocallyConstant.toFun s (pointMap f hf U.unop
            (LocallyConstantSheaf.pointMap ((preimage f hf).map k.unop) x)))
        congr 2
        apply Subtype.ext
        exact (hf k.unop.label x.val).symm }

@[simp]
theorem coefficientMap_apply (ρ : Representation R G M) (U : ActionOpens G Y)
    (s : LocallyConstant U.openSet M) (x : ((preimage f hf).obj U).openSet) :
    LocallyConstant.toFun (((coefficientMap f hf ρ).hom.app (op U)).hom s) x = s (pointMap f hf U x) := rfl

/-- Section precomposition is natural in every original coefficient intertwiner. -/
def coefficientNatTrans :
    LocallyConstantSheaf.functor R G Y ⟶
      LocallyConstantSheaf.functor R G X ⋙ sheaf f hf (ModuleCat.{max u w} R) where
  app P := coefficientMap f hf P.ρ
  naturality P Q k := by
    apply ObjectProperty.hom_ext
    ext s x
    rfl

/-- Coefficient precomposition along the identity is the original identity map. -/
@[simp]
theorem coefficientMap_id (ρ : Representation R G M) :
    coefficientMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) ρ =
      𝟙 (LocallyConstantSheaf.sheaf (X := X) ρ) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply LocallyConstant.ext
  intro x
  rfl

/-- Coefficient precomposition retains the actual composite of continuous maps. -/
theorem coefficientMap_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (ρ : Representation R G M) :
    coefficientMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) ρ =
      coefficientMap g hg ρ ≫
        (sheaf g hg (ModuleCat.{max u w} R)).map (coefficientMap f hf ρ) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply LocallyConstant.ext
  intro x
  rfl

end Coefficients

end Langlands.Sheaf.Equivariant.DirectImage
