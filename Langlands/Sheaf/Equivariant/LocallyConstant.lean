import Langlands.Sheaf.Equivariant.Topological
import Langlands.Representation.LocallyConstant.CompactAction
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Sites.Preserves

/-! # Full locally constant module sheaves for moving-space actions -/

noncomputable section

universe u v r w

namespace Langlands.Sheaf.Equivariant.LocallyConstantSheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {R : Type r} [CommRing R] {G : Type v} [Group G]
  {X : Type u} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  {M : Type w} [AddCommGroup M] [Module R M]

/-- The actual point map of a labelled open-set arrow. -/
def pointMap {U V : ActionOpens G X} (f : U ⟶ V) :
    C(U.openSet, V.openSet) where
  toFun x := ⟨f.label • x.val, f.mapsTo x.val x.property⟩
  continuous_toFun :=
    ((continuous_const_smul f.label).comp continuous_subtype_val).subtype_mk _

/-- Pullback combines the labelled point map with the inverse coefficient operator. -/
def pullback (ρ : Representation R G M) {U V : ActionOpens G X} (f : U ⟶ V) :
    LocallyConstant V.openSet M →ₗ[R] LocallyConstant U.openSet M :=
  (LocallyConstant.mapₗ R (ρ f.label⁻¹)).comp (LocallyConstant.comapₗ R (pointMap f))

@[simp]
theorem pullback_apply (ρ : Representation R G M) {U V : ActionOpens G X}
    (f : U ⟶ V) (s : LocallyConstant V.openSet M) (x : U.openSet) :
    pullback ρ f s x = ρ f.label⁻¹ (s (pointMap f x)) := rfl

/-- Every locally constant function on every open, with all labelled restrictions. -/
def presheaf (ρ : Representation R G M) :
    (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{max u w} R where
  obj U := ModuleCat.of R (LocallyConstant U.unop.openSet M)
  map f := ModuleCat.ofHom (pullback ρ f.unop)
  map_id U := by
    ext s x
    change ρ (1 : G)⁻¹ (s ⟨(1 : G) • x.val, _⟩) = s x
    simp
  map_comp f g := by
    ext s x
    change ρ (f.unop.label * g.unop.label)⁻¹
        (s ⟨(f.unop.label * g.unop.label) • x.val, _⟩) =
      ρ g.unop.label⁻¹
        (ρ f.unop.label⁻¹ (s ⟨f.unop.label • (g.unop.label • x.val), _⟩))
    simp [mul_inv_rev, mul_smul, map_mul, Module.End.mul_apply]

/-- Local constancy is a local predicate without a topology on the coefficients. -/
def localPredicate (X : Type u) [TopologicalSpace X] (M : Type w) :
    TopCat.LocalPredicate (fun _ : TopCat.of X => M) where
  pred f := IsLocallyConstant f
  res i f hf := hf.comp_continuous (Opens.isOpenEmbedding_of_le i.le).continuous
  locality f hf := by
    let : TopologicalSpace M := ⊥
    let : DiscreteTopology M := discreteTopology_bot M
    apply (IsLocallyConstant.iff_continuous f).mpr
    apply (TopCat.continuousLocal (TopCat.of X) M).locality f
    intro x
    obtain ⟨V, hxV, i, hi⟩ := hf x
    exact ⟨V, hxV, i, hi.continuous⟩

/-- Forgetting modules and labels gives the full local-predicate function presheaf. -/
def underlyingIso (ρ : Representation R G M) :
    (underlyingPresheaf G X (ModuleCat.{max u w} R)).obj (presheaf (X := X) ρ) ⋙
        forget (ModuleCat.{max u w} R) ≅
      TopCat.subpresheafToTypes (localPredicate X M).toPrelocalPredicate :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom (fun s => ⟨s.toFun, s.isLocallyConstant⟩)
      inv := TypeCat.ofHom (fun s => ⟨s.val, s.property⟩) }) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    funext x
    change ρ (1 : G)⁻¹ (LocallyConstant.toFun s ⟨(1 : G) • x.val, _⟩) =
      LocallyConstant.toFun s ⟨x.val, _⟩
    simp)

/-- Arbitrary open covers glue in the entire locally constant function set. -/
theorem forget_isSheaf (ρ : Representation R G M) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      ((underlyingPresheaf G X (ModuleCat.{max u w} R)).obj
        (presheaf (X := X) ρ) ⋙ forget (ModuleCat.{max u w} R)) :=
  (Presheaf.isSheaf_of_iso_iff (underlyingIso ρ)).mpr
    (TopCat.subpresheafToTypes.isSheaf (localPredicate X M))

/-- The actual matching limits are reflected to modules with independent ring size. -/
theorem isSheaf (ρ : Representation R G M) :
    ((underlyingPresheaf G X (ModuleCat.{max u w} R)).obj
      (presheaf (X := X) ρ)).IsSheaf := by
  let : ReflectsLimitsOfSize.{0, u} (forget (ModuleCat.{max u w} R)) := by
    refine { reflectsLimitsOfShape := ?_ }
    intro J _
    refine { reflectsLimit := ?_ }
    intro F
    refine { reflects := ?_ }
    intro c hc
    let : HasLimit (F ⋙ forget (ModuleCat.{max u w} R)) := ⟨_, hc⟩
    let : Small.{max u w} (F ⋙ forget (ModuleCat.{max u w} R)).sections :=
      (Types.hasLimit_iff_small_sections _).mp inferInstance
    let : HasLimit F := ModuleCat.hasLimit F
    let : PreservesLimit F (forget (ModuleCat.{max u w} R)) :=
      preservesLimit_of_preserves_limit_cone (ModuleCat.HasLimits.limitConeIsLimit F)
        (Types.Small.limitConeIsLimit _)
    let : ReflectsLimit F (forget (ModuleCat.{max u w} R)) :=
      reflectsLimit_of_reflectsIsomorphisms F _
    exact ⟨isLimitOfReflects _ hc⟩
  exact Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{max u w} R))
    (forget_isSheaf ρ)

/-- The constructed full locally constant module sheaf on a moving space. -/
def sheaf (ρ : Representation R G M) :
    TopologicalSheaf G X (ModuleCat.{max u w} R) :=
  ⟨presheaf ρ, isSheaf ρ⟩

/-- A coefficient intertwiner acts pointwise on every open section. -/
def map {P Q : Rep.{w} R G} (a : P ⟶ Q) :
    sheaf (X := X) P.ρ ⟶ sheaf (X := X) Q.ρ :=
  ObjectProperty.homMk
    { app _ := ModuleCat.ofHom (LocallyConstant.mapₗ R a.hom.toLinearMap)
      naturality U V f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        apply LocallyConstant.ext
        intro x
        exact Rep.hom_comm_apply a f.unop.label⁻¹
          (LocallyConstant.toFun s (pointMap f.unop x)) }

/-- Full moving-space locally constant sheaves are functorial in coefficients. -/
def functor (R : Type r) [CommRing R] (G : Type v) [Group G]
    (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] :
    Rep.{w} R G ⥤ TopologicalSheaf G X (ModuleCat.{max u w} R) where
  obj P := sheaf P.ρ
  map := map
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply LocallyConstant.ext
    intro x
    rfl

/-- Restriction along the whole-space homeomorphism identifies actual global sections. -/
def globalSectionsLinearEquiv (ρ : Representation R G M) :
    LocallyConstant X M ≃ₗ[R] (presheaf (X := X) ρ).obj (op ActionOpens.top) where
  toFun := LocallyConstant.comapₗ R
    ⟨fun x : (ActionOpens.top (G := G) (X := X)).openSet => x.val,
      continuous_subtype_val⟩
  invFun := LocallyConstant.comapₗ R
    ⟨fun x : X => (⟨x, by trivial⟩ :
      (ActionOpens.top (G := G) (X := X)).openSet), continuous_id.subtype_mk (fun _ => by trivial)⟩
  left_inv s := by ext x; rfl
  right_inv s := by apply LocallyConstant.ext; intro x; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem globalSectionsLinearEquiv_apply (ρ : Representation R G M)
    (s : LocallyConstant X M) (x : X) :
    LocallyConstant.toFun (globalSectionsLinearEquiv (X := X) ρ s) ⟨x, by trivial⟩ =
      s x := rfl

/-- The actual action on whole-space sections, converted to a representation. -/
def globalRepresentation (ρ : Representation R G M) :
    Representation R G ((presheaf (X := X) ρ).obj (op ActionOpens.top)) :=
  ((Rep.ActionToRep R G).obj (sectionAction (presheaf (X := X) ρ))).ρ

@[simp]
theorem globalRepresentation_apply (ρ : Representation R G M) (g : G)
    (s : LocallyConstant (ActionOpens.top (G := G) (X := X)).openSet M)
    (x : (ActionOpens.top (G := G) (X := X)).openSet) :
    LocallyConstant.toFun (globalRepresentation (X := X) ρ g s) x =
      ρ g (s ⟨g⁻¹ • x.val, by trivial⟩) := by
  change ρ (g⁻¹)⁻¹ (s ⟨g⁻¹ • x.val, _⟩) = _
  rw [inv_inv]

/-- The section identification respects the original diagonal group action. -/
theorem globalSectionsLinearEquiv_equivariant (ρ : Representation R G M)
    (g : G) (s : LocallyConstant X M) :
    globalSectionsLinearEquiv ρ
        (Langlands.CompactAction.LocallyConstantModule.diagonalRepresentation ρ g s) =
      globalRepresentation ρ g (globalSectionsLinearEquiv ρ s) := by
  apply LocallyConstant.ext
  intro x
  change ρ g (s (g⁻¹ • x.val)) = ρ (g⁻¹)⁻¹ (s (g⁻¹ • x.val))
  rw [inv_inv]

/-- Actual global sheaf sections have exactly the diagonal function representation. -/
def globalSectionsRepIso (ρ : Representation R G M) :
    Rep.of (Langlands.CompactAction.LocallyConstantModule.diagonalRepresentation
      (X := X) ρ) ≅ Rep.of (globalRepresentation (X := X) ρ) where
  hom := Rep.ofHom
    { toLinearMap := (globalSectionsLinearEquiv ρ).toLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro s
        exact globalSectionsLinearEquiv_equivariant ρ g s }
  inv := Rep.ofHom
    { toLinearMap := (globalSectionsLinearEquiv ρ).symm.toLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro s
        change (globalSectionsLinearEquiv ρ).symm (globalRepresentation ρ g s) =
          Langlands.CompactAction.LocallyConstantModule.diagonalRepresentation ρ g
            ((globalSectionsLinearEquiv ρ).symm s)
        apply (globalSectionsLinearEquiv ρ).injective
        simp only [LinearEquiv.apply_symm_apply]
        rw [globalSectionsLinearEquiv_equivariant, LinearEquiv.apply_symm_apply] }
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro s
    exact (globalSectionsLinearEquiv ρ).symm_apply_apply s
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro s
    exact (globalSectionsLinearEquiv ρ).apply_symm_apply s

end Langlands.Sheaf.Equivariant.LocallyConstantSheaf
