import Langlands.Cohomology.EquivariantComposite.Statement
import Langlands.Cohomology.DerivedComparison
import Langlands.Representation.Category.SmoothPartAdjunction
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Smooth cofree representations and their higher invariants -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.EquivariantComposite

universe u

variable (R G : Type u) [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Forget the action on a smooth representation. -/
abbrev underlying : SmoothRep.{u,u,u} R G ⥤ ModuleCat.{u} R :=
  SmoothRep.toRep ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R)

/-- Left translation on all functions, before taking the smooth part. -/
def functionRepresentation (M : ModuleCat.{u} R) : Representation R G (G → M) where
  toFun g :=
    { toFun f h := f (g⁻¹ * h)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by ext f h; simp
  map_mul' g h := by ext f k; simp [mul_assoc]

/-- Uniformly smooth functions on the group with arbitrary module values. -/
def cofreeObj (M : ModuleCat.{u} R) : SmoothRep.{u,u,u} R G :=
  SmoothRep.smoothPartObj R G (Rep.of (functionRepresentation R G M))

/-- Postcompose a smooth function by a module homomorphism. -/
def cofreeMap {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    cofreeObj R G M ⟶ cofreeObj R G N :=
  SmoothRep.ofHom (smoothMap
    { toLinearMap :=
        { toFun s g := f (s g)
          map_add' _ _ := by ext g; exact map_add f.hom _ _
          map_smul' _ _ := by ext g; exact map_smul f.hom _ _ }
      isIntertwining' _ := rfl })

/-- The smooth cofree representation functor. -/
def cofree : ModuleCat.{u} R ⥤ SmoothRep.{u,u,u} R G where
  obj := cofreeObj R G
  map := cofreeMap R G
  map_id _ := rfl
  map_comp _ _ := rfl

instance cofree_additive : (cofree R G).Additive where
  map_add := rfl

/-- The adjoint of a linear map is its orbit function. -/
def corec (V : SmoothRep.{u,u,u} R G) (M : ModuleCat.{u} R)
    (f : (underlying R G).obj V ⟶ M) : V ⟶ cofreeObj R G M :=
  SmoothRep.ofHom (Langlands.smoothLift V.isSmooth
    { toLinearMap :=
        { toFun v g := f (V.representation g⁻¹ v)
          map_add' v w := by ext g; simp
          map_smul' r v := by ext g; simp }
      isIntertwining' g := by
        ext v h
        change f (V.representation h⁻¹ (V.representation g v)) =
          f (V.representation (g⁻¹ * h)⁻¹ v)
        simp [map_mul, Module.End.mul_apply] })

/-- Evaluation at the identity recovers the original linear map. -/
def evaluate (V : SmoothRep.{u,u,u} R G) (M : ModuleCat.{u} R)
    (f : V ⟶ cofreeObj R G M) : (underlying R G).obj V ⟶ M :=
  ModuleCat.ofHom
    { toFun v := (SmoothRep.hom f v).val 1
      map_add' v w := congrFun (congrArg Subtype.val (map_add (SmoothRep.hom f) v w)) 1
      map_smul' r v := congrFun (congrArg Subtype.val (map_smul (SmoothRep.hom f) r v)) 1 }

/-- Forgetting the action is left adjoint to smooth coinduction. -/
def cofreeAdjunction : underlying R G ⊣ cofree R G :=
  Adjunction.mkOfHomEquiv
    { homEquiv V M :=
        { toFun := corec R G V M
          invFun := evaluate R G V M
          left_inv f := by ext v; change f (V.representation (1 : G)⁻¹ v) = f v; simp
          right_inv f := by
            apply ObjectProperty.hom_ext
            apply Rep.hom_ext
            apply Representation.IntertwiningMap.ext
            ext v
            apply Subtype.ext
            funext g
            change (SmoothRep.hom f (V.representation g⁻¹ v)).val 1 =
              (SmoothRep.hom f v).val g
            rw [Representation.IntertwiningMap.isIntertwining]
            change (SmoothRep.hom f v).val ((g⁻¹)⁻¹ * 1) = _
            simp }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

instance cofree_isRightAdjoint : (cofree R G).IsRightAdjoint :=
  (cofreeAdjunction R G).isRightAdjoint

/-- A set theoretic section of a surjection lifts a uniformly smooth function
without changing its open stabilizer. -/
instance cofree_preservesEpimorphisms : (cofree R G).PreservesEpimorphisms where
  preserves {M N} f _ := by
    have hf := (ModuleCat.epi_iff_surjective f).1 inferInstance
    choose lift hlift using hf
    apply (SmoothRep.epi_iff_surjective _).2
    intro s
    refine ⟨⟨fun g => lift (s.val g), ?_⟩, ?_⟩
    · obtain ⟨H, hH⟩ := s.property
      refine ⟨H, fun h => ?_⟩
      funext g
      exact congrArg lift (congrFun (hH h) g)
    · apply Subtype.ext
      funext g
      exact hlift _

instance cofree_preservesHomology : (cofree R G).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (cofree R G)

instance cofree_preservesInjectiveObjects : (cofree R G).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (cofreeAdjunction R G)

end Langlands.Cohomology.EquivariantComposite
