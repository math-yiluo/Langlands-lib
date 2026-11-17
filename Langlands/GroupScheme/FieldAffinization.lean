import Langlands.GroupScheme.FieldAffinizationProducts
import Langlands.GroupScheme.AntiAffine
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.GroupScheme.SmoothFieldComponent

/-! # The actual affine group and canonical homomorphism of a field group -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FieldAffinization

variable {k : Type u} [Field k]

instance inclusionPreservesFiniteProducts : PreservesFiniteProducts (inclusion k) :=
  .of_preserves_binary_and_terminal _

instance inclusionMonoidal : (inclusion k).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

variable (G : GroupScheme (Spec (CommRingCat.of k))) [QuasiCompact G.X.hom]

/-- A quasi-compact field group is an object of the category used for affinization. -/
def object : SchemeCategory k := ⟨G.X, ⟨inferInstance, fieldSeparated k G⟩⟩

/-- The original group object, regarded inside the full category of
quasi-compact separated field schemes. -/
def liftedGroup : Grp (SchemeCategory k) := by
  letI : GrpObj ((inclusion k).obj (object G)) := by
    change GrpObj G.X
    infer_instance
  let : GrpObj (object G) :=
    (ObjectProperty.fullyFaithfulι _).grpObj (object G)
  exact .mk (object G)

/-- Forgetting the full-category lift recovers the original actual group. -/
def inclusionIso : (inclusion k).mapGrp.obj (liftedGroup G) ≅ G := by
  refine Grp.mkIso (G := (inclusion k).mapGrp.obj (liftedGroup G))
    (H := G) (Iso.refl G.X) ?_ ?_
  · change (𝟙 _ ≫ (𝟙 _ ≫ η[G.X])) ≫ 𝟙 _ = η[G.X]
    simp only [Category.id_comp, Category.comp_id]
  · change (𝟙 _ ≫ (𝟙 _ ≫ μ[G.X])) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ[G.X]
    simp only [Category.id_comp, Category.comp_id, id_tensorHom_id]

/-- The actual affine group with underlying scheme `Spec Γ(G,O)`. -/
def group : GroupScheme (Spec (CommRingCat.of k)) :=
  (functor k).mapGrp.obj (liftedGroup G)

/-- The canonical actual homomorphism from the field group to its affinization. -/
def projection : G ⟶ group G :=
  (inclusionIso G).inv ≫ (CategoryTheory.Functor.mapGrpNatTrans (unit k)).app (liftedGroup G)

@[simp]
lemma group_left : (group G).X.left = Spec Γ(G.X.left, ⊤) := rfl

@[simp]
lemma group_hom : (group G).X.hom =
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ G.X.hom.appTop) := rfl

@[simp]
lemma projection_left : (projection G).hom.hom.left = G.X.left.toSpecΓ := by
  simp [projection, inclusionIso, liftedGroup, object]

instance isAffine_group : IsAffine (group G).X.left :=
  inferInstanceAs (IsAffine (Spec Γ(G.X.left, ⊤)))

instance isAffineHom_group : IsAffineHom (group G).X.hom :=
  inferInstanceAs (IsAffineHom (Spec.map _))

/-- The specified canonical homomorphism induces the actual isomorphism
on global functions. -/
theorem isAffinization : IsAffinization (projection G) where
  isAffine := inferInstance
  isIso_appTop := by
    rw [projection_left, Scheme.toSpecΓ_appTop]
    infer_instance

/-- Every smooth connected field group has an actual affine group affinization.
This conclusion records the canonical group and map, without quotient geometry. -/
theorem exists_of_smooth_connected (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [ConnectedSpace H.X.left] :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : H ⟶ Q), IsAffinization q := by
  have : QuasiCompact H.X.hom := quasiCompact_of_smooth_connected H
  exact ⟨group H, projection H, isAffinization H⟩

end Langlands.GroupScheme.FieldAffinization
