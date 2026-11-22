import Langlands.Geometry.FormalGroup.PDivisibleGroupTatePresheaf

/-! # Compatible sections of the schematic Tate point presheaf -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]

/-- Evaluate the additive inverse diagram of the finite schematic levels on `T`. -/
def schematicTateTestDiagram (G : PDivisibleGroup R p) (T : Over (Spec R)) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (schematicTatePointSystem R p).obj G ⋙ (evaluation _ _).obj (op T)

/-- The usual compatible families in the additive groups of actual points of the finite levels. -/
def schematicTateSections (G : PDivisibleGroup R p) (T : Over (Spec R)) :
    AddSubgroup (∀ n : ℕᵒᵖ, (G.schematicTateTestDiagram T).obj n) :=
  AddGrpCat.sectionsAddSubgroup (G.schematicTateTestDiagram T ⋙ forget₂ _ AddGrpCat)

/-- Compatibility in the inverse diagram is postcomposition with the actual transfer. -/
theorem schematicTateSection_transfer {G : PDivisibleGroup R p} {T : Over (Spec R)}
    (x : G.schematicTateSections T) {m n : ℕ} (i : m ⟶ n) :
    (x.val (op n)).toMul ≫ (CommGroupScheme.groupHom (G.transfer i)).hom.hom =
      (x.val (op m)).toMul :=
  congrArg Additive.toMul (x.property i.op)

/-- Evaluation of the presheaf gives the compatible families of actual schematic points. -/
def schematicTatePointEquivSections (G : PDivisibleGroup R p) (T : Over (Spec R)) :
    ((schematicTatePointFunctor R p).obj G).obj (op T) ≃+ G.schematicTateSections T := by
  let E := (evaluation ((Over (Spec R))ᵒᵖ) AddCommGrpCat.{u}).obj (op T) ⋙ forget _
  let h := isLimitOfPreserves E (limit.isLimit ((schematicTatePointSystem R p).obj G))
  refine { Types.isLimitEquivSections h with map_add' := ?_ }
  intro x y
  apply Subtype.ext
  funext n
  exact map_add ((limit.π ((schematicTatePointSystem R p).obj G) n).app (op T)).hom x y

@[simp] theorem schematicTatePointEquivSections_apply (G : PDivisibleGroup R p)
    (T : Over (Spec R)) (x : ((schematicTatePointFunctor R p).obj G).obj (op T)) (n : ℕ) :
    (G.schematicTatePointEquivSections T x).val (op n) =
      (G.schematicTatePointProjection n).app (op T) x := rfl

@[simp] theorem schematicTatePointEquivSections_symm_apply (G : PDivisibleGroup R p)
    (T : Over (Spec R)) (x : G.schematicTateSections T) (n : ℕ) :
    (G.schematicTatePointProjection n).app (op T)
        ((G.schematicTatePointEquivSections T).symm x) = x.val (op n) := by
  rw [← schematicTatePointEquivSections_apply, AddEquiv.apply_symm_apply]

/-- Restrict a Tate point to a new test by precomposing its actual point at each level. -/
theorem schematicTatePointProjection_restrict (G : PDivisibleGroup R p)
    {T U : Over (Spec R)} (b : U ⟶ T)
    (x : ((schematicTatePointFunctor R p).obj G).obj (op T)) (n : ℕ) :
    (G.schematicTatePointProjection n).app (op U)
        (((schematicTatePointFunctor R p).obj G).map b.op x) =
      Additive.ofMul (b ≫ ((G.schematicTatePointProjection n).app (op T) x).toMul) :=
  ConcreteCategory.congr_hom ((G.schematicTatePointProjection n).naturality b.op) x

/-- A tower morphism acts on Tate points by its actual morphism at each finite level. -/
theorem schematicTatePointProjection_map {G H : PDivisibleGroup R p} (f : G ⟶ H)
    (T : Over (Spec R)) (x : ((schematicTatePointFunctor R p).obj G).obj (op T)) (n : ℕ) :
    (H.schematicTatePointProjection n).app (op T)
        (((schematicTatePointFunctor R p).map f).app (op T) x) =
      Additive.ofMul (((G.schematicTatePointProjection n).app (op T) x).toMul ≫
        (CommGroupScheme.groupHom (f.app n)).hom.hom) := by
  have h := NatTrans.congr_app (schematicTatePointProjection_naturality f n) (op T)
  exact ConcreteCategory.congr_hom h x

/-- Two Tate points agree if their projections to all actual levels agree. -/
theorem schematicTatePoint_ext {G : PDivisibleGroup R p} {T : Over (Spec R)}
    {x y : ((schematicTatePointFunctor R p).obj G).obj (op T)}
    (h : ∀ n : ℕ, (G.schematicTatePointProjection n).app (op T) x =
      (G.schematicTatePointProjection n).app (op T) y) : x = y := by
  apply (G.schematicTatePointEquivSections T).injective
  apply Subtype.ext
  funext n
  induction n using Opposite.rec with | op n => exact h n

end Langlands.PDivisibleGroup
