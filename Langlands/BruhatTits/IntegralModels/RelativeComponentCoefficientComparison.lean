import Langlands.BruhatTits.IntegralModels.RelativeComponentFunctoriality

/-! # Actual coefficient comparisons for supplied neutral models -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelData

open Langlands.GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  (D : RelativeComponentModelData R K G) (E : RelativeComponentModelData R K H)

/-- Restrict an actual full-model map with arbitrary specified generic map
through the actual relative identity components. -/
def mapNeutral {f : G ⟶ H} (φ : D.full.Hom E.full f) :
    D.neutral.Hom E.neutral f := by
  let : GeometricallyConnected D.neutral.group.X.hom := D.neutral_geometricallyConnected
  let ψ : D.neutral.Hom E.full f := by
    simpa only [Category.id_comp] using D.inclusion.comp φ
  exact E.toNeutral ψ

@[reassoc]
theorem mapNeutral_comp {f : G ⟶ H} (φ : D.full.Hom E.full f) :
    (D.mapNeutral E φ).hom ≫ E.inclusion.hom = D.inclusion.hom ≫ φ.hom := by
  let : GeometricallyConnected D.neutral.group.X.hom := D.neutral_geometricallyConnected
  exact E.toNeutral_comp _

/-- A full-model isomorphism restricts to a compatible neutral-model
isomorphism over the same original generic isomorphism. -/
def neutralIsoOver (f : G ≅ H) (e : D.full.Iso E.full f) :
    D.neutral.Iso E.neutral f :=
  IntegralModel.Iso.ofHoms (D.mapNeutral E e.toHom) (E.mapNeutral D e.symm.toHom)

@[reassoc]
theorem neutralIsoOver_hom_comp (f : G ≅ H) (e : D.full.Iso E.full f) :
    (D.neutralIsoOver E f e).iso.hom ≫ E.inclusion.hom =
      D.inclusion.hom ≫ e.iso.hom :=
  D.mapNeutral_comp E e.toHom

variable
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (v : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
  (hvc : v ≫ Spec.algebraMap R K = Spec.algebraMap R K ≫ a)

/-- Twist both actual models and their relative-component inclusion along
the coefficient square. -/
def twist : RelativeComponentModelData R K ((GroupScheme.baseChange v).obj G) where
  full := D.full.twist a v hvc
  neutral := D.neutral.twist a v hvc
  full_smooth := D.full.isSmooth_twist a v hvc D.full_smooth
  neutral_smooth := D.neutral.isSmooth_twist a v hvc D.neutral_smooth
  neutral_connectedFibres := by
    let : GeometricallyConnected D.neutral.group.X.hom := D.neutral_geometricallyConnected
    apply IntegralModel.hasConnectedFibres_of_geometricallyConnected
    change GeometricallyConnected (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom a)
    infer_instance
  inclusion :=
    { hom := (GroupScheme.baseChange a).map D.inclusion.hom
      generic_comm := by
        simpa only [IntegralModel.Hom.twist, CategoryTheory.Functor.map_id] using
          (D.inclusion.twist a v hvc).generic_comm }
  isRelativeComponent := by
    let : GeometricallyConnected D.neutral.group.X.hom := D.neutral_geometricallyConnected
    exact D.isRelativeComponent.baseChange a

/-- Construct the neutral coefficient isomorphism from an actual full one. -/
def neutralTwistIso (f : (GroupScheme.baseChange v).obj G ≅ H)
    (e : (D.full.twist a v hvc).Iso E.full f) :
    (D.neutral.twist a v hvc).Iso E.neutral f :=
  (D.twist a v hvc).neutralIsoOver E f e

@[reassoc]
theorem neutralTwistIso_hom_comp (f : (GroupScheme.baseChange v).obj G ≅ H)
    (e : (D.full.twist a v hvc).Iso E.full f) :
    (D.neutralTwistIso E a v hvc f e).iso.hom ≫ E.inclusion.hom =
      (GroupScheme.baseChange a).map D.inclusion.hom ≫ e.iso.hom :=
  (D.twist a v hvc).neutralIsoOver_hom_comp E f e

/-- Every actual full coefficient comparison supplies an actual neutral
comparison with the original generic map and inclusion square. -/
def CoefficientComparisonStatement : Prop :=
  ∀ (f : (GroupScheme.baseChange v).obj G ≅ H)
    (e : (D.full.twist a v hvc).Iso E.full f),
    ∃ e₀ : (D.neutral.twist a v hvc).Iso E.neutral f,
      e₀.iso.hom ≫ E.inclusion.hom =
        (GroupScheme.baseChange a).map D.inclusion.hom ≫ e.iso.hom

theorem coefficientComparison : D.CoefficientComparisonStatement E a v hvc := by
  intro f e
  exact ⟨D.neutralTwistIso E a v hvc f e, D.neutralTwistIso_hom_comp E a v hvc f e⟩

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelData

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  (M₀ M₁ : IntegralModel R K G) (N₀ N₁ : IntegralModel R K H)
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (v : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
  (hvc : v ≫ Spec.algebraMap R K = Spec.algebraMap R K ≫ a)
  (f : (GroupScheme.baseChange v).obj G ≅ H)
  (e₀ : (M₀.twist a v hvc).Iso N₀ f)
  (e₁ : (M₁.twist a v hvc).Iso N₁ f)
  (φ : M₀.Hom M₁ (𝟙 G)) (ψ : N₀.Hom N₁ (𝟙 H))

/-- Actual integral incidence maps commute with every coefficient
comparison extending the same generic isomorphism, by generic rigidity. -/
theorem twist_comparison_naturality :
    e₀.iso.hom ≫ ψ.hom = (GroupScheme.baseChange a).map φ.hom ≫ e₁.iso.hom := by
  let p : (M₀.twist a v hvc).Hom N₁ f.hom :=
    { hom := (GroupScheme.baseChange a).map φ.hom ≫ e₁.iso.hom
      generic_comm := by
        simpa only [Hom.comp, Hom.twist, Iso.toHom,
          CategoryTheory.Functor.map_id, Category.id_comp] using
          ((φ.twist a v hvc).comp e₁.toHom).generic_comm }
  let q : (M₀.twist a v hvc).Hom N₁ f.hom :=
    { hom := e₀.iso.hom ≫ ψ.hom
      generic_comm := by
        simpa only [Hom.comp, Iso.toHom, Category.comp_id] using
          (e₀.toHom.comp ψ).generic_comm }
  exact (p.hom_eq q).symm

variable [IsLocalRing R]
  (r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
    Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
  (hra : r ≫ residueBaseMap R = residueBaseMap R ≫ a)

/-- An actual integral coefficient comparison induces the actual residue
coefficient isomorphism by the canonical commuting-square comparison. -/
def Iso.residueTwistIso :
    (GroupScheme.baseChange r).obj M₀.specialFibre ≅ N₀.specialFibre :=
  Descent.squareComparison (residueBaseMap R) r a (residueBaseMap R) hra M₀.group ≪≫
    (GroupScheme.baseChange (residueBaseMap R)).mapIso e₀.iso

/-- The residue coefficient isomorphisms satisfy the original incidence
map square automatically. -/
theorem residue_twist_comparison_naturality :
    (Iso.residueTwistIso M₀ N₀ a v hvc f e₀ r hra).hom ≫ ψ.specialFibreMap =
      (GroupScheme.baseChange r).map φ.specialFibreMap ≫
        (Iso.residueTwistIso M₁ N₁ a v hvc f e₁ r hra).hom := by
  simp only [Iso.residueTwistIso, CategoryTheory.Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Hom.specialFibreMap, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp,
    twist_comparison_naturality M₀ M₁ N₀ N₁ a v hvc f e₀ e₁ φ ψ,
    CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, ← Descent.squareComparison_naturality]
  simp only [Category.assoc]

end Langlands.GroupScheme.IntegralModel
