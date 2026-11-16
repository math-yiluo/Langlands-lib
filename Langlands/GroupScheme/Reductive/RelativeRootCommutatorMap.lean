import Langlands.GroupScheme.Reductive.LocalRootGroupTorusCoordinate
import Langlands.GroupScheme.AutomorphicAction.BaseChange
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationField

/-! # Commutator maps on actual relative root groups -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Langlands.GroupScheme.AutomorphicAction

variable {S S' : Scheme.{u}} {H V G : GroupScheme S}
  (a : AutomorphicAction H V) (t : Over.mk (𝟙 S) ⟶ H.X)

/-- The scheme map sending `v` to the commutator of a fixed acting section
with `v`. -/
def commutatorMap : V.X ⟶ V.X :=
  a.act (H.constantPoint t V.X) (𝟙 V.X) * (𝟙 V.X)⁻¹

theorem commutatorMap_apply {T : Over S} (x : T ⟶ V.X) :
    x ≫ a.commutatorMap t = a.act (H.constantPoint t T) x * x⁻¹ := by
  simp only [commutatorMap, MonObj.comp_mul, GrpObj.comp_inv, a.naturality,
    constantPoint_naturality, Category.comp_id]

theorem baseChangePointsEquiv_comp_map (b : S' ⟶ S) (f : V.X ⟶ V.X)
    (T : Over S') (x : T ⟶ ((GroupScheme.baseChange b).obj V).X) :
    baseChangePointsEquiv b V T (x ≫ (Over.pullback b).map f) =
      baseChangePointsEquiv b V T x ≫ f :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

/-- Pullback preserves the actual commutator map and its fixed section. -/
theorem commutatorMap_baseChange (b : S' ⟶ S) :
    (Over.pullback b).map (a.commutatorMap t) =
      (a.baseChange b).commutatorMap (baseChangeBasePoint b H t) := by
  apply (baseChangePointsEquiv b V ((GroupScheme.baseChange b).obj V).X).injective
  change baseChangePointsEquiv b V _
      ((𝟙 _) ≫ (Over.pullback b).map (a.commutatorMap t)) =
    baseChangePointsEquiv b V _
      ((𝟙 _) ≫ (a.baseChange b).commutatorMap (baseChangeBasePoint b H t))
  rw [baseChangePointsEquiv_comp_map, commutatorMap_apply, commutatorMap_apply,
    map_mul, map_inv, baseChangePointsEquiv_act, baseChangePointsEquiv_constantPoint]
  rfl

variable (k : H ⟶ G) (j : V ⟶ G)
  (hact : ∀ (T : Over S) (h : T ⟶ H.X) (v : T ⟶ V.X),
    a.act h v ≫ j.hom.hom =
      (h ≫ k.hom.hom) * (v ≫ j.hom.hom) * (h ≫ k.hom.hom)⁻¹)

include hact in
theorem commutatorMap_comp {T : Over S} (x : T ⟶ V.X) :
    (x ≫ a.commutatorMap t) ≫ j.hom.hom =
      (H.constantPoint t T ≫ k.hom.hom) * (x ≫ j.hom.hom) *
        (H.constantPoint t T ≫ k.hom.hom)⁻¹ * (x ≫ j.hom.hom)⁻¹ := by
  rw [commutatorMap_apply, MonObj.mul_comp, GrpObj.inv_comp, hact]

include hact in
theorem commutatorMap_baseChange_comp (b : S' ⟶ S)
    {T : Over S'} (x : T ⟶ ((GroupScheme.baseChange b).obj V).X) :
    (x ≫ (Over.pullback b).map (a.commutatorMap t)) ≫
        ((GroupScheme.baseChange b).map j).hom.hom =
      (((GroupScheme.baseChange b).obj H).constantPoint (baseChangeBasePoint b H t) T ≫
          ((GroupScheme.baseChange b).map k).hom.hom) *
        (x ≫ ((GroupScheme.baseChange b).map j).hom.hom) *
        (((GroupScheme.baseChange b).obj H).constantPoint (baseChangeBasePoint b H t) T ≫
          ((GroupScheme.baseChange b).map k).hom.hom)⁻¹ *
        (x ≫ ((GroupScheme.baseChange b).map j).hom.hom)⁻¹ := by
  apply (baseChangePointsEquiv b G T).injective
  simp only [baseChangePointsEquiv_comp, baseChangePointsEquiv_comp_map,
    map_mul, map_inv, baseChangePointsEquiv_constantPoint]
  exact commutatorMap_comp a t k j hact _

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme.LocalRootGroup

open LocalSplitCell Corepresented

/-- A scheme map is an isomorphism if additive coordinates on every test
identify it with multiplication by a unit. -/
theorem isIso_of_scalar_points {R : Type u} [CommRing R]
    {V : GroupScheme (Spec (CommRingCat.of R))} (f : V.X ⟶ V.X)
    (Φ : Ga R ≅ V)
    (c : ∀ T : Over (Spec (CommRingCat.of R)), Γ(T.left, ⊤))
    (hc : ∀ T, IsUnit (c T))
    (hf : ∀ (T : Over (Spec (CommRingCat.of R))) (x : Γ(T.left, ⊤)),
      (VectorGroup.scalarPoint _ T x ≫ Φ.hom.hom.hom) ≫ f =
        VectorGroup.scalarPoint _ T (c T * x) ≫ Φ.hom.hom.hom) :
    IsIso f := by
  apply CategoryTheory.isIso_of_yoneda_map_bijective
  intro T
  let e : Γ(T.left, ⊤) ≃ (T ⟶ V.X) :=
    (Equiv.ofBijective (VectorGroup.scalarPoint _ T) (scalarPoint_bijective _ T)).trans
      (CategoryTheory.Iso.homCongr (Iso.refl T)
        ((Grp.forget _).mapIso Φ))
  have he (x : Γ(T.left, ⊤)) : e x =
      VectorGroup.scalarPoint _ T x ≫ Φ.hom.hom.hom := by
    simp [e]
  have hbij : Function.Bijective (fun x : Γ(T.left, ⊤) => c T * x) :=
    (IsUnit.isUnit_iff_mulLeft_bijective).mp (hc T)
  constructor
  · intro x y h
    obtain ⟨x', rfl⟩ := e.surjective x
    obtain ⟨y', rfl⟩ := e.surjective y
    dsimp only at h
    rw [he, he, hf, hf] at h
    exact congrArg e (hbij.1 (e.injective (by simpa only [he] using h)))
  · intro x
    obtain ⟨x', rfl⟩ := e.surjective x
    obtain ⟨y, hy⟩ := hbij.2 x'
    exact ⟨e y, by simp only [he, hf, hy]⟩

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu : I → ℤ)

/-- The root commutator map on the actual dynamic group over the ring. -/
def rootCommutatorMap
    (t : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      (splitTorus (Spec (CommRingCat.of R)) I).X) :
    (Uc i mu nu).X ⟶ (Uc i mu nu).X :=
  (UnipotentTorus.action (torusZ i mu) nu).commutatorMap t

theorem rootCommutatorMap_apply
    (t : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      (splitTorus (Spec (CommRingCat.of R)) I).X)
    {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ (Uc i mu nu).X) :
    (x ≫ rootCommutatorMap i mu nu t) ≫ (incl i mu nu).hom.hom =
      ((splitTorus _ I).constantPoint t T ≫ i.hom.hom) *
        (x ≫ (incl i mu nu).hom.hom) *
        ((splitTorus _ I).constantPoint t T ≫ i.hom.hom)⁻¹ *
        (x ≫ (incl i mu nu).hom.hom)⁻¹ :=
  AutomorphicAction.commutatorMap_comp _ t i (incl i mu nu)
    (fun _ => action_act_comp_incl i mu nu) x

end Langlands.GroupScheme.LocalRootGroup
