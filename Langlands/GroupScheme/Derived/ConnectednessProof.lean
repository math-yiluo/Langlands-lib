import Langlands.GroupScheme.Derived.StructureStatement
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.IdentityComponent

/-! # Connectedness of the scheme-theoretic derived subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_connected_clopen_subgroup
    {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom] :
    ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ H),
      IsOpenImmersion j.hom.hom.left ∧ IsClosedSubgroup j ∧
      ConnectedSpace P.X.left ∧
      Set.range j.hom.hom.left = IdentityComponent.identitySet H := by
  let : GrpObj (Over.mk H.X.hom) := H.grp
  obtain ⟨P₀, i, L₀, hi, hc, hirr, -, -, hr, -, hmul, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
      k (GoodReductionJacobian.relativeGroupLawOfGrpObj k H.X.hom)
  let P := Over.mk (i ≫ H.X.hom)
  let : GrpObj P := L₀.grpObjOverMk
  let j : P ⟶ H.X := Over.homMk i
  have hmul' (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ P) :
      (x * y) ≫ j = (x ≫ j) * (y ≫ j) := by
    have h := hmul T.hom
      (GoodReductionJacobian.overHomEquivSchemeHomOver T _ x)
      (GoodReductionJacobian.overHomEquivSchemeHomOver T _ y)
    rw [← L₀.overHomEquivSchemeHomOver_mul T x y] at h
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val h
  let : IsMonHom j := {
    one_hom := by
      rw [MonObj.one_eq_one, MonObj.one_eq_one]
      apply mul_left_cancel (a := (1 : 𝟙_ _ ⟶ P) ≫ j)
      rw [← hmul', one_mul, mul_one]
    mul_hom := by
      rw [MonObj.mul_eq_mul, hmul']
      simp only [Hom.mul_def, lift_fst_comp_snd_comp] }
  refine ⟨{ X := P }, Grp.homMk j, hi, hc, ?_, ?_⟩
  · let : IrreducibleSpace P₀ := hirr
    exact inferInstanceAs (ConnectedSpace P₀)
  · rw [GoodReductionJacobian.relativeGroupLawOfGrpObj_one] at hr
    change Set.range i = _
    convert hr using 1
    change connectedComponent
        ((toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ η[H.X]).left
          (IdentityComponent.basePoint k)) =
      connectedComponent (IdentityComponent.identityPoint H)
    rw [Over.comp_left, Scheme.Hom.comp_apply, IdentityComponent.unit_left_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- An actual scheme-theoretic derived subgroup of a connected affine finite-type
field group is connected, without a smoothness hypothesis. -/
theorem derivedSubgroupConnectedness : DerivedSubgroupConnectednessStatement.{u} := by
  intro k _ G _ _ D d hd hG
  let : ConnectedSpace G.X.left := hG
  let : IsClosedImmersion d.hom.hom.left := hd.1
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  let : LocallyOfFiniteType D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  obtain ⟨P, j, hjopen, hjclosed, hP, hjrange⟩ := exists_connected_clopen_subgroup D
  let : IsOpenImmersion j.hom.hom.left := hjopen
  let : IsClosedImmersion j.hom.hom.left := hjclosed
  let : ConnectedSpace P.X.left := hP
  let : GeometricallyConnected G.X.hom := G.geometricallyConnected_of_connected
  let : UniversallyOpen G.X.hom := UniversallyOpen.of_flat _
  let : ConnectedSpace (G.X ⊗ G.X).left :=
    inferInstanceAs (ConnectedSpace ↥(pullback G.X.hom G.X.hom : Scheme.{u}))
  let c : G.X ⊗ G.X ⟶ G.X :=
    fst G.X G.X * snd G.X G.X * (fst G.X G.X)⁻¹ * (snd G.X G.X)⁻¹
  obtain ⟨f, hf⟩ := SubgroupFunctor.mem_range.mp
    (hd.containsCommutators (G.X ⊗ G.X) (fst G.X G.X) (snd G.X G.X))
  change f ≫ d.hom.hom = c at hf
  let a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X ⊗ G.X := lift 1 1
  have ha : a ≫ f = η[D.X] := by
    rw [MonObj.one_eq_one]
    apply (cancel_mono d.hom.hom).mp
    rw [Category.assoc, hf, MonObj.one_comp]
    dsimp only [a, c]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd,
      inv_one, mul_one]
  have hfrange : Set.range f.left ⊆ Set.range j.hom.hom.left := by
    rw [hjrange]
    exact IdentityComponent.range_subset_identitySet D f a ha
  let f₀ : G.X ⊗ G.X ⟶ P.X :=
    FiniteEtaleImage.liftOver j.hom.hom f hfrange
  have hf₀ : f₀ ≫ j.hom.hom = f := FiniteEtaleImage.liftOver_fac _ _ _
  have hclosed : IsClosedSubgroup (j ≫ d) := by
    change IsClosedImmersion (j.hom.hom.left ≫ d.hom.hom.left)
    infer_instance
  have hcomm : (SubgroupFunctor.range (j ≫ d)).ContainsCommutators := by
    intro T x y
    refine SubgroupFunctor.mem_range.mpr ⟨lift x y ≫ f₀, ?_⟩
    change (lift x y ≫ f₀) ≫ (j.hom.hom ≫ d.hom.hom) = _
    calc
      _ = lift x y ≫ ((f₀ ≫ j.hom.hom) ≫ d.hom.hom) := by
        simp only [Category.assoc]
      _ = lift x y ≫ c := by rw [hf₀, hf]
      _ = x * y * x⁻¹ * y⁻¹ := by
        dsimp only [c]
        simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]
  have hle := hd.range_le (j ≫ d) hclosed hcomm
  have hmem : d.hom.hom ∈ (SubgroupFunctor.range d).carrier D.X :=
    SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨r, hr⟩ := SubgroupFunctor.mem_range.mp (hle D.X hmem)
  have hri : r ≫ j.hom.hom = 𝟙 D.X := by
    apply (cancel_mono d.hom.hom).mp
    change r ≫ (j.hom.hom ≫ d.hom.hom) = d.hom.hom at hr
    simpa only [Category.assoc, Category.id_comp] using hr
  have hsurj : Function.Surjective j.hom.hom.left := by
    intro z
    refine ⟨r.left z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hri]
    rfl
  exact hsurj.connectedSpace j.hom.hom.left.continuous

end Langlands.GroupScheme
