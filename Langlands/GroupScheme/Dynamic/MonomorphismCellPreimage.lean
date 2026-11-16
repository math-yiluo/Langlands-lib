import Langlands.GroupScheme.Dynamic.OppositeCellPreimage
import Langlands.GroupScheme.Dynamic.BaseTripleCell
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Absolute.TripleCellIsomorphism
import Langlands.GroupScheme.Absolute.SplitTorusDynamicDescent
import Langlands.GroupScheme.HomImageEmbedding
import Langlands.GroupScheme.SubgroupFunctor.FppfImagePullback

/-! # Inverse images of dynamic triple cells under monomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Dynamic

section FieldTests

variable {S : Scheme.{u}} {H G : GroupScheme S}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm S).toGrp ⟶ H) (f : H ⟶ G) [Mono f.hom.hom]

/-- Triple-cell factors lift on every test scheme whose structure map
factors through a field-valued point of the base. -/
theorem exists_triple_factors_over_fieldPoint
    (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S)
    {T : Over (Spec (CommRingCat.of K))}
    (g : (Over.map b).obj T ⟶ H.X) (m z v : (Over.map b).obj T ⟶ G.X)
    (hm : m ∈ (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom S (-1)) ≫ (χ ≫ f))).carrier _)
    (hz : z ∈ (centralizer (χ ≫ f)).carrier _)
    (hv : v ∈ (unipotent (χ ≫ f)).carrier _)
    (hmzv : m * (z * v) = g ≫ f.hom.hom) :
    ∃ (m₀ z₀ v₀ : (Over.map b).obj T ⟶ H.X),
      m₀ ∈ (unipotent (CommGroupScheme.groupHom
        (Gm.powerHom S (-1)) ≫ χ)).carrier _ ∧
      z₀ ∈ (centralizer χ).carrier _ ∧ v₀ ∈ (unipotent χ).carrier _ ∧
      m₀ ≫ f.hom.hom = m ∧ z₀ ≫ f.hom.hom = z ∧
      v₀ ≫ f.hom.hom = v ∧ m₀ * (z₀ * v₀) = g := by
  let Hb := (GroupScheme.baseChange b).obj H
  let Gb := (GroupScheme.baseChange b).obj G
  let fb := (GroupScheme.baseChange b).map f
  let χb := baseChangeCocharacter b χ
  have : Smooth Hb.X.hom := DynamicBaseSmoothConnected.smooth_baseChange b
  have : IsAffineHom Hb.X.hom := DynamicBaseSmoothConnected.isAffineHom_baseChange b
  have : ConnectedSpace Hb.X.left := DynamicBaseSmoothConnected.connectedSpace_baseChange b
  have : IsAffineHom Gb.X.hom := DynamicBaseSmoothConnected.isAffineHom_baseChange b
  have : LocallyOfFiniteType Gb.X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) G.X.hom b inferInstance
  have : Mono fb.hom.hom :=
    (inferInstance : Mono ((Over.pullback b).map f.hom.hom))
  have hfb : IsClosedSubgroup fb := HomImage.isClosedSubgroup_of_mono fb
  let eg := baseChangePointsEquiv b H T
  let ef := baseChangePointsEquiv b G T
  have hm' : ef.symm m ∈ (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom _ (-1)) ≫ (χb ≫ fb))).carrier T := by
    change ef.symm m ∈ (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom _ (-1)) ≫ (baseChangeCocharacter b χ ≫
        (GroupScheme.baseChange b).map f))).carrier T
    rw [← baseChangeCocharacter_comp, ← baseChangeCocharacter_powerHom,
      unipotent_baseChange, SubgroupFunctor.mem_baseChange]
    simpa only [ef, MulEquiv.apply_symm_apply] using hm
  have hz' : ef.symm z ∈ (centralizer (χb ≫ fb)).carrier T := by
    change ef.symm z ∈ (centralizer (baseChangeCocharacter b χ ≫
      (GroupScheme.baseChange b).map f)).carrier T
    rw [← baseChangeCocharacter_comp, centralizer_baseChange,
      SubgroupFunctor.mem_baseChange]
    simpa only [ef, MulEquiv.apply_symm_apply] using hz
  have hv' : ef.symm v ∈ (unipotent (χb ≫ fb)).carrier T := by
    change ef.symm v ∈ (unipotent (baseChangeCocharacter b χ ≫
      (GroupScheme.baseChange b).map f)).carrier T
    rw [← baseChangeCocharacter_comp, unipotent_baseChange,
      SubgroupFunctor.mem_baseChange]
    simpa only [ef, MulEquiv.apply_symm_apply] using hv
  have hprod : ef.symm m * (ef.symm z * ef.symm v) = eg.symm g ≫ fb.hom.hom := by
    apply ef.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply]
    exact hmzv
  obtain ⟨m₁, z₁, v₁, hm₁, hz₁, hv₁, hmf, hzf, hvf, hprod₁⟩ :=
    exists_triple_factors_of_isClosedSubgroup χb fb hfb
      (eg.symm g) (ef.symm m) (ef.symm z) (ef.symm v) hm' hz' hv' hprod
  rw [← baseChangeCocharacter_powerHom, unipotent_baseChange,
    SubgroupFunctor.mem_baseChange] at hm₁
  rw [centralizer_baseChange, SubgroupFunctor.mem_baseChange] at hz₁
  rw [unipotent_baseChange, SubgroupFunctor.mem_baseChange] at hv₁
  refine ⟨eg m₁, eg z₁, eg v₁, hm₁, hz₁, hv₁, ?_, ?_, ?_, ?_⟩
  · rw [← baseChangePointsEquiv_comp, hmf, MulEquiv.apply_symm_apply]
  · rw [← baseChangePointsEquiv_comp, hzf, MulEquiv.apply_symm_apply]
  · rw [← baseChangePointsEquiv_comp, hvf, MulEquiv.apply_symm_apply]
  · rw [← map_mul, ← map_mul, hprod₁, MulEquiv.apply_symm_apply]

end FieldTests

section Cells

variable {S : Scheme.{u}} {H G MH ZH UH MG ZG UG : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ H) (f : H ⟶ G)
    {iM : MH ⟶ H} {iZ : ZH ⟶ H} {iU : UH ⟶ H}
    {jM : MG ⟶ G} {jZ : ZG ⟶ G} {jU : UG ⟶ G}
    (hM : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom S (-1)) ≫ χ)).IsRepresentedBy iM)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (hMG : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom S (-1)) ≫ (χ ≫ f))).IsRepresentedBy jM)
    (hZG : (centralizer (χ ≫ f)).IsRepresentedBy jZ)
    (hUG : (unipotent (χ ≫ f)).IsRepresentedBy jU)

/-- The map between the represented triple cells induced by an ambient
homomorphism, on the actual three dynamic factors. -/
def tripleCellFactor : MH.X ⊗ (ZH.X ⊗ UH.X) ⟶ MG.X ⊗ (ZG.X ⊗ UG.X) :=
  (hM.restrictionHom hMG f (by
      simpa only [Category.assoc] using
        unipotent_le_comap (CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ) f)).hom.hom ⊗ₘ
    ((hZ.restrictionHom hZG f (centralizer_le_comap χ f)).hom.hom ⊗ₘ
      (hU.restrictionHom hUG f (unipotent_le_comap χ f)).hom.hom)

/-- The induced map on triple cells commutes with their multiplication maps. -/
theorem tripleCellFactor_comp :
    tripleCellFactor χ f hM hZ hU hMG hZG hUG ≫ tripleCellMultiplication jM jZ jU =
      tripleCellMultiplication iM iZ iU ≫ f.hom.hom := by
  rw [tripleCellFactor, tensorHom_comp_tripleCellMultiplication,
    SubgroupFunctor.IsRepresentedBy.restrictionHom_comp,
    SubgroupFunctor.IsRepresentedBy.restrictionHom_comp,
    SubgroupFunctor.IsRepresentedBy.restrictionHom_comp,
    tripleCellMultiplication_comp_hom]

include χ hM hZ hU hMG hZG hUG in
/-- A field-point test of the source lifts to its triple cell whenever its
image lifts to the target triple cell. -/
theorem exists_tripleCell_lift_over_fieldPoint
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Mono f.hom.hom]
    (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S)
    {T : Over (Spec (CommRingCat.of K))}
    (g : (Over.map b).obj T ⟶ H.X)
    (t : (Over.map b).obj T ⟶ MG.X ⊗ (ZG.X ⊗ UG.X))
    (ht : t ≫ tripleCellMultiplication jM jZ jU = g ≫ f.hom.hom) :
    ∃ s : (Over.map b).obj T ⟶ MH.X ⊗ (ZH.X ⊗ UH.X),
      s ≫ tripleCellMultiplication iM iZ iU = g := by
  let m := t ≫ fst MG.X (ZG.X ⊗ UG.X)
  let z := t ≫ snd MG.X (ZG.X ⊗ UG.X) ≫ fst ZG.X UG.X
  let v := t ≫ snd MG.X (ZG.X ⊗ UG.X) ≫ snd ZG.X UG.X
  have hm := (hMG.pointsEquiv _ m).property
  have hz := (hZG.pointsEquiv _ z).property
  have hv := (hUG.pointsEquiv _ v).property
  have hprod : (m ≫ jM.hom.hom) *
      ((z ≫ jZ.hom.hom) * (v ≫ jU.hom.hom)) = g ≫ f.hom.hom := by
    simpa only [tripleCellMultiplication, SubgroupFunctor.cellMultiplication,
      MonObj.comp_mul, Category.assoc, m, z, v] using ht
  obtain ⟨m₀, z₀, v₀, hm₀, hz₀, hv₀, -, -, -, hprod₀⟩ :=
    exists_triple_factors_over_fieldPoint χ f K b g
      (m ≫ jM.hom.hom) (z ≫ jZ.hom.hom) (v ≫ jU.hom.hom) hm hz hv hprod
  refine ⟨lift ((hM.pointsEquiv _).symm ⟨m₀, hm₀⟩)
    (lift ((hZ.pointsEquiv _).symm ⟨z₀, hz₀⟩)
      ((hU.pointsEquiv _).symm ⟨v₀, hv₀⟩)), ?_⟩
  simpa only [lift_tripleCellMultiplication,
    SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp] using hprod₀

include χ hM hZ hU hMG hZG hUG in
/-- The inverse image of the target triple cell is exactly the source
triple cell, over an arbitrary base scheme. -/
theorem preimage_range_tripleCellMultiplication
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Mono f.hom.hom] :
    f.hom.hom.left ⁻¹' Set.range (tripleCellMultiplication jM jZ jU).left =
      Set.range (tripleCellMultiplication iM iZ iU).left := by
  have : IsOpenImmersion (tripleCellMultiplication jM jZ jU).left :=
    isOpenImmersion_tripleCellMultiplication_overBase (χ ≫ f) hMG hZG hUG
  ext x
  constructor
  · intro hx
    let b := H.X.left.fromSpecResidueField x ≫ H.X.hom
    let T : Over (Spec (H.X.left.residueField x)) := Over.mk (𝟙 _)
    let g : (Over.map b).obj T ⟶ H.X :=
      Over.homMk (H.X.left.fromSpecResidueField x) (by simp [T, b])
    have hrange : Set.range (g.left ≫ f.hom.hom.left) ⊆
        Set.range (tripleCellMultiplication jM jZ jU).left := by
      rintro _ ⟨y, rfl⟩
      change f.hom.hom.left (H.X.left.fromSpecResidueField x y) ∈ _
      rw [Scheme.fromSpecResidueField_apply]
      exact hx
    let l := IsOpenImmersion.lift (tripleCellMultiplication jM jZ jU).left
      (g.left ≫ f.hom.hom.left) hrange
    let t : (Over.map b).obj T ⟶ MG.X ⊗ (ZG.X ⊗ UG.X) :=
      Over.homMk l (by
        rw [← Over.w (tripleCellMultiplication jM jZ jU), ← Category.assoc,
          IsOpenImmersion.lift_fac]
        exact Over.w (g ≫ f.hom.hom))
    have ht : t ≫ tripleCellMultiplication jM jZ jU = g ≫ f.hom.hom :=
      Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ hrange)
    obtain ⟨s, hs⟩ := exists_tripleCell_lift_over_fieldPoint χ f
      hM hZ hU hMG hZG hUG (H.X.left.residueField x) b g t ht
    refine ⟨s.left (IsLocalRing.closedPoint (H.X.left.residueField x)), ?_⟩
    have hs' := congrArg
      (fun q : (Over.map b).obj T ⟶ H.X =>
        q.left (IsLocalRing.closedPoint (H.X.left.residueField x))) hs
    change (tripleCellMultiplication iM iZ iU).left
      (s.left (IsLocalRing.closedPoint (H.X.left.residueField x))) =
        H.X.left.fromSpecResidueField x
          (IsLocalRing.closedPoint (H.X.left.residueField x)) at hs'
    simpa only [Scheme.fromSpecResidueField_apply] using hs'
  · rintro ⟨y, rfl⟩
    refine ⟨(tripleCellFactor χ f hM hZ hU hMG hZG hUG).left y, ?_⟩
    exact congrArg
      (fun q : MH.X ⊗ (ZH.X ⊗ UH.X) ⟶ G.X => q.left y)
      (tripleCellFactor_comp χ f hM hZ hU hMG hZG hUG)

/-- The actual triple-cell square of a monomorphism is cartesian. -/
theorem isPullback_tripleCellFactor
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Mono f.hom.hom] :
    IsPullback (tripleCellFactor χ f hM hZ hU hMG hZG hUG).left
      (tripleCellMultiplication iM iZ iU).left
      (tripleCellMultiplication jM jZ jU).left f.hom.hom.left := by
  have : IsOpenImmersion (tripleCellMultiplication iM iZ iU).left :=
    isOpenImmersion_tripleCellMultiplication_overBase χ hM hZ hU
  have : IsOpenImmersion (tripleCellMultiplication jM jZ jU).left :=
    isOpenImmersion_tripleCellMultiplication_overBase (χ ≫ f) hMG hZG hUG
  apply IsOpenImmersion.isPullback
  · exact congrArg Over.Hom.left
      (tripleCellFactor_comp χ f hM hZ hU hMG hZG hUG).symm
  · apply TopologicalSpace.Opens.ext
    exact preimage_range_tripleCellMultiplication χ f hM hZ hU hMG hZG hUG

end Cells

end Langlands.GroupScheme.Dynamic
