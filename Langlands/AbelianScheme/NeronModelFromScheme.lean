import Langlands.AbelianScheme.NeronModel
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Mathlib.CategoryTheory.Monoidal.Subcategory

/-! # The commutative group law on a scheme with the Néron mapping property -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Langlands.AbelianScheme

open NeronModelInfra

variable {V K : Type u} [CommRing V] [Field K] [Algebra V K]

private abbrev genericFibre (V K : Type u) [CommRing V] [Field K] [Algebra V K] :=
  Over.pullback (specGenericFibreInclusion V K)

private theorem restriction_bijective_iff (T X : Over (Spec (CommRingCat.of V))) :
    Function.Bijective ((genericFibre V K).map : (T ⟶ X) → _) ↔
      Function.Bijective (genericFibreRestrict V K X.hom T.hom) := by
  let source := GoodReductionJacobian.overHomEquivSchemeHomOver T X.hom
  let target := GoodReductionJacobian.overHomEquivSchemeHomOver
    ((genericFibre V K).obj T) ((genericFibre V K).obj X).hom
  have hcomp : genericFibreRestrict V K X.hom T.hom ∘ source =
      target ∘ (genericFibre V K).map := rfl
  constructor
  · intro h
    exact (Function.Bijective.of_comp_iff _ source.bijective).mp
      (hcomp.symm ▸ target.bijective.comp h)
  · intro h
    exact (Function.Bijective.of_comp_iff' target.bijective _).mp
      (hcomp ▸ h.comp source.bijective)

variable [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K]

/-- The Néron mapping property as a bijection of morphisms in the over categories. -/
theorem neron_genericFibreMap_bijective (T X : Over (Spec (CommRingCat.of V)))
    (hT : Smooth T.hom) (hX : NeronModelPropertyBundle V K X.hom) :
    Function.Bijective ((Over.pullback (specGenericFibreInclusion V K)).map : (T ⟶ X) → _) :=
  (restriction_bijective_iff T X).mpr (hX.neronMapping _ _ hT)

private def neronSchemes (V K : Type u) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] :
    ObjectProperty (Over (Spec (CommRingCat.of V))) :=
  fun X => NeronModelPropertyBundle V K X.hom

private instance : (neronSchemes V K).IsMonoidal where
  prop_unit := neronModelPropertyBundle_id V K
  prop_tensor X Y hX hY := by
    let hX : NeronModelPropertyBundle V K X.hom := hX
    let hY : NeronModelPropertyBundle V K Y.hom := hY
    let : Smooth X.hom := hX.smooth
    let : Smooth Y.hom := hY.smooth
    let : IsSeparated X.hom := hX.separated
    let : IsSeparated Y.hom := hY.separated
    let : QuasiCompact X.hom := hX.quasiCompact
    let : QuasiCompact Y.hom := hY.quasiCompact
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Over.tensorObj_hom]; infer_instance
    · rw [Over.tensorObj_hom]; infer_instance
    · rw [Over.tensorObj_hom]; infer_instance
    · rw [Over.tensorObj_hom]; infer_instance
    intro T t ht
    let Z := Over.mk t
    let F := genericFibre V K
    apply (restriction_bijective_iff Z (X ⊗ Y)).mp
    have h1 := neron_genericFibreMap_bijective Z X ht hX
    have h2 := neron_genericFibreMap_bijective Z Y ht hY
    constructor
    · intro f g h
      apply CartesianMonoidalCategory.hom_ext
      · apply h1.1
        rw [F.map_comp, F.map_comp, h]
      · apply h2.1
        rw [F.map_comp, F.map_comp, h]
    · intro a
      obtain ⟨a₁, ha₁⟩ := h1.2 (a ≫ F.map (fst X Y))
      obtain ⟨a₂, ha₂⟩ := h2.2 (a ≫ F.map (snd X Y))
      refine ⟨lift a₁ a₂, (cancel_mono (OplaxMonoidal.δ F X Y)).mp ?_⟩
      rw [OplaxMonoidal.lift_δ, ha₁, ha₂]
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, Category.assoc, OplaxMonoidal.δ_fst F X Y]
      · rw [lift_snd, Category.assoc, OplaxMonoidal.δ_snd F X Y]

private abbrev NeronSchemes (V K : Type u) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] :=
  (neronSchemes V K).FullSubcategory

private instance : CartesianMonoidalCategory (NeronSchemes V K) where
  __ := ObjectProperty.fullMonoidalSubcategory (neronSchemes V K)
  isTerminalTensorUnit := .ofUniqueHom (fun X => ObjectProperty.homMk (toUnit X.1))
    fun _ _ => ObjectProperty.hom_ext _ (toUnit_unique _ _)
  fst X Y := ObjectProperty.homMk (fst X.1 Y.1)
  snd X Y := ObjectProperty.homMk (snd X.1 Y.1)
  tensorProductIsBinaryProduct X Y :=
    BinaryFan.IsLimit.mk _ (fun f g => ObjectProperty.homMk (lift f.hom g.hom))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def X Y := ObjectProperty.hom_ext _ (fst_def X.1 Y.1)
  snd_def X Y := ObjectProperty.hom_ext _ (snd_def X.1 Y.1)

private abbrev modelGenericFibre (V K : Type u) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] :=
  (neronSchemes V K).ι ⋙ genericFibre V K

private def modelGenericFibreFullyFaithful : (modelGenericFibre V K).FullyFaithful := by
  let e : ∀ M N : NeronSchemes V K, (M ⟶ N) ≃ _ := fun M N =>
    ((neronSchemes V K).fullyFaithfulι.homEquiv (X := M) (Y := N)).trans
      (Equiv.ofBijective _ (neron_genericFibreMap_bijective M.1 N.1 M.2.smooth N.2))
  exact ⟨fun {M N} f => (e M N).symm f, fun {M N} f => (e M N).apply_symm_apply f,
    fun {M N} f => (e M N).symm_apply_apply f⟩

set_option maxHeartbeats 800000 in
/-- A supplied smooth separated scheme with the Néron mapping property and
an identified abelian generic fibre carries the extending commutative group law. -/
def NeronModel.ofScheme {B : AbelianScheme (Spec (CommRingCat.of K))}
    (X : Over (Spec (CommRingCat.of V))) (hX : NeronModelPropertyBundle V K X.hom)
    (e : B.X ≅ (Over.pullback (specGenericFibreInclusion V K)).obj X) : NeronModel V K B := by
  let I := (neronSchemes V K).ι
  let F := modelGenericFibre V K
  let hF : F.FullyFaithful := modelGenericFibreFullyFaithful
  let M : NeronSchemes V K := ⟨X, hX⟩
  let e' : B.X ≅ F.obj M := e
  let : GrpObj (F.obj M) := GrpObj.ofIso e'
  let : IsMonHom e'.hom := isMonHom_ofIso e'
  let : IsCommMonObj (F.obj M) := Langlands.GroupScheme.isCommMonObj_of_iso e'
  let : GrpObj M := hF.grpObj M
  let : IsCommMonObj M := ⟨by
    apply hF.map_injective
    change F.map ((β_ M M).hom ≫ hF.preimage (OplaxMonoidal.δ F M M ≫ μ[F.obj M])) =
      F.map (hF.preimage (OplaxMonoidal.δ F M M ≫ μ[F.obj M]))
    simp [IsCommMonObj.mul_comm]⟩
  let H : Grp (NeronSchemes V K) := Grp.mk M
  let G : CommGroupScheme (Spec (CommRingCat.of V)) :=
    { toGrp := I.mapGrp.obj H
      comm := Functor.isCommMonObj_obj (F := I) (M := M) }
  let g : B.toCommGroupScheme.toGrp ≅ F.mapGrp.obj H := Grp.mkIso e'
    (by
      change η[B.X] ≫ e'.hom = LaxMonoidal.ε F ≫
        F.map (hF.preimage (OplaxMonoidal.η F ≫ η[F.obj M]))
      rw [hF.map_preimage, Monoidal.ε_η_assoc]
      exact IsMonHom.one_hom e'.hom)
    (by
      change μ[B.X] ≫ e'.hom = (e'.hom ⊗ₘ e'.hom) ≫ LaxMonoidal.μ F M M ≫
        F.map (hF.preimage (OplaxMonoidal.δ F M M ≫ μ[F.obj M]))
      rw [hF.map_preimage, Monoidal.μ_δ_assoc]
      exact IsMonHom.mul_hom e'.hom)
  let c := (Functor.mapGrpCompIso (F := I) (G := genericFibre V K)).app H
  exact ⟨G, hX, Langlands.GroupScheme.CommGroupScheme.isoOfGroupIso (g ≪≫ c)⟩

@[simp]
theorem NeronModel.ofScheme_group_X {B : AbelianScheme (Spec (CommRingCat.of K))}
    (X : Over (Spec (CommRingCat.of V))) (hX : NeronModelPropertyBundle V K X.hom)
    (e : B.X ≅ (Over.pullback (specGenericFibreInclusion V K)).obj X) :
    (ofScheme X hX e).group.X = X :=
  rfl

@[simp]
theorem NeronModel.ofScheme_genericIso_hom {B : AbelianScheme (Spec (CommRingCat.of K))}
    (X : Over (Spec (CommRingCat.of V))) (hX : NeronModelPropertyBundle V K X.hom)
    (e : B.X ≅ (Over.pullback (specGenericFibreInclusion V K)).obj X) :
    (CommGroupScheme.groupHom (ofScheme X hX e).genericIso.hom).hom.hom = e.hom := by
  change e.hom ≫ 𝟙 _ = e.hom
  exact Category.comp_id _

end Langlands.AbelianScheme
