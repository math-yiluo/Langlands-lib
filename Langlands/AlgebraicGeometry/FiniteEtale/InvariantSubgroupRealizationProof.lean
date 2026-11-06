import Langlands.AlgebraicGeometry.FiniteEtale.InvariantSubgroupRealizationStatement
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricContinuousActionEquivalenceProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberConservativeProof
import Mathlib.CategoryTheory.Action.Concrete

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj FintypeCatDiscrete
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hs : ∀ Y : Cover S, Finite (Fiber s Y))

/-- Fullness lifts an equivariant map of the actual point sets. -/
private def liftPointMap
    [(continuousActionFunctor s hs).Full] {Y Z : Cover S}
    (f : Fiber s Y → Fiber s Z)
    (hf : ∀ (g : FundamentalGroup s hs) x, f (g • x) = g • f x) : Y ⟶ Z :=
  (continuousActionFunctor s hs).preimage (ObjectProperty.homMk
    { hom := FintypeCat.homMk f
      comm := fun g => ConcreteCategory.hom_ext _ _ (hf g) })

private theorem liftPointMap_apply
    [(continuousActionFunctor s hs).Full] {Y Z : Cover S}
    (f : Fiber s Y → Fiber s Z)
    (hf : ∀ (g : FundamentalGroup s hs) x, f (g • x) = g • f x)
    (x : Fiber s Y) :
    x ≫ (liftPointMap s hs f hf).hom = f x := by
  exact ConcreteCategory.congr_hom
    ((continuousActionFunctor s hs).map_preimage
      (ObjectProperty.homMk
        { hom := FintypeCat.homMk f
          comm := fun g => ConcreteCategory.hom_ext _ _ (hf g) })) x

/-- The invariant subgroup first gives an actual cover with the exact point image. -/
private theorem realizePointSubset [ConnectedSpace S] [IsLocallyNoetherian S]
    [IsAlgClosed Ω] (G : Langlands.CommGroupScheme S)
    [IsFinite G.X.hom] [Etale G.X.hom]
    (M : AddSubgroup (Additive (Over.mk s ⟶ G.X)))
    (hM : ∀ (g : FundamentalGroup s hs) x,
      groupMonodromy s hs G.toGrp g x ∈ M ↔ x ∈ M) :
    ∃ (Y : Cover S) (i : Y.obj ⟶ G.X),
      Function.Injective (fun x : Fiber s Y => x ≫ i) ∧
      ∀ x : Over.mk s ⟶ G.X,
        Additive.ofMul x ∈ M ↔ ∃ y : Fiber s Y, y ≫ i = x := by
  let F := continuousActionFunctor s hs
  let : F.IsEquivalence := geometricContinuousActionEquivalence s hs
  let A : SubMulAction (FundamentalGroup s hs) (Fiber s (ofOver G.X)) :=
    { carrier := {x | Additive.ofMul x ∈ M}
      smul_mem' := fun g x hx => (hM g (Additive.ofMul x)).mpr hx }
  let : Finite (Fiber s (ofOver G.X)) := hs _
  let : Fintype A := Fintype.ofFinite A
  let a : ContAction FintypeCat.{u} (FundamentalGroup s hs) :=
    ⟨Action.FintypeCat.ofMulAction _ (FintypeCat.of A), by
      change @ContinuousSMul (FundamentalGroup s hs) A _ _ ⊥
      convert (inferInstance : ContinuousSMul (FundamentalGroup s hs) A) using 1
      exact DiscreteTopology.eq_bot.symm⟩
  let Y := F.objPreimage a
  let e := F.objObjPreimageIso a
  let e' : Fiber s Y ≃ A :=
    { toFun := fun x => e.hom x
      invFun := fun x => e.inv x
      left_inv := fun x => ConcreteCategory.congr_hom e.hom_inv_id x
      right_inv := fun x => ConcreteCategory.congr_hom e.inv_hom_id x }
  have he (g : FundamentalGroup s hs) (x : Fiber s Y) :
      e' (g • x) = g • e' x := by
    exact ConcreteCategory.congr_hom (e.hom.hom.comm g) x
  let i : Y ⟶ ofOver G.X := liftPointMap s hs (fun x => (e' x).val)
    (fun g x => congrArg Subtype.val (he g x))
  have hi (x : Fiber s Y) : x ≫ i.hom = (e' x).val :=
    liftPointMap_apply s hs _ _ x
  refine ⟨Y, i.hom, ?_, ?_⟩
  · intro x y h
    apply e'.injective
    apply Subtype.ext
    simpa only [hi] using h
  · intro x
    constructor
    · intro hx
      refine ⟨e'.symm ⟨x, hx⟩, ?_⟩
      rw [hi, e'.apply_symm_apply]
    · rintro ⟨y, rfl⟩
      rw [hi]
      exact (e' y).property

/-- Faithfulness detects equality of actual slice morphisms on this fibre. -/
private theorem pointMap_ext
    [(continuousActionFunctor s hs).Faithful] {Y Z : Cover S}
    {f g : Y.obj ⟶ Z.obj}
    (h : ∀ x : Fiber s Y, x ≫ f = x ≫ g) : f = g := by
  have he : (ObjectProperty.homMk f : Y ⟶ Z) = ObjectProperty.homMk g :=
    (continuousActionFunctor s hs).map_injective
      (ConcreteCategory.hom_ext _ _ h)
  exact congrArg (fun k : Y ⟶ Z => k.hom) he

/-- A map whose geometric-point image lies in the realized subset factors through it. -/
private theorem factorPointSubset
    [(continuousActionFunctor s hs).Full] [(continuousActionFunctor s hs).Faithful]
    {Y Z W : Cover S} (i : Y.obj ⟶ W.obj)
    (hi : Function.Injective (fun x : Fiber s Y => x ≫ i))
    (f : Z.obj ⟶ W.obj)
    (hf : ∀ x : Fiber s Z, ∃ y : Fiber s Y, y ≫ i = x ≫ f) :
    ∃ j : Z.obj ⟶ Y.obj, j ≫ i = f := by
  choose j hj using hf
  have he (g : FundamentalGroup s hs) (x : Fiber s Z) :
      j (g • x) = g • j x := by
    apply hi
    change j (g • x) ≫ i = (g • j x) ≫ i
    calc
      j (g • x) ≫ i = (g • x) ≫ f := hj _
      _ = g • (x ≫ f) := (smul_naturality s hs (ObjectProperty.homMk f) g x).symm
      _ = g • (j x ≫ i) := congrArg (g • ·) (hj x).symm
      _ = (g • j x) ≫ i := smul_naturality s hs (ObjectProperty.homMk i) g (j x)
  refine ⟨(liftPointMap s hs j he).hom, ?_⟩
  apply pointMap_ext s hs (Y := Z) (Z := W)
  intro x
  rw [← Category.assoc, liftPointMap_apply, hj]

section GroupTransfer

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]
  {X B : C} [GrpObj B]
  (i : X ⟶ B) [Mono i]
  (e : 𝟙_ C ⟶ X) (m : X ⊗ X ⟶ X) (v : X ⟶ X)
  (he : e ≫ i = η[B]) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[B])
  (hv : v ≫ i = i ≫ ι[B])

include hm in
omit [Mono i] in
private theorem transfer_mul {T : C} (f : T ⟶ X ⊗ X) :
    f ≫ m ≫ i = (f ≫ fst X X ≫ i) * (f ≫ snd X X ≫ i) := by
  rw [hm]
  rw [← Category.assoc]
  change (f ≫ (i ⊗ₘ i)) ≫ μ[B] = lift _ _ ≫ μ[B]
  congr 1
  apply hom_ext <;> simp

/-- Restrict the ambient group operations along a monomorphism. -/
@[instance_reducible] private def restrictedGroupObj : GrpObj X where
  one := e
  mul := m
  inv := v
  one_mul := by
    apply (cancel_mono i).1
    rw [Category.assoc, transfer_mul i m hm]
    simp only [whiskerRight_fst_assoc, whiskerRight_snd_assoc, he,
      leftUnitor_hom]
    rw [show fst (𝟙_ C) X = toUnit _ from toUnit_unique _ _]
    exact one_mul _
  mul_one := by
    apply (cancel_mono i).1
    rw [Category.assoc, transfer_mul i m hm]
    simp only [whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, he,
      rightUnitor_hom]
    rw [show snd X (𝟙_ C) = toUnit _ from toUnit_unique _ _]
    exact mul_one _
  mul_assoc := by
    apply (cancel_mono i).1
    simp only [Category.assoc]
    rw [transfer_mul i m hm, transfer_mul i m hm]
    simp only [whiskerRight_fst_assoc, whiskerRight_snd_assoc, whiskerLeft_snd_assoc]
    rw [transfer_mul i m hm, transfer_mul i m hm]
    simp only [MonObj.comp_mul, whiskerLeft_fst_assoc,
      associator_hom_fst_assoc, associator_hom_snd_fst_assoc,
      associator_hom_snd_snd_assoc]
    exact mul_assoc _ _ _
  left_inv := by
    apply (cancel_mono i).1
    rw [Category.assoc, transfer_mul i m hm]
    simp only [lift_fst_assoc, lift_snd_assoc, Category.id_comp, hv,
      Category.assoc, he]
    exact inv_mul_cancel _
  right_inv := by
    apply (cancel_mono i).1
    rw [Category.assoc, transfer_mul i m hm]
    simp only [lift_fst_assoc, lift_snd_assoc, Category.id_comp, hv,
      Category.assoc, he]
    exact mul_inv_cancel _

end GroupTransfer

/-- Every invariant subgroup of the actual geometric point group is realized. -/
theorem invariantSubgroupRealization : InvariantSubgroupRealizationStatement.{u} := by
  intro S _ _ Ω _ _ s hs G _ _ M hM
  let : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  obtain ⟨Y, i, hi, himage⟩ := realizePointSubset s hs G M hM
  have : Mono i.left :=
    cover_mono_of_fiber_injective s (Y := ofOver G.X) (ObjectProperty.homMk i) hi
  have : Mono i := Over.mono_of_mono_left i
  obtain ⟨e, he⟩ := factorPointSubset s hs (W := ofOver G.X)
    (Z := ofOver (𝟙_ (Over S))) i hi η[G.X] (by
      intro x
      apply (himage _).mp
      have hx : x = toUnit _ := toUnit_unique _ _
      rw [hx]
      exact M.zero_mem)
  obtain ⟨m, hm⟩ := factorPointSubset s hs (W := ofOver G.X)
    (Z := ofOver (Y.obj ⊗ Y.obj)) i hi ((i ⊗ₘ i) ≫ μ[G.X]) (by
      intro x
      apply (himage _).mp
      have hx : x ≫ ((i ⊗ₘ i) ≫ μ[G.X]) =
          (x ≫ fst _ _ ≫ i) * (x ≫ snd _ _ ≫ i) := by
        rw [← Category.assoc]
        change (x ≫ (i ⊗ₘ i)) ≫ μ[G.X] = lift _ _ ≫ μ[G.X]
        congr 1
        apply hom_ext <;> simp
      rw [hx]
      exact M.add_mem
        ((himage _).mpr ⟨x ≫ fst _ _, rfl⟩)
        ((himage _).mpr ⟨x ≫ snd _ _, rfl⟩))
  obtain ⟨v, hv⟩ := factorPointSubset s hs (W := ofOver G.X)
    (Z := Y) i hi (i ≫ ι[G.X]) (by
      intro x
      apply (himage _).mp
      rw [← Category.assoc]
      exact M.neg_mem ((himage _).mpr ⟨x, rfl⟩))
  let : GrpObj Y.obj := restrictedGroupObj i e m v he hm hv
  let : IsMonHom i := ⟨he, hm⟩
  let : IsCommMonObj Y.obj := ⟨by
    apply (cancel_mono i).1
    change ((β_ Y.obj Y.obj).hom ≫ m) ≫ i = m ≫ i
    rw [Category.assoc, transfer_mul i m hm, ← Category.id_comp m,
      Category.assoc, transfer_mul i m hm]
    simp only [braiding_hom_fst_assoc, braiding_hom_snd_assoc, Category.id_comp]
    exact mul_comm _ _⟩
  let K : Langlands.CommGroupScheme S := { X := Y.obj }
  let j : K ⟶ G := Additive.ofMul (Grp.homMk i)
  refine ⟨K, j, inferInstance, inferInstance, ?_, ?_⟩
  · change IsClosedImmersion i.left
    apply (IsClosedImmersion.iff_isFinite_and_mono _).mpr
    refine ⟨?_, inferInstance⟩
    have : IsFinite (i.left ≫ G.X.hom) := (Over.w i).symm ▸ inferInstance
    exact IsFinite.of_comp _ G.X.hom
  · intro x
    exact himage x.toMul

end Langlands.AlgebraicGeometry.FiniteEtale
