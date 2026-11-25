/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.Mathlib.Algebra.Group.Subgroup.Ker
public import WeilConjectures.CategoryTheory.Sites.SheafifyGrp

/-!
# The group law on the Picard group

The Picard group `Pic Y` of a scheme `Y` is a commutative group under the tensor product of
invertible modules: the unit is the class of `𝒪_Y`, the inverse of the class of `ℒ` is the class
of its dual `ℒᵛ`, and pulling back along a morphism of schemes is a group homomorphism.

The Picard presheaf `T ↦ Pic (X_T)` of a morphism `f: X ⟶ S` is therefore a presheaf of groups,
`AlgebraicGeometry.picardPresheafGrp`. Its fppf sheafification, the relative Picard functor
`Pic_{X/S}`, inherits the group law (`CategoryTheory.sheafifyGrp`), so a scheme representing
`Pic_{X/S}` is a commutative group scheme whose group law is the tensor product of invertible
modules (`AlgebraicGeometry.exists_commGrpObj_isPicardMul`).

For a morphism `f: X ⟶ S` with a section `σ`, the `σ`-normalized Picard functor `Pic_{X/S,σ}` is
the kernel of `σ_T^*: Pic (X_T) ⟶ Pic T`, so it is a presheaf of groups; this is
`AlgebraicGeometry.picardFunctorNormalizedGrp`, whose underlying presheaf of sets is
`AlgebraicGeometry.picardFunctorNormalized`.

## Main definitions

- `AlgebraicGeometry.Scheme.Pic.instCommGroup`: the group law on `Pic Y`.
- `AlgebraicGeometry.Scheme.Pic.mapHom`: the pullback `Pic Y →* Pic X` along `X ⟶ Y`.
- `AlgebraicGeometry.picardPresheafGrp`: the Picard presheaf as a presheaf of groups.
- `AlgebraicGeometry.IsPicardMul`: a representation of `Pic_{X/S}` by a group scheme respects the
  group laws.
- `AlgebraicGeometry.picardFunctorNormalizedGrp`: the `σ`-normalized Picard functor as a presheaf
  of groups.
- `AlgebraicGeometry.picardFunctorGrp`, `AlgebraicGeometry.toPicardFunctorHom`: `Pic_{X/S}` as a
  presheaf of groups, and the homomorphism `Pic (X_T) →* Pic_{X/S}(T)`.
- `AlgebraicGeometry.picMulEquivProdPicardFunctorNormalized`: the splitting
  `Pic (X_T) ≃* Pic T × Pic_{X/S,σ}(T)`.
- `AlgebraicGeometry.picardFunctorNormalizedMulEquiv`: `Pic_{X/S,σ}(T) ≃* Pic_{X/S}(T)` under
  the hypotheses of the split exact sequence.

## Main statements

- `AlgebraicGeometry.exists_commGrpObj_isPicardMul`: a scheme representing `Pic_{X/S}` carries a
  commutative group scheme structure respecting the group laws.
- `AlgebraicGeometry.range_pic_mapHom_snd_eq_ker_toPicardFunctorHom` and
  `AlgebraicGeometry.surjective_toPicardFunctorHom`: exactness of
  `0 → Pic T → Pic (X_T) → Pic_{X/S}(T) → 0` as groups.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

namespace Scheme.Pic

variable {X Y : Scheme.{u}}

local instance (Y : Scheme.{u}) :
    SheafOfModules.IsInvertible.{u, u, u} (SheafOfModules.unit Y.ringCatSheaf) :=
  SheafOfModules.instIsInvertibleUnit.{u, u, u}

/-- The chosen representative of a class in the Picard group is invertible. -/
instance isInvertible_fromSkeleton (L : Y.Pic) :
    Modules.IsInvertible ((fromSkeleton Y.Modules).obj L.val) :=
  have := L.isInvertible
  Modules.IsInvertible.of_sheafOfModules _

/-- The class of a module which is invertible in the sense of
`AlgebraicGeometry.Scheme.Modules.IsInvertible`. -/
noncomputable def ofIsInvertible (M : Y.Modules) [Modules.IsInvertible M] : Y.Pic :=
  have := Modules.IsInvertible.sheafOfModules_isInvertible M
  mk M

/-- The representative of `ofIsInvertible M` is isomorphic to `M`. -/
noncomputable def ofIsInvertibleIso (M : Y.Modules) [Modules.IsInvertible M] :
    (fromSkeleton Y.Modules).obj (ofIsInvertible M).val ≅ M :=
  fromSkeletonToSkeletonIso M

/-- A class is `ofIsInvertible M` if and only if its representative is isomorphic to `M`. -/
lemma eq_ofIsInvertible_iff (L : Y.Pic) (M : Y.Modules) [Modules.IsInvertible M] :
    L = ofIsInvertible M ↔ Nonempty ((fromSkeleton Y.Modules).obj L.val ≅ M) :=
  eq_iff_nonempty_iso.trans
    ⟨fun ⟨e⟩ ↦ ⟨e ≪≫ ofIsInvertibleIso M⟩, fun ⟨e⟩ ↦ ⟨e ≪≫ (ofIsInvertibleIso M).symm⟩⟩

noncomputable instance : One Y.Pic :=
  ⟨ofIsInvertible (𝟙_ Y.Modules)⟩

noncomputable instance : Mul Y.Pic :=
  ⟨fun L L' ↦ ofIsInvertible
    ((fromSkeleton Y.Modules).obj L.val ⊗ (fromSkeleton Y.Modules).obj L'.val)⟩

noncomputable instance : Inv Y.Pic :=
  ⟨fun L ↦ ofIsInvertible ((fromSkeleton Y.Modules).obj L.val)ᵛ⟩

lemma one_def : (1 : Y.Pic) = ofIsInvertible (𝟙_ Y.Modules) :=
  rfl

lemma mul_def (L L' : Y.Pic) : L * L' =
    ofIsInvertible ((fromSkeleton Y.Modules).obj L.val ⊗ (fromSkeleton Y.Modules).obj L'.val) :=
  rfl

lemma inv_def (L : Y.Pic) : L⁻¹ = ofIsInvertible ((fromSkeleton Y.Modules).obj L.val)ᵛ :=
  rfl

/-- The unit of the Picard group is the class of the structure sheaf. -/
lemma one_eq_mk_unit : (1 : Y.Pic) = mk (SheafOfModules.unit Y.ringCatSheaf) :=
  rfl

/-- The representative of `L * L'` is the tensor product of the representatives. -/
noncomputable def mulIso (L L' : Y.Pic) :
    (fromSkeleton Y.Modules).obj (L * L').val ≅
      (fromSkeleton Y.Modules).obj L.val ⊗ (fromSkeleton Y.Modules).obj L'.val :=
  ofIsInvertibleIso _

/-- The representative of `1` is the structure sheaf. -/
noncomputable def oneIso : (fromSkeleton Y.Modules).obj (1 : Y.Pic).val ≅ 𝟙_ Y.Modules :=
  ofIsInvertibleIso _

/-- **The group law on the Picard group**, induced by the tensor product of invertible modules.
The unit is the class of `𝒪_Y` and the inverse of a class is the class of the dual module;
tensor products and duals of invertible modules are invertible by
`AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorObj` and
`AlgebraicGeometry.Scheme.Modules.IsInvertible.dual`. -/
noncomputable instance instCommGroup : CommGroup Y.Pic where
  mul_assoc L L' L'' := by
    refine eq_iff_nonempty_iso.2 ⟨mulIso _ _ ≪≫ whiskerRightIso (mulIso _ _) _ ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ (mulIso _ _).symm ≪≫ (mulIso _ _).symm⟩
  one_mul L := by
    refine (eq_iff_nonempty_iso.2 ?_)
    exact ⟨mulIso _ _ ≪≫ whiskerRightIso oneIso _ ≪≫ λ_ _⟩
  mul_one L := by
    refine (eq_iff_nonempty_iso.2 ?_)
    exact ⟨mulIso _ _ ≪≫ whiskerLeftIso _ oneIso ≪≫ ρ_ _⟩
  inv_mul_cancel L := by
    obtain ⟨d⟩ := Modules.nonempty_tensorObj_dual_iso_unit ((fromSkeleton Y.Modules).obj L.val)
    refine (eq_iff_nonempty_iso.2 ?_)
    exact ⟨mulIso _ _ ≪≫ whiskerRightIso (ofIsInvertibleIso _) _ ≪≫ β_ _ _ ≪≫ d ≪≫ oneIso.symm⟩
  mul_comm L L' := by
    exact eq_iff_nonempty_iso.2 ⟨mulIso _ _ ≪≫ β_ _ _ ≪≫ (mulIso _ _).symm⟩

/-- Pulling back along `g` commutes with the tensor product of invertible modules. -/
lemma map_mul (g : X ⟶ Y) (L L' : Y.Pic) : map g (L * L') = map g L * map g L' := by
  obtain ⟨t⟩ := Modules.nonempty_pullback_tensorObj_iso g ((fromSkeleton Y.Modules).obj L.val)
    ((fromSkeleton Y.Modules).obj L'.val)
  exact eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Modules.pullback g).mapIso (mulIso L L') ≪≫ t ≪≫
    ((fromSkeletonToSkeletonIso _).symm ⊗ᵢ (fromSkeletonToSkeletonIso _).symm) ≪≫
    (mulIso (map g L) (map g L')).symm⟩

lemma map_one (g : X ⟶ Y) : map g (1 : Y.Pic) = 1 :=
  map_mk_unit g

/-- The pullback `g^* : Pic Y →* Pic X` along a morphism of schemes `g : X ⟶ Y`, as a group
homomorphism. -/
noncomputable def mapHom (g : X ⟶ Y) : Y.Pic →* X.Pic :=
  MonoidHom.mk' (map g) (map_mul g)

@[simp]
lemma mapHom_apply (g : X ⟶ Y) (L : Y.Pic) : mapHom g L = map g L :=
  rfl

/-- Isomorphic invertible modules have the same class. -/
lemma ofIsInvertible_eq_of_iso {M N : Y.Modules} [Modules.IsInvertible M]
    [Modules.IsInvertible N] (e : M ≅ N) : ofIsInvertible M = ofIsInvertible N :=
  (eq_ofIsInvertible_iff _ N).2 ⟨ofIsInvertibleIso M ≪≫ e⟩

/-- Invertible modules with the same class are isomorphic. -/
lemma nonempty_iso_of_ofIsInvertible_eq {M N : Y.Modules} [Modules.IsInvertible M]
    [Modules.IsInvertible N] (h : ofIsInvertible M = ofIsInvertible N) : Nonempty (M ≅ N) := by
  obtain ⟨e⟩ := (eq_ofIsInvertible_iff _ N).1 h
  exact ⟨(ofIsInvertibleIso M).symm ≪≫ e⟩

/-- Every class is the class of its representative. -/
lemma ofIsInvertible_fromSkeleton (L : Y.Pic) :
    ofIsInvertible ((fromSkeleton Y.Modules).obj L.val) = L :=
  ((eq_ofIsInvertible_iff L _).2 ⟨Iso.refl _⟩).symm

lemma ofIsInvertible_unit : ofIsInvertible (𝟙_ Y.Modules) = 1 :=
  rfl

/-- The class of a tensor product of invertible modules is the product of their classes. -/
lemma ofIsInvertible_tensorObj (M N : Y.Modules) [Modules.IsInvertible M]
    [Modules.IsInvertible N] : ofIsInvertible (M ⊗ N) = ofIsInvertible M * ofIsInvertible N :=
  ofIsInvertible_eq_of_iso ((ofIsInvertibleIso M).symm ⊗ᵢ (ofIsInvertibleIso N).symm)

/-- The class of the dual of an invertible module is the inverse of its class. -/
lemma ofIsInvertible_dual (M : Y.Modules) [Modules.IsInvertible M] :
    ofIsInvertible Mᵛ = (ofIsInvertible M)⁻¹ := by
  obtain ⟨d⟩ := Modules.nonempty_tensorObj_dual_iso_unit M
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← ofIsInvertible_tensorObj, ofIsInvertible_eq_of_iso d, ofIsInvertible_unit]

/-- **The Picard group of a one-point scheme is trivial**: an invertible module on a scheme with
a single point is trivial on a neighbourhood of that point, which is the whole scheme. -/
theorem eq_one_of_subsingleton [Subsingleton Y] (y : Y) (L : Y.Pic) : L = 1 := by
  obtain ⟨e⟩ := Modules.IsInvertible.nonempty_iso_unit y ((fromSkeleton Y.Modules).obj L.val)
  exact eq_iff_nonempty_iso.2 ⟨e ≪≫ oneIso.symm⟩

end Scheme.Pic

variable {X S : Scheme.{u}}

/-- **The Picard presheaf is a presheaf of groups**: `T ↦ Pic (X_T)` with the tensor product of
invertible modules, pulling back along `X_{T'} ⟶ X_T` being a group homomorphism. The underlying
presheaf of sets is `AlgebraicGeometry.picardPresheaf`
(`AlgebraicGeometry.picardPresheafGrp_comp_forget`). -/
noncomputable def picardPresheafGrp (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of (pullback f T.unop.hom).Pic
  map φ := GrpCat.ofHom (Pic.mapHom (baseChangeMap f φ.unop))
  map_id T := by
    refine GrpCat.hom_ext (MonoidHom.ext fun L ↦ ?_)
    change Pic.map (baseChangeMap f (𝟙 T).unop) L = L
    rw [unop_id, baseChangeMap_id, Pic.map_id]
  map_comp φ ψ := by
    refine GrpCat.hom_ext (MonoidHom.ext fun L ↦ ?_)
    change Pic.map (baseChangeMap f (φ ≫ ψ).unop) L =
      Pic.map (baseChangeMap f ψ.unop) (Pic.map (baseChangeMap f φ.unop) L)
    rw [unop_comp, baseChangeMap_comp, Pic.map_comp]

/-- The underlying presheaf of sets of `picardPresheafGrp` is `picardPresheaf`. -/
lemma picardPresheafGrp_comp_forget (f : X ⟶ S) :
    picardPresheafGrp f ⋙ forget GrpCat.{u + 1} = picardPresheaf f :=
  rfl

/-- A representation `e` of the relative Picard functor `Pic_{X/S}` by a group scheme `A`
*respects the group laws* if, for every `S`-scheme `T`, the map `Pic (X_T) ⟶ (T ⟶ A)` sending a
class `ℒ` to the point of `A` classifying its image in `Pic_{X/S}(T)` is a group homomorphism:
the group law of `A` is the tensor product of invertible modules. -/
def IsPicardMul (f : X ⟶ S) {A : Over S} [GrpObj A]
    (e : (picardFunctor f).obj.RepresentableBy A) : Prop :=
  ∀ {T : Over S} (L M : (pullback f T.hom).Pic),
    e.homEquiv.symm ((toPicardFunctor f).app (.op T) (L * M)) =
      e.homEquiv.symm ((toPicardFunctor f).app (.op T) L) *
        e.homEquiv.symm ((toPicardFunctor f).app (.op T) M)

/-- **A scheme representing the Picard functor is a commutative group scheme.** Let `A` represent
the relative Picard functor `Pic_{X/S}`. Then `A` carries a commutative group scheme structure
for which the representation respects the group laws: its group law is induced by the tensor
product of invertible modules. -/
theorem exists_commGrpObj_isPicardMul (f : X ⟶ S) {A : Over S}
    (e : (picardFunctor f).obj.RepresentableBy A) : ∃ _ : CommGrpObj A, IsPicardMul f e := by
  let G := picardPresheafGrp f
  let e' : (sheafify (fppfTopology.over S) (G ⋙ forget GrpCat)).RepresentableBy A := e
  let := GrpObj.ofRepresentableBySheafify _ G A e'
  have := isCommMonObj_ofRepresentableBySheafify _ G
    (fun Y (x y : (pullback f Y.unop.hom).Pic) ↦ mul_comm x y) e'
  exact ⟨{ }, fun {T} L M ↦ homEquiv_symm_toSheafify_mul _ G e' (Y := T) L M⟩

/-- **The `σ`-normalized Picard functor is a presheaf of groups.** For `f: X ⟶ S` with a
section `σ`, the `σ`-normalized classes form the kernel of the group homomorphism
`σ_T^*: Pic (X_T) ⟶ Pic T`, and pulling back along `X_{T'} ⟶ X_T` is a group homomorphism.
The underlying presheaf of sets is `AlgebraicGeometry.picardFunctorNormalized`
(`AlgebraicGeometry.picardFunctorNormalizedGrp_comp_forget`). The group law is the tensor
product of invertible modules. -/
noncomputable def picardFunctorNormalizedGrp (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of (Pic.mapHom (sectionBaseChange f σ hσ T.unop)).ker
  map φ := GrpCat.ofHom
    { toFun L := ⟨Pic.map (baseChangeMap f φ.unop) L.1,
        (picardFunctorNormalized f σ hσ).map φ L.2⟩
      map_one' := Subtype.ext (Pic.map_one _)
      map_mul' L L' := Subtype.ext (Pic.map_mul _ L.1 L'.1) }
  map_id T := by
    refine GrpCat.hom_ext (MonoidHom.ext fun L ↦ Subtype.ext ?_)
    change Pic.map (baseChangeMap f (𝟙 T).unop) L.1 = L.1
    rw [unop_id, baseChangeMap_id, Pic.map_id]
  map_comp φ ψ := by
    refine GrpCat.hom_ext (MonoidHom.ext fun L ↦ Subtype.ext ?_)
    change Pic.map (baseChangeMap f (φ ≫ ψ).unop) L.1 =
      Pic.map (baseChangeMap f ψ.unop) (Pic.map (baseChangeMap f φ.unop) L.1)
    rw [unop_comp, baseChangeMap_comp, Pic.map_comp]

/-- The underlying presheaf of sets of `picardFunctorNormalizedGrp` is
`picardFunctorNormalized`. -/
lemma picardFunctorNormalizedGrp_comp_forget (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    picardFunctorNormalizedGrp f σ hσ ⋙ forget GrpCat.{u + 1} =
      (picardFunctorNormalized f σ hσ).toFunctor :=
  rfl


/-- **The splitting `Pic (X_T) ≅ Pic T × Pic_{X/S,σ}(T)` as groups.** For `f: X ⟶ S` with a
section `σ`, the pullback `f_T^*: Pic T ⟶ Pic (X_T)` is split by `σ_T^*`, so
`ℒ ↦ (σ_T^* ℒ, ℒ ⊗ f_T^* σ_T^* ℒ⁻¹)` is a group isomorphism onto `Pic T × K(T)`, where
`K(T) = ker σ_T^* = Pic_{X/S,σ}(T)` (`AlgebraicGeometry.picardFunctorNormalizedGrp`). -/
noncomputable def picMulEquivProdPicardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) (T : Over S) :
    (pullback f T.hom).Pic ≃* T.left.Pic × (Pic.mapHom (sectionBaseChange f σ hσ T)).ker :=
  (Pic.mapHom (sectionBaseChange f σ hσ T)).prodKerEquivOfLeftInverse
    (Pic.mapHom (pullback.snd f T.hom)) fun N ↦ by
      rw [Pic.mapHom_apply, Pic.mapHom_apply, ← Pic.map_comp, sectionBaseChange_snd, Pic.map_id]

@[simp]
lemma picMulEquivProdPicardFunctorNormalized_apply_fst (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) (T : Over S) (L : (pullback f T.hom).Pic) :
    (picMulEquivProdPicardFunctorNormalized f σ hσ T L).1 =
      Pic.map (sectionBaseChange f σ hσ T) L :=
  rfl

@[simp]
lemma coe_picMulEquivProdPicardFunctorNormalized_apply_snd (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) (T : Over S) (L : (pullback f T.hom).Pic) :
    ((picMulEquivProdPicardFunctorNormalized f σ hσ T L).2 : (pullback f T.hom).Pic) =
      L * (Pic.map (pullback.snd f T.hom) (Pic.map (sectionBaseChange f σ hσ T) L))⁻¹ :=
  rfl

@[simp]
lemma picMulEquivProdPicardFunctorNormalized_symm_apply (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) (T : Over S)
    (p : T.left.Pic × (Pic.mapHom (sectionBaseChange f σ hσ T)).ker) :
    (picMulEquivProdPicardFunctorNormalized f σ hσ T).symm p =
      Pic.map (pullback.snd f T.hom) p.1 * p.2 :=
  rfl

/-- **The relative Picard functor as a presheaf of groups.** The fppf sheafification `Pic_{X/S}`
of the Picard presheaf inherits its group law (`CategoryTheory.sheafifyGrp`); the underlying
presheaf of sets is `(AlgebraicGeometry.picardFunctor f).obj`
(`AlgebraicGeometry.picardFunctorGrp_comp_forget`). -/
noncomputable def picardFunctorGrp (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ GrpCat.{u + 1} :=
  sheafifyGrp (fppfTopology.over S) (picardPresheafGrp f)

/-- The underlying presheaf of sets of `picardFunctorGrp` is `Pic_{X/S}`. -/
lemma picardFunctorGrp_comp_forget (f : X ⟶ S) :
    picardFunctorGrp f ⋙ forget GrpCat.{u + 1} = (picardFunctor f).obj :=
  rfl

/-- The canonical map `Pic (X_T) ⟶ Pic_{X/S}(T)` is a group homomorphism. -/
noncomputable def toPicardFunctorHom (f : X ⟶ S) (T : Over S) :
    (pullback f T.hom).Pic →* (picardFunctorGrp f).obj (.op T) where
  toFun := (toPicardFunctor f).app (.op T)
  map_one' := rfl
  map_mul' := toSheafify_mul (fppfTopology.over S) (picardPresheafGrp f)

@[simp]
lemma toPicardFunctorHom_apply (f : X ⟶ S) (T : Over S) (L : (pullback f T.hom).Pic) :
    toPicardFunctorHom f T L = (toPicardFunctor f).app (.op T) L :=
  rfl

/-- **Exactness in the middle of `0 → Pic T → Pic (X_T) → Pic_{X/S}(T)`, as groups.** If
`𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an isomorphism for every `T` over `S`, the kernel of the group
homomorphism `Pic (X_T) ⟶ Pic_{X/S}(T)` is the image of `f_T^*: Pic T ⟶ Pic (X_T)`
(`AlgebraicGeometry.toPicardFunctor_app_eq_iff`). Exactness on the left is
`AlgebraicGeometry.injective_pic_map_snd`. -/
theorem range_pic_mapHom_snd_eq_ker_toPicardFunctorHom (f : X ⟶ S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (pullback.snd f T.hom))) (T : Over S) :
    (Pic.mapHom (pullback.snd f T.hom)).range = (toPicardFunctorHom f T).ker := by
  ext L
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨N, rfl⟩
    exact toPicardFunctor_app_eq_of_iso f _ 1 N (fromSkeletonToSkeletonIso _ ≪≫ (λ_ _).symm ≪≫
      whiskerRightIso Pic.oneIso.symm _)
  · obtain ⟨N, ⟨e⟩⟩ := (toPicardFunctor_app_eq_iff f hf L 1).1 h
    exact ⟨N, Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫ (λ_ _).symm ≪≫
      whiskerRightIso Pic.oneIso.symm _ ≪≫ e.symm⟩⟩

/-- **Exactness on the right of `0 → Pic T → Pic (X_T) → Pic_{X/S}(T) → 0`.** If `f` has a
section and `𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an isomorphism for every `T` over `S`, the group
homomorphism `Pic (X_T) ⟶ Pic_{X/S}(T)` is surjective
(`AlgebraicGeometry.bijective_toPicardFunctor_picardFunctorNormalized`). -/
theorem surjective_toPicardFunctorHom (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (pullback.snd f T.hom))) (T : Over S) :
    Function.Surjective (toPicardFunctorHom f T) := fun s ↦
  have ⟨L, hL⟩ := (bijective_toPicardFunctor_picardFunctorNormalized f σ hσ hf T).2 s
  ⟨L.1, hL⟩

/-- **`Pic_{X/S,σ}(T) ≅ Pic_{X/S}(T)` as groups.** Under the hypotheses of
`AlgebraicGeometry.bijective_toPicardFunctor_picardFunctorNormalized`, the restriction of the
group homomorphism `Pic (X_T) ⟶ Pic_{X/S}(T)` to `K(T) = ker σ_T^*` is a group isomorphism. -/
noncomputable def picardFunctorNormalizedMulEquiv (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (pullback.snd f T.hom))) (T : Over S) :
    (Pic.mapHom (sectionBaseChange f σ hσ T)).ker ≃* (picardFunctorGrp f).obj (.op T) :=
  MulEquiv.ofBijective ((toPicardFunctorHom f T).comp (Subgroup.subtype _))
    (bijective_toPicardFunctor_picardFunctorNormalized f σ hσ hf T)

@[simp]
lemma picardFunctorNormalizedMulEquiv_apply (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (pullback.snd f T.hom))) (T : Over S)
    (L : (Pic.mapHom (sectionBaseChange f σ hσ T)).ker) :
    picardFunctorNormalizedMulEquiv f σ hσ hf T L = (toPicardFunctor f).app (.op T) L.1 :=
  rfl

end AlgebraicGeometry
