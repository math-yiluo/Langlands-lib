/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Localization.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Rationalization of recollement data

Let `M` be a submonoid of a commutative ring `R`. We show that the rationalization
`CategoryTheory.Rationalization M -` (the Verdier quotient by the `M`-torsion objects) is
functorial in `R`-linear triangulated functors *and natural transformations*:

- the functor `CategoryTheory.Rationalization.map M F` induced by `F` commutes with the shifts
  and is triangulated;
- a natural transformation `α : F ⟶ G` induces `CategoryTheory.Rationalization.mapNatTrans M α`;
- `map M (F ⋙ G) ≅ map M F ⋙ map M G` and `map M (𝟭 C) ≅ 𝟭 _`;
- an adjunction `adj : F ⊣ G` induces `CategoryTheory.Rationalization.mapAdjunction M adj`,
  whose counit (resp. unit) is invertible when that of `adj` is.

An object `Q X` of the rationalization is zero if and only if `X` is `M`-torsion
(`CategoryTheory.Rationalization.isZero_Q_obj_iff`). Using this we show that the rationalization
of recollement data (in the sense of `WeilConjectures.CategoryTheory.Triangulated.Recollement`)
is again recollement data, so that the closed part `map M i` of the rationalized data has a right
adjoint and the supported localization triangle exists at the rational stage (blueprint
`lemma-local-cohomology-right-adjoint--2`, rational stage `E`).

Finally, we provide the `R`-linearity of the functors `ObjectProperty.liftFullSubcategory`, so
that all this applies to triangulated full subcategories of `R`-linear triangulated categories.
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory

namespace ObjectProperty

/-- The functor between full subcategories induced by an `R`-linear functor is `R`-linear. -/
instance liftFullSubcategory_linear {R : Type*} [Semiring R] {C D : Type*} [Category* C]
    [Category* D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D) [F.Linear R]
    (h : ∀ X, P X → Q (F.obj X)) : (P.liftFullSubcategory Q F h).Linear R where
  map_smul f r := Q.hom_ext (F.map_smul r f.hom)

end ObjectProperty

namespace Rationalization

variable {R : Type w} [CommRing R] (M : Submonoid R)
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D n).Linear R]
  [Pretriangulated D] [IsTriangulated D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear R E] [HasZeroObject E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [∀ n : ℤ, (shiftFunctor E n).Linear R]
  [Pretriangulated E] [IsTriangulated E]

omit [IsTriangulated D] [IsTriangulated E] in
variable {M} in
/-- An object of `C` becomes zero in the rationalization if and only if it is `M`-torsion. -/
lemma isZero_Q_obj_iff (X : C) : IsZero ((Q M C).obj X) ↔ torsion M C X := by
  rw [IsZero.iff_id_eq_zero, ← (Q M C).map_id, ← (Q M C).map_zero, map_eq_map_iff, torsion_iff]
  simp

section Functoriality

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]

/-- The functor induced on rationalizations by an `R`-linear triangulated functor commutes
with the shifts. -/
noncomputable instance commShift_map : (map M F).CommShift ℤ :=
  Functor.commShiftOfLocalization (Q M C) (W M C) ℤ (F ⋙ Q M D) (map M F)

/-- The isomorphism `mapFac M F` commutes with the shifts. -/
instance commShift_mapFac_hom : NatTrans.CommShift (mapFac M F).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (Q M C) (W M C) ℤ (F ⋙ Q M D) (map M F)

/-- The functor induced on rationalizations by an `R`-linear triangulated functor is
triangulated. -/
instance isTriangulated_map : (map M F).IsTriangulated := by
  have := Localization.essSurj_mapArrow (Q M C) (W M C)
  exact Functor.isTriangulated_of_precomp_iso (mapFac M F)

/-- The `2`-commutative square expressing that `map M F` is induced by `F`. -/
noncomputable instance catCommSq : CatCommSq F (Q M C) (Q M D) (map M F) :=
  ⟨(mapFac M F).symm⟩

end Functoriality

section NatTrans

variable {F G H : C ⥤ D} [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]
  [G.CommShift ℤ] [G.IsTriangulated] [G.Linear R] [H.CommShift ℤ] [H.IsTriangulated]
  [H.Linear R]

/-- The natural transformation `map M F ⟶ map M G` induced by a natural transformation
`α : F ⟶ G` of `R`-linear triangulated functors. -/
noncomputable def mapNatTrans (α : F ⟶ G) : map M F ⟶ map M G :=
  Localization.liftNatTrans (Q M C) (W M C) (F ⋙ Q M D) (G ⋙ Q M D) (map M F) (map M G)
    (Functor.whiskerRight α (Q M D))

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- The components of `mapNatTrans M α` at the objects `Q X`. -/
@[simp]
lemma mapNatTrans_app (α : F ⟶ G) (X : C) :
    (mapNatTrans M α).app ((Q M C).obj X) =
      (mapFac M F).hom.app X ≫ (Q M D).map (α.app X) ≫ (mapFac M G).inv.app X :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ _

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- `mapNatTrans M α` is compatible with `mapFac`. -/
@[reassoc]
lemma mapFac_hom_naturality (α : F ⟶ G) (X : C) :
    (mapNatTrans M α).app ((Q M C).obj X) ≫ (mapFac M G).hom.app X =
      (mapFac M F).hom.app X ≫ (Q M D).map (α.app X) := by
  simp

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- `mapNatTrans` preserves identities. -/
@[simp]
lemma mapNatTrans_id : mapNatTrans M (𝟙 F) = 𝟙 (map M F) :=
  Localization.natTrans_ext (Q M C) (W M C) fun X ↦ by simp

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- `mapNatTrans` preserves composition. -/
@[reassoc (attr := simp)]
lemma mapNatTrans_comp (α : F ⟶ G) (β : G ⟶ H) :
    mapNatTrans M (α ≫ β) = mapNatTrans M α ≫ mapNatTrans M β :=
  Localization.natTrans_ext (Q M C) (W M C) fun X ↦ by simp

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- The natural isomorphism `map M F ≅ map M G` induced by a natural isomorphism `e : F ≅ G` of
`R`-linear triangulated functors. -/
@[simps]
noncomputable def mapNatIso (e : F ≅ G) : map M F ≅ map M G where
  hom := mapNatTrans M e.hom
  inv := mapNatTrans M e.inv
  hom_inv_id := by rw [← mapNatTrans_comp, e.hom_inv_id, mapNatTrans_id]
  inv_hom_id := by rw [← mapNatTrans_comp, e.inv_hom_id, mapNatTrans_id]

end NatTrans

section Comp

variable (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]
  [G.CommShift ℤ] [G.IsTriangulated] [G.Linear R]

/-- The functor `map M F ⋙ map M G` lifts `(F ⋙ G) ⋙ Q M E`. -/
noncomputable instance liftingMapComp : Localization.Lifting (Q M C) (W M C) ((F ⋙ G) ⋙ Q M E)
    (map M F ⋙ map M G) :=
  ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (mapFac M F) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (mapFac M G) ≪≫
    (Functor.associator _ _ _).symm⟩

/-- The rationalization of a composite is the composite of the rationalizations. -/
noncomputable def mapComp : map M (F ⋙ G) ≅ map M F ⋙ map M G :=
  Localization.liftNatIso (Q M C) (W M C) ((F ⋙ G) ⋙ Q M E) ((F ⋙ G) ⋙ Q M E) _ _ (Iso.refl _)

/-- The rationalization of the identity is the identity. -/
noncomputable def mapId : map M (𝟭 C) ≅ 𝟭 (Rationalization M C) :=
  letI : Localization.Lifting (Q M C) (W M C) (𝟭 C ⋙ Q M C) (𝟭 (Rationalization M C)) :=
    ⟨Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm⟩
  Localization.liftNatIso (Q M C) (W M C) (𝟭 C ⋙ Q M C) (𝟭 C ⋙ Q M C) _ _ (Iso.refl _)

end Comp

section Adjunction

variable {M} {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]
  [G.CommShift ℤ] [G.IsTriangulated] [G.Linear R]

variable (M) in
/-- The adjunction between rationalizations induced by an adjunction `F ⊣ G` of `R`-linear
triangulated functors. -/
noncomputable def mapAdjunction (adj : F ⊣ G) : map M F ⊣ map M G :=
  adj.localization (Q M C) (W M C) (Q M D) (W M D) (map M F) (map M G)

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- The components of the unit of `mapAdjunction M adj` at the objects `Q X`. -/
lemma mapAdjunction_unit_app (adj : F ⊣ G) (X : C) :
    (mapAdjunction M adj).unit.app ((Q M C).obj X) =
      (Q M C).map (adj.unit.app X) ≫ (mapFac M G).inv.app (F.obj X) ≫
        (map M G).map ((mapFac M F).inv.app X) :=
  adj.localization_unit_app _ _ _ _ _ _ X

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- The components of the counit of `mapAdjunction M adj` at the objects `Q Y`. -/
lemma mapAdjunction_counit_app (adj : F ⊣ G) (Y : D) :
    (mapAdjunction M adj).counit.app ((Q M D).obj Y) =
      (map M F).map ((mapFac M G).hom.app Y) ≫ (mapFac M F).hom.app (G.obj Y) ≫
        (Q M D).map (adj.counit.app Y) :=
  adj.localization_counit_app _ _ _ _ _ _ Y

omit [IsTriangulated C] [∀ n : ℤ, (shiftFunctor C n).Linear R] in
/-- A natural transformation of functors out of the rationalization is an isomorphism if its
components at the objects `Q X` are. -/
lemma isIso_of_isIso_app_Q {T : Type*} [Category* T] {F₁ F₂ : Rationalization M C ⥤ T}
    (τ : F₁ ⟶ F₂) (h : ∀ X : C, IsIso (τ.app ((Q M C).obj X))) : IsIso τ := by
  have := Localization.essSurj (Q M C) (W M C)
  have (Y : Rationalization M C) : IsIso (τ.app Y) :=
    (NatTrans.isIso_app_iff_of_iso τ ((Q M C).objObjPreimageIso Y)).1 (h _)
  exact NatIso.isIso_of_isIso_app τ

/-- The rationalization of an adjunction with invertible counit has invertible counit. -/
instance isIso_mapAdjunction_counit (adj : F ⊣ G) [IsIso adj.counit] :
    IsIso (mapAdjunction M adj).counit :=
  isIso_of_isIso_app_Q _ fun Y ↦ by
    rw [mapAdjunction_counit_app]
    infer_instance

/-- The rationalization of an adjunction with invertible unit has invertible unit. -/
instance isIso_mapAdjunction_unit (adj : F ⊣ G) [IsIso adj.unit] :
    IsIso (mapAdjunction M adj).unit :=
  isIso_of_isIso_app_Q _ fun X ↦ by
    rw [mapAdjunction_unit_app]
    infer_instance

end Adjunction

/-! ### Rationalization of recollement data

Here `C` plays the role of the closed part, `D` of the ambient category and `E` of the open
part: `i : C ⥤ D`, `jUp : D ⥤ E` and `jUp ⊣ jLow`. -/

section Recollement

variable {M} {i : C ⥤ D} {jUp : D ⥤ E} {jLow : E ⥤ D} [i.CommShift ℤ] [i.IsTriangulated]
  [i.Linear R] [jUp.CommShift ℤ] [jUp.IsTriangulated] [jUp.Linear R] [jLow.CommShift ℤ]
  [jLow.IsTriangulated] [jLow.Linear R]

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, rational stage `E`: if `j^* i = 0` then the
same holds for the rationalizations. -/
lemma isZero_map_obj_map_obj (h₀ : ∀ X, IsZero (jUp.obj (i.obj X)))
    (X : Rationalization M C) : IsZero ((map M jUp).obj ((map M i).obj X)) := by
  have := Localization.essSurj (Q M C) (W M C)
  exact ((Q M E).map_isZero (h₀ _)).of_iso ((map M jUp).mapIso ((map M i).mapIso
    ((Q M C).objObjPreimageIso X).symm ≪≫ (mapFac M i).app _) ≪≫ (mapFac M jUp).app _)

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, rational stage `E`: in a recollement
situation, every object of the rationalization killed by `map M jUp` lies in the essential image of
`map M i`. The proof: write the object as `Q K`; then `jUp K` is `M`-torsion, hence so is
`jLow (jUp K)`, so that the first map of the triangle `F ⟶ K ⟶ jLow (jUp K) ⟶` (with `F` in the
essential image of `i`) becomes invertible in the rationalization. -/
lemma essImage_map_of_isZero (adj : jUp ⊣ jLow) [IsIso adj.counit]
    (hess : ∀ K, IsZero (jUp.obj K) → i.essImage K) (K : Rationalization M D)
    (hK : IsZero ((map M jUp).obj K)) : (map M i).essImage K := by
  have := Localization.essSurj (Q M D) (W M D)
  set e := (Q M D).objObjPreimageIso K
  obtain ⟨m, hm, hm₀⟩ := (isZero_Q_obj_iff _).1
    (hK.of_iso (((mapFac M jUp).app _).symm ≪≫ (map M jUp).mapIso e))
  obtain ⟨F, a, δ, hT, Y, ⟨eY⟩⟩ := Pretriangulated.Recollement.exists_distTriang_unit adj hess
    ((Q M D).objPreimage K)
  have : IsIso ((Q M D).map a) := Localization.inverts (Q M D) (W M D) a
    (ObjectProperty.trW.mk _ hT ⟨m, hm, by
      rw [Triangle.mk_obj₃, Functor.comp_obj, ← jLow.map_id, ← jLow.map_smul, hm₀, jLow.map_zero]⟩)
  exact ⟨(Q M C).obj Y, ⟨(mapFac M i).app Y ≪≫ (Q M D).mapIso eY ≪≫ asIso ((Q M D).map a) ≪≫
    e⟩⟩

variable [i.Full] [i.Faithful]

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, rational stage `E`: the closed part of the
rationalized recollement data has a right adjoint (the rational `Ri^!`). -/
lemma isLeftAdjoint_map (adj : jUp ⊣ jLow) [IsIso adj.counit]
    (h₀ : ∀ X, IsZero (jUp.obj (i.obj X))) (hess : ∀ K, IsZero (jUp.obj K) → i.essImage K) :
    (map M i).IsLeftAdjoint :=
  Pretriangulated.Recollement.isLeftAdjoint (mapAdjunction M adj)
    (Functor.FullyFaithful.ofFullyFaithful _) (isZero_map_obj_map_obj h₀)
    (essImage_map_of_isZero adj hess)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, rational stage `E`: the supported
localization triangle `i i^! K ⟶ K ⟶ j_* j^* K ⟶` of the rationalized recollement data, for any
right adjoint `G'` of `map M i`, exists and has a unique third map. -/
theorem existsUnique_distTriang_counit_unit_map (adj : jUp ⊣ jLow) [IsIso adj.counit]
    (h₀ : ∀ X, IsZero (jUp.obj (i.obj X))) (hess : ∀ K, IsZero (jUp.obj K) → i.essImage K)
    {G' : Rationalization M D ⥤ Rationalization M C} (adj' : map M i ⊣ G')
    (K : Rationalization M D) :
    ∃! w, Pretriangulated.Recollement.triangle (mapAdjunction M adj) adj' K w ∈ distTriang _ :=
  Pretriangulated.Recollement.existsUnique_distTriang_counit_unit (mapAdjunction M adj) adj'
    (Functor.FullyFaithful.ofFullyFaithful _) (isZero_map_obj_map_obj h₀)
    (essImage_map_of_isZero adj hess) K

end Recollement

end Rationalization

end CategoryTheory
