/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian

/-!

# The tensor product of sheaves is preadditive and linear,
  the pushforward of sheaves is lax braided, the pullback is monoidal

Let `A` be an abelian monoidal category whose tensor product is additive in each variable
and `J` a Grothendieck topology with `HasSheafify J A` such that the localized monoidal
structure `Sheaf.monoidalCategory` on `Sheaf J A` is available (`(J.W).IsMonoidal`).
We show that this monoidal structure is compatible with the preadditive structure on
`Sheaf J A`, i.e. `MonoidalPreadditive (Sheaf J A)`, and, when `A` is moreover `R`-linear
with `R`-linear tensor product, that it is compatible with the `R`-linear structure,
i.e. `MonoidalLinear R (Sheaf J A)`.

The sheafification functor `presheafToSheaf J A` is braided, hence its right adjoint
`sheafToPresheaf J A` is lax braided.

If `F : C ⥤ D` is a continuous functor of sites, the pushforward
`F.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A` is obtained by sheafifying the
restriction along `F.op` of the underlying presheaf. As restriction is a braided functor
between the (pointwise monoidal) categories of presheaves, the pushforward is lax braided.
When `A` is symmetric this says that `F.sheafPushforwardContinuous A J K` is lax symmetric
monoidal.

Its left adjoint, the pullback `sheafPullbackConstruction.sheafPullback F A J K` (left Kan
extension along `F.op` followed by sheafification), is therefore oplax monoidal. If the comma
categories `CostructuredArrow F.op X` are sifted (for example if `F` is representably flat)
and tensoring in `A` preserves colimits of these shapes (for example if `A` is closed), then
the pullback is strong monoidal. The proof compares the sheaf-level adjunction, precomposed with
sheafification, with the composite of the presheaf-level adjunction
`F.op.lan ⊣ (whiskeringLeft _ _ A).obj F.op` and sheafification: both have right adjoint the
underlying presheaf of the pushforward, as lax monoidal functors up to a monoidal isomorphism,
so their oplax structures correspond (`CategoryTheory.isIso_δ_of_conjugateIso`). The left Kan
extension is strong monoidal by `CategoryTheory.Functor.isIso_lan_δ`, and so is
sheafification.

## Main results

- `CategoryTheory.Sheaf.monoidalPreadditive`: the monoidal category structure on
  `Sheaf J A` obtained in `Sheaf.monoidalCategory` is preadditive.
- `CategoryTheory.Sheaf.monoidalLinear`: the monoidal category structure on
  `Sheaf J A` obtained in `Sheaf.monoidalCategory` is `R`-linear.
- `CategoryTheory.sheafToPresheafLaxBraided`: the underlying presheaf functor is lax braided.
- `CategoryTheory.Functor.sheafPushforwardContinuousLaxBraided`: the pushforward of sheaves
  along a continuous functor of sites is lax braided.
- `CategoryTheory.Functor.ε_sheafPushforwardContinuous_of_iso_id` and
  `CategoryTheory.Functor.ε_sheafPushforwardContinuous_of_iso_comp`: the unit `ε` of the lax
  monoidal pushforward is compatible with the identity and composition isomorphisms of
  pushforwards.
- `CategoryTheory.Functor.sheafPullbackConstruction.isIso_δ_sheafPullback` and
  `CategoryTheory.Functor.sheafPullbackConstruction.isIso_η_sheafPullback`: the comparison
  maps of the oplax monoidal pullback are isomorphisms, e.g. along a representably flat
  continuous functor.
- `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackMonoidal`: the pullback of
  sheaves is then strong monoidal.
-/




@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Sheaf

open MonoidalCategory CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A] [Abelian A] [MonoidalPreadditive A]
  [HasSheafify J A] [(J.W (A := A)).IsMonoidal]

attribute [local instance] monoidalCategory

/-- The isomorphism `L P ⊗ L Q ≅ L (P ⊗ Q)` for sheafification `L`, as a natural
isomorphism `presheafToSheaf J A ⋙ tensorLeft ((presheafToSheaf J A).obj P) ≅
tensorLeft P ⋙ presheafToSheaf J A` in the second variable. -/
noncomputable def presheafToSheafCompTensorLeftIso (P : Cᵒᵖ ⥤ A) :
    presheafToSheaf J A ⋙ tensorLeft ((presheafToSheaf J A).obj P) ≅
      tensorLeft P ⋙ presheafToSheaf J A :=
  NatIso.ofComponents (fun Q ↦ Functor.Monoidal.μIso (presheafToSheaf J A) P Q)
    (fun _ ↦ by simp)

/-- The isomorphism `L P ⊗ L Q ≅ L (P ⊗ Q)` for sheafification `L`, as a natural
isomorphism `presheafToSheaf J A ⋙ tensorRight ((presheafToSheaf J A).obj Q) ≅
tensorRight Q ⋙ presheafToSheaf J A` in the first variable. -/
noncomputable def presheafToSheafCompTensorRightIso (Q : Cᵒᵖ ⥤ A) :
    presheafToSheaf J A ⋙ tensorRight ((presheafToSheaf J A).obj Q) ≅
      tensorRight Q ⋙ presheafToSheaf J A :=
  NatIso.ofComponents (fun P ↦ Functor.Monoidal.μIso (presheafToSheaf J A) P Q)
    (fun _ ↦ by simp)

/-- Tensoring on the left with a sheaf `X` is, up to natural isomorphism, computed by
tensoring the underlying presheaves with `X.obj` and sheafifying. -/
noncomputable def tensorLeftIso (X : Sheaf J A) :
    tensorLeft X ≅ sheafToPresheaf J A ⋙ tensorLeft X.obj ⋙ presheafToSheaf J A :=
  (curriedTensor (Sheaf J A)).mapIso
      (asIso ((sheafificationAdjunction J A).counit.app X)).symm ≪≫
    (tensorLeft _).leftUnitor.symm ≪≫
    isoWhiskerRight (asIso (sheafificationAdjunction J A).counit).symm _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (sheafToPresheaf J A) (presheafToSheafCompTensorLeftIso X.obj)

/-- Tensoring on the right with a sheaf `X` is, up to natural isomorphism, computed by
tensoring the underlying presheaves with `X.obj` and sheafifying. -/
noncomputable def tensorRightIso (X : Sheaf J A) :
    tensorRight X ≅ sheafToPresheaf J A ⋙ tensorRight X.obj ⋙ presheafToSheaf J A :=
  (curriedTensor (Sheaf J A)).flip.mapIso
      (asIso ((sheafificationAdjunction J A).counit.app X)).symm ≪≫
    (tensorRight _).leftUnitor.symm ≪≫
    isoWhiskerRight (asIso (sheafificationAdjunction J A).counit).symm _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (sheafToPresheaf J A) (presheafToSheafCompTensorRightIso X.obj)

noncomputable instance (X : Sheaf J A) : (tensorLeft X).Additive :=
  Functor.additive_of_iso (tensorLeftIso X).symm

noncomputable instance (X : Sheaf J A) : (tensorRight X).Additive :=
  Functor.additive_of_iso (tensorRightIso X).symm

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory`
is preadditive when `A` is an abelian monoidal category with additive tensor product. -/
instance monoidalPreadditive : MonoidalPreadditive (Sheaf J A) where
  whiskerLeft_zero {X Y Z} := (tensorLeft X).map_zero Y Z
  zero_whiskerRight {X Y Z} := (tensorRight X).map_zero Y Z
  whiskerLeft_add {X _ _} _ _ := (tensorLeft X).map_add
  add_whiskerRight {X _ _} _ _ := (tensorRight X).map_add

section Linear

variable (R : Type*) [Semiring R] [Linear R A] [MonoidalLinear R A]

noncomputable instance (X : Sheaf J A) : (tensorLeft X).Linear R :=
  Functor.linear_of_iso R (tensorLeftIso X).symm

noncomputable instance (X : Sheaf J A) : (tensorRight X).Linear R :=
  Functor.linear_of_iso R (tensorRightIso X).symm

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory`
is `R`-linear when `A` is an abelian `R`-linear monoidal category with `R`-linear tensor
product. -/
instance monoidalLinear : MonoidalLinear R (Sheaf J A) where
  whiskerLeft_smul X {_ _} r f := (tensorLeft X).map_smul r f
  smul_whiskerRight r {_ _} f X := (tensorRight X).map_smul r f

end Linear

end CategoryTheory.Sheaf

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A] [BraidedCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The functor sending a sheaf to its underlying presheaf is lax monoidal, being the right
adjoint of the (strong) monoidal sheafification functor. -/
noncomputable instance sheafToPresheafLaxMonoidal : (sheafToPresheaf J A).LaxMonoidal :=
  (sheafificationAdjunction J A).rightAdjointLaxMonoidal

/-- The functor sending a sheaf to its underlying presheaf is lax braided, being the right
adjoint of the braided sheafification functor. -/
noncomputable instance sheafToPresheafLaxBraided : (sheafToPresheaf J A).LaxBraided :=
  (sheafificationAdjunction J A).rightAdjointLaxBraided

namespace Functor

variable [F.IsContinuous J K] [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]

/-- The pushforward of sheaves along a continuous functor `F : C ⥤ D` is the sheafification of
the restriction along `F.op` of the underlying presheaf. -/
noncomputable def sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso :
    sheafToPresheaf K A ⋙ (whiskeringLeft _ _ A).obj F.op ⋙ presheafToSheaf J A ≅
      F.sheafPushforwardContinuous A J K :=
  isoWhiskerLeft (F.sheafPushforwardContinuous A J K)
      (asIso (sheafificationAdjunction J A).counit) ≪≫
    (F.sheafPushforwardContinuous A J K).rightUnitor

/-- The pushforward of sheaves along a continuous functor of sites is lax monoidal. -/
noncomputable instance sheafPushforwardContinuousLaxMonoidal :
    (F.sheafPushforwardContinuous A J K).LaxMonoidal :=
  LaxMonoidal.transport (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)

/-- The pushforward of sheaves along a continuous functor of sites is lax braided. When `A` is
symmetric, this says that the pushforward is lax symmetric monoidal. -/
noncomputable instance sheafPushforwardContinuousLaxBraided :
    (F.sheafPushforwardContinuous A J K).LaxBraided :=
  have := LaxMonoidal.natTransIsMonoidal_of_transport
    (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)
  LaxBraided.ofNatIso (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)

end Functor

namespace Functor.sheafPullbackConstruction

open Limits MonoidalCategory OplaxMonoidal

variable [F.IsContinuous J K] [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseLeftKanExtension P]

/-- The pullback of sheaves along a continuous functor of sites is oplax monoidal, being left
adjoint to the lax monoidal pushforward. -/
noncomputable instance sheafPullbackOplaxMonoidal : (sheafPullback F A J K).OplaxMonoidal :=
  (sheafAdjunctionContinuous F A J K).leftAdjointOplaxMonoidal

/-- The adjunction between the pullback and the pushforward of sheaves is monoidal. -/
instance isMonoidal_sheafAdjunctionContinuous :
    (sheafAdjunctionContinuous F A J K).IsMonoidal := by
  let := (sheafAdjunctionContinuous F A J K).leftAdjointOplaxMonoidal
  infer_instance

/-- The isomorphism from the restriction along `F.op` of the underlying presheaf of a sheaf to
the underlying presheaf of its pushforward. Both functors send a sheaf `P` to `F.op ⋙ P.obj`,
but the lax monoidal structure of the target is transported along
`sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso`. At `P` it is
```
  F.op ⋙ P.obj ──toSheafify──▶ sheafify (F.op ⋙ P.obj) ──≅──▶ ((F_*) P).obj
```
where the first map is invertible since `F.op ⋙ P.obj` is a sheaf, and this is a monoidal
isomorphism. -/
noncomputable def sheafToPresheafCompWhiskeringLeftIsoPushforward :
    sheafToPresheaf K A ⋙ (whiskeringLeft _ _ A).obj F.op ≅
      F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A :=
  have : IsIso (whiskerLeft (sheafToPresheaf K A ⋙ (whiskeringLeft _ _ A).obj F.op)
      (sheafificationAdjunction J A).unit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun P ↦ isIso_toSheafify J ((F.sheafPushforwardContinuous A J K).obj P).property
  (sheafToPresheaf K A ⋙ (whiskeringLeft _ _ A).obj F.op).rightUnitor.symm ≪≫
    asIso (whiskerLeft _ (sheafificationAdjunction J A).unit) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    isoWhiskerRight (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K) _

instance : NatTrans.IsMonoidal (sheafToPresheafCompWhiskeringLeftIsoPushforward F A J K).hom := by
  have := LaxMonoidal.natTransIsMonoidal_of_transport
    (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)
  dsimp only [sheafToPresheafCompWhiskeringLeftIsoPushforward, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, isoWhiskerRight_hom]
  infer_instance

section Connected

variable [∀ X : Dᵒᵖ, IsConnected (CostructuredArrow F.op X)]

/-- The comparison map `η : F^*𝟙 ⟶ 𝟙` of the pullback of sheaves is an isomorphism if the
comma categories `CostructuredArrow F.op X` are connected, e.g. if `F` is representably flat.
The pullback precomposed with sheafification and left Kan extension along `F.op` followed by
sheafification are both left adjoint to the underlying presheaf of the pushforward, and the
second is strong monoidal. So `η` of the first one is invertible by the conjugate triangle
`CategoryTheory.conjugateEquiv_symm_app_unit_comp_η`. -/
instance isIso_η_sheafPullback : IsIso (η (sheafPullback F A J K)) := by
  have : IsIso (η (F.op.lan ⋙ presheafToSheaf K A)) := by
    rw [comp_η]
    infer_instance
  have := isIso_η_of_conjugateIso
    ((sheafificationAdjunction J A).comp (sheafAdjunctionContinuous F A J K))
    ((F.op.lanAdjunction A).comp (sheafificationAdjunction K A))
    (sheafToPresheafCompWhiskeringLeftIsoPushforward F A J K)
  rw [comp_η] at this
  exact IsIso.of_isIso_comp_left ((sheafPullback F A J K).map (η (presheafToSheaf J A))) _

end Connected

section Sifted

variable [∀ X : Dᵒᵖ, IsSifted (CostructuredArrow F.op X)]
  [∀ (X : Dᵒᵖ) (M : A), PreservesColimitsOfShape (CostructuredArrow F.op X) (tensorLeft M)]

/-- The comparison map `δ : F^*(S ⊗ T) ⟶ F^*S ⊗ F^*T` of the pullback of sheaves is an
isomorphism if the comma categories `CostructuredArrow F.op X` are sifted (e.g. if `F` is
representably flat) and tensoring in `A` on the left preserves colimits of these shapes; via
the braiding, so does tensoring on the right.

On sheafifications of presheaves `P`, `Q` this follows, as for `isIso_η_sheafPullback`, from
the conjugate square `CategoryTheory.conjugateEquiv_symm_app_tensor_comp_δ`, since `δ` is
invertible for left Kan extension along `F.op` followed by sheafification. For general
sheaves it follows from the naturality square of `δ` along the counit isomorphisms
`sheafify S.obj ⟶ S` and `sheafify T.obj ⟶ T`:
```
  F^*(sheafify S.obj ⊗ sheafify T.obj) ──δ──▶ F^*(sheafify S.obj) ⊗ F^*(sheafify T.obj)
              │ F^*(ε_S ⊗ ε_T)                          │ F^*ε_S ⊗ F^*ε_T
              ▼                                         ▼
          F^*(S ⊗ T) ─────────────δ─────────────▶ F^*S ⊗ F^*T
```
-/
instance isIso_δ_sheafPullback (S T : Sheaf J A) : IsIso (δ (sheafPullback F A J K) S T) := by
  have (X : Dᵒᵖ) (M : A) : PreservesColimitsOfShape (CostructuredArrow F.op X) (tensorRight M) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : IsIso (δ (F.op.lan ⋙ presheafToSheaf K A) S.obj T.obj) := by
    rw [comp_δ]
    infer_instance
  have := isIso_δ_of_conjugateIso
    ((sheafificationAdjunction J A).comp (sheafAdjunctionContinuous F A J K))
    ((F.op.lanAdjunction A).comp (sheafificationAdjunction K A))
    (sheafToPresheafCompWhiskeringLeftIsoPushforward F A J K) S.obj T.obj
  rw [comp_δ] at this
  have : IsIso (δ (sheafPullback F A J K) ((presheafToSheaf J A).obj S.obj)
      ((presheafToSheaf J A).obj T.obj)) :=
    IsIso.of_isIso_comp_left ((sheafPullback F A J K).map (δ (presheafToSheaf J A) S.obj T.obj)) _
  let εS : (presheafToSheaf J A).obj S.obj ⟶ S := (sheafificationAdjunction J A).counit.app S
  let εT : (presheafToSheaf J A).obj T.obj ⟶ T := (sheafificationAdjunction J A).counit.app T
  have : IsIso ((sheafPullback F A J K).map (εS ⊗ₘ εT) ≫ δ (sheafPullback F A J K) S T) := by
    rw [← δ_natural]
    infer_instance
  exact IsIso.of_isIso_comp_left ((sheafPullback F A J K).map (εS ⊗ₘ εT)) _

end Sifted

/-- The pullback of sheaves along a continuous functor `F` is strong monoidal if the comma
categories `CostructuredArrow F.op X` are sifted (e.g. if `F` is representably flat) and
tensoring in `A` on the left preserves colimits of these shapes. Its underlying oplax monoidal
structure is `sheafPullbackOplaxMonoidal`, by definition. -/
noncomputable instance sheafPullbackMonoidal
    [∀ X : Dᵒᵖ, IsSifted (CostructuredArrow F.op X)]
    [∀ (X : Dᵒᵖ) (M : A), PreservesColimitsOfShape (CostructuredArrow F.op X) (tensorLeft M)] :
    (sheafPullback F A J K).Monoidal :=
  .ofOplaxMonoidal _

example [∀ X : Dᵒᵖ, IsSifted (CostructuredArrow F.op X)]
    [∀ (X : Dᵒᵖ) (M : A), PreservesColimitsOfShape (CostructuredArrow F.op X) (tensorLeft M)] :
    (sheafPullbackMonoidal F A J K).toOplaxMonoidal = sheafPullbackOplaxMonoidal F A J K :=
  rfl

end Functor.sheafPullbackConstruction

section PushforwardUnit

open MonoidalCategory

namespace Functor

open LaxMonoidal

variable {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
  (A : Type*) [Category A] [MonoidalCategory A] [BraidedCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [F.IsContinuous J K]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]

attribute [local instance] Sheaf.monoidalCategory

omit [MonoidalCategory A] [BraidedCategory A] [(J.W (A := A)).IsMonoidal]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A] in
/-- The comparison isomorphism `sheafToPresheafCompWhiskeringLeftIsoPushforward` between the
restriction along `F.op` of the underlying presheaf and the underlying presheaf of the
pushforward is the identity on components, by the triangle identity of sheafification. -/
lemma sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app (G : Sheaf K A) :
    (sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F A J K).hom.app G = 𝟙 _ := by
  simp [sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward,
    sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso]
  rfl

/-- The unit `ε` of the lax monoidal pushforward `F_*` of sheaves, read on underlying
presheaves after the unit of the lax monoidal functor `sheafToPresheaf`, is the restriction
along `F.op` of the unit of `sheafToPresheaf`. -/
lemma ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous :
    ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map (ε (F.sheafPushforwardContinuous A J K)) =
      ε ((whiskeringLeft _ _ A).obj F.op) ≫
        ((whiskeringLeft _ _ A).obj F.op).map (ε (sheafToPresheaf K A)) := by
  have h := NatTrans.IsMonoidal.unit
    (τ := (sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F A J K).hom)
  rw [sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app, comp_ε, comp_ε] at h
  simpa using h.symm

/-- The componentwise form of
`CategoryTheory.Functor.ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous`. -/
@[reassoc]
lemma ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app (U : Cᵒᵖ) :
    (ε (sheafToPresheaf J A)).app U ≫ (ε (F.sheafPushforwardContinuous A J K)).hom.app U =
      (ε (sheafToPresheaf K A)).app (F.op.obj U) := by
  simpa using congr_app (ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous F A J K) U

end Functor

namespace Sheaf

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type*} [Category C] {A : Type*} [Category A] [MonoidalCategory A]
  {J : GrothendieckTopology C} [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory

/-- Two morphisms of sheaves out of the monoidal unit agree as soon as they agree on
underlying presheaves after the unit `ε : 𝟙_ ⟶ (𝟙_ : Sheaf J A).obj` of the lax monoidal functor
`sheafToPresheaf`: this unit is adjoint to the isomorphism `η` of the monoidal sheafification. -/
lemma hom_ext_of_ε_comp {G : Sheaf J A} {a b : 𝟙_ (Sheaf J A) ⟶ G}
    (h : ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map a =
      ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map b) : a = b := by
  have e (c : 𝟙_ (Sheaf J A) ⟶ G) : ((sheafificationAdjunction J A).homEquiv _ _).symm
      (ε (sheafToPresheaf J A) ≫ (sheafToPresheaf J A).map c) =
        η (presheafToSheaf J A) ≫ c := by
    rw [Adjunction.homEquiv_naturality_right_symm]
    congr 1
    exact Equiv.symm_apply_apply _ _
  rw [← cancel_epi (η (presheafToSheaf J A)), ← e, ← e]
  exact congrArg _ h

end Sheaf

namespace Functor

open LaxMonoidal

attribute [local instance] Sheaf.monoidalCategory

variable {C : Type*} [Category C] (A : Type*) [Category A] [MonoidalCategory A]
  [BraidedCategory A] (J : GrothendieckTopology C) [(J.W (A := A)).IsMonoidal]
  [HasWeakSheafify J A]

/-- For a continuous functor `F` isomorphic to the identity, the unit `ε` of the lax monoidal
pushforward `F_*` is the identification `F_* ≅ 𝟭` of
`CategoryTheory.Functor.sheafPushforwardContinuousId'` at the monoidal unit. -/
lemma ε_sheafPushforwardContinuous_of_iso_id {F : C ⥤ C} (e : F ≅ 𝟭 C)
    [hF : F.IsContinuous J J] :
    ε (F.sheafPushforwardContinuous A J J) =
      (sheafPushforwardContinuousId' e A J).inv.app (𝟙_ _) := by
  apply Sheaf.hom_ext_of_ε_comp
  rw [ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous]
  ext U
  simpa [sheafPushforwardContinuousId'] using
    (ε (sheafToPresheaf J A)).naturality (e.hom.app U.unop).op

/-- For continuous functors `F`, `G` and `FG ≅ F ⋙ G`, the unit `ε` of the lax monoidal
pushforward `FG_*` is the composite of the units of `F_*` and `G_*` followed by the
identification `G_* ⋙ F_* ≅ FG_*` of `CategoryTheory.Functor.sheafPushforwardContinuousComp'`. -/
lemma ε_sheafPushforwardContinuous_of_iso_comp {D E : Type*} [Category D] [Category E]
    (K : GrothendieckTopology D) (L : GrothendieckTopology E) [(K.W (A := A)).IsMonoidal]
    [HasWeakSheafify K A] [(L.W (A := A)).IsMonoidal] [HasWeakSheafify L A]
    {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E} (e : F ⋙ G ≅ FG) [hF : F.IsContinuous J K]
    [hG : G.IsContinuous K L] [hFG : FG.IsContinuous J L] :
    ε (FG.sheafPushforwardContinuous A J L) =
      ε (F.sheafPushforwardContinuous A J K) ≫
        (F.sheafPushforwardContinuous A J K).map (ε (G.sheafPushforwardContinuous A K L)) ≫
          (sheafPushforwardContinuousComp' e A J K L).hom.app (𝟙_ _) := by
  apply Sheaf.hom_ext_of_ε_comp
  rw [ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous]
  ext U
  simpa [sheafPushforwardContinuousComp', sheafPushforwardContinuousComp,
    ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc] using
    (ε (sheafToPresheaf L A)).naturality (e.inv.app U.unop).op

end Functor

end PushforwardUnit

end CategoryTheory
