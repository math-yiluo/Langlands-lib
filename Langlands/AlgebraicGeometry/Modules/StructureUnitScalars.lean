import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs

/-! # Global units as automorphisms of the structure module -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

variable {X Y : Scheme.{u}}

/-- The value at one of an endomorphism of the structure module on an open subscheme,
viewed as a section of the structure sheaf. -/
noncomputable def structureEndValue (φ : structureModule X ⟶ structureModule X)
    (U : X.Opens) : Γ(X, U) :=
  φ.app U (1 : Γ(X, U))

/-- An endomorphism of the structure module acts on each open subscheme by
multiplication with its value at one. -/
lemma structureEnd_app_eq_mul (φ : structureModule X ⟶ structureModule X)
    (U : X.Opens) (a : Γ(X, U)) :
    φ.app U a = a * structureEndValue φ U := by
  have h := φ.app_smul a (1 : Γ(X, U))
  change φ.app U (a * 1 : Γ(X, U)) = a * structureEndValue φ U at h
  simpa only [mul_one] using h

/-- The value at one on an open subscheme is the restriction of the global value at one. -/
lemma structureEndValue_eq_res (φ : structureModule X ⟶ structureModule X) (U : X.Opens) :
    structureEndValue φ U =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (structureEndValue φ ⊤) := by
  have h := ConcreteCategory.congr_hom
    (φ.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op) (1 : Γ(X, ⊤))
  change φ.app U (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (1 : Γ(X, ⊤))) =
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (structureEndValue φ ⊤) at h
  rw [map_one] at h
  exact h

/-- Every local component of an endomorphism of the structure module is multiplication
by the restriction of its global value at one. -/
lemma structureEnd_app_eq_mul_res (φ : structureModule X ⟶ structureModule X)
    (U : X.Opens) (a : Γ(X, U)) :
    φ.app U a = a * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (structureEndValue φ ⊤) := by
  rw [structureEnd_app_eq_mul, structureEndValue_eq_res]

/-- Endomorphisms of the structure module are determined by their global value at one. -/
lemma structureEnd_ext {φ ψ : structureModule X ⟶ structureModule X}
    (h : structureEndValue φ ⊤ = structureEndValue ψ ⊤) : φ = ψ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  change φ.app U a = ψ.app U a
  rw [structureEnd_app_eq_mul_res, structureEnd_app_eq_mul_res, h]

/-- The value at one of a composite of endomorphisms of the structure module. -/
lemma structureEndValue_comp (φ ψ : structureModule X ⟶ structureModule X) (U : X.Opens) :
    structureEndValue (φ ≫ ψ) U = structureEndValue φ U * structureEndValue ψ U := by
  change ψ.app U (structureEndValue φ U) = _
  exact structureEnd_app_eq_mul ψ U _

/-- The value at one of the identity of the structure module. -/
@[simp]
lemma structureEndValue_id (U : X.Opens) : structureEndValue (𝟙 (structureModule X)) U = 1 :=
  rfl

/-- Multiplication by a global function, as an endomorphism of the structure module. -/
noncomputable def structureMulHom (r : Γ(X, ⊤)) : structureModule X ⟶ structureModule X :=
  sectionHom (structureModule X) r

/-- The global value at one of multiplication by a global function is that function. -/
@[simp]
lemma structureEndValue_mulHom (r : Γ(X, ⊤)) : structureEndValue (structureMulHom r) ⊤ = r := by
  have h := congrArg (fun s ↦ s.val (op (⊤ : X.Opens)))
    ((structureModule X).unitHomEquiv.apply_symm_apply (sectionFamily (structureModule X) r))
  change structureEndValue (structureMulHom r) ⊤ =
    X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r at h
  rw [h]
  change X.presheaf.map (𝟙 (op (⊤ : X.Opens))) r = r
  simp

/-- Multiplication by a global function acts on each open subscheme by multiplication
with its restriction. -/
lemma structureMulHom_app (r : Γ(X, ⊤)) (U : X.Opens) (a : Γ(X, U)) :
    (structureMulHom r).app U a = a * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r := by
  rw [structureEnd_app_eq_mul_res, structureEndValue_mulHom]

/-- The global unit by which an automorphism of the structure module acts: its value
is the image of one under the global component. -/
noncomputable def structureAutScalar (e : structureModule X ≅ structureModule X) :
    Γ(X, ⊤)ˣ where
  val := structureEndValue e.hom ⊤
  inv := structureEndValue e.inv ⊤
  val_inv := by
    rw [← structureEndValue_comp, e.hom_inv_id, structureEndValue_id]
  inv_val := by
    rw [← structureEndValue_comp, e.inv_hom_id, structureEndValue_id]

/-- The value of the global unit of an automorphism is the image of one under its
global component. -/
lemma structureAutScalar_val (e : structureModule X ≅ structureModule X) :
    (structureAutScalar e : Γ(X, ⊤)) = e.hom.app ⊤ (1 : Γ(X, ⊤)) :=
  rfl

/-- The inverse of the global unit of an automorphism is the image of one under the
global component of the inverse automorphism. -/
lemma structureAutScalar_inv_val (e : structureModule X ≅ structureModule X) :
    (((structureAutScalar e)⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) = e.inv.app ⊤ (1 : Γ(X, ⊤)) :=
  rfl

/-- Every local component of an automorphism of the structure module is multiplication by
the restriction of its global unit. -/
lemma structureAutScalar_hom_app (e : structureModule X ≅ structureModule X)
    (U : X.Opens) (a : Γ(X, U)) :
    e.hom.app U a =
      a * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (structureAutScalar e : Γ(X, ⊤)) :=
  structureEnd_app_eq_mul_res e.hom U a

/-- The inverse of an automorphism of the structure module is locally multiplication by
the restriction of the inverse global unit. -/
lemma structureAutScalar_inv_app (e : structureModule X ≅ structureModule X)
    (U : X.Opens) (a : Γ(X, U)) :
    e.inv.app U a =
      a * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (((structureAutScalar e)⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) :=
  structureEnd_app_eq_mul_res e.inv U a

/-- The automorphism of the structure module given by multiplication with a global unit. -/
noncomputable def structureAutOfUnit (r : Γ(X, ⊤)ˣ) : structureModule X ≅ structureModule X where
  hom := structureMulHom (r : Γ(X, ⊤))
  inv := structureMulHom ((r⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤))
  hom_inv_id := structureEnd_ext (by
    rw [structureEndValue_comp, structureEndValue_mulHom, structureEndValue_mulHom,
      Units.mul_inv, structureEndValue_id])
  inv_hom_id := structureEnd_ext (by
    rw [structureEndValue_comp, structureEndValue_mulHom, structureEndValue_mulHom,
      Units.inv_mul, structureEndValue_id])

lemma structureAutOfUnit_hom (r : Γ(X, ⊤)ˣ) :
    (structureAutOfUnit r).hom = structureMulHom (r : Γ(X, ⊤)) :=
  rfl

lemma structureAutOfUnit_inv (r : Γ(X, ⊤)ˣ) :
    (structureAutOfUnit r).inv = structureMulHom ((r⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) :=
  rfl

/-- The automorphism attached to a global unit acts locally by multiplication with its
restriction. -/
lemma structureAutOfUnit_hom_app (r : Γ(X, ⊤)ˣ) (U : X.Opens) (a : Γ(X, U)) :
    (structureAutOfUnit r).hom.app U a =
      a * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (r : Γ(X, ⊤)) :=
  structureMulHom_app _ U a

/-- The inverse of the automorphism attached to a global unit acts locally by
multiplication with the restriction of the inverse unit. -/
lemma structureAutOfUnit_inv_app (r : Γ(X, ⊤)ˣ) (U : X.Opens) (a : Γ(X, U)) :
    (structureAutOfUnit r).inv.app U a =
      a * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ((r⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) :=
  structureMulHom_app _ U a

/-- The scalar of the automorphism attached to a global unit is that unit. -/
@[simp]
lemma structureAutScalar_ofUnit (r : Γ(X, ⊤)ˣ) :
    structureAutScalar (structureAutOfUnit r) = r :=
  Units.ext (structureEndValue_mulHom _)

/-- An automorphism of the structure module is multiplication by its global unit. -/
@[simp]
lemma structureAutOfUnit_scalar (e : structureModule X ≅ structureModule X) :
    structureAutOfUnit (structureAutScalar e) = e :=
  Iso.ext (structureEnd_ext (structureEndValue_mulHom _))

/-- Automorphisms of the structure module correspond to global units. -/
noncomputable def structureAutUnitsEquiv :
    (structureModule X ≅ structureModule X) ≃ Γ(X, ⊤)ˣ where
  toFun := structureAutScalar
  invFun := structureAutOfUnit
  left_inv := structureAutOfUnit_scalar
  right_inv := structureAutScalar_ofUnit

@[simp]
lemma structureAutUnitsEquiv_apply (e : structureModule X ≅ structureModule X) :
    structureAutUnitsEquiv e = structureAutScalar e :=
  rfl

@[simp]
lemma structureAutUnitsEquiv_symm_apply (r : Γ(X, ⊤)ˣ) :
    structureAutUnitsEquiv.symm r = structureAutOfUnit r :=
  rfl

/-- Distinct automorphisms of the structure module have distinct global units. -/
lemma structureAutScalar_injective :
    Function.Injective (structureAutScalar : (structureModule X ≅ structureModule X) → _) :=
  structureAutUnitsEquiv.injective

/-- The identity automorphism has scalar one. -/
@[simp]
lemma structureAutScalar_refl : structureAutScalar (Iso.refl (structureModule X)) = 1 :=
  Units.ext rfl

/-- The scalar of a composite automorphism is the product of the scalars. -/
@[simp]
lemma structureAutScalar_trans (e e' : structureModule X ≅ structureModule X) :
    structureAutScalar (e ≪≫ e') = structureAutScalar e * structureAutScalar e' :=
  Units.ext (structureEndValue_comp e.hom e'.hom ⊤)

/-- The scalar of an inverse automorphism is the inverse scalar. -/
@[simp]
lemma structureAutScalar_symm (e : structureModule X ≅ structureModule X) :
    structureAutScalar e.symm = (structureAutScalar e)⁻¹ :=
  Units.ext rfl

/-- The automorphism group of the structure module is the group of global units. -/
noncomputable def structureAutMulEquiv : Aut (structureModule X) ≃* Γ(X, ⊤)ˣ where
  toEquiv := structureAutUnitsEquiv
  map_mul' e e' := by
    change structureAutScalar (e' ≪≫ e) = structureAutScalar e * structureAutScalar e'
    rw [structureAutScalar_trans, mul_comm]

@[simp]
lemma structureAutMulEquiv_apply (e : Aut (structureModule X)) :
    structureAutMulEquiv e = structureAutScalar e :=
  rfl

@[simp]
lemma structureAutMulEquiv_symm_apply (r : Γ(X, ⊤)ˣ) :
    structureAutMulEquiv.symm r = structureAutOfUnit r :=
  rfl

/-- The automorphism of the structure module of `X` obtained from an automorphism of the
structure module of `Y` by pulling back along `f` and conjugating with the canonical
comparison `pullbackUnitIso f`. -/
noncomputable def structureAutPullback (f : X ⟶ Y) (e : structureModule Y ≅ structureModule Y) :
    structureModule X ≅ structureModule X :=
  (Langlands.Scheme.Modules.pullbackUnitIso f).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫ Langlands.Scheme.Modules.pullbackUnitIso f

lemma structureAutPullback_hom (f : X ⟶ Y) (e : structureModule Y ≅ structureModule Y) :
    (structureAutPullback f e).hom =
      (Langlands.Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map e.hom ≫ (Langlands.Scheme.Modules.pullbackUnitIso f).hom :=
  rfl

/-- The pulled-back automorphism is multiplication by the image of the global unit under
the actual ring map `f.appTop`. -/
lemma structureAutPullback_eq_ofUnit (f : X ⟶ Y) (e : structureModule Y ≅ structureModule Y) :
    structureAutPullback f e =
      structureAutOfUnit (Units.map f.appTop.hom.toMonoidHom (structureAutScalar e)) := by
  apply Iso.ext
  rw [structureAutPullback_hom, Iso.inv_comp_eq]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  erw [Langlands.Scheme.Modules.pullbackUnitAdjunction X Y f]
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  change f.app U (e.hom.app U a) = (structureAutOfUnit _).hom.app (f ⁻¹ᵁ U) (f.app U a)
  rw [structureAutScalar_hom_app, structureAutOfUnit_hom_app, map_mul]
  congr 1
  exact ConcreteCategory.congr_hom
    (f.naturality (homOfLE (le_top : U ≤ ⊤)).op) (structureAutScalar e : Γ(Y, ⊤))

/-- Naturality of the global unit: conjugating the pullback of an automorphism `e` of
`𝒪_Y` by `pullbackUnitIso f` gives the automorphism of `𝒪_X` whose global unit is the
image of the global unit of `e` under `f.appTop`. -/
theorem structureAutScalar_pullback (f : X ⟶ Y) (e : structureModule Y ≅ structureModule Y) :
    structureAutScalar (structureAutPullback f e) =
      Units.map f.appTop.hom.toMonoidHom (structureAutScalar e) := by
  rw [structureAutPullback_eq_ofUnit, structureAutScalar_ofUnit]

end Langlands.SchemeModule
