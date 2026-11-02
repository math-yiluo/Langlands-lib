/-
Adapted from `Definitions/Def_AlgebraicGeometry_RelativeGroupLawGrpObj.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: generalized from the base `Spec R` of a commutative ring `R` to an arbitrary base
scheme `S`, with the namespace `GoodReductionJacobian` renamed `GroupLawOverBase`; FLT
commands from `P2M.Util` are replaced by standard Lean commands. The paired Markdown file
lists all changes.
-/
import Langlands.AnthropicFLT.OverBase.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory NeronModelInfra

open scoped CategoryTheory.MonObj

namespace GroupLawOverBase

def overHomEquivSchemeHomOver {S : Scheme.{u}} {A : Scheme.{u}}
    (T : Over (S)) (f : A ⟶ S) :
    (T ⟶ Over.mk f) ≃ SchemeHomOver T.hom f where
  toFun φ := ⟨φ.left, by simpa using Over.w φ⟩
  invFun x := Over.homMk x.1 (by simpa using x.2)
  left_inv φ := Over.OverMorphism.ext (by simp)
  right_inv x := Subtype.ext (by simp)

@[simp]
theorem overHomEquivSchemeHomOver_apply_coe {S : Scheme.{u}} {A : Scheme.{u}}
    (T : Over (S)) (f : A ⟶ S)
    (φ : T ⟶ Over.mk f) : (overHomEquivSchemeHomOver T f φ).1 = φ.left :=
  rfl

@[simp]
theorem overHomEquivSchemeHomOver_symm_apply_left {S : Scheme.{u}} {A : Scheme.{u}}
    (T : Over (S)) (f : A ⟶ S)
    (x : SchemeHomOver T.hom f) : ((overHomEquivSchemeHomOver T f).symm x).left = x.1 :=
  rfl

theorem overHomEquivSchemeHomOver_mk_apply {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} {T : Scheme.{u}}
    (t : T ⟶ S) (h : Over.mk t ⟶ Over.mk f) :
    overHomEquivSchemeHomOver (Over.mk t) f h = overHomToSchemeHomOver h :=
  rfl

theorem overHomEquivSchemeHomOver_mk_symm_apply {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} {T : Scheme.{u}}
    (t : T ⟶ S) (x : SchemeHomOver t f) :
    (overHomEquivSchemeHomOver (Over.mk t) f).symm x = schemeHomOverToOverHom x :=
  rfl

theorem overHomToSchemeHomOver_injective {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} {T : Scheme.{u}}
    {t : T ⟶ S} :
    Function.Injective
      (overHomToSchemeHomOver : (Over.mk t ⟶ Over.mk f) → SchemeHomOver t f) := by
  intro a b h
  have h2 := congrArg schemeHomOverToOverHom h
  simpa using h2

def relativeGroupLawOfGrpObj (S : Scheme.{u}) {A : Scheme.{u}}
    (f : A ⟶ S) [GrpObj (Over.mk f)] : RelativeGroupLaw S f where
  mul {T} t x y :=
    overHomToSchemeHomOver (schemeHomOverToOverHom x * schemeHomOverToOverHom y)
  one {T} t := overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f)
  inv {T} t x := overHomToSchemeHomOver (schemeHomOverToOverHom x)⁻¹
  mul_assoc {T} t x y z := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [mul_assoc]
  one_mul {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [one_mul, overHomToSchemeHomOver_schemeHomOverToOverHom]
  mul_one {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [mul_one, overHomToSchemeHomOver_schemeHomOverToOverHom]
  inv_mul_cancel {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [inv_mul_cancel]
  mul_natural {T T'} t t' ψ hψ x y := by
    have key : ∀ z : SchemeHomOver t f,
        schemeHomOverComp ψ hψ z =
          overHomToSchemeHomOver
            ((Over.homMk ψ (by simpa using hψ) : Over.mk t' ⟶ Over.mk t) ≫
              schemeHomOverToOverHom z) := by
      intro z
      apply Subtype.ext
      simp
    rw [key, key, key]
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [MonObj.comp_mul]

@[simp]
theorem relativeGroupLawOfGrpObj_mul {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ S) (x y : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj S f).mul t x y =
      overHomToSchemeHomOver (schemeHomOverToOverHom x * schemeHomOverToOverHom y) :=
  rfl

@[simp]
theorem relativeGroupLawOfGrpObj_one {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ S) :
    (relativeGroupLawOfGrpObj S f).one t =
      overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f) :=
  rfl

@[simp]
theorem relativeGroupLawOfGrpObj_inv {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ S) (x : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj S f).inv t x =
      overHomToSchemeHomOver (schemeHomOverToOverHom x)⁻¹ :=
  rfl

def RelativeGroupLaw.yonedaGrpObjPresheaf {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) :
    (Over (S))ᵒᵖ ⥤ GrpCat.{u} where
  obj T := @GrpCat.of (SchemeHomOver T.unop.hom f) (G.pointGroup T.unop.hom)
  map {S T} χ :=
    letI := G.pointGroup S.unop.hom
    letI := G.pointGroup T.unop.hom
    GrpCat.ofHom
      { toFun := fun x => schemeHomOverComp χ.unop.left (Over.w χ.unop) x
        map_one' := G.one_natural _ _ _ _
        map_mul' := fun x y => G.mul_natural _ _ _ _ x y }
  map_id S := by
    letI := G.pointGroup S.unop.hom
    refine GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext ?_)
    simp
  map_comp {S T U} χ χ' := by
    letI := G.pointGroup S.unop.hom
    letI := G.pointGroup T.unop.hom
    letI := G.pointGroup U.unop.hom
    refine GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext ?_)
    simp

def RelativeGroupLaw.overMkRepresentableBy {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) :
    (G.yonedaGrpObjPresheaf ⋙ forget GrpCat).RepresentableBy (Over.mk f) where
  homEquiv {T} := overHomEquivSchemeHomOver T f
  homEquiv_comp _ _ := Subtype.ext rfl

@[reducible]
def RelativeGroupLaw.grpObjOverMk {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) : GrpObj (Over.mk f) :=
  GrpObj.ofRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf G.overMkRepresentableBy

theorem RelativeGroupLaw.overHomToSchemeHomOver_mul {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ S) (a b : Over.mk t ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver (a * b) =
      G.mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b) := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom.map_mul a b

theorem RelativeGroupLaw.overHomToSchemeHomOver_one {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ S) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f) = G.one t := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom.map_one

theorem RelativeGroupLaw.overHomToSchemeHomOver_inv {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ S) (a : Over.mk t ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver a⁻¹ = G.inv t (overHomToSchemeHomOver a) := by
  letI := G.grpObjOverMk
  letI := G.pointGroup t
  exact map_inv ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom a

theorem RelativeGroupLaw.overHomEquivSchemeHomOver_mul {S : Scheme.{u}}
    {A : Scheme.{u}} {f : A ⟶ S} (G : RelativeGroupLaw S f)
    (T : Over (S)) (a b : T ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver T f (a * b) =
      G.mul T.hom (overHomEquivSchemeHomOver T f a) (overHomEquivSchemeHomOver T f b) := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op T)).hom.map_mul a b

theorem RelativeGroupLaw.overHomEquivSchemeHomOver_one {S : Scheme.{u}}
    {A : Scheme.{u}} {f : A ⟶ S} (G : RelativeGroupLaw S f)
    (T : Over (S)) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver T f (1 : T ⟶ Over.mk f) = G.one T.hom := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op T)).hom.map_one

theorem RelativeGroupLaw.overHomEquivSchemeHomOver_inv {S : Scheme.{u}}
    {A : Scheme.{u}} {f : A ⟶ S} (G : RelativeGroupLaw S f)
    (T : Over (S)) (a : T ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver T f a⁻¹ = G.inv T.hom (overHomEquivSchemeHomOver T f a) := by
  letI := G.grpObjOverMk
  letI := G.pointGroup T.hom
  exact map_inv ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op T)).hom a

theorem RelativeGroupLaw.grpObjOverMk_mul_eq {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver (Over.mk f ⊗ Over.mk f) f μ[Over.mk f] =
      G.mul (Over.mk f ⊗ Over.mk f).hom
        (overHomEquivSchemeHomOver (Over.mk f ⊗ Over.mk f) f (fst (Over.mk f) (Over.mk f)))
        (overHomEquivSchemeHomOver (Over.mk f ⊗ Over.mk f) f (snd (Over.mk f) (Over.mk f))) := by
  letI := G.grpObjOverMk
  rw [MonObj.mul_eq_mul]
  exact G.overHomEquivSchemeHomOver_mul (Over.mk f ⊗ Over.mk f)
    (fst (Over.mk f) (Over.mk f)) (snd (Over.mk f) (Over.mk f))

theorem RelativeGroupLaw.grpObjOverMk_one_eq {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver (𝟙_ (Over (S))) f η[Over.mk f] =
      G.one (𝟙_ (Over (S))).hom := by
  letI := G.grpObjOverMk
  rw [MonObj.one_eq_one]
  exact G.overHomEquivSchemeHomOver_one (𝟙_ (Over (S)))

theorem RelativeGroupLaw.grpObjOverMk_inv_eq {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver (Over.mk f) f ι[Over.mk f] =
      G.inv (Over.mk f).hom (overHomEquivSchemeHomOver (Over.mk f) f (𝟙 (Over.mk f))) := by
  letI := G.grpObjOverMk
  rw [GrpObj.inv_eq_inv]
  exact G.overHomEquivSchemeHomOver_inv (Over.mk f) (𝟙 (Over.mk f))

theorem relativeGroupLawOfGrpObj_grpObjOverMk_mul {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ S) (x y : SchemeHomOver t f) :
    letI := G.grpObjOverMk
    (relativeGroupLawOfGrpObj S f).mul t x y = G.mul t x y := by
  letI := G.grpObjOverMk
  have h := G.overHomToSchemeHomOver_mul t (schemeHomOverToOverHom x)
    (schemeHomOverToOverHom y)
  simpa using h

theorem relativeGroupLawOfGrpObj_grpObjOverMk_one {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ S) :
    letI := G.grpObjOverMk
    (relativeGroupLawOfGrpObj S f).one t = G.one t := by
  letI := G.grpObjOverMk
  exact G.overHomToSchemeHomOver_one t

theorem relativeGroupLawOfGrpObj_grpObjOverMk_inv {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ S) (x : SchemeHomOver t f) :
    letI := G.grpObjOverMk
    (relativeGroupLawOfGrpObj S f).inv t x = G.inv t x := by
  letI := G.grpObjOverMk
  have h := G.overHomToSchemeHomOver_inv t (schemeHomOverToOverHom x)
  simpa using h

theorem relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj {S : Scheme.{u}}
    {A : Scheme.{u}} {f : A ⟶ S} [GrpObj (Over.mk f)]
    (h : IsCommMonObj (Over.mk f)) {T : Scheme.{u}} (t : T ⟶ S)
    (x y : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj S f).mul t x y = (relativeGroupLawOfGrpObj S f).mul t y x := by
  haveI := (isCommMonObj_iff_isMulCommutative (Over.mk f)).mp h (Over.mk t)
  show overHomToSchemeHomOver (schemeHomOverToOverHom x * schemeHomOverToOverHom y) =
    overHomToSchemeHomOver (schemeHomOverToOverHom y * schemeHomOverToOverHom x)
  rw [mul_comm]

theorem isCommMonObj_of_relativeGroupLawOfGrpObj_comm {S : Scheme.{u}}
    {A : Scheme.{u}} {f : A ⟶ S} [GrpObj (Over.mk f)]
    (hc : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t f),
      (relativeGroupLawOfGrpObj S f).mul t x y = (relativeGroupLawOfGrpObj S f).mul t y x) :
    IsCommMonObj (Over.mk f) := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro X
  constructor
  constructor
  intro a b
  have h := hc X.hom (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)
  show a * b = b * a
  simp only [relativeGroupLawOfGrpObj, schemeHomOverToOverHom_overHomToSchemeHomOver] at h
  exact overHomToSchemeHomOver_injective h

theorem isCommMonObj_iff_relativeGroupLawOfGrpObj_comm {S : Scheme.{u}}
    {A : Scheme.{u}} {f : A ⟶ S} [GrpObj (Over.mk f)] :
    IsCommMonObj (Over.mk f) ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t f),
        (relativeGroupLawOfGrpObj S f).mul t x y = (relativeGroupLawOfGrpObj S f).mul t y x :=
  ⟨fun h _ _ x y => relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj h _ x y,
    fun hc => isCommMonObj_of_relativeGroupLawOfGrpObj_comm fun t x y => hc t x y⟩

theorem RelativeGroupLaw.isCommMonObj_grpObjOverMk_iff_mul_comm {S : Scheme.{u}}
    {A : Scheme.{u}} {f : A ⟶ S} (G : RelativeGroupLaw S f) :
    (letI := G.grpObjOverMk; IsCommMonObj (Over.mk f)) ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t f),
        G.mul t x y = G.mul t y x := by
  letI := G.grpObjOverMk
  constructor
  · intro h T t x y
    rw [← relativeGroupLawOfGrpObj_grpObjOverMk_mul G t x y,
      ← relativeGroupLawOfGrpObj_grpObjOverMk_mul G t y x]
    exact relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj h t x y
  · intro hc
    rw [isCommMonObj_iff_isMulCommutative]
    intro X
    constructor
    constructor
    intro a b
    apply (overHomEquivSchemeHomOver X f).injective
    rw [G.overHomEquivSchemeHomOver_mul X a b, G.overHomEquivSchemeHomOver_mul X b a]
    exact hc X.hom _ _

end GroupLawOverBase
