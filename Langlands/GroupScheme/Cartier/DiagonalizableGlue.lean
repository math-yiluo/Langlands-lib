import Langlands.GroupScheme.Cartier.DiagonalizablePoints
import Langlands.AlgebraicGeometry.LocallyConstantUnitPower

/-! # Characters of a diagonalizable group from locally constant functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.LocallyConstantUnitPower

namespace Langlands.GroupScheme.Cartier.DiagonalizableCharacters

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]

/-- For a locally constant `f : X → M`, the homomorphism `t ↦ lcPow t f` from
character-valued points `Multiplicative M →* Γ(X, ⊤)ˣ` to units. -/
def lcPowHom {X : Scheme.{u}} (f : LocallyConstant X M) :
    (Multiplicative M →* Γ(X, ⊤)ˣ) →* Γ(X, ⊤)ˣ where
  toFun t := lcPow t f
  map_one' := lcPow_one f
  map_mul' t t' := lcPow_mul t t' f

@[simp] lemma lcPowHom_apply {X : Scheme.{u}} (f : LocallyConstant X M)
    (t : Multiplicative M →* Γ(X, ⊤)ˣ) : lcPowHom f t = lcPow t f := rfl

/-- Pulling back a locally constant function along a composite is pulling back twice. -/
lemma comap_comp_base {N : Type*} {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (f : LocallyConstant Z N) :
    f.comap (g ≫ h).base.hom = (f.comap h.base.hom).comap g.base.hom := rfl

/-- The family `V ↦ lcPowHom (f ∘ V.hom)` is natural in `V`. -/
lemma isNaturalAct_lcPowHom {T : Over S} (f : LocallyConstant T.left M) :
    IsNaturalAct (fun V : Over T.left => lcPowHom (f.comap V.hom.base.hom)) := by
  intro V V' b t
  rw [lcPowHom_apply, lcPowHom_apply, lcPow_naturality, ← comap_comp_base, Over.w b]

/-- The character of `D_S(M)` over `T` attached to a locally constant function
`f : T → M`: on the character-valued point `t` over `V → T` it is the unit equal to
`t (f v)` near each point `v` of `V`. -/
def ofLocallyConstant {T : Over S} (f : LocallyConstant T.left M) :
    (characters (model S M)).obj (op T) :=
  ofAct (fun V => lcPowHom (f.comap V.hom.base.hom)) (isNaturalAct_lcPowHom f)

lemma act_ofLocallyConstant {T : Over S} (f : LocallyConstant T.left M) (V : Over T.left)
    (t : Multiplicative M →* Γ(V.left, ⊤)ˣ) :
    act (ofLocallyConstant f) V t = lcPow t (f.comap V.hom.base.hom) :=
  act_ofAct _ _ V t

lemma ofLocallyConstant_add {T : Over S} (f g : LocallyConstant T.left M) :
    ofLocallyConstant (f + g) = ofLocallyConstant f + ofLocallyConstant g := by
  apply act_ext
  intro V t
  rw [act_add, act_ofLocallyConstant, act_ofLocallyConstant, act_ofLocallyConstant,
    ← lcPow_add]
  rfl

lemma ofLocallyConstant_zero {T : Over S} :
    ofLocallyConstant (0 : LocallyConstant T.left M) = 0 := by
  apply act_ext
  intro V t
  rw [act_zero, act_ofLocallyConstant, ← lcPow_zero t]
  rfl

variable (M) in
/-- `ofLocallyConstant` as an additive homomorphism. -/
def ofLocallyConstantHom (T : Over S) :
    LocallyConstant T.left M →+ (characters (model S M)).obj (op T) where
  toFun := ofLocallyConstant
  map_zero' := ofLocallyConstant_zero
  map_add' := ofLocallyConstant_add

@[simp] lemma ofLocallyConstantHom_apply (T : Over S) (f : LocallyConstant T.left M) :
    ofLocallyConstantHom M T f = ofLocallyConstant f := rfl

/-- The constant function `m` gives the evaluation character at `m`. -/
lemma ofLocallyConstant_const (T : Over S) (m : M) :
    ofLocallyConstant (LocallyConstant.const T.left m) = evalChar T m := by
  rw [eq_evalChar_iff]
  intro V t
  rw [act_ofLocallyConstant]
  exact lcPow_const t m

/-- `ofLocallyConstant` commutes with Cartier restriction along `a : T' ⟶ T`. -/
lemma restrict_ofLocallyConstant {T T' : Over S} (a : T' ⟶ T) (f : LocallyConstant T.left M) :
    (characters (model S M)).map a.op (ofLocallyConstant f) =
      ofLocallyConstant (f.comap a.left.base.hom) := by
  apply act_ext
  intro V t
  rw [act_restrict, act_ofLocallyConstant, act_ofLocallyConstant]
  rfl

/-- If `f ∘ a` is constantly `m`, the restriction of `ofLocallyConstant f` along `a` is the
evaluation character at `m`. -/
lemma restrict_ofLocallyConstant_eq_evalChar {T T' : Over S} (a : T' ⟶ T)
    (f : LocallyConstant T.left M) (m : M) (h : ∀ x : T'.left, f (a.left x) = m) :
    (characters (model S M)).map a.op (ofLocallyConstant f) = evalChar T' m := by
  rw [restrict_ofLocallyConstant, ← ofLocallyConstant_const]
  congr 1
  ext x
  exact h x

end Langlands.GroupScheme.Cartier.DiagonalizableCharacters
