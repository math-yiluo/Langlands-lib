import Langlands.AlgebraicGeometry.Picard.MumfordBundle
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethProof
import Langlands.AlgebraicGeometry.Modules.SchemeIsoCohomology
import Langlands.AlgebraicGeometry.Modules.PullbackMonoidal
import Langlands.AlgebraicGeometry.Modules.KunnethEulerProduct

/-! # The Euler characteristic of `m^* L ⊗ p^* M` on the self-product of an abelian scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

section Shear

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- A morphism into the parameter-first self-product from its two coordinates. -/
def mumfordProductLift {T : Over S} (a b : T ⟶ A.X) : T ⟶ mumfordProduct A :=
  Over.homMk (pullback.lift a.left b.left (by rw [Over.w a, Over.w b]))
    (by
      change pullback.lift a.left b.left _ ≫ pullback.fst A.X.hom A.X.hom ≫ A.X.hom = T.hom
      rw [pullback.lift_fst_assoc, Over.w a])

@[simp] lemma mumfordProductLift_first {T : Over S} (a b : T ⟶ A.X) :
    mumfordProductLift A a b ≫ mumfordFirst A = a := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[simp] lemma mumfordProductLift_second {T : Over S} (a b : T ⟶ A.X) :
    mumfordProductLift A a b ≫ mumfordSecond A = b := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

/-- Morphisms into the self-product are determined by their two coordinates. -/
lemma mumfordProduct_hom_ext {T : Over S} {a b : T ⟶ mumfordProduct A}
    (h₁ : a ≫ mumfordFirst A = b ≫ mumfordFirst A)
    (h₂ : a ≫ mumfordSecond A = b ≫ mumfordSecond A) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg CommaMorphism.left h₁
  · exact congrArg CommaMorphism.left h₂

/-- The shear `(x, y) ↦ (x + y, y)` of the self-product. -/
def mumfordShear : mumfordProduct A ⟶ mumfordProduct A :=
  mumfordProductLift A (mumfordFirst A * mumfordSecond A) (mumfordSecond A)

/-- The inverse shear `(x, y) ↦ (x - y, y)` of the self-product. -/
def mumfordShearInv : mumfordProduct A ⟶ mumfordProduct A :=
  mumfordProductLift A (mumfordFirst A * (mumfordSecond A)⁻¹) (mumfordSecond A)

/-- The shear as an automorphism of the self-product over the base. -/
def mumfordShearIso : mumfordProduct A ≅ mumfordProduct A where
  hom := mumfordShear A
  inv := mumfordShearInv A
  hom_inv_id := by
    apply mumfordProduct_hom_ext
    · rw [Category.assoc, mumfordShearInv, mumfordProductLift_first, MonObj.comp_mul,
        GrpObj.comp_inv, mumfordShear, mumfordProductLift_first, mumfordProductLift_second,
        mul_inv_cancel_right, Category.id_comp]
    · rw [Category.assoc, mumfordShearInv, mumfordProductLift_second, mumfordShear,
        mumfordProductLift_second, Category.id_comp]
  inv_hom_id := by
    apply mumfordProduct_hom_ext
    · rw [Category.assoc, mumfordShear, mumfordProductLift_first, MonObj.comp_mul,
        mumfordShearInv, mumfordProductLift_first, mumfordProductLift_second,
        inv_mul_cancel_right, Category.id_comp]
    · rw [Category.assoc, mumfordShear, mumfordProductLift_second, mumfordShearInv,
        mumfordProductLift_second, Category.id_comp]

/-- The first coordinate of the shear is the addition map. -/
lemma mumfordShear_left_fst :
    (mumfordShear A).left ≫ pullback.fst A.X.hom A.X.hom = mumfordAddition A :=
  pullback.lift_fst _ _ _

/-- The second coordinate of the shear is the second projection. -/
lemma mumfordShear_left_snd :
    (mumfordShear A).left ≫ pullback.snd A.X.hom A.X.hom = pullback.snd A.X.hom A.X.hom :=
  pullback.lift_snd _ _ _

/-- The shear `(x, y) ↦ (x + y, x)` of the self-product. -/
def mumfordShearFst : mumfordProduct A ⟶ mumfordProduct A :=
  mumfordProductLift A (mumfordFirst A * mumfordSecond A) (mumfordFirst A)

/-- The inverse shear `(u, v) ↦ (v, -v + u)` of the self-product. -/
def mumfordShearFstInv : mumfordProduct A ⟶ mumfordProduct A :=
  mumfordProductLift A (mumfordSecond A) ((mumfordSecond A)⁻¹ * mumfordFirst A)

/-- The shear `(x, y) ↦ (x + y, x)` as an automorphism of the self-product over the base. -/
def mumfordShearFstIso : mumfordProduct A ≅ mumfordProduct A where
  hom := mumfordShearFst A
  inv := mumfordShearFstInv A
  hom_inv_id := by
    apply mumfordProduct_hom_ext
    · rw [Category.assoc, mumfordShearFstInv, mumfordProductLift_first, mumfordShearFst,
        mumfordProductLift_second, Category.id_comp]
    · rw [Category.assoc, mumfordShearFstInv, mumfordProductLift_second, MonObj.comp_mul,
        GrpObj.comp_inv, mumfordShearFst, mumfordProductLift_first, mumfordProductLift_second,
        inv_mul_cancel_left, Category.id_comp]
  inv_hom_id := by
    apply mumfordProduct_hom_ext
    · rw [Category.assoc, mumfordShearFst, mumfordProductLift_first, MonObj.comp_mul,
        mumfordShearFstInv, mumfordProductLift_first, mumfordProductLift_second,
        mul_inv_cancel_left, Category.id_comp]
    · rw [Category.assoc, mumfordShearFst, mumfordProductLift_second, mumfordShearFstInv,
        mumfordProductLift_first, Category.id_comp]

/-- The first coordinate of the shear `(x, y) ↦ (x + y, x)` is the addition map. -/
lemma mumfordShearFst_left_fst :
    (mumfordShearFst A).left ≫ pullback.fst A.X.hom A.X.hom = mumfordAddition A :=
  pullback.lift_fst _ _ _

/-- The second coordinate of the shear `(x, y) ↦ (x + y, x)` is the first projection. -/
lemma mumfordShearFst_left_snd :
    (mumfordShearFst A).left ≫ pullback.snd A.X.hom A.X.hom = pullback.fst A.X.hom A.X.hom :=
  pullback.lift_snd _ _ _

/-- The scheme isomorphism from the self-product to the chosen categorical product in
`Over S` given by an automorphism `σ` of the self-product. -/
def mumfordProductIsoOf (σ : mumfordProduct A ≅ mumfordProduct A) :
    (mumfordProduct A).left ≅ (A.X ⨯ A.X).left :=
  (Over.forget S).mapIso σ ≪≫ (Over.prodLeftIsoPullback A.X A.X).symm

lemma mumfordProductIsoOf_hom_fst (σ : mumfordProduct A ≅ mumfordProduct A) :
    (mumfordProductIsoOf A σ).hom ≫ (prod.fst : A.X ⨯ A.X ⟶ A.X).left =
      σ.hom.left ≫ pullback.fst A.X.hom A.X.hom := by
  change σ.hom.left ≫ (Over.prodLeftIsoPullback A.X A.X).inv ≫
    (prod.fst : A.X ⨯ A.X ⟶ A.X).left = _
  rw [Over.prodLeftIsoPullback_inv_fst]

lemma mumfordProductIsoOf_hom_snd (σ : mumfordProduct A ≅ mumfordProduct A) :
    (mumfordProductIsoOf A σ).hom ≫ (prod.snd : A.X ⨯ A.X ⟶ A.X).left =
      σ.hom.left ≫ pullback.snd A.X.hom A.X.hom := by
  change σ.hom.left ≫ (Over.prodLeftIsoPullback A.X A.X).inv ≫
    (prod.snd : A.X ⨯ A.X ⟶ A.X).left = _
  rw [Over.prodLeftIsoPullback_inv_snd]

lemma mumfordProductIsoOf_hom_comp (σ : mumfordProduct A ≅ mumfordProduct A) :
    (mumfordProductIsoOf A σ).hom ≫ (A.X ⨯ A.X).hom = (mumfordProduct A).hom := by
  rw [← Over.w (prod.fst : A.X ⨯ A.X ⟶ A.X), ← Category.assoc,
    mumfordProductIsoOf_hom_fst, Category.assoc]
  exact Over.w σ.hom

/-- If an automorphism `σ` of the self-product has coordinates `f` and `g`, pulling the
external tensor product back along `mumfordProductIsoOf A σ` gives `f^* L ⊗ g^* M`. -/
def mumfordProductIsoOfPullbackIso (σ : mumfordProduct A ≅ mumfordProduct A)
    {f g : (mumfordProduct A).left ⟶ A.X.left}
    (hf : σ.hom.left ≫ pullback.fst A.X.hom A.X.hom = f)
    (hg : σ.hom.left ≫ pullback.snd A.X.hom A.X.hom = g) (L M : A.X.left.Modules) :
    (Scheme.Modules.pullback (mumfordProductIsoOf A σ).hom).obj
        (tensorObj
          ((Scheme.Modules.pullback (prod.fst : A.X ⨯ A.X ⟶ A.X).left).obj L)
          ((Scheme.Modules.pullback (prod.snd : A.X ⨯ A.X ⟶ A.X).left).obj M)) ≅
      tensorObj ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback g).obj M) :=
  Langlands.Scheme.Modules.pullbackTensorIso (mumfordProductIsoOf A σ).hom _ _ ≪≫
    (tensorFunctor (mumfordProduct A).left).mapIso
      ((((Scheme.Modules.pullbackComp _ _).app L ≪≫
          (Scheme.Modules.pullbackCongr ((mumfordProductIsoOf_hom_fst A σ).trans hf)).app L)).prod
        ((Scheme.Modules.pullbackComp _ _).app M ≪≫
          (Scheme.Modules.pullbackCongr ((mumfordProductIsoOf_hom_snd A σ).trans hg)).app M))

end Shear

section Euler

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- If an automorphism `σ` of the self-product has coordinates `f` and `g`, then in each
degree the cohomology of `f^* L ⊗ g^* M` is the Künneth sum of the cohomologies of `L`
and `M`. -/
lemma nonempty_mumfordProduct_kunnethIso_of (σ : mumfordProduct A ≅ mumfordProduct A)
    {f g : (mumfordProduct A).left ⟶ A.X.left}
    (hf : σ.hom.left ≫ pullback.fst A.X.hom A.X.hom = f)
    (hg : σ.hom.left ≫ pullback.snd A.X.hom A.X.hom = g) (L M : LineBundle A.X.left) (n : ℕ) :
    Nonempty ((relativeCohomology (mumfordProduct A).hom n).obj
        (tensorObj ((Scheme.Modules.pullback f).obj L.obj)
          ((Scheme.Modules.pullback g).obj M.obj)) ≅
      kunnethSum (fun a => (relativeCohomology A.X.hom a).obj L.obj)
        (fun b => (relativeCohomology A.X.hom b).obj M.obj) n) := by
  -- move the module along `σ`
  have e₁ := (relativeCohomology (mumfordProduct A).hom n).mapIso
    (mumfordProductIsoOfPullbackIso A σ hf hg L.obj M.obj).symm
  -- identify the cohomology with that on the categorical product
  have e₂ := relativeCohomologyPullbackIso (mumfordProductIsoOf A σ) (A.X ⨯ A.X).hom
    (tensorObj
      ((Scheme.Modules.pullback (prod.fst : A.X ⨯ A.X ⟶ A.X).left).obj L.obj)
      ((Scheme.Modules.pullback (prod.snd : A.X ⨯ A.X ⟶ A.X).left).obj M.obj)) n
  rw [mumfordProductIsoOf_hom_comp] at e₂
  obtain ⟨e₃⟩ := coherentFieldExternalTensorKunneth K A.X A.X L M n
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩

/-- In each degree, the cohomology of `m^* L ⊗ p₂^* M` on the self-product is the Künneth sum
of the cohomologies of `L` and `M`. -/
lemma nonempty_mumfordProduct_kunnethIso (L M : LineBundle A.X.left) (n : ℕ) :
    Nonempty ((relativeCohomology (mumfordProduct A).hom n).obj
        (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
          ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj)) ≅
      kunnethSum (fun a => (relativeCohomology A.X.hom a).obj L.obj)
        (fun b => (relativeCohomology A.X.hom b).obj M.obj) n) :=
  nonempty_mumfordProduct_kunnethIso_of A (mumfordShearIso A) (mumfordShear_left_fst A)
    (mumfordShear_left_snd A) L M n

/-- In each degree, the cohomology of `m^* L ⊗ p₁^* M` on the self-product is the Künneth sum
of the cohomologies of `L` and `M`. -/
lemma nonempty_mumfordProduct_kunnethIso_fst (L M : LineBundle A.X.left) (n : ℕ) :
    Nonempty ((relativeCohomology (mumfordProduct A).hom n).obj
        (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
          ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M.obj)) ≅
      kunnethSum (fun a => (relativeCohomology A.X.hom a).obj L.obj)
        (fun b => (relativeCohomology A.X.hom b).obj M.obj) n) :=
  nonempty_mumfordProduct_kunnethIso_of A (mumfordShearFstIso A) (mumfordShearFst_left_fst A)
    (mumfordShearFst_left_snd A) L M n

/-- On the self-product of an abelian scheme over a field, `m^* L ⊗ p₂^* M` has finite
cohomology when `L` and `M` do. -/
theorem hasFiniteCohomology_mumfordAddition_tensor_snd (L M : LineBundle A.X.left)
    (hL : HasFiniteCohomology A.X.hom L.obj) (hM : HasFiniteCohomology A.X.hom M.obj) :
    HasFiniteCohomology (mumfordProduct A).hom
      (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
        ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj)) :=
  hasFiniteCohomology_of_kunnethIso A.X.hom A.X.hom (mumfordProduct A).hom L.obj M.obj _ hL hM
    fun n => (nonempty_mumfordProduct_kunnethIso A L M n).some

/-- On the self-product of an abelian scheme over a field, the Euler characteristic of
`m^* L ⊗ p₂^* M` is `χ(L) χ(M)`, by the shear `(x, y) ↦ (x + y, y)` and Künneth. -/
theorem eulerCharacteristic_mumfordAddition_tensor_snd (L M : LineBundle A.X.left)
    (hL : HasFiniteCohomology A.X.hom L.obj) (hM : HasFiniteCohomology A.X.hom M.obj)
    (hQ : HasFiniteCohomology (mumfordProduct A).hom
      (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
        ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj))) :
    eulerCharacteristic (mumfordProduct A).hom
        (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
          ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj)) hQ =
      eulerCharacteristic A.X.hom L.obj hL * eulerCharacteristic A.X.hom M.obj hM :=
  eulerCharacteristic_eq_mul_of_kunnethIso A.X.hom A.X.hom (mumfordProduct A).hom L.obj M.obj _
    hL hM hQ fun n => (nonempty_mumfordProduct_kunnethIso A L M n).some

/-- On the self-product of an abelian scheme over a field, `m^* L ⊗ p₁^* M` has finite
cohomology when `L` and `M` do. -/
theorem hasFiniteCohomology_mumfordAddition_tensor_fst (L M : LineBundle A.X.left)
    (hL : HasFiniteCohomology A.X.hom L.obj) (hM : HasFiniteCohomology A.X.hom M.obj) :
    HasFiniteCohomology (mumfordProduct A).hom
      (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
        ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M.obj)) :=
  hasFiniteCohomology_of_kunnethIso A.X.hom A.X.hom (mumfordProduct A).hom L.obj M.obj _ hL hM
    fun n => (nonempty_mumfordProduct_kunnethIso_fst A L M n).some

/-- On the self-product of an abelian scheme over a field, the Euler characteristic of
`m^* L ⊗ p₁^* M` is `χ(L) χ(M)`, by the shear `(x, y) ↦ (x + y, x)` and Künneth. -/
theorem eulerCharacteristic_mumfordAddition_tensor_fst (L M : LineBundle A.X.left)
    (hL : HasFiniteCohomology A.X.hom L.obj) (hM : HasFiniteCohomology A.X.hom M.obj)
    (hQ : HasFiniteCohomology (mumfordProduct A).hom
      (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
        ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M.obj))) :
    eulerCharacteristic (mumfordProduct A).hom
        (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
          ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M.obj)) hQ =
      eulerCharacteristic A.X.hom L.obj hL * eulerCharacteristic A.X.hom M.obj hM :=
  eulerCharacteristic_eq_mul_of_kunnethIso A.X.hom A.X.hom (mumfordProduct A).hom L.obj M.obj _
    hL hM hQ fun n => (nonempty_mumfordProduct_kunnethIso_fst A L M n).some

end Euler

end Langlands.AbelianScheme
