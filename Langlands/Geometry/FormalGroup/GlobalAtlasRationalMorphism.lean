import Langlands.Geometry.FormalGroup.GlobalAtlasMorphism
import Langlands.Geometry.FormalGroup.AtlasRationalMorphism

/-! # Global rational formal maps induce atlas maps -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory TensorProduct

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type w} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

namespace RationalHom

/-- Global rational endomorphisms form a ring under actual formal composition. -/
instance : Ring (RationalHom F M M) where
  mul := comp
  one := id M
  natCast n := (n : F) ⊗ₜ[O] Hom.id M
  intCast n := (n : F) ⊗ₜ[O] Hom.id M
  natCast_zero := by simp only [Nat.cast_zero, zero_tmul]
  natCast_succ n := by simp only [Nat.cast_succ, add_tmul]; rfl
  intCast_ofNat n := by simp only [Int.cast_natCast]; rfl
  intCast_negSucc n := by
    change (Int.negSucc n : F) ⊗ₜ[O] Hom.id M = -((n + 1 : ℕ) : F) ⊗ₜ[O] Hom.id M
    rw [Int.cast_negSucc, neg_tmul]
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  left_distrib := comp_add
  right_distrib := add_comp
  zero_mul := zero_comp
  mul_zero := comp_zero

end RationalHom

namespace BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Atlases of global laws on a supplied cover have the same cover. -/
theorem ofGlobalCover_opens_eq (M : ModuleLaw O R σ) (N : ModuleLaw O R τ)
    (s : Set R) (hs : Ideal.span s = ⊤) :
    (ofGlobalCover M s hs).opens = (ofGlobalCover N s hs).opens := rfl

/-- Coefficient-chart conjugation preserves addition of global formal maps. -/
theorem globalChartHom_add (f g : ModuleLaw.Hom M N) (a : R)
    (A : CommAlgCat.{v} R) (ha : IsUnit (algebraMap R A a)) :
    globalChartHom (f + g) a A ha = globalChartHom f a A ha + globalChartHom g a A ha := by
  have he : (f + g).map (IsScalarTower.toAlgHom O R A) =
      f.map (IsScalarTower.toAlgHom O R A) + g.map (IsScalarTower.toAlgHom O R A) :=
    (ModuleLaw.Hom.mapLinear (IsScalarTower.toAlgHom O R A)).map_add f g
  unfold globalChartHom
  rw [he, ModuleLaw.Hom.add_comp, ModuleLaw.Hom.comp_add]

/-- Coefficient-chart conjugation preserves O-scalars on global formal maps. -/
theorem globalChartHom_smul (c : O) (f : ModuleLaw.Hom M N) (a : R)
    (A : CommAlgCat.{v} R) (ha : IsUnit (algebraMap R A a)) :
    globalChartHom (c • f) a A ha = c • globalChartHom f a A ha := by
  have he : (c • f).map (IsScalarTower.toAlgHom O R A) =
      c • f.map (IsScalarTower.toAlgHom O R A) :=
    (ModuleLaw.Hom.mapLinear (IsScalarTower.toAlgHom O R A)).map_smul c f
  unfold globalChartHom
  rw [he, ModuleLaw.Hom.smul_comp, ModuleLaw.Hom.comp_smul]

/-- Restriction of global integral maps to a supplied cover is O-linear. -/
def ofGlobalHomLinear (s : Set R) (hs : Ideal.span s = ⊤) :
    ModuleLaw.Hom M N →ₗ[O] Hom (ofGlobalCover M s hs) (ofGlobalCover N s hs)
      (ofGlobalCover_opens_eq M N s hs) where
  toFun f := ofGlobalHom f s hs
  map_add' f g := by
    apply Hom.ext (X := ofGlobalCover M s hs) (Y := ofGlobalCover N s hs)
      (h := ofGlobalCover_opens_eq M N s hs)
    intro A b hb
    exact globalChartHom_add f g b.val A hb
  map_smul' c f := by
    apply Hom.ext (X := ofGlobalCover M s hs) (Y := ofGlobalCover N s hs)
      (h := ofGlobalCover_opens_eq M N s hs)
    intro A b hb
    exact globalChartHom_smul c f b.val A hb

@[simp]
theorem ofGlobalHomLinear_apply (s : Set R) (hs : Ideal.span s = ⊤)
    (f : ModuleLaw.Hom M N) :
    ofGlobalHomLinear (M := M) (N := N) s hs f = ofGlobalHom f s hs := rfl

/-- Restrict both actual integral inverse maps to the same supplied cover. -/
def ofGlobalIso (f : ModuleLaw.Iso M N) (s : Set R) (hs : Ideal.span s = ⊤) :
    Iso (ofGlobalCover M s hs) (ofGlobalCover N s hs)
      (ofGlobalCover_opens_eq M N s hs) where
  hom := ofGlobalHom f.hom s hs
  inv := ofGlobalHom f.inv s hs
  inv_hom := by rw [← ofGlobalHom_comp, f.inv_hom, ofGlobalHom_id]
  hom_inv := by rw [← ofGlobalHom_comp, f.hom_inv, ofGlobalHom_id]

/-- Scalar extension of the actual integral global-to-atlas map. -/
def ofGlobalRationalHom (s : Set R) (hs : Ideal.span s = ⊤) :
    ModuleLaw.RationalHom F M N →ₗ[F]
      RationalHom F (ofGlobalCover M s hs) (ofGlobalCover N s hs)
      (ofGlobalCover_opens_eq M N s hs) :=
  (ofGlobalHomLinear (M := M) (N := N) s hs).baseChange F

@[simp]
theorem ofGlobalRationalHom_tmul (s : Set R) (hs : Ideal.span s = ⊤)
    (a : F) (f : ModuleLaw.Hom M N) :
    ofGlobalRationalHom s hs (a ⊗ₜ[O] f) =
      (a ⊗ₜ[O] ofGlobalHom f s hs :
        RationalHom F (ofGlobalCover M s hs) (ofGlobalCover N s hs)
          (ofGlobalCover_opens_eq M N s hs)) :=
  LinearMap.baseChange_tmul _ _ _

@[simp]
theorem ofGlobalRationalHom_ofHom (s : Set R) (hs : Ideal.span s = ⊤)
    (f : ModuleLaw.Hom M N) :
    ofGlobalRationalHom s hs (ModuleLaw.RationalHom.ofHom (F := F) f) =
      RationalHom.ofHom (F := F) (ofGlobalHom f s hs) :=
  ofGlobalRationalHom_tmul s hs 1 f

@[simp]
theorem ofGlobalRationalHom_id (M : ModuleLaw O R σ) (s : Set R)
    (hs : Ideal.span s = ⊤) :
    ofGlobalRationalHom s hs (ModuleLaw.RationalHom.id (F := F) M) =
      RationalHom.id (ofGlobalCover M s hs) := by
  rw [ModuleLaw.RationalHom.id, ofGlobalRationalHom_ofHom, ofGlobalHom_id]
  rfl

/-- Restriction of global rational maps preserves actual formal composition. -/
@[simp]
theorem ofGlobalRationalHom_comp (g : ModuleLaw.RationalHom F N P)
    (f : ModuleLaw.RationalHom F M N) (s : Set R) (hs : Ideal.span s = ⊤) :
    ofGlobalRationalHom s hs (ModuleLaw.RationalHom.comp g f) =
      RationalHom.comp (ofGlobalRationalHom s hs g) (ofGlobalRationalHom s hs f) := by
  induction g using TensorProduct.inductionOn with
  | add g₁ g₂ hg₁ hg₂ =>
    simp only [ModuleLaw.RationalHom.add_comp, _root_.map_add,
      RationalHom.add_comp, hg₁, hg₂]
  | tmul a g =>
    induction f using TensorProduct.inductionOn with
    | add f₁ f₂ hf₁ hf₂ =>
      simp only [ModuleLaw.RationalHom.comp_add, _root_.map_add,
        RationalHom.comp_add, hf₁, hf₂]
    | tmul b f =>
      simp only [ModuleLaw.RationalHom.comp_tmul, ofGlobalRationalHom_tmul,
        RationalHom.comp_tmul, ofGlobalHom_comp]

/-- The rational endomorphism restriction is a homomorphism of composition rings. -/
def ofGlobalRationalEnd (M : ModuleLaw O R σ) (s : Set R) (hs : Ideal.span s = ⊤) :
    ModuleLaw.RationalHom F M M →+*
      RationalHom F (ofGlobalCover M s hs) (ofGlobalCover M s hs) rfl where
  toFun := ofGlobalRationalHom s hs
  map_zero' := (ofGlobalRationalHom s hs).map_zero
  map_add' := (ofGlobalRationalHom s hs).map_add
  map_one' := ofGlobalRationalHom_id M s hs
  map_mul' := fun g f => ofGlobalRationalHom_comp g f s hs

/-- Chart evaluation is conjugation of the actual coefficient-extended rational map. -/
theorem onChart_ofGlobalRationalHom (f : ModuleLaw.RationalHom F M N)
    (s : Set R) (hs : Ideal.span s = ⊤) (A : CommAlgCat.{v} R) (b : s)
    (hb : IsUnit (algebraMap R A b.val)) :
    RationalHom.onChart (X := ofGlobalCover M s hs) (Y := ofGlobalCover N s hs)
      (h := ofGlobalCover_opens_eq M N s hs) A b hb
      (ofGlobalRationalHom s hs f) =
        ModuleLaw.RationalHom.comp
          (ModuleLaw.RationalHom.ofHom (globalChartIso N b.val A hb).inv)
          (ModuleLaw.RationalHom.comp
            (ModuleLaw.RationalHom.map (IsScalarTower.toAlgHom O R A) f)
            (ModuleLaw.RationalHom.ofHom (globalChartIso M b.val A hb).hom)) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    simp only [_root_.map_add]
    exact (congrArg₂ (fun x y => x + y) hf hg).trans
      ((congrArg
        (fun z => ModuleLaw.RationalHom.comp
          (ModuleLaw.RationalHom.ofHom (globalChartIso N b.val A hb).inv) z)
        (ModuleLaw.RationalHom.add_comp _ _ _)).trans
          (ModuleLaw.RationalHom.comp_add _ _ _)).symm
  | tmul a f =>
    change a ⊗ₜ[O] globalChartHom f b.val A hb =
      ModuleLaw.RationalHom.comp
        (1 ⊗ₜ[O] (globalChartIso N b.val A hb).inv)
        (ModuleLaw.RationalHom.comp
          (a ⊗ₜ[O] f.map (IsScalarTower.toAlgHom O R A))
          (1 ⊗ₜ[O] (globalChartIso M b.val A hb).hom))
    change a ⊗ₜ[O] globalChartHom f b.val A hb =
      (1 * (a * 1)) ⊗ₜ[O] globalChartHom f b.val A hb
    exact congrArg (fun z : F => z ⊗ₜ[O] globalChartHom f b.val A hb)
      (by rw [mul_one, one_mul])

section QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- Global quasi-isogenies induce actual quasi-isogenies on a supplied cover. -/
def ofGlobalQuasiIsogeny (f : ModuleLaw.QuasiIsogeny F M N)
    (s : Set R) (hs : Ideal.span s = ⊤) :
    QuasiIsogeny F (ofGlobalCover M s hs) (ofGlobalCover N s hs)
      (ofGlobalCover_opens_eq M N s hs) where
  hom := ofGlobalRationalHom s hs f.hom
  inv := ofGlobalRationalHom s hs f.inv
  inv_hom := by rw [← ofGlobalRationalHom_comp, f.inv_hom, ofGlobalRationalHom_id]
  hom_inv := by rw [← ofGlobalRationalHom_comp, f.hom_inv, ofGlobalRationalHom_id]

@[simp]
theorem ofGlobalQuasiIsogeny_hom (f : ModuleLaw.QuasiIsogeny F M N)
    (s : Set R) (hs : Ideal.span s = ⊤) :
    (ofGlobalQuasiIsogeny f s hs).hom = ofGlobalRationalHom s hs f.hom := rfl

@[simp]
theorem ofGlobalQuasiIsogeny_inv (f : ModuleLaw.QuasiIsogeny F M N)
    (s : Set R) (hs : Ideal.span s = ⊤) :
    (ofGlobalQuasiIsogeny f s hs).inv = ofGlobalRationalHom s hs f.inv := rfl

@[simp]
theorem ofGlobalQuasiIsogeny_refl (M : ModuleLaw O R σ) (s : Set R)
    (hs : Ideal.span s = ⊤) :
    ofGlobalQuasiIsogeny (ModuleLaw.QuasiIsogeny.refl (F := F) M) s hs =
      QuasiIsogeny.refl (ofGlobalCover M s hs) := by
  apply QuasiIsogeny.ext_hom
  exact ofGlobalRationalHom_id M s hs

@[simp]
theorem ofGlobalQuasiIsogeny_symm (f : ModuleLaw.QuasiIsogeny F M N)
    (s : Set R) (hs : Ideal.span s = ⊤) :
    ofGlobalQuasiIsogeny f.symm s hs = (ofGlobalQuasiIsogeny f s hs).symm := by
  apply QuasiIsogeny.ext_hom
  rfl

@[simp]
theorem ofGlobalQuasiIsogeny_trans (f : ModuleLaw.QuasiIsogeny F M N)
    (g : ModuleLaw.QuasiIsogeny F N P) (s : Set R) (hs : Ideal.span s = ⊤) :
    ofGlobalQuasiIsogeny (f.trans g) s hs =
      (ofGlobalQuasiIsogeny f s hs).trans (ofGlobalQuasiIsogeny g s hs) := by
  apply QuasiIsogeny.ext_hom
  exact ofGlobalRationalHom_comp g.hom f.hom s hs

@[simp]
theorem ofGlobalQuasiIsogeny_ofIso (f : ModuleLaw.Iso M N) (s : Set R)
    (hs : Ideal.span s = ⊤) :
    ofGlobalQuasiIsogeny (ModuleLaw.QuasiIsogeny.ofIso (F := F) f) s hs =
      QuasiIsogeny.ofIso (ofGlobalIso f s hs) := by
  apply QuasiIsogeny.ext_hom
  exact ofGlobalRationalHom_ofHom s hs f.hom

/-- The chart quasi-isogeny is the coefficient extension through actual chart isomorphisms. -/
theorem onChart_ofGlobalQuasiIsogeny (f : ModuleLaw.QuasiIsogeny F M N)
    (s : Set R) (hs : Ideal.span s = ⊤) (A : CommAlgCat.{v} R) (b : s)
    (hb : IsUnit (algebraMap R A b.val)) :
    (ofGlobalQuasiIsogeny f s hs).onChart A b hb =
      (ModuleLaw.QuasiIsogeny.ofIso (globalChartIso M b.val A hb)).trans
        ((f.map (IsScalarTower.toAlgHom O R A)).trans
          (ModuleLaw.QuasiIsogeny.ofIso (globalChartIso N b.val A hb).symm)) := by
  apply ModuleLaw.QuasiIsogeny.ext_hom
  exact (onChart_ofGlobalRationalHom f.hom s hs A b hb).trans
    (ModuleLaw.RationalHom.comp_assoc _ _ _).symm

end QuasiIsogeny

end BasicAtlas

end Langlands.FormalGroup.ModuleLaw
