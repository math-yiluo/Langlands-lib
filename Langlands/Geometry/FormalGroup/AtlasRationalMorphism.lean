import Langlands.Geometry.FormalGroup.AtlasHomModule
import Langlands.Geometry.FormalGroup.AtlasComparison

/-! # Rational formal maps and quasi-isogenies on a common atlas cover -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory TensorProduct

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable (F : Type w) [Field F] [Algebra O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Scalar extension of the actual integral formal maps on a common cover. -/
abbrev RationalHom (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ)
    (h : X.opens = Y.opens) := F ⊗[O] Hom X Y h

namespace RationalHom

variable {F}
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {Z : BasicAtlas O R υ} {W : BasicAtlas O R ω}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens} {l : Z.opens = W.opens}

/-- Exchange the tensor factors to recover Hom tensor F. -/
def sourceTensorEquiv : RationalHom F X Y h ≃ₗ[O] (Hom X Y h) ⊗[O] F :=
  TensorProduct.comm O F (Hom X Y h)

/-- The canonical map from integral to rational formal atlas Hom. -/
def ofHom : Hom X Y h →ₗ[O] RationalHom F X Y h :=
  TensorProduct.mk O F (Hom X Y h) 1

@[simp]
theorem ofHom_apply (f : Hom X Y h) : (ofHom (F := F)) f = 1 ⊗ₜ[O] f := rfl

/-- Tensor extension of integral composition and multiplication of scalars. -/
def compLinearO : RationalHom F Y Z k →ₗ[O]
    RationalHom F X Y h →ₗ[O] RationalHom F X Z (h.trans k) :=
  TensorProduct.map₂ (LinearMap.mul O F) Hom.compLinear

/-- Composition of rational formal atlas maps, right map first. -/
def comp (g : RationalHom F Y Z k) (f : RationalHom F X Y h) :
    RationalHom F X Z (h.trans k) := compLinearO g f

@[simp]
theorem comp_tmul (a b : F) (g : Hom Y Z k) (f : Hom X Y h) :
    comp (a ⊗ₜ[O] g) (b ⊗ₜ[O] f) = (a * b) ⊗ₜ[O] g.comp f := rfl

@[simp]
theorem comp_add (g : RationalHom F Y Z k) (f₁ f₂ : RationalHom F X Y h) :
    comp g (f₁ + f₂) = comp g f₁ + comp g f₂ := (compLinearO g).map_add f₁ f₂

@[simp]
theorem add_comp (g₁ g₂ : RationalHom F Y Z k) (f : RationalHom F X Y h) :
    comp (g₁ + g₂) f = comp g₁ f + comp g₂ f := compLinearO.map_add₂ g₁ g₂ f

@[simp]
theorem comp_zero (g : RationalHom F Y Z k) :
    comp g (0 : RationalHom F X Y h) = 0 := (compLinearO g).map_zero

@[simp]
theorem zero_comp (f : RationalHom F X Y h) :
    comp (0 : RationalHom F Y Z k) f = 0 := compLinearO.map_zero₂ f

/-- The rational identity comes from the actual integral identity. -/
def id (X : BasicAtlas O R σ) : RationalHom F X X rfl := ofHom (Hom.id X)

@[simp]
theorem comp_id (f : RationalHom F X Y h) : comp f (id X) = f := by
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp [id, ofHom]
  | add f g hf hg => simp only [add_comp, hf, hg]

@[simp]
theorem id_comp (f : RationalHom F X Y h) : comp (id Y) f = f := by
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp [id, ofHom]
  | add f g hf hg => simp only [comp_add, hf, hg]

theorem comp_assoc (q : RationalHom F Z W l) (g : RationalHom F Y Z k)
    (f : RationalHom F X Y h) : comp (comp q g) f = comp q (comp g f) := by
  induction q using TensorProduct.inductionOn with
  | add q₁ q₂ hq₁ hq₂ => simp only [add_comp, hq₁, hq₂]
  | tmul a q =>
    induction g using TensorProduct.inductionOn with
    | add g₁ g₂ hg₁ hg₂ => simp only [comp_add, add_comp, hg₁, hg₂]
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | add f₁ f₂ hf₁ hf₂ => simp only [comp_add, hf₁, hf₂]
      | tmul c f => simp only [comp_tmul, mul_assoc, Hom.comp_assoc]

@[simp]
theorem comp_smul (g : RationalHom F Y Z k) (a : F) (f : RationalHom F X Y h) :
    comp g (a • f) = a • comp g f := by
  induction g using TensorProduct.inductionOn with
  | add g₁ g₂ hg₁ hg₂ => simp only [add_comp, hg₁, hg₂, smul_add]
  | tmul b g =>
    induction f using TensorProduct.inductionOn with
    | add f₁ f₂ hf₁ hf₂ => simp only [smul_add, comp_add, hf₁, hf₂]
    | tmul c f => simp only [smul_tmul', smul_eq_mul, comp_tmul, mul_left_comm]

@[simp]
theorem smul_comp (a : F) (g : RationalHom F Y Z k) (f : RationalHom F X Y h) :
    comp (a • g) f = a • comp g f := by
  induction g using TensorProduct.inductionOn with
  | add g₁ g₂ hg₁ hg₂ => simp only [smul_add, add_comp, hg₁, hg₂]
  | tmul b g =>
    induction f using TensorProduct.inductionOn with
    | add f₁ f₂ hf₁ hf₂ => simp only [comp_add, hf₁, hf₂, smul_add]
    | tmul c f => simp only [smul_tmul', smul_eq_mul, comp_tmul, mul_assoc]

/-- Rational formal composition is bilinear over F. -/
def compLinear : RationalHom F Y Z k →ₗ[F]
    RationalHom F X Y h →ₗ[F] RationalHom F X Z (h.trans k) where
  toFun g := {
    toFun := comp g
    map_add' := comp_add g
    map_smul' := comp_smul g }
  map_add' g₁ g₂ := by apply LinearMap.ext; intro f; exact add_comp g₁ g₂ f
  map_smul' a g := by apply LinearMap.ext; intro f; exact smul_comp a g f

@[simp]
theorem ofHom_id : ofHom (F := F) (Hom.id X) = id X := rfl

@[simp]
theorem ofHom_comp (g : Hom Y Z k) (f : Hom X Y h) :
    ofHom (F := F) (g.comp f) = comp (ofHom g) (ofHom f) := by
  simp only [ofHom_apply, comp_tmul, one_mul]

/-- Actual rational formal evaluation on a test chart. -/
def onChart (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    RationalHom F X Y h →ₗ[F] ModuleLaw.RationalHom F
      ((X.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb))
      ((Y.chart b).map (coefficientLift (O := O) b.val A hb)) :=
  (Hom.chartLinear (X := X) (h := h) A b hb).baseChange F

@[simp]
theorem onChart_tmul (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) (a : F) (f : Hom X Y h) :
    onChart (X := X) (h := h) A b hb (a ⊗ₜ[O] f) = a ⊗ₜ[O] f.hom A b hb :=
  LinearMap.baseChange_tmul _ _ _

@[simp]
theorem onChart_ofHom (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) (f : Hom X Y h) :
    onChart (X := X) (h := h) A b hb (ofHom (F := F) f) = ModuleLaw.RationalHom.ofHom (f.hom A b hb) :=
  onChart_tmul A b hb 1 f

@[simp]
theorem onChart_id (A : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    onChart (X := X) (h := rfl) A b hb (id (F := F) X) = ModuleLaw.RationalHom.id _ :=
  onChart_ofHom A b hb (Hom.id X)

@[simp]
theorem onChart_comp (g : RationalHom F Y Z k) (f : RationalHom F X Y h)
    (A : CommAlgCat.{v} R) (b : Z.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    onChart (X := X) (h := h.trans k) A b hb (comp g f) = ModuleLaw.RationalHom.comp
      (onChart (X := Y) (h := k) A b hb g)
      (onChart (X := X) (h := h) A (sourceChart k b) hb f) := by
  induction g using TensorProduct.inductionOn with
  | add g₁ g₂ hg₁ hg₂ =>
    simp only [add_comp, _root_.map_add, ModuleLaw.RationalHom.add_comp, hg₁, hg₂]
  | tmul a g =>
    induction f using TensorProduct.inductionOn with
    | add f₁ f₂ hf₁ hf₂ =>
      simp only [comp_add, _root_.map_add, ModuleLaw.RationalHom.comp_add, hf₁, hf₂]
    | tmul b f => rfl

/-- The formal transition square persists in the actual chart tensor Hom. -/
theorem onChart_transition (f : RationalHom F X Y h) (A : CommAlgCat.{v} R)
    (b c : Y.opens) (hb : IsUnit (algebraMap R A b.val))
    (hc : IsUnit (algebraMap R A c.val)) :
    ModuleLaw.RationalHom.comp
      (ModuleLaw.RationalHom.ofHom (Y.transition A b c hb hc).hom) (onChart (X := X) (h := h) A b hb f) =
    ModuleLaw.RationalHom.comp (onChart (X := X) (h := h) A c hc f)
      (ModuleLaw.RationalHom.ofHom
        (X.transition A (sourceChart h b) (sourceChart h c) hb hc).hom) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    simp only [_root_.map_add, ModuleLaw.RationalHom.comp_add,
      ModuleLaw.RationalHom.add_comp, hf, hg]
  | tmul a f =>
    change (1 * a) ⊗ₜ[O] ((Y.transition A b c hb hc).hom.comp (f.hom A b hb)) =
      (a * 1) ⊗ₜ[O] ((f.hom A c hc).comp
        (X.transition A (sourceChart h b) (sourceChart h c) hb hc).hom)
    rw [one_mul, mul_one, f.transition]

/-- Coefficient naturality expressed using actual identity-coordinate comparisons. -/
theorem onChart_natural (f : RationalHom F X Y h) {A B : CommAlgCat.{v} R}
    (φ : A ⟶ B) (b : Y.opens) (ha : IsUnit (algebraMap R A b.val))
    (hb : IsUnit (algebraMap R B b.val)) :
    ModuleLaw.RationalHom.comp (onChart (X := X) (h := h) B b hb f)
      (ModuleLaw.RationalHom.ofHom
        (coefficientTriangleIso (X.chart (sourceChart h b)) φ ha hb).hom) =
    ModuleLaw.RationalHom.comp
      (ModuleLaw.RationalHom.ofHom (coefficientTriangleIso (Y.chart b) φ ha hb).hom)
      (ModuleLaw.RationalHom.map (φ.hom.restrictScalars O) (onChart (X := X) (h := h) A b ha f)) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    simp only [_root_.map_add, ModuleLaw.RationalHom.comp_add,
      ModuleLaw.RationalHom.add_comp, hf, hg]
  | tmul a f =>
    change (a * 1) ⊗ₜ[O] ((f.hom B b hb).comp
        (coefficientTriangleIso (X.chart (sourceChart h b)) φ ha hb).hom) =
      (1 * a) ⊗ₜ[O] ((coefficientTriangleIso (Y.chart b) φ ha hb).hom.comp
        ((f.hom A b ha).map (φ.hom.restrictScalars O)))
    rw [mul_one, one_mul]
    apply congrArg (fun q => a ⊗ₜ[O] q)
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (f.hom B b hb).toHom.toCoordinateMap.comp CoordinateMap.id =
      CoordinateMap.id.comp ((f.hom A b ha).toHom.toCoordinateMap.map φ.hom.toRingHom)
    rw [CoordinateMap.comp_id, CoordinateMap.id_comp, f.natural]

/-- Rational endomorphisms retain the actual formal composition ring. -/
instance : Ring (RationalHom F X X rfl) where
  mul := comp
  one := id X
  natCast n := (n : F) ⊗ₜ[O] Hom.id X
  intCast n := (n : F) ⊗ₜ[O] Hom.id X
  natCast_zero := by simp only [Nat.cast_zero, zero_tmul]
  natCast_succ n := by simp only [Nat.cast_succ, add_tmul]; rfl
  intCast_ofNat n := by simp only [Int.cast_natCast]; rfl
  intCast_negSucc n := by
    change (Int.negSucc n : F) ⊗ₜ[O] Hom.id X = -((n + 1 : ℕ) : F) ⊗ₜ[O] Hom.id X
    rw [Int.cast_negSucc, neg_tmul]
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  left_distrib := comp_add
  right_distrib := add_comp
  zero_mul := zero_comp
  mul_zero := comp_zero

end RationalHom

/-- A same-cover quasi-isogeny has inverse maps in the actual tensor Hom. -/
structure QuasiIsogeny [IsDomain O] [IsFractionRing O F]
    (X : BasicAtlas O R σ) (Y : BasicAtlas O R τ) (h : X.opens = Y.opens) where
  hom : RationalHom F X Y h
  inv : RationalHom F Y X h.symm
  inv_hom : RationalHom.comp inv hom = RationalHom.id X
  hom_inv : RationalHom.comp hom inv = RationalHom.id Y

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]
variable {F}
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- Identity quasi-isogeny. -/
def refl (X : BasicAtlas O R σ) : QuasiIsogeny F X X rfl where
  hom := RationalHom.id X
  inv := RationalHom.id X
  inv_hom := RationalHom.id_comp _
  hom_inv := RationalHom.id_comp _

/-- Exchange the two actual rational maps. -/
def symm (f : QuasiIsogeny F X Y h) : QuasiIsogeny F Y X h.symm where
  hom := f.inv
  inv := f.hom
  inv_hom := f.hom_inv
  hom_inv := f.inv_hom

/-- Compose quasi-isogenies using the formal rational composition. -/
def trans (f : QuasiIsogeny F X Y h) (g : QuasiIsogeny F Y Z k) :
    QuasiIsogeny F X Z (h.trans k) where
  hom := RationalHom.comp g.hom f.hom
  inv := RationalHom.comp f.inv g.inv
  inv_hom := by
    rw [RationalHom.comp_assoc, ← RationalHom.comp_assoc g.inv, g.inv_hom,
      RationalHom.id_comp, f.inv_hom]
  hom_inv := by
    rw [RationalHom.comp_assoc, ← RationalHom.comp_assoc f.hom, f.hom_inv,
      RationalHom.id_comp, g.hom_inv]

/-- Every actual integral atlas isomorphism gives a quasi-isogeny. -/
def ofIso (f : Iso X Y h) : QuasiIsogeny F X Y h where
  hom := RationalHom.ofHom f.hom
  inv := RationalHom.ofHom f.inv
  inv_hom := by
    rw [← RationalHom.ofHom_comp, f.inv_hom, RationalHom.ofHom_id]
  hom_inv := by
    rw [← RationalHom.ofHom_comp, f.hom_inv, RationalHom.ofHom_id]

/-- The inverse is forced by one inverse equation. -/
theorem inv_unique (f : QuasiIsogeny F X Y h) (g : RationalHom F Y X h.symm)
    (hg : RationalHom.comp g f.hom = RationalHom.id X) : g = f.inv := by
  calc
    g = RationalHom.comp g (RationalHom.id Y) := (RationalHom.comp_id g).symm
    _ = RationalHom.comp g (RationalHom.comp f.hom f.inv) := by rw [f.hom_inv]
    _ = RationalHom.comp (RationalHom.comp g f.hom) f.inv :=
      (RationalHom.comp_assoc _ _ _).symm
    _ = f.inv := by rw [hg, RationalHom.id_comp]

@[ext]
theorem ext_hom {f g : QuasiIsogeny F X Y h} (he : f.hom = g.hom) : f = g := by
  have hi : f.inv = g.inv := g.inv_unique f.inv (by rw [← he]; exact f.inv_hom)
  cases f
  cases g
  cases he
  cases hi
  rfl

/-- Evaluate a quasi-isogeny as an actual coordinate quasi-isogeny on a test chart. -/
def onChart (f : QuasiIsogeny F X Y h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    ModuleLaw.QuasiIsogeny F
      ((X.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb))
      ((Y.chart b).map (coefficientLift (O := O) b.val A hb)) where
  hom := RationalHom.onChart (X := X) (h := h) A b hb f.hom
  inv := RationalHom.onChart (X := Y) (h := h.symm) A (sourceChart h b) hb f.inv
  inv_hom := by
    have he := congrArg (RationalHom.onChart (X := X) (h := rfl) A (sourceChart h b) hb) f.inv_hom
    rw [RationalHom.onChart_comp (F := F), RationalHom.onChart_id (F := F)] at he
    exact he
  hom_inv := by
    have he := congrArg (RationalHom.onChart (X := Y) (h := rfl) A b hb) f.hom_inv
    rw [RationalHom.onChart_comp (F := F), RationalHom.onChart_id (F := F)] at he
    exact he

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
