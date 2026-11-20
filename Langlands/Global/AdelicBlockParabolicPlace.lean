import Langlands.Global.AdelicParabolicInduction
import Langlands.Global.RankinSelberg.ArchimedeanPlaces

/-! # Local block parabolics inside the adelic block parabolic -/

noncomputable section

universe uF uV

namespace Langlands.Global

open NumberField Langlands.GeneralLinear RankinSelbergGlobal
open scoped Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable (F : Type uF) [Field F] [NumberField F]

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

namespace AdelicGL

/-- Insert a real general linear matrix at one place in the actual full adelic group. -/
def realPlaceInclusion (n : ℕ) (v : RP) : Langlands.GeneralLinear n ℝ →* AdelicGL F n :=
  (ofInfinite F n).toMonoidHom.comp
    ((archimedeanGLCoordinates F n).symm.toMonoidHom.comp (realPlaceGL F n v))

/-- Insert a complex general linear matrix at one place in the actual full adelic group. -/
def complexPlaceInclusion (n : ℕ) (v : CP) : Langlands.GeneralLinear n ℂ →* AdelicGL F n :=
  (ofInfinite F n).toMonoidHom.comp
    ((archimedeanGLCoordinates F n).symm.toMonoidHom.comp (complexPlaceGL F n v))

end AdelicGL

namespace AdelicBlockParabolic

variable {n : ℕ} (B : BlockShape n)

private theorem blockIndex_ne {i j : Fin B.length} (h : i ≠ j)
    (a : Fin (B.size i)) (b : Fin (B.size j)) : B.index i a ≠ B.index j b := by
  intro he
  exact h (congrArg Sigma.fst (B.indexEquiv.injective he))

omit [NumberField F] in
private theorem realPlaceGL_lowerBlock (v : RP) (p : B.parabolic ℝ)
    (i j : Fin B.length) (a : Fin (B.size i)) (b : Fin (B.size j)) (hji : j < i) :
    realPlaceGL F n v p.val (B.index i a) (B.index j b) = 0 := by
  have hij := blockIndex_ne B (ne_of_gt hji) a b
  refine Prod.ext (funext fun w => ?_) (funext fun _ => ?_)
  · change ((Pi.mulSingle v p.val : RP → Langlands.GeneralLinear n ℝ) w).val
      (B.index i a) (B.index j b) = 0
    by_cases hw : w = v
    · subst w
      rw [Pi.mulSingle_eq_same]
      exact (B.mem_parabolic_iff ℝ p.val).mp p.property i j a b hji
    · simp only [Pi.mulSingle_eq_of_ne hw, Units.val_one, Matrix.one_apply, ite_eq_right hij]
  · change (1 : Matrix (Fin n) (Fin n) ℂ) (B.index i a) (B.index j b) = 0
    rw [Matrix.one_apply, ite_eq_right hij]

omit [NumberField F] in
private theorem complexPlaceGL_lowerBlock (v : CP) (p : B.parabolic ℂ)
    (i j : Fin B.length) (a : Fin (B.size i)) (b : Fin (B.size j)) (hji : j < i) :
    complexPlaceGL F n v p.val (B.index i a) (B.index j b) = 0 := by
  have hij := blockIndex_ne B (ne_of_gt hji) a b
  refine Prod.ext (funext fun _ => ?_) (funext fun w => ?_)
  · change (1 : Matrix (Fin n) (Fin n) ℝ) (B.index i a) (B.index j b) = 0
    rw [Matrix.one_apply, ite_eq_right hij]
  · change ((Pi.mulSingle v p.val : CP → Langlands.GeneralLinear n ℂ) w).val
      (B.index i a) (B.index j b) = 0
    by_cases hw : w = v
    · subst w
      rw [Pi.mulSingle_eq_same]
      exact (B.mem_parabolic_iff ℂ p.val).mp p.property i j a b hji
    · simp only [Pi.mulSingle_eq_of_ne hw, Units.val_one, Matrix.one_apply, ite_eq_right hij]

/-- The actual real-place block parabolic embeds into the global one of the same shape. -/
def realPlaceInclusion (v : RP) : B.parabolic ℝ →* Full F B where
  toFun p := ⟨AdelicGL.realPlaceInclusion F n v p.val, by
    apply (B.mem_parabolic_iff (Adeles F) _).mpr
    intro i j a b hji
    change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (realPlaceGL F n v p.val (B.index i a) (B.index j b)),
      (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) (B.index i a) (B.index j b)) = 0
    rw [realPlaceGL_lowerBlock F B v p i j a b hji, map_zero, Matrix.one_apply,
      ite_eq_right (blockIndex_ne B (ne_of_gt hji) a b)]
    rfl⟩
  map_one' := Subtype.ext ((AdelicGL.realPlaceInclusion F n v).map_one)
  map_mul' p q := Subtype.ext ((AdelicGL.realPlaceInclusion F n v).map_mul p.val q.val)

/-- The actual complex-place block parabolic embeds into the global one of the same shape. -/
def complexPlaceInclusion (v : CP) : B.parabolic ℂ →* Full F B where
  toFun p := ⟨AdelicGL.complexPlaceInclusion F n v p.val, by
    apply (B.mem_parabolic_iff (Adeles F) _).mpr
    intro i j a b hji
    change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (complexPlaceGL F n v p.val (B.index i a) (B.index j b)),
      (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) (B.index i a) (B.index j b)) = 0
    rw [complexPlaceGL_lowerBlock F B v p i j a b hji, map_zero, Matrix.one_apply,
      ite_eq_right (blockIndex_ne B (ne_of_gt hji) a b)]
    rfl⟩
  map_one' := Subtype.ext ((AdelicGL.complexPlaceInclusion F n v).map_one)
  map_mul' p q := Subtype.ext ((AdelicGL.complexPlaceInclusion F n v).map_mul p.val q.val)

@[simp]
theorem realPlaceInclusion_val (v : RP) (p : B.parabolic ℝ) :
    (realPlaceInclusion F B v p).val = AdelicGL.realPlaceInclusion F n v p.val := rfl

@[simp]
theorem complexPlaceInclusion_val (v : CP) (p : B.parabolic ℂ) :
    (complexPlaceInclusion F B v p).val = AdelicGL.complexPlaceInclusion F n v p.val := rfl

private theorem one_blockEntry {R : Type*} [Zero R] [One R]
    (i : Fin B.length) (a b : Fin (B.size i)) :
    (1 : Matrix (Fin n) (Fin n) R) (B.index i a) (B.index i b) =
      (1 : Matrix (Fin (B.size i)) (Fin (B.size i)) R) a b := by
  simp only [Matrix.one_apply, (B.index i).injective.eq_iff]

/-- Diagonal block extraction commutes with insertion at the real place. -/
theorem leviProjection_realPlaceInclusion (v : RP) (p : B.parabolic ℝ) :
    B.leviProjection (Adeles F) (realPlaceInclusion F B v p) =
      fun i => AdelicGL.realPlaceInclusion F (B.size i) v (B.leviProjection ℝ p i) := by
  funext i
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  have hm : realPlaceGL F n v p.val (B.index i a) (B.index i b) =
      realPlaceGL F (B.size i) v (B.leviProjection ℝ p i) a b := by
    refine Prod.ext (funext fun w => ?_) (funext fun _ => one_blockEntry B i a b)
    change ((Pi.mulSingle v p.val : RP → Langlands.GeneralLinear n ℝ) w).val
      (B.index i a) (B.index i b) =
        ((Pi.mulSingle v (B.leviProjection ℝ p i) :
          RP → Langlands.GeneralLinear (B.size i) ℝ) w).val a b
    by_cases hw : w = v
    · subst w
      simp only [Pi.mulSingle_eq_same]
      rfl
    · simp only [Pi.mulSingle_eq_of_ne hw, Units.val_one, one_blockEntry B]
  change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (realPlaceGL F n v p.val (B.index i a) (B.index i b)),
      (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) (B.index i a) (B.index i b)) =
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (realPlaceGL F (B.size i) v (B.leviProjection ℝ p i) a b),
      (1 : Matrix (Fin (B.size i)) (Fin (B.size i)) (FiniteAdeles F)) a b)
  rw [hm, one_blockEntry B]

/-- Diagonal block extraction commutes with insertion at the complex place. -/
theorem leviProjection_complexPlaceInclusion (v : CP) (p : B.parabolic ℂ) :
    B.leviProjection (Adeles F) (complexPlaceInclusion F B v p) =
      fun i => AdelicGL.complexPlaceInclusion F (B.size i) v (B.leviProjection ℂ p i) := by
  funext i
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  have hm : complexPlaceGL F n v p.val (B.index i a) (B.index i b) =
      complexPlaceGL F (B.size i) v (B.leviProjection ℂ p i) a b := by
    refine Prod.ext (funext fun _ => one_blockEntry B i a b) (funext fun w => ?_)
    change ((Pi.mulSingle v p.val : CP → Langlands.GeneralLinear n ℂ) w).val
      (B.index i a) (B.index i b) =
        ((Pi.mulSingle v (B.leviProjection ℂ p i) :
          CP → Langlands.GeneralLinear (B.size i) ℂ) w).val a b
    by_cases hw : w = v
    · subst w
      simp only [Pi.mulSingle_eq_same]
      rfl
    · simp only [Pi.mulSingle_eq_of_ne hw, Units.val_one, one_blockEntry B]
  change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (complexPlaceGL F n v p.val (B.index i a) (B.index i b)),
      (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) (B.index i a) (B.index i b)) =
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (complexPlaceGL F (B.size i) v (B.leviProjection ℂ p i) a b),
      (1 : Matrix (Fin (B.size i)) (Fin (B.size i)) (FiniteAdeles F)) a b)
  rw [hm, one_blockEntry B]

end AdelicBlockParabolic

namespace AdelicParabolicInduction

open AdelicBlockParabolic

variable {n : ℕ} (B : BlockShape n)
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable (σ : Representation ℂ (FullLevi F B) V)

section LocalRestriction

variable {R : Type} [CommRing R]
variable (ι : Langlands.GeneralLinear n R →* AdelicGL F n)
variable (ιP : B.parabolic R →* Full F B)

/-- At an adelic point commuting with the local parabolic, evaluate the full section
on the indicated local matrix group. Covariance uses the restricted normalized
parabolic action, and the map intertwines right translation in the local group. -/
def localSectionRestriction (hιP : ∀ p, (ιP p).val = ι p.val)
    (y : AdelicGL F n) (hy : ∀ p, Commute y (ιP p).val) :
    Representation.IntertwiningMap ((smoothInduced F B σ).comp ι)
      (Induction.equivariantAction (B.parabolic R)
        ((inducingRepresentation F B σ).comp ιP)) where
  toLinearMap :=
    { toFun f := ⟨fun g => evaluate F B σ f.val (y * ι g), by
        intro p g
        change evaluate F B σ f.val (y * ι (p.val * g)) =
          inducingRepresentation F B σ (ιP p) (evaluate F B σ f.val (y * ι g))
        have hm : y * ι (p.val * g) = (ιP p).val * (y * ι g) := by
          rw [map_mul, ← mul_assoc, ← hιP p, (hy p).eq, mul_assoc]
        rw [hm]
        exact f.val.property (ιP p) _⟩
      map_add' _ _ := Subtype.ext rfl
      map_smul' _ _ := Subtype.ext rfl }
  isIntertwining' h := by
    ext f g
    change evaluate F B σ (smoothInduced F B σ (ι h) f).val (y * ι g) =
      evaluate F B σ f.val (y * ι (g * h))
    rw [evaluate_smoothInduced, map_mul, mul_assoc]

@[simp]
theorem localSectionRestriction_apply (hιP : ∀ p, (ιP p).val = ι p.val)
    (y : AdelicGL F n) (hy : ∀ p, Commute y (ιP p).val) (f : SmoothSections F B σ)
    (g : Langlands.GeneralLinear n R) :
    (localSectionRestriction F B σ ι ιP hιP y hy f).val g =
      evaluate F B σ f.val (y * ι g) := rfl

end LocalRestriction

/-- Restrict an actual smooth adelic section to the real-place block induction
with its inherited normalized covariance. -/
def realPlaceSectionRestriction (v : RP) (y : AdelicGL F n)
    (hy : ∀ p : B.parabolic ℝ, Commute y (AdelicBlockParabolic.realPlaceInclusion F B v p).val) :=
  localSectionRestriction F B σ (AdelicGL.realPlaceInclusion F n v)
    (AdelicBlockParabolic.realPlaceInclusion F B v) (realPlaceInclusion_val F B v) y hy

/-- Restrict an actual smooth adelic section to the complex-place block induction
with its inherited normalized covariance. -/
def complexPlaceSectionRestriction (v : CP) (y : AdelicGL F n)
    (hy : ∀ p : B.parabolic ℂ,
      Commute y (AdelicBlockParabolic.complexPlaceInclusion F B v p).val) :=
  localSectionRestriction F B σ (AdelicGL.complexPlaceInclusion F n v)
    (AdelicBlockParabolic.complexPlaceInclusion F B v) (complexPlaceInclusion_val F B v) y hy

end AdelicParabolicInduction

end Langlands.Global
