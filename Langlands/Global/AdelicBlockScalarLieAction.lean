import Langlands.Global.AdelicBlockScalarDifferential
import Langlands.Automorphic.RealDifferentialCovarianceProof

/-!
# Lie differentiation on smooth compact-finite adelic block sections

The differentiated section has the original open finite level and a
finite-dimensional infinite compact orbit span.
-/

noncomputable section

open scoped BigOperators Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
set_option synthInstance.maxHeartbeats 85000

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear NumberField
open ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "V" => FiniteSmoothRealizedSections F B S
local notation "KI" => standardInfiniteCompact F n
local notation "U" => B.unipotentRadical (Adeles F)

local instance : AddCommGroup V := Submodule.addCommGroup _

/-- The scalar function in one fixed finite slice. -/
def scalarSlice (d : FiniteAdelicGL F n) : V →ₗ[ℂ] (InfiniteAdelicGL F n → ℂ) where
  toFun f a := f.val.val (AdelicGL.pair F n a d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem scalarSlice_apply (d : FiniteAdelicGL F n) (f : V) (a : InfiniteAdelicGL F n) :
    scalarSlice F B S d f a = f.val.val (AdelicGL.pair F n a d) := rfl

/-- Smooth archimedean slices and finite infinite compact orbit span, with
one open finite stabilizer already imposed by the ambient carrier. -/
def smoothCompactFiniteSections : Submodule ℂ V :=
  CompactFiniteRealizedSections F B S ⊓
    ⨅ d : FiniteAdelicGL F n, (smoothFunctions F n).comap (scalarSlice F B S d)

local notation "W" => smoothCompactFiniteSections F B S

theorem mem_smoothCompactFiniteSections (f : V) :
    f ∈ W ↔ FiniteVectors.IsFiniteVector (finiteSmoothCompactAction F B S) f ∧
      ∀ d : FiniteAdelicGL F n, scalarSlice F B S d f ∈ smoothFunctions F n := by
  rw [smoothCompactFiniteSections, Submodule.mem_inf, Submodule.mem_iInf]
  rfl

/-- On the compact-finite carrier the smoothness condition is equivalent to
smooth scalar evaluation of normalized compact Levi slices. -/
theorem mem_smoothCompactFiniteSections_iff_compactSlices
    (f : CompactFiniteRealizedSections F B S) :
    f.val ∈ W ↔ HasSmoothCompactSlices F B S f.val.val := by
  rw [mem_smoothCompactFiniteSections]
  exact ⟨fun h => hasSmoothCompactSlices_of_infiniteSlice_mem F B S f.val.val h.2,
    fun h => ⟨f.property, infiniteSlice_mem_smoothFunctions F B S f h⟩⟩

/-- Finite translation shifts the finite argument of every full smooth slice. -/
def smoothCompactFiniteFiniteSubrepresentation :
    Subrepresentation (finiteSmoothAction F B S) where
  toSubmodule := W
  apply_mem_toSubmodule d f hf := by
    rw [mem_smoothCompactFiniteSections] at hf ⊢
    refine ⟨hf.1.map (finiteSmoothTranslateIntertwiner F B S d), fun b => ?_⟩
    have he : scalarSlice F B S b (finiteSmoothAction F B S d f) =
        scalarSlice F B S (b * d) f := by
      funext a
      change f.val.val (AdelicGL.pair F n a b * AdelicGL.ofFinite F n d) =
        f.val.val (AdelicGL.pair F n a (b * d))
      rw [AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one]
    exact he ▸ hf.2 (b * d)

/-- Infinite compact translation right-translates every full smooth slice. -/
def smoothCompactFiniteCompactSubrepresentation :
    Subrepresentation (finiteSmoothCompactAction F B S) where
  toSubmodule := W
  apply_mem_toSubmodule k f hf := by
    rw [mem_smoothCompactFiniteSections] at hf ⊢
    refine ⟨hf.1.action k, fun b => ?_⟩
    have h : scalarSlice F B S b (finiteSmoothCompactAction F B S k f) =
        (smoothRightAction F n k.val ⟨scalarSlice F B S b f, hf.2 b⟩).val := by
      funext a
      change f.val.val (AdelicGL.pair F n a b * AdelicGL.ofInfinite F n k.val) =
        f.val.val (AdelicGL.pair F n (a * k.val) b)
      rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one]
    rw [h]
    exact Subtype.property _

/-- The actual finite factor acts on the smooth compact-finite sections. -/
abbrev smoothCompactFiniteAction : Representation ℂ (FiniteAdelicGL F n) W :=
  (smoothCompactFiniteFiniteSubrepresentation F B S).toRepresentation

/-- The actual infinite compact factor acts on the smooth compact-finite sections. -/
abbrev smoothCompactAction : Representation ℂ KI W :=
  (smoothCompactFiniteCompactSubrepresentation F B S).toRepresentation

/-- A fixed finite slice bundled as an actual smooth archimedean function. -/
def smoothScalarSlice (d : FiniteAdelicGL F n) : W →ₗ[ℂ] SmoothFunctions F n where
  toFun f := ⟨scalarSlice F B S d f.val,
    ((mem_smoothCompactFiniteSections F B S f.val).mp f.property).2 d⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem smoothScalarSlice_apply (d : FiniteAdelicGL F n) (f : W)
    (a : InfiniteAdelicGL F n) :
    (smoothScalarSlice F B S d f).val a = f.val.val.val (AdelicGL.pair F n a d) := rfl

@[simp]
theorem smoothScalarSlice_finiteAction (d b : FiniteAdelicGL F n) (f : W) :
    smoothScalarSlice F B S b (smoothCompactFiniteAction F B S d f) =
      smoothScalarSlice F B S (b * d) f := by
  apply Subtype.ext
  funext a
  change f.val.val.val (AdelicGL.pair F n a b * AdelicGL.ofFinite F n d) =
    f.val.val.val (AdelicGL.pair F n a (b * d))
  rw [AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one]

@[simp]
theorem smoothScalarSlice_compactAction (k : KI) (b : FiniteAdelicGL F n) (f : W) :
    smoothScalarSlice F B S b (smoothCompactAction F B S k f) =
      smoothRightAction F n k.val (smoothScalarSlice F B S b f) := by
  apply Subtype.ext
  funext a
  change f.val.val.val (AdelicGL.pair F n a b * AdelicGL.ofInfinite F n k.val) =
    f.val.val.val (AdelicGL.pair F n (a * k.val) b)
  rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one]

private theorem finiteSmooth_ext_of_pairs {f g : V}
    (h : ∀ a d, f.val.val (AdelicGL.pair F n a d) = g.val.val (AdelicGL.pair F n a d)) :
    f = g := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  simpa only [AdelicGL.pair_projections] using h (AdelicGL.infinite F n x) (AdelicGL.finite F n x)

/-- The smooth slices jointly determine the adelic scalar section. -/
theorem smoothScalarSlice_injective :
    Function.Injective (fun f : W => fun d => smoothScalarSlice F B S d f) := by
  intro f g h
  apply Subtype.ext
  apply finiteSmooth_ext_of_pairs F B S
  intro a d
  exact congrArg (fun q : SmoothFunctions F n => q.val a) (congrFun h d)

private theorem scalarDirectionalDerivative_eq_smoothDifferential
    (X : RealLieAlgebra F n) (f : W) (a : InfiniteAdelicGL F n) (d : FiniteAdelicGL F n) :
    scalarDirectionalDerivative F X f.val.val.val (AdelicGL.pair F n a d) =
      (smoothDifferential F n X (smoothScalarSlice F B S d f)).val a := by
  rw [scalarDirectionalDerivative_pair]
  symm
  exact smoothDifferential_eq_of_extension F n X _ _
    (fun h => infiniteSliceExtension_apply F _ _ h) a

private theorem scalarDerivative_leftInvariant (X : RealLieAlgebra F n) (f : W)
    (p : U) (g : AdelicGL F n) :
    scalarDirectionalDerivative F X f.val.val.val (p.val.val * g) =
      scalarDirectionalDerivative F X f.val.val.val g := by
  let a := AdelicGL.infinite F n p.val.val
  let b := AdelicGL.finite F n p.val.val
  let x := AdelicGL.infinite F n g
  let d := AdelicGL.finite F n g
  have hleft : smoothLeftTranslation F n a (smoothScalarSlice F B S (b * d) f) =
      smoothScalarSlice F B S d f := by
    apply Subtype.ext
    funext y
    change f.val.val.val (AdelicGL.pair F n (a * y) (b * d)) =
      f.val.val.val (AdelicGL.pair F n y d)
    rw [← AdelicGL.pair_mul, show AdelicGL.pair F n a b = p.val.val from
      AdelicGL.pair_projections F n _]
    exact f.val.val.property.1 p _
  have hc := congrArg (fun T : Module.End ℂ (SmoothFunctions F n) =>
    (T (smoothScalarSlice F B S (b * d) f)).val x)
      (smoothDifferential_leftTranslation F n X a)
  simp only [LinearMap.comp_apply, hleft, smoothLeftTranslation_apply] at hc
  rw [← AdelicGL.pair_projections F n g, ← AdelicGL.pair_projections F n p.val.val,
    AdelicGL.pair_mul, scalarDirectionalDerivative_eq_smoothDifferential F B S,
    scalarDirectionalDerivative_eq_smoothDifferential F B S]
  exact hc.symm

private def realizedDerivative (X : RealLieAlgebra F n) (f : W) : RealizedSections F B S :=
  ⟨scalarDirectionalDerivative F X f.val.val.val, scalarDerivative_leftInvariant F B S X f,
    fun k =>
      let f₀ : CompactFiniteRealizedSections F B S := ⟨f.val, f.property.1⟩
      normalizedSlice_derivative_mem F B S f₀
        ((mem_smoothCompactFiniteSections_iff_compactSlices F B S f₀).mp f.property) X k⟩

private def finiteSmoothDerivative (X : RealLieAlgebra F n) (f : W) : V :=
  ⟨realizedDerivative F B S X f, by
    obtain ⟨L, hL⟩ := f.val.property
    refine ⟨L, fun l => ?_⟩
    apply Subtype.ext
    funext g
    have hl (d : FiniteAdelicGL F n) :
        smoothScalarSlice F B S (d * l.val) f = smoothScalarSlice F B S d f := by
      apply Subtype.ext
      funext a
      have h := congrArg (fun v : RealizedSections F B S => v.val (AdelicGL.pair F n a d)) (hL l)
      change (RealizedSections.finiteAction F B S l.val f.val.val).val (AdelicGL.pair F n a d) =
        f.val.val.val (AdelicGL.pair F n a d) at h
      simpa only [smoothScalarSlice_apply, RealizedSections.finiteAction_apply, AdelicGL.ofFinite_eq_pair,
        AdelicGL.pair_mul, mul_one] using h
    change scalarDirectionalDerivative F X f.val.val.val (g * AdelicGL.ofFinite F n l.val) =
      scalarDirectionalDerivative F X f.val.val.val g
    rw [← AdelicGL.pair_projections F n g, AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one,
      scalarDirectionalDerivative_eq_smoothDifferential F B S,
      scalarDirectionalDerivative_eq_smoothDifferential F B S, hl]⟩

private theorem scalarSlice_finiteSmoothDerivative
    (X : RealLieAlgebra F n) (f : W) (d : FiniteAdelicGL F n) (a : InfiniteAdelicGL F n) :
    scalarSlice F B S d (finiteSmoothDerivative F B S X f) a =
      (smoothDifferential F n X (smoothScalarSlice F B S d f)).val a :=
  scalarDirectionalDerivative_eq_smoothDifferential F B S X f a d

private def finiteSmoothDifferential (X : RealLieAlgebra F n) : W →ₗ[ℂ] V where
  toFun := finiteSmoothDerivative F B S X
  map_add' f g := by
    apply finiteSmooth_ext_of_pairs F B S
    intro a d
    change scalarSlice F B S d (finiteSmoothDerivative F B S X (f + g)) a =
      scalarSlice F B S d (finiteSmoothDerivative F B S X f) a +
        scalarSlice F B S d (finiteSmoothDerivative F B S X g) a
    simp only [scalarSlice_finiteSmoothDerivative, map_add, Submodule.coe_add, Pi.add_apply]
  map_smul' c f := by
    apply finiteSmooth_ext_of_pairs F B S
    intro a d
    change scalarSlice F B S d (finiteSmoothDerivative F B S X (c • f)) a =
      c • scalarSlice F B S d (finiteSmoothDerivative F B S X f) a
    simp only [scalarSlice_finiteSmoothDerivative, map_smul, Submodule.coe_smul, Pi.smul_apply]

private def realFiniteSmoothDifferential : RealLieAlgebra F n →ₗ[ℝ] (W →ₗ[ℂ] V) where
  toFun := finiteSmoothDifferential F B S
  map_add' X Y := by
    apply LinearMap.ext
    intro f
    apply finiteSmooth_ext_of_pairs F B S
    intro a d
    change scalarSlice F B S d (finiteSmoothDerivative F B S (X + Y) f) a =
      scalarSlice F B S d (finiteSmoothDerivative F B S X f) a +
        scalarSlice F B S d (finiteSmoothDerivative F B S Y f) a
    simp only [scalarSlice_finiteSmoothDerivative, ← realSmoothLieAction_apply, map_add,
      LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  map_smul' c X := by
    apply LinearMap.ext
    intro f
    apply finiteSmooth_ext_of_pairs F B S
    intro a d
    change scalarSlice F B S d (finiteSmoothDerivative F B S (c • X) f) a =
      c • scalarSlice F B S d (finiteSmoothDerivative F B S X f) a
    simp only [scalarSlice_finiteSmoothDerivative, ← realSmoothLieAction_apply, map_smul,
      LinearMap.smul_apply, Submodule.coe_smul_of_tower, Pi.smul_apply]

private theorem finiteSmoothDerivative_compactAction (k : KI) (X : RealLieAlgebra F n) (f : W) :
    finiteSmoothCompactAction F B S k (finiteSmoothDerivative F B S X f) =
      finiteSmoothDerivative F B S (realLieConjugation F n k.val X)
        (smoothCompactAction F B S k f) := by
  apply finiteSmooth_ext_of_pairs F B S
  intro a d
  change (finiteSmoothDerivative F B S X f).val.val
      (AdelicGL.pair F n a d * AdelicGL.ofInfinite F n k.val) = _
  rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one]
  change scalarSlice F B S d (finiteSmoothDerivative F B S X f) (a * k.val) =
    scalarSlice F B S d (finiteSmoothDerivative F B S _
      (smoothCompactAction F B S k f)) a
  simp only [scalarSlice_finiteSmoothDerivative, smoothScalarSlice_compactAction]
  exact congrArg (fun q : SmoothFunctions F n => q.val a)
    (smoothRightAction_smoothDifferential_realLieConjugation F n k.val X
      (smoothScalarSlice F B S d f))

private theorem isFiniteVector_finiteSmoothDerivative (X : RealLieAlgebra F n) (f : W) :
    FiniteVectors.IsFiniteVector (finiteSmoothCompactAction F B S)
      (finiteSmoothDerivative F B S X f) := by
  let ρ := smoothCompactAction F B S
  let σ := finiteSmoothCompactAction F B S
  let j : ρ.IntertwiningMap σ :=
    { toLinearMap := (smoothCompactFiniteSections F B S).subtype
      isIntertwining' _ := LinearMap.ext fun _ => rfl }
  let O := FiniteVectors.orbitSpan ρ f
  have : Module.Finite ℂ O :=
    (FiniteVectors.isFiniteVector_map_iff j Subtype.val_injective f).mp f.property.1
  have : Module.Finite ℝ (RealLieAlgebra F n) :=
    (realLieAlgebraToMatrix F n).symm.finiteDimensional
  let b := Module.finBasis ℝ (RealLieAlgebra F n)
  let D := realFiniteSmoothDifferential F B S
  let T := ⨆ i, LinearMap.range ((D (b i)).comp O.subtype)
  have : Module.Finite ℂ T := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := T)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  change σ k (finiteSmoothDerivative F B S X f) ∈ T
  rw [finiteSmoothDerivative_compactAction F B S]
  let Y := realLieConjugation F n k.val X
  let v : O := ⟨ρ k f, FiniteVectors.action_mem_orbitSpan ρ k f⟩
  change D Y v.val ∈ T
  rw [← b.sum_repr Y, map_sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul, LinearMap.smul_apply]
  exact T.smul_of_tower_mem (b.repr Y i) ((le_iSup
    (fun j => LinearMap.range ((D (b j)).comp O.subtype)) i) ⟨v, rfl⟩)

/-- A real generator restricts to the smooth compact-finite scalar carrier. -/
def sectionDifferential (X : RealLieAlgebra F n) : Module.End ℂ W :=
  (finiteSmoothDifferential F B S X).codRestrict W fun f => by
    rw [mem_smoothCompactFiniteSections]
    refine ⟨isFiniteVector_finiteSmoothDerivative F B S X f, fun d => ?_⟩
    change scalarSlice F B S d (finiteSmoothDerivative F B S X f) ∈ smoothFunctions F n
    have h : scalarSlice F B S d (finiteSmoothDerivative F B S X f) =
        (smoothDifferential F n X (smoothScalarSlice F B S d f)).val :=
      funext (scalarSlice_finiteSmoothDerivative F B S X f d)
    rw [h]
    exact Subtype.property _

@[simp]
theorem smoothScalarSlice_sectionDifferential (X : RealLieAlgebra F n)
    (f : W) (d : FiniteAdelicGL F n) :
    smoothScalarSlice F B S d (sectionDifferential F B S X f) =
      smoothDifferential F n X (smoothScalarSlice F B S d f) :=
  Subtype.ext (funext (scalarSlice_finiteSmoothDerivative F B S X f d))

end Langlands.Global.AdelicBlockScalarSections
