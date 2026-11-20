import Langlands.Automorphic.TwoBlockConstantTermActions
import Langlands.Automorphic.TwoBlockConstantTermSmooth
import Langlands.Automorphic.TwoBlockSmoothPullback
import Langlands.Global.ArchimedeanOrbitDerivativeInterchange

/-! # Actual finite-smooth slices of the two-block constant term -/

noncomputable section
universe u

open scoped Classical TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear ArchimedeanGL ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local instance blockSlicesRationalGroup (r : ℕ) : AddCommGroup (RationalInvariantFunctions F r) :=
  Submodule.addCommGroup _
local instance blockSlicesContinuousGroup (r : ℕ) : AddCommGroup (ContinuousRationalFunctions F r) :=
  Submodule.addCommGroup _
local instance blockSlicesFiniteSmoothGroup (r : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F r) := Submodule.addCommGroup _
local instance blockSlicesFormGroup (r : ℕ) : AddCommGroup (AutomorphicForms F r) :=
  Submodule.addCommGroup _

local notation "A" => AdelicGL F
local notation "G∞" => InfiniteAdelicGL F
local notation "Gf" => FiniteAdelicGL F

/-- The induced open level in the first block, obtained by inserting identity in the second. -/
def firstBlockConstantTermLevel (L : OpenSubgroup (Gf n)) (d : Gf n) : OpenSubgroup (Gf a) :=
  (twoBlockConstantTermLevel F h L d).comap (MonoidHom.inl (Gf a) (Gf b))
    (continuous_id.prodMk continuous_const)

/-- The induced open level in the second block, obtained by inserting identity in the first. -/
def secondBlockConstantTermLevel (L : OpenSubgroup (Gf n)) (d : Gf n) : OpenSubgroup (Gf b) :=
  (twoBlockConstantTermLevel F h L d).comap (MonoidHom.inr (Gf a) (Gf b))
    (continuous_const.prodMk continuous_id)

/-- The first compact group inserted into the ambient compact subgroup. -/
def firstBlockInfiniteCompact : standardInfiniteCompact F a →* standardInfiniteCompact F n :=
  (twoBlockInfiniteCompact F h).comp
    (MonoidHom.inl (standardInfiniteCompact F a) (standardInfiniteCompact F b))

/-- The second compact group inserted into the ambient compact subgroup. -/
def secondBlockInfiniteCompact : standardInfiniteCompact F b →* standardInfiniteCompact F n :=
  (twoBlockInfiniteCompact F h).comp
    (MonoidHom.inr (standardInfiniteCompact F a) (standardInfiniteCompact F b))

theorem blockDiagonalEmbedding_mul_ofFinite_eq_pair (z : A a × A b) (d : Gf n) :
    blockDiagonalEmbedding h z * AdelicGL.ofFinite F n d =
      AdelicGL.pair F n
        (blockDiagonalEmbedding h (AdelicGL.infinite F a z.1, AdelicGL.infinite F b z.2))
        (blockDiagonalEmbedding h (AdelicGL.finite F a z.1, AdelicGL.finite F b z.2) * d) := by
  apply (AdelicGL.split F n).injective
  change (AdelicGL.infinite F n _, AdelicGL.finite F n _) =
    (AdelicGL.infinite F n _, AdelicGL.finite F n _)
  simp only [map_mul, AdelicGL.infinite_blockDiagonalEmbedding, AdelicGL.finite_blockDiagonalEmbedding,
    AdelicGL.infinite_pair, AdelicGL.finite_pair, AdelicGL.infinite_ofFinite, AdelicGL.finite_ofFinite,
    mul_one]

variable [CompactSpace (AdeleQuotient F)]

/-- Hold the second input fixed in the actual constant term to obtain a continuous
rational-invariant function on the first block. -/
def firstBlockConstantTermContinuous (d : Gf n) (y : A b) :
    AutomorphicForms F n →ₗ[ℂ] ContinuousRationalFunctions F a where
  toFun f := ⟨⟨fun x => blockConstantTermAt F n h d f (x, y), by
      intro γ x
      change blockConstantTermAt F n h d f (AdelicGL.rational F a γ * x, y) =
        blockConstantTermAt F n h d f (x, y)
      simpa only [map_one, Prod.mk_mul_mk, one_mul] using
        blockConstantTermAt_mul_rational F h d f (x, y) (γ, 1)⟩,
    (continuous_blockConstantTermAt F h d f).comp (continuous_id.prodMk continuous_const)⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact congrFun ((blockConstantTermAt F n h d).map_add f g) (x, y)
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact congrFun ((blockConstantTermAt F n h d).map_smul c f) (x, y)

/-- Hold the first input fixed in the actual constant term to obtain a continuous
rational-invariant function on the second block. -/
def secondBlockConstantTermContinuous (d : Gf n) (x : A a) :
    AutomorphicForms F n →ₗ[ℂ] ContinuousRationalFunctions F b where
  toFun f := ⟨⟨fun y => blockConstantTermAt F n h d f (x, y), by
      intro γ y
      change blockConstantTermAt F n h d f (x, AdelicGL.rational F b γ * y) =
        blockConstantTermAt F n h d f (x, y)
      simpa only [map_one, Prod.mk_mul_mk, one_mul] using
        blockConstantTermAt_mul_rational F h d f (x, y) (1, γ)⟩,
    (continuous_blockConstantTermAt F h d f).comp (continuous_const.prodMk continuous_id)⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext y
    exact congrFun ((blockConstantTermAt F n h d).map_add f g) (x, y)
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext y
    exact congrFun ((blockConstantTermAt F n h d).map_smul c f) (x, y)

@[simp]
theorem firstBlockConstantTermContinuous_apply (d : Gf n) (f : AutomorphicForms F n)
    (x : A a) (y : A b) :
    evaluate F a (firstBlockConstantTermContinuous F h d y f) x =
      blockConstantTermAt F n h d f (x, y) := rfl

@[simp]
theorem secondBlockConstantTermContinuous_apply (d : Gf n) (f : AutomorphicForms F n)
    (x : A a) (y : A b) :
    evaluate F b (secondBlockConstantTermContinuous F h d x f) y =
      blockConstantTermAt F n h d f (x, y) := rfl

theorem firstBlockConstantTermContinuous_fixed (d : Gf n) (y : A b) (f : AutomorphicForms F n)
    (L : OpenSubgroup (Gf n)) (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f) :
    firstBlockConstantTermContinuous F h d y f ∈
      levelSubmodule F a (firstBlockConstantTermLevel F h L d).toSubgroup := by
  intro l
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change blockConstantTermAt F n h d f (x * AdelicGL.ofFinite F a l.val, y) =
    blockConstantTermAt F n h d f (x, y)
  let l' : twoBlockConstantTermLevel F h L d := ⟨(l.val, 1), l.property⟩
  simpa only [l', map_one, Prod.mk_mul_mk, mul_one] using
    blockConstantTermAt_level_invariant F h L d f hf (x, y) l'

theorem secondBlockConstantTermContinuous_fixed (d : Gf n) (x : A a) (f : AutomorphicForms F n)
    (L : OpenSubgroup (Gf n)) (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f) :
    secondBlockConstantTermContinuous F h d x f ∈
      levelSubmodule F b (secondBlockConstantTermLevel F h L d).toSubgroup := by
  intro l
  apply Subtype.ext
  apply Subtype.ext
  funext y
  change blockConstantTermAt F n h d f (x, y * AdelicGL.ofFinite F b l.val) =
    blockConstantTermAt F n h d f (x, y)
  let l' : twoBlockConstantTermLevel F h L d := ⟨(1, l.val), l.property⟩
  simpa only [l', map_one, Prod.mk_mul_mk, mul_one] using
    blockConstantTermAt_level_invariant F h L d f hf (x, y) l'

theorem firstBlockConstantTermContinuous_compact (d : Gf n) (y : A b) (f : AutomorphicForms F n)
    (k : standardInfiniteCompact F a) :
    continuousRightAction F a (AdelicGL.ofInfinite F a k.val)
      (firstBlockConstantTermContinuous F h d y f) =
        firstBlockConstantTermContinuous F h d y
          (automorphicCompactRightAction F n (firstBlockInfiniteCompact F h k) f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change blockConstantTermAt F n h d f (x * AdelicGL.ofInfinite F a k.val, y) =
    blockConstantTermAt F n h d
      (automorphicCompactRightAction F n (firstBlockInfiniteCompact F h k) f) (x, y)
  simpa only [firstBlockInfiniteCompact, MonoidHom.comp_apply, MonoidHom.inl_apply,
    Subgroup.coe_one, map_one, Prod.mk_mul_mk, mul_one] using
    blockConstantTermAt_mul_compact F h d f (x, y) (k, 1)

theorem secondBlockConstantTermContinuous_compact (d : Gf n) (x : A a) (f : AutomorphicForms F n)
    (k : standardInfiniteCompact F b) :
    continuousRightAction F b (AdelicGL.ofInfinite F b k.val)
      (secondBlockConstantTermContinuous F h d x f) =
        secondBlockConstantTermContinuous F h d x
          (automorphicCompactRightAction F n (secondBlockInfiniteCompact F h k) f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext y
  change blockConstantTermAt F n h d f (x, y * AdelicGL.ofInfinite F b k.val) =
    blockConstantTermAt F n h d
      (automorphicCompactRightAction F n (secondBlockInfiniteCompact F h k) f) (x, y)
  simpa only [secondBlockInfiniteCompact, MonoidHom.comp_apply, MonoidHom.inr_apply,
    Subgroup.coe_one, map_one, Prod.mk_mul_mk, mul_one] using
    blockConstantTermAt_mul_compact F h d f (x, y) (1, k)

private def smoothConstantTermSliceLinear (d : Gf n) :
    FiniteSmoothRationalFunctions F n →ₗ[ℂ] SmoothFunctions F n where
  toFun f := smoothConstantTermSlice F n h f d
  map_add' f g := Subtype.ext (funext fun x =>
    constantTerm_add h f.val g.val (AdelicGL.pair F n x d))
  map_smul' c f := Subtype.ext (funext fun x =>
    constantTerm_smul h c f.val (AdelicGL.pair F n x d))

local notation "U" => EnvelopingAlgebra F

omit [CompactSpace (AdeleQuotient F)] in
private theorem smoothPullback_enveloping {r : ℕ}
    (ι : U r →ₐ[ℂ] U n)
    (T : FiniteSmoothRationalFunctions F n →ₗ[ℂ] SmoothFunctions F r)
    (hT : ∀ X f, smoothDifferential F r X (T f) =
      T (finiteSmoothEnvelopingAction F n (ι (envelopingGenerator F r (complexify F r X))) f))
    (u : U r) (f : FiniteSmoothRationalFunctions F n) :
    envelopingAction F r u (T f) = T (finiteSmoothEnvelopingAction F n (ι u) f) := by
  induction u using enveloping_real_left_induction F r generalizing f with
  | h1 => simp only [map_one, Module.End.one_apply]
  | hadd u v hu hv =>
    simp only [map_add, LinearMap.add_apply, hu, hv]
  | hsmul c u hu =>
    simp only [map_smul, LinearMap.smul_apply, hu]
  | hgen X u hu =>
    simp only [map_mul, Module.End.mul_apply, hu, envelopingAction_real_generator, hT]

/-- The constant term at a fixed ambient finite argument, sliced in the first infinite block. -/
def firstBlockSmoothConstantTerm (d : Gf n) (y : G∞ b) :
    FiniteSmoothRationalFunctions F n →ₗ[ℂ] SmoothFunctions F a :=
  (firstBlockSmoothPullback F h y).comp (smoothConstantTermSliceLinear F h d)

/-- The constant term at a fixed ambient finite argument, sliced in the second infinite block. -/
def secondBlockSmoothConstantTerm (d : Gf n) (x : G∞ a) :
    FiniteSmoothRationalFunctions F n →ₗ[ℂ] SmoothFunctions F b :=
  (secondBlockSmoothPullback F h x).comp (smoothConstantTermSliceLinear F h d)

@[simp]
theorem firstBlockSmoothConstantTerm_apply (d : Gf n) (f : FiniteSmoothRationalFunctions F n)
    (x : G∞ a) (y : G∞ b) :
    (firstBlockSmoothConstantTerm F h d y f).val x =
      constantTerm F n h f.val (AdelicGL.pair F n (blockDiagonalEmbedding h (x, y)) d) := rfl

@[simp]
theorem secondBlockSmoothConstantTerm_apply (d : Gf n) (f : FiniteSmoothRationalFunctions F n)
    (x : G∞ a) (y : G∞ b) :
    (secondBlockSmoothConstantTerm F h d x f).val y =
      constantTerm F n h f.val (AdelicGL.pair F n (blockDiagonalEmbedding h (x, y)) d) := rfl

theorem firstBlockSmoothConstantTerm_enveloping (d : Gf n) (y : G∞ b)
    (f : FiniteSmoothRationalFunctions F n) (u : U a) :
    envelopingAction F a u (firstBlockSmoothConstantTerm F h d y f) =
      firstBlockSmoothConstantTerm F h d y
        (finiteSmoothEnvelopingAction F n (firstBlockEnvelopingInclusion F h u) f) := by
  apply smoothPullback_enveloping F (firstBlockEnvelopingInclusion F h)
  intro X f'
  apply Subtype.ext
  funext x
  change (smoothDifferential F a X
    (firstBlockSmoothPullback F h y (smoothConstantTermSlice F n h f' d))).val x = _
  rw [smoothDifferential_firstBlockSmoothPullback, smoothDifferential_smoothConstantTermSlice,
    firstBlockSmoothConstantTerm_apply]
  simp only [firstBlockEnvelopingInclusion_generator, complexify_apply,
    firstBlockComplexLieInclusion_tmul]

theorem secondBlockSmoothConstantTerm_enveloping (d : Gf n) (x : G∞ a)
    (f : FiniteSmoothRationalFunctions F n) (u : U b) :
    envelopingAction F b u (secondBlockSmoothConstantTerm F h d x f) =
      secondBlockSmoothConstantTerm F h d x
        (finiteSmoothEnvelopingAction F n (secondBlockEnvelopingInclusion F h u) f) := by
  apply smoothPullback_enveloping F (secondBlockEnvelopingInclusion F h)
  intro Y f'
  apply Subtype.ext
  funext y
  change (smoothDifferential F b Y
    (secondBlockSmoothPullback F h x (smoothConstantTermSlice F n h f' d))).val y = _
  rw [smoothDifferential_secondBlockSmoothPullback, smoothDifferential_smoothConstantTermSlice,
    secondBlockSmoothConstantTerm_apply]
  simp only [secondBlockEnvelopingInclusion_generator, complexify_apply,
    secondBlockComplexLieInclusion_tmul]

private theorem blockConstantTermAt_eq_pair (d : Gf n) (f : AutomorphicForms F n)
    (z : A a × A b) :
    blockConstantTermAt F n h d f z = constantTerm F n h f.val.val
      (AdelicGL.pair F n
        (blockDiagonalEmbedding h (AdelicGL.infinite F a z.1, AdelicGL.infinite F b z.2))
        (blockDiagonalEmbedding h (AdelicGL.finite F a z.1, AdelicGL.finite F b z.2) * d)) := by
  change constantTerm F n h f.val.val (blockDiagonalEmbedding h z * AdelicGL.ofFinite F n d) = _
  rw [blockDiagonalEmbedding_mul_ofFinite_eq_pair]

private theorem firstBlockConstantTerm_infiniteSlice (d : Gf n) (y : A b)
    (f : AutomorphicForms F n) (l : Gf a) :
    infiniteSlice F a l (firstBlockConstantTermContinuous F h d y f) =
      (firstBlockSmoothConstantTerm F h (blockDiagonalEmbedding h (l, AdelicGL.finite F b y) * d)
        (AdelicGL.infinite F b y) f.val).val := by
  funext x
  change blockConstantTermAt F n h d f (AdelicGL.pair F a x l, y) = _
  rw [blockConstantTermAt_eq_pair, firstBlockSmoothConstantTerm_apply,
    AdelicGL.infinite_pair, AdelicGL.finite_pair]

private theorem secondBlockConstantTerm_infiniteSlice (d : Gf n) (x : A a)
    (f : AutomorphicForms F n) (l : Gf b) :
    infiniteSlice F b l (secondBlockConstantTermContinuous F h d x f) =
      (secondBlockSmoothConstantTerm F h (blockDiagonalEmbedding h (AdelicGL.finite F a x, l) * d)
        (AdelicGL.infinite F a x) f.val).val := by
  funext y
  change blockConstantTermAt F n h d f (x, AdelicGL.pair F b y l) = _
  rw [blockConstantTermAt_eq_pair, secondBlockSmoothConstantTerm_apply,
    AdelicGL.infinite_pair, AdelicGL.finite_pair]

/-- The first-variable constant-term slice with its smoothness and open stabilizer. -/
def firstBlockConstantTermFiniteSmooth (d : Gf n) (y : A b) (f : AutomorphicForms F n)
    (L : OpenSubgroup (Gf n)) (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f) :
    FiniteSmoothRationalFunctions F a :=
  ⟨firstBlockConstantTermContinuous F h d y f,
    ⟨(Submodule.mem_iInf _).mpr fun l => by
        apply Submodule.mem_comap.mpr
        rw [firstBlockConstantTerm_infiniteSlice]
        exact Subtype.property _,
      ⟨firstBlockConstantTermLevel F h L d, firstBlockConstantTermContinuous_fixed F h d y f L hf⟩⟩⟩

/-- The second-variable constant-term slice with its smoothness and open stabilizer. -/
def secondBlockConstantTermFiniteSmooth (d : Gf n) (x : A a) (f : AutomorphicForms F n)
    (L : OpenSubgroup (Gf n)) (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f) :
    FiniteSmoothRationalFunctions F b :=
  ⟨secondBlockConstantTermContinuous F h d x f,
    ⟨(Submodule.mem_iInf _).mpr fun l => by
        apply Submodule.mem_comap.mpr
        rw [secondBlockConstantTerm_infiniteSlice]
        exact Subtype.property _,
      ⟨secondBlockConstantTermLevel F h L d, secondBlockConstantTermContinuous_fixed F h d x f L hf⟩⟩⟩

theorem firstBlockConstantTermFiniteSmooth_slice (d : Gf n) (y : A b) (f : AutomorphicForms F n)
    (L : OpenSubgroup (Gf n)) (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f) (l : Gf a) :
    finiteSmoothSlice F a l (firstBlockConstantTermFiniteSmooth F h d y f L hf) =
      firstBlockSmoothConstantTerm F h (blockDiagonalEmbedding h (l, AdelicGL.finite F b y) * d)
        (AdelicGL.infinite F b y) f.val :=
  Subtype.ext (firstBlockConstantTerm_infiniteSlice F h d y f l)

theorem secondBlockConstantTermFiniteSmooth_slice (d : Gf n) (x : A a) (f : AutomorphicForms F n)
    (L : OpenSubgroup (Gf n)) (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f) (l : Gf b) :
    finiteSmoothSlice F b l (secondBlockConstantTermFiniteSmooth F h d x f L hf) =
      secondBlockSmoothConstantTerm F h (blockDiagonalEmbedding h (AdelicGL.finite F a x, l) * d)
        (AdelicGL.infinite F a x) f.val :=
  Subtype.ext (secondBlockConstantTerm_infiniteSlice F h d x f l)

end Langlands.Automorphic
