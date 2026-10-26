import Langlands.Representation.Whittaker.Algebraic
import Langlands.LocalField.Normalization.Proof
import Mathlib.Topology.LocallyConstant.Basic

/-!
# JPS function spaces and coordinate germs

The actual function spaces and coordinate quotients in JPS (1979), Lemma
(2.2.1), with algebraic constructions separated from smoothness assumptions.
-/

noncomputable section

namespace Langlands.Whittaker.JPSFunctionSpace

universe uF

variable {p : ℕ} [Fact p.Prime]

/-- The multiplicative coordinate group, including the singleton group at `n = 0`. -/
abbrev Torus (F : PadicField.{uF} p) (n : ℕ) := Fin n → F.Carrierˣ

/-- An actual translation-stable complex subspace of functions on the coordinate group. -/
abbrev FunctionSpace (F : PadicField.{uF} p) (n : ℕ) :=
  Subrepresentation (rightTranslation ℂ (Torus F n))

variable {F : PadicField.{uF} p} {n : ℕ}

/-- Embed one multiplicative coordinate, setting every other coordinate to one. -/
def coordinateEmbedding (i : Fin n) : F.Carrierˣ →* Torus F n where
  toFun b j := if j = i then b else 1
  map_one' := by ext j; simp
  map_mul' b c := by
    ext j
    by_cases h : j = i <;> simp [h]

@[simp] theorem coordinateEmbedding_apply (i j : Fin n) (b : F.Carrierˣ) :
    coordinateEmbedding i b j = if j = i then b else 1 := rfl

@[simp] theorem coordinateEmbedding_same (i : Fin n) (b : F.Carrierˣ) :
    coordinateEmbedding i b i = b := by simp

theorem coordinateEmbedding_commute (i j : Fin n) (b c : F.Carrierˣ) :
    coordinateEmbedding i b * coordinateEmbedding j c =
      coordinateEmbedding j c * coordinateEmbedding i b := mul_comm _ _

/-- Multiplication by the embedding multiplies exactly the specified coordinate. -/
theorem mul_coordinateEmbedding (a : Torus F n) (i : Fin n) (b : F.Carrierˣ) :
    a * coordinateEmbedding i b = Function.update a i (a i * b) := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

variable (W : FunctionSpace F n)

/-- Restricted translation still evaluates the actual underlying function at `a * s`. -/
@[simp] theorem translate_apply (s : Torus F n) (f : W.toSubmodule) (a : Torus F n) :
    (W.toRepresentation s f).val a = f.val (a * s) := rfl

/-- Coordinate translation on the original function space. -/
def coordinateRepresentation (i : Fin n) : Representation ℂ F.Carrierˣ W.toSubmodule :=
  W.toRepresentation.comp (coordinateEmbedding i)

@[simp] theorem coordinateRepresentation_apply (i : Fin n) (b : F.Carrierˣ)
    (f : W.toSubmodule) (a : Torus F n) :
    (coordinateRepresentation W i b f).val a = f.val (a * coordinateEmbedding i b) := rfl

theorem coordinateRepresentation_apply_update (i : Fin n) (b : F.Carrierˣ)
    (f : W.toSubmodule) (a : Torus F n) :
    (coordinateRepresentation W i b f).val a =
      f.val (Function.update a i (a i * b)) := by
  rw [coordinateRepresentation_apply, mul_coordinateEmbedding]

/-- Coordinate translations commute, also when the coordinates coincide. -/
theorem coordinateRepresentation_commute (i j : Fin n) (b c : F.Carrierˣ)
    (f : W.toSubmodule) :
    coordinateRepresentation W i b (coordinateRepresentation W j c f) =
      coordinateRepresentation W j c (coordinateRepresentation W i b f) := by
  apply Subtype.ext
  funext a
  change f.val ((a * coordinateEmbedding i b) * coordinateEmbedding j c) =
    f.val ((a * coordinateEmbedding j c) * coordinateEmbedding i b)
  ac_rfl

variable (T : F.TopologicalData)

/-- A bound may depend on the function and coordinate, but not on the other coordinates. -/
def HasCoordinateUpperSupport : Prop :=
  ∀ f : W.toSubmodule, ∀ i : Fin n, ∃ R : ℝ, 0 < R ∧
    ∀ a : Torus F n, R < T.normalizedAbs (a i : F.Carrier) → f.val a = 0

/-- Uniform vanishing near zero in coordinate `i`, on the multiplicative torus. -/
def VanishesNearCoordinateZero (i : Fin n) (f : Torus F n → ℂ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ a : Torus F n, T.normalizedAbs (a i : F.Carrier) < ε → f a = 0

theorem vanishesNearCoordinateZero_zero (i : Fin n) :
    VanishesNearCoordinateZero T i (0 : Torus F n → ℂ) :=
  ⟨1, zero_lt_one, fun _ _ => rfl⟩

theorem vanishesNearCoordinateZero_add (i : Fin n) {f g : Torus F n → ℂ}
    (hf : VanishesNearCoordinateZero T i f) (hg : VanishesNearCoordinateZero T i g) :
    VanishesNearCoordinateZero T i (f + g) := by
  obtain ⟨ε, hε, hf⟩ := hf
  obtain ⟨δ, hδ, hg⟩ := hg
  refine ⟨min ε δ, lt_min hε hδ, fun a ha => ?_⟩
  change f a + g a = 0
  rw [hf a (lt_of_lt_of_le ha (min_le_left _ _)),
    hg a (lt_of_lt_of_le ha (min_le_right _ _)), add_zero]

theorem vanishesNearCoordinateZero_smul (i : Fin n) (c : ℂ) {f : Torus F n → ℂ}
    (hf : VanishesNearCoordinateZero T i f) :
    VanishesNearCoordinateZero T i (c • f) := by
  obtain ⟨ε, hε, hf⟩ := hf
  exact ⟨ε, hε, fun a ha => by change c * f a = 0; rw [hf a ha, mul_zero]⟩

/-- Every translation preserves near-zero vanishing; its threshold is rescaled by `|s_i|`. -/
theorem vanishesNearCoordinateZero_translate (i : Fin n) (s : Torus F n)
    {f : Torus F n → ℂ} (hf : VanishesNearCoordinateZero T i f) :
    VanishesNearCoordinateZero T i (rightTranslation ℂ (Torus F n) s f) := by
  obtain ⟨ε, hε, hf⟩ := hf
  have hs : 0 < T.normalizedAbs (s i : F.Carrier) := T.normalizedAbs_pos (s i).ne_zero
  refine ⟨ε / T.normalizedAbs (s i : F.Carrier), div_pos hε hs, fun a ha => ?_⟩
  apply hf (a * s)
  change T.normalizedAbs ((a i : F.Carrier) * (s i : F.Carrier)) < ε
  rw [T.normalizedAbs_mul]
  exact (lt_div_iff₀ hs).mp ha

/-- The actual invariant subspace `W_i` inside `W`, not an arbitrary supplied subspace. -/
def coordinateVanishing (i : Fin n) : Subrepresentation W.toRepresentation where
  toSubmodule :=
    { carrier := {f | VanishesNearCoordinateZero T i f.val}
      zero_mem' := vanishesNearCoordinateZero_zero T i
      add_mem' := fun hf hg => vanishesNearCoordinateZero_add T i hf hg
      smul_mem' := fun c _ hf => vanishesNearCoordinateZero_smul T i c hf }
  apply_mem_toSubmodule := fun s _ hf => vanishesNearCoordinateZero_translate T i s hf

@[simp] theorem mem_coordinateVanishing_iff (i : Fin n) (f : W.toSubmodule) :
    f ∈ coordinateVanishing W T i ↔ VanishesNearCoordinateZero T i f.val := Iff.rfl

/-- The genuine algebraic coordinate-germ quotient `W / W_i`. -/
abbrev CoordinateGerm (i : Fin n) :=
  W.toSubmodule ⧸ (coordinateVanishing W T i).toSubmodule

/-- The full translation representation on the actual quotient. -/
def germRepresentation (i : Fin n) : Representation ℂ (Torus F n) (CoordinateGerm W T i) :=
  W.toRepresentation.quotient (coordinateVanishing W T i).toSubmodule
    (fun s _ hf => (coordinateVanishing W T i).apply_mem_toSubmodule s hf)

/-- Canonical projection from functions to coordinate germs, as an intertwiner. -/
def germMap (i : Fin n) : W.toRepresentation.IntertwiningMap (germRepresentation W T i) where
  toLinearMap := (coordinateVanishing W T i).toSubmodule.mkQ
  isIntertwining' _ := rfl

theorem germMap_surjective (i : Fin n) : Function.Surjective (germMap W T i) :=
  Submodule.mkQ_surjective _

@[simp] theorem germMap_eq_zero_iff (i : Fin n) (f : W.toSubmodule) :
    germMap W T i f = 0 ↔ VanishesNearCoordinateZero T i f.val :=
  Submodule.Quotient.mk_eq_zero _

@[simp] theorem germRepresentation_apply_mk (i : Fin n) (s : Torus F n)
    (f : W.toSubmodule) :
    germRepresentation W T i s (germMap W T i f) = germMap W T i (W.toRepresentation s f) := rfl

/-- JPS's coordinate action `σ_i` on this actual coordinate-germ quotient. -/
def sigma (i : Fin n) : Representation ℂ F.Carrierˣ (CoordinateGerm W T i) :=
  (germRepresentation W T i).comp (coordinateEmbedding i)

/-- Translating a germ amounts to taking the germ of the translated representative. -/
@[simp] theorem sigma_apply_mk (i : Fin n) (b : F.Carrierˣ) (f : W.toSubmodule) :
    sigma W T i b (germMap W T i f) =
      germMap W T i (coordinateRepresentation W i b f) := rfl

/-- On the quotient, coordinate dilation commutes with every full-torus translation. -/
theorem sigma_translate_commute (i : Fin n) (b : F.Carrierˣ) (s : Torus F n)
    (q : CoordinateGerm W T i) :
    sigma W T i b (germRepresentation W T i s q) =
      germRepresentation W T i s (sigma W T i b q) := by
  change germRepresentation W T i (coordinateEmbedding i b)
      (germRepresentation W T i s q) =
    germRepresentation W T i s (germRepresentation W T i (coordinateEmbedding i b) q)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_comm]

/-- The finite-dimensional operator-span hypothesis, in the endomorphisms of `W / W_i`. -/
def HasFiniteCoordinateOperatorSpan (i : Fin n) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range (sigma W T i)))

/-- The preceding hypothesis in every coordinate; vacuous at rank zero. -/
def HasFiniteOperatorSpans : Prop := ∀ i : Fin n, HasFiniteCoordinateOperatorSpan W T i

/-- Smoothness of the translation representation, kept as a separate hypothesis. -/
def IsSmoothSpace : Prop :=
  letI := T.topology
  IsSmooth W.toRepresentation

/-- The locally constant interpretation of the source's smooth scalar-valued functions. -/
def IsLocallyConstantSpace : Prop :=
  letI := T.topology
  ∀ f : W.toSubmodule, IsLocallyConstant f.val

/-- The exact continuous translation-finite predicate, with the parent's `b * a` convention. -/
def IsFiniteFunction (χ : Torus F n → ℂ) : Prop :=
  letI := T.topology
  Continuous χ ∧
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun b : Torus F n => fun a => χ (b * a)))

end Langlands.Whittaker.JPSFunctionSpace
