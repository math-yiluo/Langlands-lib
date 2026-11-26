import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Regular.SMul
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Finite jets of an intertwiner with a finite inverse pole

Let `s` be an element of a commutative ring `R`, and let `U`, `W` be modules over an
`R`-algebra `𝔄`. For `j : ℕ` the jet module `U_j = U / s ^ j U` is the quotient of `U` by the
image of multiplication by `s ^ j`, and an `𝔄`-linear map `I : U → W` induces
`I_j : U_j → W_j`. This module defines these jets, the multiplication and projection maps
between them, and the submodules and maps of the comparison in Bernstein–Krötz,
*Smooth Fréchet globalizations of Harish-Chandra modules*, §10.1, Lemma 10.3 and the
discussion before Proposition 10.4. It states that comparison for an intertwiner `I` with
an inverse `J` up to `s ^ k` in `InversePoleJetSqueezeStatement`, and does not prove it.

All constructions are `𝔄`-linear. Operators on `U` and `W` that commute with `R` and are
intertwined by `I` can be made to act through `𝔄` (for instance through a free `R`-algebra),
and then every map below commutes with the maps they induce.
-/

noncomputable section

universe uR uA uU uW

set_option autoImplicit false

namespace Langlands.Archimedean

namespace JetSqueeze

variable {R : Type*} [CommRing R] (𝔄 : Type*) [Ring 𝔄] [Algebra R 𝔄]

section Carrier

variable (U : Type*) [AddCommGroup U] [Module R U] [Module 𝔄 U] [IsScalarTower R 𝔄 U]

/-- The submodule `s ^ j U`: the image of multiplication by `s ^ j`. -/
def powerImage (s : R) (j : ℕ) : Submodule 𝔄 U :=
  LinearMap.range (DistribSMul.toLinearMap 𝔄 U (s ^ j))

/-- The jet module `U_j = U / s ^ j U`. -/
abbrev Jet (s : R) (j : ℕ) : Type _ :=
  U ⧸ powerImage 𝔄 U s j

theorem powerImage_le_comap_mul (s : R) (m : ℕ) {j l : ℕ} (h : l ≤ m + j) :
    powerImage 𝔄 U s j ≤
      (powerImage 𝔄 U s l).comap (DistribSMul.toLinearMap 𝔄 U (s ^ m)) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨s ^ (m + j - l) • v, ?_⟩
  simp only [DistribSMul.toLinearMap_apply, smul_smul, ← pow_add]
  congr 2
  omega

/-- Multiplication by `s ^ m`, from `U_j` to `U_l`; it is well defined when `l ≤ m + j`. -/
def jetMul (s : R) (m : ℕ) {j l : ℕ} (h : l ≤ m + j) : Jet 𝔄 U s j →ₗ[𝔄] Jet 𝔄 U s l :=
  (powerImage 𝔄 U s j).mapQ (powerImage 𝔄 U s l) (DistribSMul.toLinearMap 𝔄 U (s ^ m))
    (powerImage_le_comap_mul 𝔄 U s m h)

theorem powerImage_le_comap_id (s : R) {j l : ℕ} (h : j ≤ l) :
    powerImage 𝔄 U s l ≤ (powerImage 𝔄 U s j).comap LinearMap.id := by
  rintro _ ⟨v, rfl⟩
  refine ⟨s ^ (l - j) • v, ?_⟩
  simp only [DistribSMul.toLinearMap_apply, LinearMap.id_apply, smul_smul, ← pow_add]
  congr 2
  omega

/-- The jet projection `U_l → U_j` for `j ≤ l`, induced by the identity of `U`. -/
def jetProj (s : R) {j l : ℕ} (h : j ≤ l) : Jet 𝔄 U s l →ₗ[𝔄] Jet 𝔄 U s j :=
  (powerImage 𝔄 U s l).mapQ (powerImage 𝔄 U s j) LinearMap.id (powerImage_le_comap_id 𝔄 U s h)

/-- The submodule `s ^ j U / s ^ l U` of `U_l`: the image of `s ^ j U` in `U_l`. -/
def jetSub (s : R) (j l : ℕ) : Submodule 𝔄 (Jet 𝔄 U s l) :=
  (powerImage 𝔄 U s j).map (powerImage 𝔄 U s l).mkQ

theorem jetMul_mem_jetSub (s : R) (k : ℕ) (x : Jet 𝔄 U s k) :
    jetMul 𝔄 U s k (by omega : 2 * k ≤ k + k) x ∈ jetSub 𝔄 U s k (2 * k) := by
  induction x using Submodule.Quotient.induction_on with
  | H u => exact ⟨s ^ k • u, ⟨u, rfl⟩, rfl⟩

/-- Multiplication by `s ^ k`, as a map from `U_k` to `s ^ k U / s ^ (2k) U`. -/
def jetMulToSub (s : R) (k : ℕ) : Jet 𝔄 U s k →ₗ[𝔄] jetSub 𝔄 U s k (2 * k) :=
  (jetMul 𝔄 U s k (by omega : 2 * k ≤ k + k)).codRestrict _ (jetMul_mem_jetSub 𝔄 U s k)

/-- Multiplication by `s ^ (k - 1)`, from `U_1` to `U_k`. -/
def jetRaise (s : R) (k : ℕ) : Jet 𝔄 U s 1 →ₗ[𝔄] Jet 𝔄 U s k :=
  jetMul 𝔄 U s (k - 1) (by omega : k ≤ k - 1 + 1)

end Carrier

section Map

variable {𝔄}
variable {U : Type*} [AddCommGroup U] [Module R U] [Module 𝔄 U] [IsScalarTower R 𝔄 U]
  {W : Type*} [AddCommGroup W] [Module R W] [Module 𝔄 W] [IsScalarTower R 𝔄 W]

theorem powerImage_le_comap (s : R) (j : ℕ) (I : U →ₗ[𝔄] W) :
    powerImage 𝔄 U s j ≤ (powerImage 𝔄 W s j).comap I := by
  rintro _ ⟨v, rfl⟩
  exact ⟨I v, (LinearMap.map_smul_of_tower I (s ^ j) v).symm⟩

/-- The map `I_j : U_j → W_j` induced by `I`. -/
def jetMap (s : R) (j : ℕ) (I : U →ₗ[𝔄] W) : Jet 𝔄 U s j →ₗ[𝔄] Jet 𝔄 W s j :=
  (powerImage 𝔄 U s j).mapQ (powerImage 𝔄 W s j) I (powerImage_le_comap s j I)

/-- The induced maps commute with multiplication by powers of `s`. -/
theorem jetMap_jetMul (s : R) (I : U →ₗ[𝔄] W) (m : ℕ) {j l : ℕ} (h : l ≤ m + j)
    (x : Jet 𝔄 U s j) :
    jetMap s l I (jetMul 𝔄 U s m h x) = jetMul 𝔄 W s m h (jetMap s j I x) := by
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    change Submodule.Quotient.mk (I (s ^ m • u)) = Submodule.Quotient.mk (s ^ m • I u)
    rw [LinearMap.map_smul_of_tower]

section Squeeze

variable (s : R) (k : ℕ) (I : U →ₗ[𝔄] W)

/-- The preimage under `I_(2k)` of `s ^ k W / s ^ (2k) W`, a submodule of `U_(2k)`. -/
def squeezeDomain : Submodule 𝔄 (Jet 𝔄 U s (2 * k)) :=
  (jetSub 𝔄 W s k (2 * k)).comap (jetMap s (2 * k) I)

/-- The image of `ker I_k` under multiplication by `s ^ k` from `U_k` to `U_(2k)`; it lies in
`s ^ k U / s ^ (2k) U`. -/
def squeezeKernel : Submodule 𝔄 (Jet 𝔄 U s (2 * k)) :=
  (LinearMap.ker (jetMap s k I)).map (jetMul 𝔄 U s k (by omega : 2 * k ≤ k + k))

theorem jetMap_mem_of_mem_squeezeDomain :
    ∀ x ∈ squeezeDomain s k I, jetMap s (2 * k) I x ∈ jetSub 𝔄 W s k (2 * k) :=
  fun _ hx => hx

/-- The restriction of `I_(2k)` to `squeezeDomain`, with values in `s ^ k W / s ^ (2k) W`. -/
def squeezeMap : squeezeDomain s k I →ₗ[𝔄] jetSub 𝔄 W s k (2 * k) :=
  (jetMap s (2 * k) I).restrict (jetMap_mem_of_mem_squeezeDomain s k I)

theorem squeezeKernel_comap_le_ker :
    (squeezeKernel s k I).comap (squeezeDomain s k I).subtype ≤
      LinearMap.ker (squeezeMap s k I) := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change jetMap s (2 * k) I ((squeezeDomain s k I).subtype x) = 0
  rw [← hyx, jetMap_jetMul, LinearMap.mem_ker.mp hy, map_zero]

/-- The map from `squeezeDomain` modulo `squeezeKernel` to `s ^ k W / s ^ (2k) W` induced by
`squeezeMap`. -/
def squeezeQuotientMap :
    (squeezeDomain s k I ⧸ (squeezeKernel s k I).comap (squeezeDomain s k I).subtype) →ₗ[𝔄]
      jetSub 𝔄 W s k (2 * k) :=
  Submodule.liftQ _ (squeezeMap s k I) (squeezeKernel_comap_le_ker s k I)

theorem ker_le_comap_jetMulToSub :
    LinearMap.ker (jetMap s k I) ≤
      ((squeezeKernel s k I).comap (jetSub 𝔄 U s k (2 * k)).subtype).comap
        (jetMulToSub 𝔄 U s k) :=
  fun x hx => ⟨x, hx, rfl⟩

/-- The map from `range I_k` to `s ^ k U / s ^ (2k) U` modulo `squeezeKernel` sending
`I_k x` to the class of `s ^ k x`. -/
def rangeToSubquotient :
    LinearMap.range (jetMap s k I) →ₗ[𝔄]
      (jetSub 𝔄 U s k (2 * k) ⧸
        (squeezeKernel s k I).comap (jetSub 𝔄 U s k (2 * k)).subtype) :=
  (Submodule.mapQ _ _ (jetMulToSub 𝔄 U s k) (ker_le_comap_jetMulToSub s k I)) ∘ₗ
    (jetMap s k I).quotKerEquivRange.symm.toLinearMap

theorem jetRaise_mem_range :
    ∀ y ∈ LinearMap.range (jetMap s 1 I),
      jetRaise 𝔄 W s k y ∈ LinearMap.range (jetMap s k I) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨jetRaise 𝔄 U s k x, jetMap_jetMul s I (k - 1) _ x⟩

/-- The map from `range I_1` to `range I_k` given by multiplication by `s ^ (k - 1)` on
`W_1`. -/
def rangeRaise : LinearMap.range (jetMap s 1 I) →ₗ[𝔄] LinearMap.range (jetMap s k I) :=
  (jetRaise 𝔄 W s k).restrict (jetRaise_mem_range s k I)

end Squeeze

end Map

end JetSqueeze

open JetSqueeze

/-- **Jet squeeze for an intertwiner with a finite inverse pole** (Bernstein–Krötz,
Lemma 10.3 and the comparisons before Proposition 10.4). Let `s` be an element of a
commutative ring `R` acting injectively on modules `U` and `W` over an `R`-algebra `𝔄`, let
`I : U → W` be `𝔄`-linear and `J : W → U` be `R`-linear with `J I = s ^ k` and `I J = s ^ k`,
where `1 ≤ k`. In `U_(2k)` let `A = squeezeDomain s k I` be the preimage under `I_(2k)` of
`s ^ k W / s ^ (2k) W`. Then:

* `A` is the preimage of `ker I_k` under the jet projection `U_(2k) → U_k`;
* the restriction `A → s ^ k W / s ^ (2k) W` of `I_(2k)` is onto, and its kernel is
  `squeezeKernel s k I`, the image of `ker I_k` under multiplication by `s ^ k` from `U_k`;
* `squeezeKernel s k I ≤ s ^ k U / s ^ (2k) U ≤ A`; multiplication by `s ^ k` is a bijection
  from `U_k` onto `s ^ k U / s ^ (2k) U`; the map `I_k x ↦ s ^ k x` is a bijection from
  `range I_k` onto `(s ^ k U / s ^ (2k) U) / squeezeKernel s k I`; the induced map is a
  bijection from `A / squeezeKernel s k I` onto `s ^ k W / s ^ (2k) W`, and multiplication
  by `s ^ k` is a bijection from `W_k` onto `s ^ k W / s ^ (2k) W`;
* multiplication by `s ^ (k - 1)` from `W_1` to `W_k` is injective and restricts to an
  injection `range I_1 → range I_k`, whose image is the image under `I_k` of
  `s ^ (k - 1) U / s ^ k U`. -/
def InversePoleJetSqueezeStatement : Prop :=
  ∀ (R : Type uR) [CommRing R] (𝔄 : Type uA) [Ring 𝔄] [Algebra R 𝔄]
    (U : Type uU) [AddCommGroup U] [Module R U] [Module 𝔄 U] [IsScalarTower R 𝔄 U]
    (W : Type uW) [AddCommGroup W] [Module R W] [Module 𝔄 W] [IsScalarTower R 𝔄 W]
    (s : R) (k : ℕ) (I : U →ₗ[𝔄] W) (J : W →ₗ[R] U),
    1 ≤ k → IsSMulRegular U s → IsSMulRegular W s →
    (∀ u : U, J (I u) = s ^ k • u) → (∀ w : W, I (J w) = s ^ k • w) →
      squeezeDomain s k I =
        (LinearMap.ker (jetMap s k I)).comap (jetProj 𝔄 U s (by omega : k ≤ 2 * k)) ∧
      Function.Surjective (squeezeMap s k I) ∧
      (LinearMap.ker (squeezeMap s k I)).map (squeezeDomain s k I).subtype =
        squeezeKernel s k I ∧
      squeezeKernel s k I ≤ jetSub 𝔄 U s k (2 * k) ∧
      jetSub 𝔄 U s k (2 * k) ≤ squeezeDomain s k I ∧
      Function.Bijective (jetMulToSub 𝔄 U s k) ∧
      Function.Bijective (rangeToSubquotient s k I) ∧
      Function.Bijective (squeezeQuotientMap s k I) ∧
      Function.Bijective (jetMulToSub 𝔄 W s k) ∧
      Function.Injective (jetRaise 𝔄 W s k) ∧
      Function.Injective (rangeRaise s k I) ∧
      (LinearMap.range (jetMap s 1 I)).map (jetRaise 𝔄 W s k) =
        (jetSub 𝔄 U s (k - 1) k).map (jetMap s k I)

end Langlands.Archimedean
