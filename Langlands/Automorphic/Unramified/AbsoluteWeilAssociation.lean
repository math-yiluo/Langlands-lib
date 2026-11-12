import Langlands.ClassField.Global.AbsoluteLocalWeilMap
import Langlands.Automorphic.Unramified.RelativeWeilAssociation

/-! # Representations of the absolute Weil group and weak association

Inflation of representations of `W_{K/F}` to the projective limit `W_F` of a supplied system
of Weil maps, local components along local-to-global Weil maps `W_{F_v} → W_F`, and weak
association of representations of `W_F` with unramified spectra and cuspidal classes. The
comparison with the relative notions is proved under an explicit hypothesis that
local-to-global Weil maps exist. No local map, representation or spectrum is constructed.
-/

noncomputable section

namespace Langlands.ClassField.Global

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.Unramified

universe u uV uW uP

namespace WeilMapSystem

variable {c : FundamentalClass.ClassFamily.{u}} {F : Type u} [Field F] [NumberField F]
  {Ω : Type u} [Field Ω] [Algebra F Ω] {h : FundamentalClass.Restriction c}
  (S : WeilMapSystem c F Ω h)

section Inflation

variable (K : FiniteGaloisIntermediateField F Ω)

/-- The projection `W_F → W_{K/F}` is continuous for the Krull topology on `Gal(K/F)`. -/
theorem continuous_levelHom_krull : Continuous (S.levelHom K) :=
  RelativeWeilGroup.continuous_krull_of_relativeGalois c _ (S.continuous_levelHom K)

/-- The inflation to `W_F` of a representation of `W_{K/F}`, along `S.toLevel K`, on the
same carrier. -/
def inflate (A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F K)) :
    FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup :=
  FiniteRepresentation.restrict (S.levelHom K) A

variable {K}

@[simp]
theorem inflate_representation (A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F K))
    (x : S.WeilGroup) :
    (S.inflate K A).representation x = A.representation (S.toLevel K x) :=
  rfl

theorem rank_inflate (A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F K)) :
    (S.inflate K A).rank = A.rank :=
  rfl

/-- Inflation preserves continuity. -/
theorem isContinuous_inflate {A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F K)}
    (hA : A.IsContinuous) : (S.inflate K A).IsContinuous :=
  FiniteRepresentation.isContinuous_restrict (S.levelHom K) (S.continuous_levelHom_krull K) hA

/-- Inflation preserves unitarizability: an invariant inner product stays invariant. -/
theorem isUnitary_inflate {A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F K)}
    (hA : A.IsUnitary) : (S.inflate K A).IsUnitary := by
  obtain ⟨b, hb⟩ := hA
  exact ⟨b, fun x => hb (S.toLevel K x)⟩

/-- Subrepresentations along a surjective homomorphism: the same submodules. -/
def subrepresentationCompOrderIso {G H V : Type*} [Monoid G] [Monoid H] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (f : H →* G) (hf : Function.Surjective f) :
    Subrepresentation ρ ≃o Subrepresentation (ρ.comp f) where
  toFun W := ⟨W.toSubmodule, fun g _ hv => W.apply_mem_toSubmodule (f g) hv⟩
  invFun W := ⟨W.toSubmodule, fun g v hv => by
    obtain ⟨g', rfl⟩ := hf g
    exact W.apply_mem_toSubmodule g' hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- If `S.toLevel K` is surjective, inflation preserves irreducibility. Surjectivity is a
hypothesis; it is not proved for the projective limit. -/
theorem isIrreducible_inflate (hK : Function.Surjective (S.toLevel K))
    {A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F K)}
    (hA : A.IsIrreducible) : (S.inflate K A).IsIrreducible :=
  (OrderIso.isSimpleOrder_iff
    (subrepresentationCompOrderIso A.representation (S.levelHom K) hK)).mp hA

end Inflation

section Local

variable {v : FinitePlace F}

/-- The local component `A ∘ θ` of a representation `A` of `W_F` along a supplied map
`θ : W_{F_v} → W_F`, on the original carrier of `A`. -/
def localComponent (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup) :
    FiniteRepresentation.{0, u, uV} ℂ (Weil.Local.localWeilGroup (padicField v)) :=
  FiniteRepresentation.restrict θ.toMonoidHom A

@[simp]
theorem localComponent_representation (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup)
    (g : Weil.Local.localWeilGroup (padicField v)) :
    (S.localComponent A θ).representation g = A.representation (θ g) :=
  rfl

/-- The local component of a continuous representation is continuous. -/
theorem localComponent_isContinuous {A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup}
    (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup) (hA : A.IsContinuous) :
    (S.localComponent A θ).IsContinuous :=
  FiniteRepresentation.isContinuous_restrict θ.toMonoidHom θ.continuous hA

/-- The polynomial `det(1 - X A(θ Fr))` on the whole carrier, at the published geometric
Frobenius lift `Fr` of `W_{F_v}`. It is the Euler denominator when `A ∘ θ` is unramified. -/
def localEulerPolynomial (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup) : Polynomial ℂ :=
  LocalFactor.eulerPolynomial
    ((S.localComponent A θ).representation (Weil.Local.localGeometricFrobenius (padicField v)))

/-- At the finite place `v` of `F`, `A` is unramified and matches the polynomial `P`: a
local-to-global Weil map `θ : W_{F_v} → W_F` exists, and every such map makes `A ∘ θ`
unramified with `det(1 - X A(θ Fr)) = P`. -/
def IsUnramifiedMatchAt (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (v : FinitePlace F) (P : Polynomial ℂ) : Prop :=
  (∃ θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup, S.IsLocalWeilMap v θ) ∧
    ∀ θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup, S.IsLocalWeilMap v θ →
      (S.localComponent A θ).IsUnramified (Weil.Local.localInertia (padicField v)) ∧
        S.localEulerPolynomial A θ = P

end Local

/-- `A` is weakly associated with the supplied spectral system `s` of rank `n`: `A` is
continuous of rank `n`, and on one cofinite set of finite places `v` of `F`, `s` is defined
at `v` and `A` is unramified and matches the Euler polynomial of the spectrum of `s` at
`v`. -/
def IsWeaklyAssociated {n : ℕ} (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (s : SpectralSystem (FinitePlace F) n) : Prop :=
  A.IsContinuous ∧ A.rank = n ∧
    ∀ᶠ v in Filter.cofinite, ∃ hs : v ∉ s.exceptional,
      S.IsUnramifiedMatchAt A v (s.eulerPolynomial v hs)

section Invariance

variable {A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup}
  {B : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup}

/-- An equivalence conjugates every operator of `A` to the corresponding operator of `B`. -/
theorem representation_eq_conj_of_equiv (φ : FiniteRepresentation.Equiv A B) (x : S.WeilGroup) :
    B.representation x = φ.toLinearEquiv.conj (A.representation x) := by
  have hc : φ.toLinearEquiv.toLinearMap ∘ₗ A.representation x ∘ₗ
      φ.toLinearEquiv.symm.toLinearMap = B.representation x := by
    ext b
    have hx := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap x (φ.symm b)
    exact hx.trans (congrArg (B.representation x) (φ.right_inv b))
  rw [LinearEquiv.conj_apply]
  exact hc.symm

/-- Continuity is invariant under equivalence. -/
theorem isContinuous_of_equiv (φ : FiniteRepresentation.Equiv A B) (hA : A.IsContinuous) :
    B.IsContinuous := by
  let : TopologicalSpace (Module.End ℂ A) := moduleTopology ℂ (Module.End ℂ A)
  let : TopologicalSpace (Module.End ℂ B) := moduleTopology ℂ (Module.End ℂ B)
  have : IsModuleTopology ℂ (Module.End ℂ A) := ⟨rfl⟩
  have : ContinuousAdd (Module.End ℂ B) := ModuleTopology.continuousAdd ℂ _
  have : ContinuousSMul ℂ (Module.End ℂ B) := ModuleTopology.continuousSMul ℂ _
  have hA' : Continuous A.representation := hA
  have hconj : (B.representation : S.WeilGroup → Module.End ℂ B) =
      φ.toLinearEquiv.conj.toLinearMap ∘ A.representation :=
    funext (S.representation_eq_conj_of_equiv φ)
  change Continuous (B.representation : S.WeilGroup → Module.End ℂ B)
  rw [hconj]
  exact (IsModuleTopology.continuous_of_linearMap _).comp hA'

/-- Equivalent representations have equal local Euler polynomials. -/
theorem localEulerPolynomial_eq_of_equiv {v : FinitePlace F} (φ : FiniteRepresentation.Equiv A B)
    (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup) :
    S.localEulerPolynomial B θ = S.localEulerPolynomial A θ := by
  set g := θ (Weil.Local.localGeometricFrobenius (padicField v))
  change LocalFactor.eulerPolynomial (B.representation g) =
    LocalFactor.eulerPolynomial (A.representation g)
  rw [S.representation_eq_conj_of_equiv φ g, LinearEquiv.conj_apply]
  exact LocalFactor.eulerPolynomial_conj φ.toLinearEquiv (A.representation g)

/-- Unramifiedness of the local component is invariant under equivalence. -/
theorem localComponent_isUnramified_of_equiv {v : FinitePlace F}
    (φ : FiniteRepresentation.Equiv A B)
    (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup)
    (hA : (S.localComponent A θ).IsUnramified (Weil.Local.localInertia (padicField v))) :
    (S.localComponent B θ).IsUnramified (Weil.Local.localInertia (padicField v)) := by
  intro i
  have hi : A.representation (θ i) = 1 := hA i
  change B.representation (θ i) = 1
  ext b
  have hx := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap (θ i)
    (φ.symm b)
  simpa [hi] using hx.symm

/-- The local matching condition depends only on the equivalence class of `A`. -/
theorem IsUnramifiedMatchAt.of_equiv {v : FinitePlace F} {P : Polynomial ℂ}
    (φ : FiniteRepresentation.Equiv A B) (hA : S.IsUnramifiedMatchAt A v P) :
    S.IsUnramifiedMatchAt B v P := by
  refine ⟨hA.1, fun θ hθ => ?_⟩
  obtain ⟨hu, hp⟩ := hA.2 θ hθ
  exact ⟨S.localComponent_isUnramified_of_equiv φ θ hu,
    (S.localEulerPolynomial_eq_of_equiv φ θ).trans hp⟩

/-- Weak association depends only on the equivalence class of `A`. -/
theorem IsWeaklyAssociated.of_equiv {n : ℕ} {s : SpectralSystem (FinitePlace F) n}
    (φ : FiniteRepresentation.Equiv A B) (hA : S.IsWeaklyAssociated A s) :
    S.IsWeaklyAssociated B s := by
  rcases hA with ⟨hc, hn, hA⟩
  exact ⟨S.isContinuous_of_equiv φ hc, (FiniteRepresentation.rank_eq_of_equiv φ).symm.trans hn,
    hA.mono fun v ⟨hs, hv⟩ => ⟨hs, hv.of_equiv S φ⟩⟩

end Invariance

section Comparison

variable {K : FiniteGaloisIntermediateField F Ω}
  {A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F K)}

/-- Conjugating an operator of `A` by `A(x)⁻¹` leaves its Euler polynomial unchanged. -/
theorem eulerPolynomial_representation_conj (x y : RelativeWeilGroup c F K) :
    LocalFactor.eulerPolynomial (A.representation (x⁻¹ * y * x)) =
      LocalFactor.eulerPolynomial (A.representation y) := by
  let e : A ≃ₗ[ℂ] A :=
    LinearEquiv.ofLinearMap (A.representation x⁻¹) (A.representation x)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
  have he : A.representation (x⁻¹ * y * x) = e.conj (A.representation y) := by
    rw [LinearEquiv.conj_apply, map_mul, map_mul]
    rfl
  rw [he, LocalFactor.eulerPolynomial_conj]

/-- If `A` is unramified and matches `P` at `v` in the relative sense, and a
local-to-global Weil map at `v` exists, then the inflation of `A` is unramified and matches
`P` at `v`. -/
theorem isUnramifiedMatchAt_inflate {v : FinitePlace F} {P : Polynomial ℂ}
    (hA : RelativeWeilGroup.IsUnramifiedMatchAt A v P)
    (hθ : ∃ θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup,
      S.IsLocalWeilMap v θ) :
    S.IsUnramifiedMatchAt (S.inflate K A) v P := by
  refine ⟨hθ, fun θ hθ' => ?_⟩
  obtain ⟨w, e, x, ι, hι, hθι⟩ := hθ'.exists_level K
  obtain ⟨hu, hp⟩ := (hA w).2 e ι hι
  refine ⟨fun i => ?_, ?_⟩
  · change A.representation (S.toLevel K (θ i)) = 1
    have hi : A.representation (ι i) = 1 := hu i
    rw [hθι, map_mul, map_mul, hi, mul_one, ← map_mul, inv_mul_cancel, map_one]
  · change LocalFactor.eulerPolynomial (A.representation (S.toLevel K (θ _))) = P
    rw [hθι, eulerPolynomial_representation_conj]
    exact hp

/-- Relative weak association gives absolute weak association of the inflation, provided
local-to-global Weil maps exist at all but finitely many finite places. The existence is a
hypothesis, not a proved fact. -/
theorem isWeaklyAssociated_inflate {n : ℕ} {s : SpectralSystem (FinitePlace F) n}
    (hA : RelativeWeilGroup.IsWeaklyAssociated A s)
    (hθ : ∀ᶠ v in Filter.cofinite,
      ∃ θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup, S.IsLocalWeilMap v θ) :
    S.IsWeaklyAssociated (S.inflate K A) s := by
  rcases hA with ⟨hc, hn, hA⟩
  refine ⟨S.isContinuous_inflate hc, hn, ?_⟩
  filter_upwards [hA, hθ] with v hv hθv
  obtain ⟨hs, hm⟩ := hv
  exact ⟨hs, S.isUnramifiedMatchAt_inflate hm hθv⟩

end Comparison

section Cuspidal

variable [CompactSpace (AdeleQuotient F)]

/-- `A` is weakly associated with the actual full cuspidal class `π` of `GL_{r+1}` over `F`:
some spectral system genuinely attached to `π` by a cuspidal spectral presentation is weakly
associated with `A`. -/
def IsWeaklyAssociatedClass {r : ℕ} (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (π : Automorphic.CuspidalOperatorRealization.IsoClass F r) : Prop :=
  ∃ s : SpectralSystem (FinitePlace F) (r + 1),
    Automorphic.CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{u, uP} π s ∧
      S.IsWeaklyAssociated A s

/-- The class relation depends only on the equivalence class of `A`. -/
theorem IsWeaklyAssociatedClass.of_equiv {r : ℕ}
    {A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup}
    {B : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup}
    {π : Automorphic.CuspidalOperatorRealization.IsoClass F r}
    (φ : FiniteRepresentation.Equiv A B) (hA : S.IsWeaklyAssociatedClass.{u, uV, uP} A π) :
    S.IsWeaklyAssociatedClass.{u, uW, uP} B π := by
  obtain ⟨s, hs, hA⟩ := hA
  exact ⟨s, hs, hA.of_equiv S φ⟩

/-- Relative class association gives absolute class association of the inflation, provided
local-to-global Weil maps exist at all but finitely many finite places. -/
theorem isWeaklyAssociatedClass_inflate {r : ℕ} {K : FiniteGaloisIntermediateField F Ω}
    {A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F K)}
    {π : Automorphic.CuspidalOperatorRealization.IsoClass F r}
    (hA : RelativeWeilGroup.IsWeaklyAssociatedClass.{u, uV, uP} A π)
    (hθ : ∀ᶠ v in Filter.cofinite,
      ∃ θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup, S.IsLocalWeilMap v θ) :
    S.IsWeaklyAssociatedClass.{u, uV, uP} (S.inflate K A) π := by
  obtain ⟨s, hs, hA⟩ := hA
  exact ⟨s, hs, S.isWeaklyAssociated_inflate hA hθ⟩

end Cuspidal

end WeilMapSystem

end Langlands.ClassField.Global
