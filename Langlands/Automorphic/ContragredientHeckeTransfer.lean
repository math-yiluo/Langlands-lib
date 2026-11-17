import Langlands.Automorphic.ContragredientSphericalSpectrum

/-! # Transfer of spherical Hecke scalars through a contragredient pairing

See the paired Markdown for the statements and the route.
-/

noncomputable section
universe uF uV uW

/-! ### Local part: Hecke scalars through an invariant pairing -/

namespace Langlands.Unramified

open Correspondence MeasureTheory MeasureTheory.Measure GeneralLinear.Iwasawa MinusculeCosets

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

namespace PairedHecke

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- **Adjointness of the standard Hecke elements.** If `b` is a spherical eigenvector of the
standard Hecke elements with scalars `l'`, then for every spherical `a` paired with it by an
invariant pairing, `l'_j B(a, b) = l'_n B(T_(n-j) a, b)`. -/
theorem scalar_mul_pairing_eq (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (hσ : IsSmooth σ) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g x y, B (ρ g x) (σ g y) = B x y)
    (a : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup)
    (b : fixedVectors σ (sphericalOpenSubgroup F r).toSubgroup) (l' : Fin (r + 2) → ℂ)
    (hb : ∀ i, corner F σ hσ (standardHeckeElement F r i) b = l' i • b) (j : Fin (r + 2)) :
    l' j * B a b =
      l' (Fin.last (r + 1)) * B (corner F ρ hρ (standardHeckeElement F r j.rev) a : V) b := by
  set t := standardDiagonal F r (Fin.last (r + 1)) with ht
  set θ := sphericalInverseTranspose F r
  let K := sphericalOpenSubgroup F r
  let c : GeneralLinear (r + 1) F.Carrier → ℂ := fun g => B (ρ g a) b
  have hfixa : ∀ k : K, ρ k a = a := fun k => a.property ⟨k, k.2⟩
  have hfixb : ∀ k : K, σ k b = b := fun k => b.property ⟨k, k.2⟩
  have hc : ∀ (k₁ k₂ : K) g, c (k₁ * g * k₂) = c g := by
    intro k₁ k₂ g
    change B (ρ (k₁ * g * k₂) a) b = B (ρ g a) b
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfixa k₂]
    conv_lhs => rw [← hfixb k₁]
    exact hB _ _ _
  have htb : σ t b = l' (Fin.last (r + 1)) • (b : W) := by
    rw [← corner_last F σ hσ, hb]
    rfl
  have hct : ∀ g, c g = l' (Fin.last (r + 1)) * c (t * g) := by
    intro g
    change B (ρ g a) b = _ * B (ρ (t * g) a) b
    rw [← hB t (ρ g a) b, htb, map_smul, smul_eq_mul, map_mul, Module.End.mul_apply]
  have hsym : ∀ u, standardHeckeElement F r j (θ u) * c (θ u)⁻¹ =
      standardHeckeElement F r j u⁻¹ * c u := by
    intro u
    obtain ⟨k₁, k₂, hu⟩ := sphericalInverseTranspose_mem_doubleCoset_inv F r u
    rw [hu, Hecke.HeckeAlgebra.Corner.apply_mul_mul]
    congr 1
    have e : ((k₁ : GeneralLinear (r + 1) F.Carrier) * u⁻¹ * k₂)⁻¹ =
        (k₂⁻¹ : K) * u * (k₁⁻¹ : K) := by
      simp [mul_assoc]
    rw [e, hc]
  have h1 : l' j * B a b = ∫ g, standardHeckeElement F r j g * c g⁻¹ ∂(sphericalHaar F r) := by
    have h := functional_corner F σ hσ (standardHeckeElement F r j) b (B a)
    rw [hb, Submodule.coe_smul, map_smul, smul_eq_mul] at h
    rw [h]
    congr 1
    funext g
    congr 1
    change B a (σ g b) = B (ρ g⁻¹ a) b
    rw [← hB g⁻¹ a (σ g b), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  have h2 : ∫ g, standardHeckeElement F r j.rev g * c g ∂(sphericalHaar F r) =
      B (corner F ρ hρ (standardHeckeElement F r j.rev) a : V) b :=
    (functional_corner F ρ hρ (standardHeckeElement F r j.rev) a (B.flip b)).symm
  calc l' j * B a b
      = ∫ g, standardHeckeElement F r j g * c g⁻¹ ∂(sphericalHaar F r) := h1
    _ = ∫ u, standardHeckeElement F r j (θ u) * c (θ u)⁻¹ ∂(sphericalHaar F r) :=
        ((sphericalHaar_measurePreserving_inverseTranspose F r).integral_comp
          θ.toHomeomorph.measurableEmbedding
          (fun g => standardHeckeElement F r j g * c g⁻¹)).symm
    _ = ∫ u, l' (Fin.last (r + 1)) *
          (standardHeckeElement F r j.rev (t * u) * c (t * u)) ∂(sphericalHaar F r) := by
        congr 1
        funext u
        rw [hsym, standardHeckeElement_inv, ← ht, hct u]
        ring
    _ = l' (Fin.last (r + 1)) * B (corner F ρ hρ (standardHeckeElement F r j.rev) a : V) b := by
        rw [integral_const_mul, integral_mul_left_eq_self
          (fun u => standardHeckeElement F r j.rev u * c u) t, h2]

section Polynomial

open Polynomial

/-- The standard Hecke scalars of the inverse spectrum:
`λ_i(s⁻¹) λ_n(s) = λ_(n-i)(s)`. -/
theorem standardHeckeScalar_map_inv_mul_last (s : Eigenvalues (r + 1)) (i : Fin (r + 2)) :
    standardHeckeScalar F (s.map fun z => z⁻¹) i * standardHeckeScalar F s (Fin.last (r + 1)) =
      standardHeckeScalar F s i.rev := by
  set P := Eigenvalues.eulerPolynomial s with hP
  set Q := Eigenvalues.eulerPolynomial (s.map fun z => z⁻¹) with hQ
  set d := ((s : Multiset ℂˣ).map fun z : ℂˣ => -(z : ℂ)).prod with hd
  have hrev : C d * Q = P.reverse := C_mul_eulerPolynomial_map_inv s
  have hnat : P.natDegree = r + 1 := Eigenvalues.eulerPolynomial_natDegree s
  have hcoef : ∀ k : ℕ, k ≤ r + 1 → d * Q.coeff k = P.coeff (r + 1 - k) := by
    intro k hk
    have e := congrArg (fun f : ℂ[X] => f.coeff k) hrev
    simp only [coeff_C_mul, coeff_reverse, hnat] at e
    rw [e, revAt_le hk]
  have hd' : P.coeff (r + 1) = d := by
    have e := hcoef 0 (Nat.zero_le _)
    rw [Nat.sub_zero, coeff_zero_eq_eval_zero, hQ, Eigenvalues.eulerPolynomial_eval_zero,
      mul_one] at e
    exact e.symm
  have hi := i.isLt
  obtain ⟨m, hm⟩ : ∃ m, r + 1 = i.val + m := ⟨r + 1 - i.val, by omega⟩
  have hrv : (i.rev : ℕ) = m := by rw [Fin.val_rev]; omega
  simp only [standardHeckeScalar, elementaryCoefficient, Fin.val_last, Nat.sub_self, mul_zero,
    pow_zero, one_mul, hrv]
  rw [← hQ, ← hP, hd', show r + 1 - m = i.val by omega, show r + 1 - i.val = m by omega]
  have hc := hcoef i.val (by omega)
  rw [show r + 1 - i.val = m by omega] at hc
  rw [← hc, hm, pow_add, Nat.mul_comm m]
  have hs : ((-1 : ℂ) ^ (i : ℕ)) * (-1) ^ (i : ℕ) = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination
    (Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ^ ((i : ℕ) * m) *
      (-1) ^ m * (d * Q.coeff i) * hs

end Polynomial

/-- **Hecke scalars through a nondegenerate invariant pairing.** If every spherical vector of
`σ` has the standard Hecke scalars of `s`, and the left kernel of an invariant pairing of `ρ`
with `σ` is zero, then every spherical vector of `ρ` has the standard Hecke scalars of the
inverse spectrum `s⁻¹`. -/
theorem corner_eq_smul_of_pairing (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (hσ : IsSmooth σ) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g x y, B (ρ g x) (σ g y) = B x y)
    (hleft : ∀ x : V, (∀ y : W, B x y = 0) → x = 0) (s : Eigenvalues (r + 1))
    (hs : ∀ (b : fixedVectors σ (sphericalOpenSubgroup F r).toSubgroup) (i : Fin (r + 2)),
      corner F σ hσ (standardHeckeElement F r i) b = standardHeckeScalar F s i • b)
    (a : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup) (i : Fin (r + 2)) :
    corner F ρ hρ (standardHeckeElement F r i) a =
      standardHeckeScalar F (s.map fun z => z⁻¹) i • a := by
  have hB' : ∀ g y x, B.flip (σ g y) (ρ g x) = B.flip y x := fun g y x => hB g x y
  apply Subtype.ext
  rw [← sub_eq_zero]
  apply hleft
  intro y
  set w : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup :=
    corner F ρ hρ (standardHeckeElement F r i) a -
      standardHeckeScalar F (s.map fun z => z⁻¹) i • a with hw
  have ew : (corner F ρ hρ (standardHeckeElement F r i) a : V) -
      ((standardHeckeScalar F (s.map fun z => z⁻¹) i • a :
        fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup) : V) = (w : V) := by
    rw [hw, Submodule.coe_sub]
  rw [ew]
  have e := pairing_sphericalProjection F σ hσ ρ B.flip hB' y w
  rw [LinearMap.flip_apply, LinearMap.flip_apply] at e
  rw [← e]
  set b := sphericalProjection F σ hσ y
  have hadj := scalar_mul_pairing_eq F ρ hρ σ hσ B hB a b _ (hs b) i.rev
  rw [Fin.rev_rev] at hadj
  have hlast : standardHeckeScalar F s (Fin.last (r + 1)) ≠ 0 := by
    have hc : (Eigenvalues.eulerPolynomial s).coeff (r + 1) ≠ 0 := by
      have h := Polynomial.leadingCoeff_ne_zero.mpr (Eigenvalues.eulerPolynomial_ne_zero s)
      rwa [Polynomial.leadingCoeff, Eigenvalues.eulerPolynomial_natDegree] at h
    rw [standardHeckeScalar, elementaryCoefficient, Fin.val_last, Nat.sub_self, mul_zero,
      pow_zero, one_mul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hc
  have hsc := standardHeckeScalar_map_inv_mul_last F s i
  apply mul_left_cancel₀ hlast
  rw [hw, Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, mul_zero, mul_sub, ← hadj, ← mul_assoc,
    mul_comm (standardHeckeScalar F s (Fin.last (r + 1))), hsc, sub_self]

end PairedHecke

end Langlands.Unramified

/-! ### Global part: the left kernel of a contragredient pairing -/

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified

variable {F : Type uF} [Field F] [NumberField F]

local instance heckeTransferRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeTransferContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTransferSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTransferFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance heckeTransferStableAddCommGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance heckeTransferRealizationAddCommGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

set_option maxHeartbeats 2000000 in
/-- A subspace stable under the real Lie algebra operators is stable under the generators
`ι(Y)`, `Y ∈ ℂ ⊗_ℝ 𝔤`, of the enveloping algebra; the generator `z ⊗ X` is `z • (1 ⊗ X)`. -/
theorem envelopingGenerator_mem_of_lieAction (S : OperatorRealization F n)
    (N : Submodule ℂ S.Space)
    (hN : ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (f : S.Space), f ∈ N → S.lieAction X f ∈ N)
    (Y : ArchimedeanGL.ComplexLieAlgebra F n) (f : S.Space) (hf : f ∈ N) :
    S.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ Y) f ∈ N := by
  revert f
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    intro f hf
    have hz : (z ⊗ₜ[ℝ] X : ArchimedeanGL.ComplexLieAlgebra F n) =
        z • ArchimedeanGL.complexify F n X := by
      rw [ArchimedeanGL.complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hX := hN X f hf
    change S.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ
        (ArchimedeanGL.complexify F n X)) f ∈ N at hX
    have h1 : (UniversalEnvelopingAlgebra.ι ℂ (z ⊗ₜ[ℝ] X : ArchimedeanGL.ComplexLieAlgebra F n) :
        ArchimedeanGL.EnvelopingAlgebra F n) =
        z • UniversalEnvelopingAlgebra.ι ℂ (ArchimedeanGL.complexify F n X) := by
      rw [hz]
      exact map_smul _ _ _
    have h2 : S.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ (z ⊗ₜ[ℝ] X)) f =
        z • S.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ
          (ArchimedeanGL.complexify F n X)) f := by
      rw [h1, map_smul]
      rfl
    rw [h2]
    exact N.smul_mem z hX
  | add Y₁ Y₂ h₁ h₂ =>
    intro f hf
    have h3 : S.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ (Y₁ + Y₂)) f =
        S.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ Y₁) f +
          S.envelopingAction (UniversalEnvelopingAlgebra.ι ℂ Y₂) f := by
      rw [map_add, map_add]
      rfl
    rw [h3]
    exact N.add_mem (h₁ f hf) (h₂ f hf)

set_option maxHeartbeats 2000000 in
/-- A subspace stable under the real Lie algebra operators is stable under the whole
enveloping algebra. -/
theorem envelopingAction_mem_of_lieAction (S : OperatorRealization F n)
    (N : Submodule ℂ S.Space)
    (hN : ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (f : S.Space), f ∈ N → S.lieAction X f ∈ N)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space) (hf : f ∈ N) :
    S.envelopingAction a f ∈ N := by
  let A : Subalgebra ℂ (ArchimedeanGL.EnvelopingAlgebra F n) :=
    { carrier := {a | ∀ f ∈ N, S.envelopingAction a f ∈ N}
      mul_mem' := fun {a b} ha hb f hf => by
        have e : S.envelopingAction (a * b) f = S.envelopingAction a (S.envelopingAction b f) := by
          rw [map_mul]
          rfl
        rw [e]
        exact ha _ (hb f hf)
      add_mem' := fun {a b} ha hb f hf => by
        have e : S.envelopingAction (a + b) f = S.envelopingAction a f + S.envelopingAction b f := by
          rw [map_add]
          rfl
        rw [e]
        exact N.add_mem (ha f hf) (hb f hf)
      algebraMap_mem' := fun z f hf => by
        have e : S.envelopingAction (algebraMap ℂ _ z) f = z • f := by
          rw [AlgHom.commutes]
          rfl
        rw [e]
        exact N.smul_mem z hf }
  have key : ∀ t : TensorAlgebra ℂ (ArchimedeanGL.ComplexLieAlgebra F n),
      UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t ∈ A := by
    intro t
    induction t using TensorAlgebra.induction with
    | algebraMap z =>
      rw [AlgHom.commutes]
      exact A.algebraMap_mem z
    | ι Y =>
      exact fun f hf => S.envelopingGenerator_mem_of_lieAction N hN Y f hf
    | mul x y hx hy =>
      rw [map_mul]
      exact A.mul_mem hx hy
    | add x y hx hy =>
      rw [map_add]
      exact A.add_mem hx hy
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ArchimedeanGL.ComplexLieAlgebra F n)) a
  exact key t f hf

section Kernel

variable {S T : OperatorRealization F n}

/-- The left kernel `{x | ∀ y, B x y = 0}` of a pairing. -/
def leftKernel (B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ) : Submodule ℂ S.Space where
  carrier := {x | ∀ y, B x y = 0}
  add_mem' := fun {a b} ha hb y => by
    rw [map_add, LinearMap.add_apply, ha y, hb y, add_zero]
  zero_mem' := fun y => by
    rw [map_zero, LinearMap.zero_apply]
  smul_mem' := fun c a ha y => by
    rw [map_smul, LinearMap.smul_apply, ha y, smul_zero]

theorem mem_leftKernel (B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ) (x : S.Space) :
    x ∈ leftKernel B ↔ ∀ y, B x y = 0 := Iff.rfl

variable {B : S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ}

theorem finiteRepresentation_mem_leftKernel (hB : S.IsInvariantPairing T B)
    (d : FiniteAdelicGL F n) (f : S.Space) (hf : f ∈ leftKernel B) :
    S.finiteRepresentation d f ∈ leftKernel B := by
  intro y
  have e : T.finiteRepresentation d (T.finiteRepresentation d⁻¹ y) = y := by
    rw [T.finiteRepresentation_mul_apply, mul_inv_cancel, map_one, Module.End.one_apply]
  exact (congrArg (B (S.finiteRepresentation d f)) e).symm.trans
    ((hB.1 d f (T.finiteRepresentation d⁻¹ y)).trans (hf _))

theorem compactRepresentation_mem_leftKernel (hB : S.IsInvariantPairing T B)
    (k : standardInfiniteCompact F n) (f : S.Space) (hf : f ∈ leftKernel B) :
    S.compactRepresentation k f ∈ leftKernel B := by
  intro y
  have e : T.compactRepresentation k (T.compactRepresentation k⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  exact (congrArg (B (S.compactRepresentation k f)) e).symm.trans
    ((hB.2.1 k f (T.compactRepresentation k⁻¹ y)).trans (hf _))

theorem lieAction_mem_leftKernel (hB : S.IsInvariantPairing T B)
    (X : ArchimedeanGL.RealLieAlgebra F n) (f : S.Space) (hf : f ∈ leftKernel B) :
    S.lieAction X f ∈ leftKernel B := by
  intro y
  have e := hB.2.2 X f y
  have h0 : B f (T.lieAction X y) = 0 := hf _
  rw [h0, add_zero] at e
  exact e

set_option maxHeartbeats 2000000 in
/-- **The left kernel of a contragredient pairing is zero** when the first realization is
irreducible and the second is nonzero. -/
theorem eq_zero_of_isContragredientPairing (hB : S.IsContragredientPairing T B)
    (hS : S.IsIrreducible) {y₀ : T.Space} (hy₀ : y₀ ≠ 0) (x : S.Space)
    (hx : ∀ y : T.Space, B x y = 0) : x = 0 := by
  by_contra hne
  have hxk : x ∈ leftKernel B := hx
  have hN : leftKernel B ≠ ⊥ := fun h => hne ((Submodule.mem_bot ℂ).mp (h ▸ hxk))
  have htop : leftKernel B = ⊤ := S.eq_top_of_generatorStable hS (leftKernel B)
    (finiteRepresentation_mem_leftKernel hB.1) (compactRepresentation_mem_leftKernel hB.1)
    (fun a f hf => S.envelopingAction_mem_of_lieAction (leftKernel B)
      (lieAction_mem_leftKernel hB.1) a f hf) hN
  have hall : ∀ f : S.Space, B f y₀ = 0 := fun f =>
    (htop.symm ▸ Submodule.mem_top : f ∈ leftKernel B) y₀
  have hflip : B.flip y₀ = B.flip 0 := by
    apply LinearMap.ext
    intro f
    exact (hall f).trans (LinearMap.congr_fun (map_zero B.flip) f).symm
  exact hy₀ (hB.2.2.1 hflip)

end Kernel

section Transfer

variable (v : FinitePlace F)

local instance heckeTransferLocalTopology (m : ℕ) : TopologicalSpace (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology m
local instance heckeTransferLocalTopologicalGroup (m : ℕ) :
    IsTopologicalGroup (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup m
local instance heckeTransferLocalT2 (m : ℕ) : T2Space (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space m
local instance heckeTransferLocalMeasurable (m : ℕ) : MeasurableSpace (FiniteLocalGL F m v) :=
  borel _
local instance heckeTransferLocalBorel (m : ℕ) : BorelSpace (FiniteLocalGL F m v) := ⟨rfl⟩

/-- **Hecke scalars through a contragredient realization.** Let `S'` realize the
contragredient of an irreducible `S`. If every spherical vector of `S'` at `v` has the
standard Hecke scalars of `s` and `S'` has a nonzero spherical vector at `v`, then every
spherical vector of `S` at `v` has the standard Hecke scalars of `s⁻¹`. -/
theorem corner_eq_smul_of_isContragredientOf {r : ℕ} (S : OperatorRealization F (r + 1))
    {S' : OperatorRealization F (r + 1)} (h : S'.IsContragredientOf S) (hS : S.IsIrreducible)
    (s : Eigenvalues (r + 1))
    (hs : ∀ (b : fixedVectors (S'.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup) (i : Fin (r + 2)),
      PairedHecke.corner (CompletionPadic.padicField v) (S'.localRepresentation v)
          (S'.localRepresentation_isSmooth_canonical v)
          (standardHeckeElement (CompletionPadic.padicField v) r i) b =
        standardHeckeScalar (CompletionPadic.padicField v) s i • b)
    (b : fixedVectors (S'.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup) (hb : b ≠ 0)
    (a : fixedVectors (S.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup) (i : Fin (r + 2)) :
    PairedHecke.corner (CompletionPadic.padicField v) (S.localRepresentation v)
        (S.localRepresentation_isSmooth_canonical v)
        (standardHeckeElement (CompletionPadic.padicField v) r i) a =
      standardHeckeScalar (CompletionPadic.padicField v) (s.map fun z => z⁻¹) i • a :=
  h.elim fun B hBc =>
    PairedHecke.corner_eq_smul_of_pairing (CompletionPadic.padicField v)
      (S.localRepresentation v) (S.localRepresentation_isSmooth_canonical v)
      (S'.localRepresentation v) (S'.localRepresentation_isSmooth_canonical v) B
      (fun g x y => hBc.1.1 (localInclusion F (r + 1) v g) x y)
      (fun x hx => eq_zero_of_isContragredientPairing hBc hS
        (fun h0 => hb (Subtype.ext h0)) x hx) s hs a i

end Transfer

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

local instance heckeTransferTopology (v : FinitePlace F) (m : ℕ) :
    TopologicalSpace (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology m
local instance heckeTransferTopologicalGroup (v : FinitePlace F) (m : ℕ) :
    IsTopologicalGroup (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup m
local instance heckeTransferT2 (v : FinitePlace F) (m : ℕ) : T2Space (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space m
local instance heckeTransferMeasurable (v : FinitePlace F) (m : ℕ) :
    MeasurableSpace (FiniteLocalGL F m v) :=
  borel _
local instance heckeTransferBorel (v : FinitePlace F) (m : ℕ) :
    BorelSpace (FiniteLocalGL F m v) := ⟨rfl⟩

/-- **Hecke scalars of `T` from a presentation of its contragredient.** If `Td` realizes the
contragredient of `T` and `Pd` is a spectral presentation of `Td`, then at every finite place
`v` outside the exceptional set of `Pd`, every spherical vector of `T` at `v` has the
standard Hecke scalars of the inverse of the presented spectrum of `Td` at `v`. -/
theorem corner_eq_smul_of_contragredient_presentation (T Td : CuspidalOperatorRealization F r)
    (h : Td.realization.IsContragredientOf T.realization)
    (Pd : CuspidalSpectralPresentation.{uF, uV} Td) (v : FinitePlace F)
    (hv : v ∉ Pd.exceptional)
    (a : fixedVectors (T.realization.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup)
    (i : Fin (r + 2)) :
    PairedHecke.corner (CompletionPadic.padicField v) (T.realization.localRepresentation v)
        (T.realization.localRepresentation_isSmooth_canonical v)
        (standardHeckeElement (CompletionPadic.padicField v) r i) a =
      standardHeckeScalar (CompletionPadic.padicField v)
        ((Pd.spectralSystem.eigenvalues v hv).map fun z => z⁻¹) i • a :=
  (Pd.exists_spherical_ne_zero v hv).elim fun b hb =>
    T.realization.corner_eq_smul_of_isContragredientOf v h T.irreducible _
      (Pd.corner_eq_smul v hv) b hb a i

end CuspidalOperatorRealization

end Langlands.Automorphic
