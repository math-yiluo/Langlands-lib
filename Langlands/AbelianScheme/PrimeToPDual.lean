import Langlands.AbelianScheme.PrimeToP
import Langlands.AbelianScheme.PolarizedFiniteLevel.Data
import Langlands.AlgebraicGeometry.Picard.DualMapRational
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeMapAdditivityProof

/-! # Duals, prime-to-`p` polarizations and the Rosati equation up to prime-to-`p` isogeny -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (P : Prerequisites.{u}) {S : Scheme.{u}} {A B C : AbelianScheme S}

/-- Actual dualization of homomorphisms is additive, for any dual witnesses. This is the
published theorem `dualSchemeMap_add`, whose two hypotheses are proved in the Library. -/
theorem DualWitness.additivity (WA : DualWitness A) (WB : DualWitness B) :
    DualSchemeMapAdditivity P.preservation P.stability A B WA.hasDual WB.hasDual :=
  fun f g => dualSchemeMap_add P.preservation picardZeroLineBundleClassification P.stability
    Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions WA.hasDual WB.hasDual f g

/-- The actual dual homomorphism `f ↦ f^∨`, bundled as an additive map. -/
def DualWitness.mapAddHom (WA : DualWitness A) (WB : DualWitness B) :
    (A ⟶ B) →+ (WB.dual P ⟶ WA.dual P) :=
  dualAbelianSchemeMapAddHom P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability WA.hasDual WB.hasDual (WA.additivity P WB)
    WA.inverseBundle WA.evaluation WB.inverseBundle WB.evaluation WA.geometry WB.geometry

@[simp] theorem DualWitness.mapAddHom_apply (WA : DualWitness A) (WB : DualWitness B)
    (f : A ⟶ B) : WA.mapAddHom P WB f = WA.map P WB f := rfl

variable (p : ℕ) [Fact p.Prime]

/-- The dual of a `ℤ_(p)`-localized homomorphism: the `ℤ_(p)`-linear extension of the actual
dual map, `r ⊗ f ↦ r ⊗ f^∨`. -/
def DualWitness.dualP (WA : DualWitness A) (WB : DualWitness B) :
    HomP p A B →ₗ[PrimeLocalIntegers p] HomP p (WB.dual P) (WA.dual P) :=
  CoefficientExtension.extendAddHom (PrimeLocalIntegers p) (WA.mapAddHom P WB)

@[simp] theorem DualWitness.dualP_tmul (WA : DualWitness A) (WB : DualWitness B)
    (r : PrimeLocalIntegers p) (f : A ⟶ B) :
    WA.dualP P p WB (r ⊗ₜ[ℤ] f) = r ⊗ₜ[ℤ] WA.map P WB f := rfl

@[simp] theorem DualWitness.dualP_homToHomP (WA : DualWitness A) (WB : DualWitness B)
    (f : A ⟶ B) : WA.dualP P p WB (homToHomP p f) = homToHomP p (WA.map P WB f) := rfl

/-- The localized dual of the identity is the identity. -/
@[simp] theorem DualWitness.dualP_idP (W : DualWitness A) :
    W.dualP P p W (idP p A) = idP p (W.dual P) := by
  change (1 : PrimeLocalIntegers p) ⊗ₜ[ℤ] W.map P W (𝟙 A) = _
  rw [DualWitness.map_id]
  rfl

/-- The localized dual reverses composition. -/
theorem DualWitness.dualP_compP (WA : DualWitness A) (WB : DualWitness B) (WC : DualWitness C)
    (f : HomP p A B) (g : HomP p B C) :
    WA.dualP P p WC (compP p A B C f g) =
      compP p _ _ _ (WB.dualP P p WC g) (WA.dualP P p WB f) := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp only [map_add, LinearMap.add_apply, hf, hf']
  | tmul r f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp only [map_add, LinearMap.add_apply, hg, hg']
    | tmul s g =>
      simp only [compP_tmul, DualWitness.dualP_tmul, DualWitness.map_comp P WA WB WC, mul_comm]

/-- The localized dual is compatible with the existing rational dual, through `ℤ_(p) ⊆ ℚ`. -/
theorem DualWitness.homPToHom0_dualP (WA : DualWitness A) (WB : DualWitness B)
    (f : HomP p A B) :
    homPToHom0 p _ _ (WA.dualP P p WB f) =
      dualHom0 P.preservation P.composition P.unitCoherence P.associativity P.comparison
        P.symmetry P.stability WA.hasDual WB.hasDual (WA.additivity P WB) WA.inverseBundle
        WA.evaluation WB.inverseBundle WB.evaluation WA.geometry WB.geometry
        (homPToHom0 p A B f) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    rw [map_add, map_add, hf, hg, map_add (homPToHom0 p A B), map_add]
    rfl
  | tmul r f => simp; rfl

/-! ## Prime-to-`p` polarizations -/

/-- A prime-to-`p` polarization of `A` in the localized category: an isomorphism of the
localized category (a `ℤ_(p)`-isogeny) which some natural number `N` prime to `p` carries to an
actual polarization that is an actual prime-to-`p` isogeny. Since `N` is a unit of `ℤ_(p)`, the
localized homomorphism is the actual polarization divided by `N`; no isogeny of degree divisible
by `p` is inverted. Invertibility is required separately: with one global denominator it does
not follow from the fibrewise degree condition over every base. -/
def DualWitness.IsPrimeToPPolarization (W : DualWitness A) (lam : HomP p A (W.dual P)) :
    Prop :=
  IsPrimeToPQuasiIsogeny p lam ∧
    ∃ (N : ℕ) (μ : A ⟶ W.dual P), N.Coprime p ∧ W.IsPolarization P μ ∧
      IsPrimeToPIsogeny p μ ∧ (N : PrimeLocalIntegers p) • lam = homToHomP p μ

/-- A prime-to-`p` polarization is invertible in the localized category. -/
theorem DualWitness.IsPrimeToPPolarization.isPrimeToPQuasiIsogeny {W : DualWitness A}
    {lam : HomP p A (W.dual P)} (h : W.IsPrimeToPPolarization P p lam) :
    IsPrimeToPQuasiIsogeny p lam :=
  h.1

/-- Equivalently, the actual numerator `μ = N • λ` is itself invertible in the localized
category. -/
theorem DualWitness.isPrimeToPPolarization_iff (W : DualWitness A) (lam : HomP p A (W.dual P)) :
    W.IsPrimeToPPolarization P p lam ↔
      ∃ (N : ℕ) (μ : A ⟶ W.dual P), N.Coprime p ∧ W.IsPolarization P μ ∧
        IsPrimeToPIsogeny p μ ∧ IsPrimeToPQuasiIsogeny p (homToHomP p μ) ∧
          (N : PrimeLocalIntegers p) • lam = homToHomP p μ := by
  constructor
  · rintro ⟨hiso, N, μ, hN, hμ, hdeg, hlam⟩
    refine ⟨N, μ, hN, hμ, hdeg, ?_, hlam⟩
    rw [← hlam, ← (PrimeLocalIntegers.isUnit_natCast p hN).unit_spec]
    exact hiso.unit_smul _
  · rintro ⟨N, μ, hN, hμ, hdeg, hiso, hlam⟩
    refine ⟨?_, N, μ, hN, hμ, hdeg, hlam⟩
    rw [← hlam, ← (PrimeLocalIntegers.isUnit_natCast p hN).unit_spec] at hiso
    exact (isPrimeToPQuasiIsogeny_unit_smul_iff p _ lam).1 hiso

/-- An actual polarization of prime-to-`p` degree that is invertible in the localized category
is a prime-to-`p` polarization. -/
theorem DualWitness.isPrimeToPPolarization_homToHomP (W : DualWitness A) {μ : A ⟶ W.dual P}
    (hμ : W.IsPolarization P μ) (hdeg : IsPrimeToPIsogeny p μ)
    (hiso : IsPrimeToPQuasiIsogeny p (homToHomP p μ)) :
    W.IsPrimeToPPolarization P p (homToHomP p μ) :=
  ⟨hiso, 1, μ, Nat.coprime_one_left p, hμ, hdeg, by simp⟩

open scoped CategoryTheory.MonObj in
/-- An actual polarization of prime-to-`p` degree whose kernel is killed by one natural number
prime to `p` is a prime-to-`p` polarization. -/
theorem DualWitness.isPrimeToPPolarization_homToHomP_of_kernel (W : DualWitness A)
    {pol : A ⟶ W.dual P} (hpol : W.IsPolarization P pol) (hdeg : IsPrimeToPIsogeny p pol)
    {n : ℕ} (hn : n.Coprime p)
    (hker : GroupScheme.multiplication (GroupScheme.kernel (AbelianScheme.groupHom pol))
      (n : ℤ) = 1) :
    W.IsPrimeToPPolarization P p (homToHomP p pol) :=
  W.isPrimeToPPolarization_homToHomP P p hpol hdeg
    (isPrimeToPQuasiIsogeny_of_kernel p pol hdeg.1 hn hker)

/-- The Rosati equation for an action `i` of a ring with involution `τ` on the localized
endomorphisms, with respect to `λ`: `i(τ b) ≫ λ = λ ≫ i(b)^∨` for every `b`. Equivalently,
`i(τ b)` is the conjugate `λ⁻¹ ∘ i(b)^∨ ∘ λ` whenever `λ` is invertible. -/
def DualWitness.RosatiCompatible {O : Type*} [Ring O] (τ : O → O) (W : DualWitness A)
    (lam : HomP p A (W.dual P)) (i : O →+* EndP p A) : Prop :=
  ∀ b : O, compP p A A (W.dual P) (i (τ b)).asHom lam =
    compP p A (W.dual P) (W.dual P) lam (W.dualP P p W (i b).asHom)

/-- Conjugation by an invertible localized `λ` after dualization: `f ↦ λ ≫ f^∨ ≫ λ⁻¹` in
diagrammatic order, that is `λ⁻¹ ∘ f^∨ ∘ λ`. It fixes the identity and reverses composition.
For a symmetric `λ` (equal to its dual under the canonical biduality) this formula is the Rosati
involution of Kottwitz §9; for a general invertible `λ` it need not be involutive. -/
def DualWitness.rosatiP (W : DualWitness A) {lam : HomP p A (W.dual P)}
    (hlam : IsPrimeToPQuasiIsogeny p lam) (f : HomP p A A) : HomP p A A :=
  compP p A (W.dual P) A lam (compP p (W.dual P) (W.dual P) A (W.dualP P p W f) hlam.invP)

@[simp] theorem DualWitness.rosatiP_idP (W : DualWitness A) {lam : HomP p A (W.dual P)}
    (hlam : IsPrimeToPQuasiIsogeny p lam) : W.rosatiP P p hlam (idP p A) = idP p A := by
  simp [DualWitness.rosatiP]

/-- Conjugation by `λ` after dualization reverses composition. -/
theorem DualWitness.rosatiP_compP (W : DualWitness A) {lam : HomP p A (W.dual P)}
    (hlam : IsPrimeToPQuasiIsogeny p lam) (f g : HomP p A A) :
    W.rosatiP P p hlam (compP p A A A f g) =
      compP p A A A (W.rosatiP P p hlam g) (W.rosatiP P p hlam f) := by
  simp only [DualWitness.rosatiP, DualWitness.dualP_compP P p W W W, compP_assoc]
  rw [← compP_assoc p hlam.invP lam, hlam.invP_compP, idP_compP]

/-- For an invertible `λ`, the Rosati equation says exactly that `i(τ b)` is the conjugate
`λ⁻¹ ∘ i(b)^∨ ∘ λ` of `i(b)`. -/
theorem DualWitness.rosatiCompatible_iff {O : Type*} [Ring O] (τ : O → O) (W : DualWitness A)
    {lam : HomP p A (W.dual P)} (hlam : IsPrimeToPQuasiIsogeny p lam) (i : O →+* EndP p A) :
    W.RosatiCompatible P p τ lam i ↔ ∀ b : O, (i (τ b)).asHom = W.rosatiP P p hlam (i b).asHom := by
  refine forall_congr' fun b => ⟨fun h => ?_, fun h => ?_⟩
  · calc (i (τ b)).asHom = compP p A A A (i (τ b)).asHom (idP p A) := (compP_idP p _).symm
      _ = compP p A (W.dual P) A (compP p A A (W.dual P) (i (τ b)).asHom lam) hlam.invP := by
          rw [compP_assoc, hlam.compP_invP]
      _ = W.rosatiP P p hlam (i b).asHom := by
          rw [h, compP_assoc]
          rfl
  · rw [h, DualWitness.rosatiP, compP_assoc, compP_assoc, hlam.invP_compP, compP_idP]

/-- For a prime-to-`p` polarization, the Rosati equation is conjugation by `λ` after
dualization. -/
theorem DualWitness.IsPrimeToPPolarization.rosatiCompatible_iff {O : Type*} [Ring O]
    (τ : O → O) {W : DualWitness A} {lam : HomP p A (W.dual P)}
    (h : W.IsPrimeToPPolarization P p lam) (i : O →+* EndP p A) :
    W.RosatiCompatible P p τ lam i ↔
      ∀ b : O, (i (τ b)).asHom = W.rosatiP P p h.isPrimeToPQuasiIsogeny (i b).asHom :=
  W.rosatiCompatible_iff P p τ h.isPrimeToPQuasiIsogeny i

/-- The pullback `e^* λ' = e ≫ λ' ≫ e^∨` of a localized homomorphism to a dual. -/
def DualWitness.pullbackP (WA : DualWitness A) (WB : DualWitness B) (e : HomP p A B)
    (lam : HomP p B (WB.dual P)) : HomP p A (WA.dual P) :=
  compP p A (WB.dual P) (WA.dual P) (compP p A B (WB.dual P) e lam) (WA.dualP P p WB e)

@[simp] theorem DualWitness.pullbackP_idP (W : DualWitness A) (lam : HomP p A (W.dual P)) :
    W.pullbackP P p W (idP p A) lam = lam := by
  simp [DualWitness.pullbackP]

/-- Pullback is contravariantly functorial: `(f ≫ g)^* = f^* ∘ g^*`. -/
theorem DualWitness.pullbackP_compP (WA : DualWitness A) (WB : DualWitness B)
    (WC : DualWitness C) (f : HomP p A B) (g : HomP p B C) (lam : HomP p C (WC.dual P)) :
    WA.pullbackP P p WC (compP p A B C f g) lam =
      WA.pullbackP P p WB f (WB.pullbackP P p WC g lam) := by
  simp only [DualWitness.pullbackP, DualWitness.dualP_compP P p WA WB WC, compP_assoc]

/-- Pullback is `ℤ_(p)`-linear in the homomorphism to the dual. -/
theorem DualWitness.pullbackP_smul (WA : DualWitness A) (WB : DualWitness B) (e : HomP p A B)
    (r : PrimeLocalIntegers p) (lam : HomP p B (WB.dual P)) :
    WA.pullbackP P p WB e (r • lam) = r • WA.pullbackP P p WB e lam := by
  simp only [DualWitness.pullbackP, map_smul, LinearMap.smul_apply]

end Langlands.AbelianScheme.PolarizedFiniteLevel
