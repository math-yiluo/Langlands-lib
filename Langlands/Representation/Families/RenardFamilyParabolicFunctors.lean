import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Renard VI.8.2–VI.8.3: base change, parabolic induction and Jacquet modules of families

A family over a commutative `ℂ`-algebra `B` is a `B`-linear representation, as in
`RenardFamilyStatements`. This file defines, for an arbitrary such `B`:

* the base change `C ⊗[B] V` of a family along a `B`-algebra `C`;
* normalized parabolic induction `i_P^G` and the normalized Jacquet module `r_P^G` for an
  actual semidirect decomposition `P = M ⋉ U` with `U` closed, the half-modulus characters
  of the Levi taking constant values in `B`; induction inflates the normalized Levi family
  along the projection `P →* M`, giving Renard's covariance (VI.1.2.3);
* their transports to the rational points of a represented parabolic `P = MN` of `G`.

No flatness, finiteness or base-change isomorphism is asserted.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

universe u uB uC uH uG uV

section BaseChange

variable {B : Type uB} [CommRing B] (C : Type uC) [CommRing C] [Algebra B C]
  {H : Type uH} [Group H] {V : Type uV} [AddCommGroup V] [Module B V]

/-- Base change of a family from `B` to a `B`-algebra `C`: the group acts on `C ⊗[B] V`
by `1 ⊗ ρ(g)`. -/
def baseChange (ρ : Representation B H V) : Representation C H (C ⊗[B] V) :=
  (Module.End.baseChangeHom B C V).toMonoidHom.comp ρ

@[simp] theorem baseChange_tmul (ρ : Representation B H V) (h : H) (c : C) (v : V) :
    baseChange C ρ h (c ⊗ₜ[B] v) = c ⊗ₜ[B] ρ h v :=
  rfl

end BaseChange

section Characters

variable (B : Type uB) [CommRing B] [Algebra ℂ B]

/-- The constant `B`-valued image of a complex unit-valued character. -/
def constantCharacter {H : Type uH} [Group H] (ψ : H →* ℂˣ) : H →* Bˣ :=
  (Units.map (algebraMap ℂ B).toMonoidHom).comp ψ

@[simp] theorem constantCharacter_val {H : Type uH} [Group H] (ψ : H →* ℂˣ) (h : H) :
    (constantCharacter B ψ h : B) = algebraMap ℂ B (ψ h : ℂ) :=
  rfl

/-- The kernel of a complex character lies in the kernel of its constant image. -/
theorem ker_le_constantCharacter_ker {H : Type uH} [Group H] (ψ : H →* ℂˣ) :
    ψ.ker ≤ (constantCharacter B ψ).ker := by
  intro h hh
  rw [MonoidHom.mem_ker] at hh ⊢
  simp [constantCharacter, hh]

/-- The constant image of a character with open kernel is a smooth `B`-valued character. -/
def constantSmoothCharacter {H : Type uH} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (ψ : H →* ℂˣ) (hψ : IsOpen (ψ.ker : Set H)) :
    Induction.SmoothCharacter B H where
  toMonoidHom := constantCharacter B ψ
  isOpen_ker := Subgroup.isOpen_mono (ker_le_constantCharacter_ker B ψ) hψ

end Characters

section Parabolic

variable (B : Type uB) [CommRing B] [Algebra ℂ B]
  {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}

/-- The positive half-modulus `c_U^{1/2}` of conjugation by the Levi on `U`, with constant
values in `B`. In Renard's reciprocal convention (VI.1.2) this is `δ_P^{-1/2}`. -/
def inductionCharacter (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) : Induction.SmoothCharacter B M :=
  constantSmoothCharacter B (HaarModulus.closedHalfCharacter U hU M hMU)
    (HaarModulus.isOpen_ker_closedHalfCharacter U hU M hMU)

/-- The inverse half-modulus `c_U^{-1/2}` on the Levi, with constant values in `B`. In
Renard's reciprocal convention (VI.1.2) this is `δ_P^{1/2}`. -/
def jacquetCharacter (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) : Induction.SmoothCharacter B M :=
  constantSmoothCharacter B (HaarModulus.closedInverseHalfCharacter U hU M hMU)
    (HaarModulus.isOpen_ker_closedInverseHalfCharacter U hU M hMU)

variable {B}

/-- The inducing representation of `P`: the normalized Levi family `m ↦ c_U(m)^{1/2} σ(m)`
inflated along the projection `P →* M`, so that `U` acts trivially. -/
abbrev inducingRepresentation (h : Aubert.General.IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) {V : Type uV} [AddCommGroup V] [Module B V]
    (σ : Representation B M V) : Representation B P V :=
  (Langlands.twist (inductionCharacter B U M hU h.levi_le_normalizer).toMonoidHom σ).comp
    h.projection

/-- The `B`-module of `i_P^G(σ)`: functions `f : G → V` with
`f(p g) = c_U(m(p))^{1/2} σ(m(p)) f(g)` and an open subgroup of right invariance. -/
abbrev Induced (h : Aubert.General.IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) {V : Type uV} [AddCommGroup V] [Module B V]
    (σ : Representation B M V) :=
  Induction.SmoothFunctions P (inducingRepresentation h hU σ)

/-- Normalized parabolic induction `i_P^G(σ)` over `B`: right translation on `Induced`. -/
def inducedRepresentation (h : Aubert.General.IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) {V : Type uV} [AddCommGroup V] [Module B V]
    (σ : Representation B M V) : Representation B G (Induced h hU σ) :=
  Induction.smoothInduced P (inducingRepresentation h hU σ)

/-- The `B`-module of `r_P^G(ρ)`: the `U`-coinvariants `V / V(U)`. -/
abbrev Jacquet {V : Type uV} [AddCommGroup V] [Module B V] (ρ : Representation B G V)
    (U : Subgroup G) :=
  Langlands.Jacquet.Localization.Coinvariants ρ U 1

/-- The normalized Jacquet module `r_P^G(ρ)` over `B`: `m · [v] = c_U(m)^{-1/2} [ρ(m) v]`. -/
def jacquetRepresentation {V : Type uV} [AddCommGroup V] [Module B V]
    (ρ : Representation B G V) (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) : Representation B M (Jacquet ρ U) :=
  Langlands.twist (jacquetCharacter B U M hU hMU).toMonoidHom
    (Langlands.Jacquet.Localization.action ρ U 1 M hMU
      (Langlands.Jacquet.Localization.isInvariant_one U M hMU))

section Laws

variable (h : Aubert.General.IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) {V : Type uV} [AddCommGroup V] [Module B V]

/-- The covariance of an induced function. -/
theorem induced_covariant (σ : Representation B M V) (f : Induced h hU σ) (p : P) (g : G) :
    Induction.eval P (inducingRepresentation h hU σ) f ((p : G) * g) =
      (inductionCharacter B U M hU h.levi_le_normalizer).toMonoidHom (h.projection p) •
        σ (h.projection p) (Induction.eval P (inducingRepresentation h hU σ) f g) :=
  f.1.2 p g

/-- Renard's covariance (VI.1.2.3): `f(m n g) = c_U(m)^{1/2} σ(m) f(g)` for `m ∈ M` and
`n ∈ U`. -/
theorem induced_covariant_levi_unipotent (σ : Representation B M V) (f : Induced h hU σ)
    (m : M) (n : U) (g : G) :
    Induction.eval P (inducingRepresentation h hU σ) f ((m : G) * (n : G) * g) =
      (inductionCharacter B U M hU h.levi_le_normalizer).toMonoidHom m •
        σ m (Induction.eval P (inducingRepresentation h hU σ) f g) := by
  have hc := induced_covariant h hU σ f (⟨m, h.levi_le m.2⟩ * ⟨n, h.unipotent_le n.2⟩) g
  rw [h.projection_mul] at hc
  exact hc

/-- With `U` unimodular, the inducing representation is the twist of `σ ∘ m` by the
constant half-modulus `c_U^{1/2}` on all of `P`, the character used by the published
complex `Aubert.General.normalizedInductionFunctor`. -/
theorem inducingRepresentation_eq_twist_of_isUnimodularModulus
    (hδ : Aubert.General.IsUnimodularModulus U hU) (σ : Representation B M V) :
    inducingRepresentation h hU σ =
      Langlands.twist
        (constantCharacter B (HaarModulus.closedHalfCharacter U hU P h.le_normalizer))
        (σ.comp h.projection) := by
  rw [Aubert.General.closedHalfCharacter_eq_comp_projection h hU hδ]
  rfl

/-- `G` acts on induced functions by right translation. -/
@[simp] theorem induced_action (σ : Representation B M V) (f : Induced h hU σ) (g x : G) :
    Induction.eval P (inducingRepresentation h hU σ) (inducedRepresentation h hU σ g f) x =
      Induction.eval P (inducingRepresentation h hU σ) f (x * g) :=
  rfl

theorem isSmooth_inducedRepresentation (σ : Representation B M V) :
    IsSmooth (inducedRepresentation h hU σ) :=
  Induction.smoothInduced_smooth _ _

@[simp] theorem jacquet_action_mk (ρ : Representation B G V) (m : M) (v : V) :
    jacquetRepresentation ρ U M hU h.levi_le_normalizer m
        (Langlands.Jacquet.Localization.mk ρ U 1 v) =
      (jacquetCharacter B U M hU h.levi_le_normalizer).toMonoidHom m •
        Langlands.Jacquet.Localization.mk ρ U 1 (ρ m v) :=
  rfl

theorem isSmooth_jacquetRepresentation (ρ : Representation B G V) (hρ : IsSmooth ρ) :
    IsSmooth (jacquetRepresentation ρ U M hU h.levi_le_normalizer) :=
  (isSmooth_twist_iff _ _ (jacquetCharacter B U M hU h.levi_le_normalizer).isOpen_ker).mpr
    (Langlands.Jacquet.Localization.isSmooth_action ρ U 1 M h.levi_le_normalizer
      (Langlands.Jacquet.Localization.isInvariant_one U M h.levi_le_normalizer) hρ)

end Laws

end Parabolic

section Represented

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {k : Type u} [Field k] [TopologicalSpace k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance familyAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- A family of `M(F)` read on the literal Levi image `pointImage (l ≫ p)` in `G(F)`,
through the inverse of `leviPointsEquiv`. -/
abbrev leviImageRepresentation (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) {E : Type uV} [AddCommGroup E] [Module B E]
    (σ : Representation B (rationalPoints M) E) : Representation B (pointImage (l ≫ p)) E :=
  letI := leviPointTopology l hl
  σ.comp (leviPointsEquiv p l hp hl).symm.toMonoidHom

/-- The `B`-module of Renard's `i_P^G(σ)` for a family `σ` of `M(F)`. -/
abbrev LeviInduced (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) {E : Type uV} [AddCommGroup E]
    [Module B E] (σ : Representation B (rationalPoints M) E) :=
  Induced (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (leviImageRepresentation p l hp hl σ)

/-- Renard's normalized parabolic induction `i_P^G(σ)` of a family `σ` of `M(F)` over `B`,
a family of `G(F)` over `B`. -/
def leviInducedRepresentation (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    {E : Type uV} [AddCommGroup E] [Module B E]
    (σ : Representation B (rationalPoints M) E) :
    Representation B (rationalPoints G) (LeviInduced p l r hp hr hl hmul σ) :=
  inducedRepresentation (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (leviImageRepresentation p l hp hl σ)

/-- Renard's normalized Jacquet module `r_P^G(ρ)` of a family `ρ` of `G(F)` over `B`, a
family of `M(F)` over `B` carried by the coinvariants of the unipotent radical. -/
def leviJacquetRepresentation (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    {V : Type uV} [AddCommGroup V] [Module B V] (ρ : Representation B (rationalPoints G) V) :
    Representation B (rationalPoints M) (Jacquet ρ (pointImage (r ≫ p))) :=
  letI := leviPointTopology l hl
  (jacquetRepresentation ρ (pointImage (r ≫ p)) (pointImage (l ≫ p))
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).levi_le_normalizer).comp
    (leviPointsEquiv p l hp hl).toMonoidHom

end Represented

end Langlands.Renard.AlgebraicFamily
