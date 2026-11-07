import Langlands.LocalFactor.InvariantsDual
import Langlands.LocalFactor.Inductive.EulerFactorProof
import Langlands.Correspondence.ArithmeticFactors
import Langlands.Correspondence.RankOneArithmeticEuler
import Langlands.Correspondence.UnramifiedReciprocityBridge
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement
import Langlands.VirtualRepresentation.ExactTensor
import Langlands.VirtualRepresentation.ExactInductionDual
import Langlands.Weil.Representation.CharacterLineDual
import Mathlib.LinearAlgebra.Contraction

/-!
# Inertia Euler polynomials on continuous virtual representations of a local Weil group

For a p-adic field `F`, the Euler polynomial `det(1 - X Fr | A^I)` of a continuous
representation `A` of `W_F` is multiplicative along short exact sequences, so it is a
homomorphism on the continuous exact virtual group. Its values on characters, on
representations induced along `W_E → W_F`, and on tensor products of zero-monodromy
pairs are computed.
-/

noncomputable section

set_option autoImplicit false

universe u w uK uG uH uA uB uC

open Polynomial

namespace Langlands.LocalFactor

variable {V : Type uA} {W : Type uB} {U : Type uC}
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ U] in
/-- Determinants are multiplicative along a short exact sequence of compatible operators. -/
theorem det_eq_mul_of_exact (A : Module.End ℂ V) (B : Module.End ℂ W) (C : Module.End ℂ U)
    (i : V →ₗ[ℂ] W) (j : W →ₗ[ℂ] U) (hi : Function.Injective i)
    (hj : Function.Surjective j) (hij : LinearMap.range i = LinearMap.ker j)
    (hA : B ∘ₗ i = i ∘ₗ A) (hC : C ∘ₗ j = j ∘ₗ B) :
    LinearMap.det B = LinearMap.det A * LinearMap.det C := by
  let N := LinearMap.ker j
  have hN : N ≤ N.comap B := by
    intro x hx
    change j (B x) = 0
    change j x = 0 at hx
    have h := LinearMap.congr_fun hC x
    simp only [LinearMap.comp_apply] at h
    rw [← h, hx, map_zero]
  let eV : V ≃ₗ[ℂ] N := (LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ hij)
  have eV_apply (v : V) : (eV v : W) = i v := rfl
  have hconjV : eV.toLinearMap ∘ₗ A ∘ₗ eV.symm.toLinearMap = B.restrict hN := by
    ext x
    change (eV (A (eV.symm x)) : W) = B (x : W)
    have h := LinearMap.congr_fun hA (eV.symm x)
    simp only [LinearMap.comp_apply] at h
    rw [eV_apply, ← h, ← eV_apply, eV.apply_symm_apply]
  have hdetV : LinearMap.det (B.restrict hN) = LinearMap.det A := by
    rw [← hconjV, LinearMap.det_conj]
  let eT : (W ⧸ N) ≃ₗ[ℂ] U := j.quotKerEquivOfSurjective hj
  have hconjT : eT.toLinearMap ∘ₗ N.mapQ N B hN ∘ₗ eT.symm.toLinearMap = C := by
    ext t
    obtain ⟨x, rfl⟩ := hj t
    change eT (N.mapQ N B hN (eT.symm (j x))) = C (j x)
    have heT : eT.symm (j x) = N.mkQ x := j.quotKerEquivOfSurjective_symm_apply hj x
    rw [heT]
    have h := LinearMap.congr_fun hC x
    simp only [LinearMap.comp_apply] at h
    exact h.symm
  have hdetT : LinearMap.det (N.mapQ N B hN) = LinearMap.det C := by
    rw [← hconjT, LinearMap.det_conj]
  rw [LinearMap.det_eq_det_mul_det N B hN, hdetV, hdetT]

/-- Euler polynomials are multiplicative along a short exact sequence of compatible
operators. -/
theorem eulerPolynomial_eq_mul_of_exact (A : Module.End ℂ V) (B : Module.End ℂ W)
    (C : Module.End ℂ U) (i : V →ₗ[ℂ] W) (j : W →ₗ[ℂ] U) (hi : Function.Injective i)
    (hj : Function.Surjective j) (hij : LinearMap.range i = LinearMap.ker j)
    (hA : B ∘ₗ i = i ∘ₗ A) (hC : C ∘ₗ j = j ∘ₗ B) :
    eulerPolynomial B = eulerPolynomial A * eulerPolynomial C := by
  apply Polynomial.funext
  intro z
  rw [Polynomial.eval_mul, eulerPolynomial_eval, eulerPolynomial_eval, eulerPolynomial_eval]
  apply det_eq_mul_of_exact _ _ _ i j hi hj hij
  · apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun hA v
    simp only [LinearMap.comp_apply] at h
    simp [h]
  · apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun hC v
    simp only [LinearMap.comp_apply] at h
    simp [h]

end Langlands.LocalFactor

namespace Langlands.FiniteRepresentation

section Equivalences

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
  {A : FiniteRepresentation.{uK, uG, uA} K G} {B : FiniteRepresentation.{uK, uG, uB} K G}

/-- An equivalence with independent carrier universes restricts to the fixed spaces of a
normal subgroup. -/
def invariantsEquivOfEquiv (I : Subgroup G) [I.Normal] (e : Equiv A B) :
    Equiv (invariants I A) (invariants I B) where
  toLinearEquiv :=
    { (invariantsMap I e.toIntertwiningMap).toLinearMap with
      invFun := invariantsMap I e.symm.toIntertwiningMap
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val) }
  isIntertwining' := (invariantsMap I e.toIntertwiningMap).isIntertwining'

/-- The Euler polynomial on normal-subgroup invariants is an invariant of equivalence. -/
theorem eulerPolynomial_invariants_eq_of_equiv (I : Subgroup G) [I.Normal] (e : Equiv A B)
    (g : G) :
    LocalFactor.eulerPolynomial ((invariants I A).representation g) =
      LocalFactor.eulerPolynomial ((invariants I B).representation g) := by
  have h := LocalFactor.eulerPolynomial_conj (invariantsEquivOfEquiv I e).toLinearEquiv
    ((invariants I A).representation g)
  rw [Representation.Equiv.conj_apply_self] at h
  exact h.symm

end Equivalences

section Exact

variable {G : Type uG} [Group G] (I : Subgroup G) [I.Normal]
  {A : FiniteRepresentation.{0, uG, uA} ℂ G} {B : FiniteRepresentation.{0, uG, uB} ℂ G}
  {C : FiniteRepresentation.{0, uG, uC} ℂ G}

/-- If the normal subgroup acts on the middle term through a finite group, invariants
preserve surjectivity. The proof averages a preimage over the finite image. -/
theorem invariantsMap_surjective (g : B.representation.IntertwiningMap C.representation)
    (hg : Function.Surjective g)
    (hfinite : (Set.range (B.representation.comp I.subtype)).Finite) :
    Function.Surjective (invariantsMap I g) := by
  classical
  let ρ := B.representation.comp I.subtype
  let Q := I ⧸ ρ.ker
  let τ : Representation ℂ Q B := QuotientGroup.lift ρ.ker ρ le_rfl
  have hr (q : Q) : τ q ∈ Set.range ρ := by
    induction q using QuotientGroup.induction_on with
    | H i => exact ⟨i, rfl⟩
  let := hfinite.to_subtype
  let : Finite Q := Finite.of_injective
    (fun q : Q => (⟨τ q, hr q⟩ : Set.range ρ)) (by
      intro a b h
      exact (QuotientGroup.injective_lift_iff ρ.ker ρ le_rfl).mpr rfl
        (congrArg Subtype.val h))
  let : Fintype Q := Fintype.ofFinite Q
  let : Invertible (Fintype.card Q : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hq (v : B) : v ∈ τ.invariants ↔ v ∈ invariantSubspace B I := by
    constructor
    · intro h i
      exact h (QuotientGroup.mk i)
    · intro h q
      induction q using QuotientGroup.induction_on with
      | H i => exact h i
  intro c
  obtain ⟨b, hb⟩ := hg c.val
  refine ⟨⟨τ.averageMap b, (hq _).mp (τ.averageMap_invariant b)⟩, ?_⟩
  apply Subtype.ext
  change g.toLinearMap (τ.averageMap b) = c.val
  have ht (q : Q) : g.toLinearMap (τ q b) = c.val := by
    induction q using QuotientGroup.induction_on with
    | H i =>
      change g (B.representation i b) = c.val
      rw [Representation.IntertwiningMap.isIntertwining _ _ g (i : G) b, hb]
      exact c.property i
  simp [Representation.averageMap, GroupAlgebra.average, map_sum, ht,
    ← Nat.cast_smul_eq_nsmul ℂ]

/-- Invariants of a short exact sequence whose middle term has finite image of the normal
subgroup form a short exact sequence. -/
theorem isShortExact_invariants {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation} (h : IsShortExact f g)
    (hfinite : (Set.range (B.representation.comp I.subtype)).Finite) :
    IsShortExact (invariantsMap I f) (invariantsMap I g) := by
  refine ⟨?_, invariantsMap_surjective I g h.2.1 hfinite, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact h.1 (congrArg Subtype.val hxy)
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      apply Subtype.ext
      have hx : f x.val ∈ LinearMap.range f.toLinearMap := ⟨x.val, rfl⟩
      rw [h.2.2] at hx
      exact hx
    · intro y hy
      have hy' : y.val ∈ LinearMap.ker g.toLinearMap := congrArg Subtype.val hy
      rw [← h.2.2] at hy'
      obtain ⟨a, ha⟩ := hy'
      refine ⟨⟨a, fun i => h.1 ?_⟩, Subtype.ext ha⟩
      change f (A.representation i a) = f a
      rw [Representation.IntertwiningMap.isIntertwining _ _ f (i : G) a]
      change B.representation i (f.toLinearMap a) = f.toLinearMap a
      rw [ha]
      exact y.property i

/-- The Euler polynomial on invariants is multiplicative along such short exact
sequences, at every group element. -/
theorem eulerPolynomial_invariants_of_shortExact
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation} (h : IsShortExact f g)
    (hfinite : (Set.range (B.representation.comp I.subtype)).Finite) (x : G) :
    LocalFactor.eulerPolynomial ((invariants I B).representation x) =
      LocalFactor.eulerPolynomial ((invariants I A).representation x) *
        LocalFactor.eulerPolynomial ((invariants I C).representation x) := by
  have hs := isShortExact_invariants I h hfinite
  exact LocalFactor.eulerPolynomial_eq_mul_of_exact _ _ _
    (invariantsMap I f).toLinearMap (invariantsMap I g).toLinearMap hs.1 hs.2.1 hs.2.2
    ((invariantsMap I f).isIntertwining' x).symm ((invariantsMap I g).isIntertwining' x).symm

end Exact

end Langlands.FiniteRepresentation

namespace Langlands.FiniteRepresentation

section CrossUniverse

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {H : Type uH} [Group H]

/-- Restriction of an equivalence with independent carrier universes. -/
def restrictEquivOfEquiv (φ : H →* G) {A : FiniteRepresentation.{uK, uG, uA} K G}
    {B : FiniteRepresentation.{uK, uG, uB} K G} (e : Equiv A B) :
    Equiv (restrict φ A) (restrict φ B) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' h := e.isIntertwining' (φ h)

/-- Finite-index induction of an equivalence with independent carrier universes, by
pointwise application of the equivalence and of its inverse. -/
def induceEquivOfEquiv (S : Subgroup G) [S.FiniteIndex]
    {A : FiniteRepresentation.{uK, uG, uA} K S} {B : FiniteRepresentation.{uK, uG, uB} K S}
    (e : Equiv A B) : Equiv (induce S A) (induce S B) where
  toLinearEquiv :=
    { (Representation.coindMap S.subtype e.toIntertwiningMap).toLinearMap with
      invFun := Representation.coindMap S.subtype e.symm.toIntertwiningMap
      left_inv := fun x => Subtype.ext (funext fun g => e.symm_apply_apply (x.val g))
      right_inv := fun x => Subtype.ext (funext fun g => e.apply_symm_apply (x.val g)) }
  isIntertwining' := (Representation.coindMap S.subtype e.toIntertwiningMap).isIntertwining'

/-- Induction along an injective map with finite-index range, for equivalences with
independent carrier universes. -/
def induceAlongEquivOfEquiv (ι : H →* G) (hι : Function.Injective ι) [ι.range.FiniteIndex]
    {A : FiniteRepresentation.{uK, uH, uA} K H} {B : FiniteRepresentation.{uK, uH, uB} K H}
    (e : Equiv A B) : Equiv (induceAlong ι hι A) (induceAlong ι hι B) :=
  induceEquivOfEquiv ι.range (restrictEquivOfEquiv (InductionAlong.rangeInverse ι hι) e)

/-- Character lines in two carrier universes are equivalent. -/
def characterLineUniverseEquiv (χ : G →* ℂˣ) :
    Equiv (characterLine.{uG, uA} χ) (characterLine.{uG, uB} χ) :=
  (characterLineEquiv.{uG, uA} χ).trans (characterLineEquiv.{uG, uB} χ).symm

/-- The tensor product of the duals is equivalent to the dual of the tensor product:
`f ⊗ g` is sent to the functional `x ⊗ y ↦ f x * g y`. -/
def tensorDualEquiv (A : FiniteRepresentation.{uK, uG, uA} K G)
    (B : FiniteRepresentation.{uK, uG, uB} K G) :
    Equiv (tensor (dual A) (dual B)) (dual (tensor A B)) where
  toLinearEquiv := TensorProduct.dualDistribEquiv K A B
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro f h
    apply TensorProduct.ext'
    intro x y
    rfl

end CrossUniverse

end Langlands.FiniteRepresentation

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

/-- The monodromy kernel of a zero-monodromy pair is the whole representation. -/
def zeroMonodromyKernelEquiv (ν : G →* Kˣ) (A : FiniteRepresentation.{uK, uG, uA} K G) :
    FiniteRepresentation.Equiv (zeroMonodromy ν A).kernelRepresentation A where
  toLinearEquiv := LinearEquiv.ofTop (LinearMap.ker (0 : Module.End K A)) LinearMap.ker_zero
  isIntertwining' _ := rfl

/-- The tensor product of two zero-monodromy pairs is the zero-monodromy pair of the
tensor product, by the identity map. -/
def tensorZeroMonodromyEquiv (ν : G →* Kˣ) (A : FiniteRepresentation.{uK, uG, uA} K G)
    (B : FiniteRepresentation.{uK, uG, uB} K G) :
    Equiv (tensor (zeroMonodromy ν A) (zeroMonodromy ν B))
      (zeroMonodromy ν (FiniteRepresentation.tensor A B)) where
  representationEquiv := Representation.Equiv.refl _
  comm_monodromy := by
    change LinearMap.id ∘ₗ (TensorProduct.map (0 : Module.End K A) (1 : Module.End K B) +
        TensorProduct.map (1 : Module.End K A) (0 : Module.End K B)) =
        (0 : Module.End K (TensorProduct K A B)) ∘ₗ LinearMap.id
    simp

end Langlands.WeilDeligneRepresentation

namespace Langlands.LocalFactor.WeilDeligne

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

/-- The Euler polynomial of a zero-monodromy pair is the Euler polynomial on inertia
invariants of its representation. -/
theorem eulerPolynomial_zeroMonodromy (ν : G →* Kˣ) (I : Subgroup G) [I.Normal]
    (A : FiniteRepresentation.{uK, uG, uA} K G) (g : G) :
    eulerPolynomial (WeilDeligneRepresentation.zeroMonodromy ν A) I g =
      LocalFactor.eulerPolynomial ((FiniteRepresentation.invariants I A).representation g) :=
  FiniteRepresentation.eulerPolynomial_invariants_eq_of_equiv I
    (WeilDeligneRepresentation.zeroMonodromyKernelEquiv ν A) g

end Langlands.LocalFactor.WeilDeligne

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} {H : Type uH} [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- Contragredients commute with induction along an open embedding with finite-index
range. -/
theorem continuousDual_continuousInduceAlong (φ : H →ₜ* G)
    (hφ : Topology.IsOpenEmbedding φ) [φ.toMonoidHom.range.FiniteIndex]
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uH, uA} ℂ H => A.IsContinuous)) :
    continuousDual (continuousInduceAlong φ hφ x) =
      continuousInduceAlong φ hφ (continuousDual x) := by
  rw [continuousInduceAlong, LinearMap.comp_apply, LinearMap.comp_apply,
    ExactGrothendieckGroup.continuousInduce,
    continuousDual_induce _ (InductionAlong.isOpen_range φ.toMonoidHom hφ),
    ExactGrothendieckGroup.continuousRestrict_continuousDual]

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.Weil.Local.InertiaEuler

open FiniteRepresentation VirtualRepresentation VirtualRepresentation.ExactGrothendieckGroup

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The Euler polynomial `det(1 - X Fr | A^I)` on inertia invariants, at the published
geometric Frobenius lift `Fr`. -/
def eulerPolynomial (A : LocalWeilRepresentation.{u, w} F) : ℂ[X] :=
  LocalFactor.eulerPolynomial
    ((invariants (localInertia F) A).representation (localGeometricFrobenius F))

/-- The L-factor `det(1 - X Fr | A^I)⁻¹` as a unit of the rational function field. -/
def lFactorUnit (A : LocalWeilRepresentation.{u, w} F) : (RatFunc ℂ)ˣ :=
  (Units.mk0 (algebraMap ℂ[X] (RatFunc ℂ) (eulerPolynomial F A))
    (RatFunc.algebraMap_ne_zero (LocalFactor.eulerPolynomial_ne_zero _)))⁻¹

@[simp]
theorem coe_lFactorUnit (A : LocalWeilRepresentation.{u, w} F) :
    (lFactorUnit F A : RatFunc ℂ) = (algebraMap ℂ[X] (RatFunc ℂ) (eulerPolynomial F A))⁻¹ :=
  rfl

theorem eulerPolynomial_eq_of_equiv {A : LocalWeilRepresentation.{u, uA} F}
    {B : LocalWeilRepresentation.{u, uB} F} (e : FiniteRepresentation.Equiv A B) :
    eulerPolynomial F A = eulerPolynomial F B :=
  eulerPolynomial_invariants_eq_of_equiv (localInertia F) e _

theorem lFactorUnit_eq_of_equiv {A : LocalWeilRepresentation.{u, uA} F}
    {B : LocalWeilRepresentation.{u, uB} F} (e : FiniteRepresentation.Equiv A B) :
    lFactorUnit F A = lFactorUnit F B := by
  apply Units.ext
  rw [coe_lFactorUnit, coe_lFactorUnit, eulerPolynomial_eq_of_equiv F e]

/-- The Euler polynomial is multiplicative on short exact sequences of continuous
representations: inertia acts on the middle term through a finite group. -/
theorem eulerPolynomial_of_shortExact {A : LocalWeilRepresentation.{u, w} F}
    {B : LocalWeilRepresentation.{u, w} F} {C : LocalWeilRepresentation.{u, w} F}
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation} (h : IsShortExact f g)
    (hB : B.IsContinuous) :
    eulerPolynomial F B = eulerPolynomial F A * eulerPolynomial F C := by
  have hc := localWeilContinuity F B
  have hfinite : B.HasFiniteInertiaImage (localInertia F) :=
    (hc.2.2.2.2.mp (hc.2.2.1.mp hB)).1
  exact eulerPolynomial_invariants_of_shortExact (localInertia F) h hfinite _

/-- The L-factor on genuine continuous classes, as an element of the additive group of
units of the rational function field. -/
def lFactorClass :
    IsomorphismClassesWith (fun A : LocalWeilRepresentation.{u, w} F => A.IsContinuous) →
      Additive (RatFunc ℂ)ˣ :=
  Quotient.lift (fun A => Additive.ofMul (lFactorUnit F A.val)) (fun _ _ h => by
    obtain ⟨e⟩ := h
    exact congrArg Additive.ofMul (lFactorUnit_eq_of_equiv F e))

theorem lFactorClass_isExactAdditive :
    IsExactAdditive (fun A : LocalWeilRepresentation.{u, w} F => A.IsContinuous)
      (lFactorClass F) := by
  intro A B C f g h
  change Additive.ofMul (lFactorUnit F B.val) =
    Additive.ofMul (lFactorUnit F A.val) + Additive.ofMul (lFactorUnit F C.val)
  rw [← ofMul_mul]
  congr 1
  apply Units.ext
  simp only [coe_lFactorUnit, Units.val_mul, eulerPolynomial_of_shortExact F h B.property,
    map_mul, mul_inv]

/-- The L-factor as a homomorphism on the continuous exact virtual group, with values in
the additive group of units of the rational function field. -/
def lFactorHom :
    ExactGrothendieckGroup.Continuous.{u, w} (localWeilGroup F) →ₗ[ℤ] Additive (RatFunc ℂ)ˣ :=
  lift _ (lFactorClass F) (lFactorClass_isExactAdditive F)

@[simp]
theorem lFactorHom_ofRepresentation
    (A : {A : LocalWeilRepresentation.{u, w} F // A.IsContinuous}) :
    lFactorHom F (ofRepresentation _ A) = Additive.ofMul (lFactorUnit F A.val) :=
  lift_ofRepresentation _ _ _ _

/-- The classical Euler polynomial of a character: `1 - χ(Fr) X` if `χ` is trivial on
inertia, and `1` otherwise. -/
def characterEulerPolynomial (χ : localWeilGroup F →ₜ* ℂˣ) : ℂ[X] := by
  classical
  exact if ∀ x ∈ localInertia F, χ x = 1 then 1 - C (χ (localGeometricFrobenius F) : ℂ) * X
    else 1

/-- The Euler polynomial of a character line is the classical Euler polynomial of the
character. -/
theorem eulerPolynomial_characterLine (χ : localWeilGroup F →ₜ* ℂˣ) :
    eulerPolynomial F (characterLine.{u, w} χ.toMonoidHom) = characterEulerPolynomial F χ := by
  classical
  let ν : localWeilGroup F →* ℂˣ := 1
  have h := LocalFactor.WeilDeligne.eulerPolynomial_zeroMonodromy ν (localInertia F)
    (characterLine.{u, w} χ.toMonoidHom) (localGeometricFrobenius F)
  rw [LocalFactor.WeilDeligne.eulerPolynomial_eq_of_equiv (localInertia F)
    (WeilDeligneRepresentation.zeroMonodromyCongr ν (characterLineEquiv χ.toMonoidHom))] at h
  change _ = eulerPolynomial F _ at h
  rw [← h, characterEulerPolynomial]
  split_ifs with hχ
  · exact LocalFactor.WeilDeligne.eulerPolynomial_scalarCharacter_of_unramified ν
      χ.toMonoidHom (localInertia F) hχ _
  · push Not at hχ
    exact LocalFactor.WeilDeligne.eulerPolynomial_scalarCharacter_of_ramified ν
      χ.toMonoidHom (localInertia F) hχ _

/-- The value of the L-factor homomorphism on a representation induced along the Weil map
of a finite extension `E` of `F`. -/
theorem lFactorHom_continuousInduceAlong (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier)
    (A : {A : LocalWeilRepresentation.{u, w} E // A.IsContinuous}) :
    lFactorHom.{u, max u w} F (continuousInduceAlong (extensionWeilMap F E g)
        (extensionWeilMap_isOpenEmbedding F E g) (ofRepresentation _ A)) =
      Additive.ofMul (lFactorUnit F (induceAlong (extensionWeilMap F E g).toMonoidHom
        (extensionWeilMap_injective F E g) A.val)) := by
  rw [ExactGrothendieckGroup.continuousInduceAlong, LinearMap.comp_apply,
    ExactGrothendieckGroup.continuousRestrict, ExactGrothendieckGroup.restrict_ofRepresentation,
    ExactGrothendieckGroup.continuousInduce, ExactGrothendieckGroup.induce_ofRepresentation,
    lFactorHom_ofRepresentation]
  rfl

/-- Tate 2.3, for characters: the Euler polynomial on inertia invariants of the
representation induced from a character `χ` of `W_E` is `P_χ(X^f)`, with `P_χ` the
classical Euler polynomial of `χ` and `f` the residue degree of `E / F`. -/
theorem eulerPolynomial_induceAlong_characterLine (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (χ : localWeilGroup E →ₜ* ℂˣ) :
    eulerPolynomial F (induceAlong (extensionWeilMap F E g).toMonoidHom
        (extensionWeilMap_injective F E g) (characterLine.{u, w} χ.toMonoidHom)) =
      expand ℂ (extensionResidueDegree F E g) (characterEulerPolynomial E χ) := by
  rw [eulerPolynomial_eq_of_equiv F (B := induceAlong (extensionWeilMap F E g).toMonoidHom
      (extensionWeilMap_injective F E g) (characterLine.{u, u} χ.toMonoidHom))
      (induceAlongEquivOfEquiv _ _ (characterLineUniverseEquiv χ.toMonoidHom)),
    ← eulerPolynomial_characterLine.{u, u} E χ]
  have hF : localDegreeInt F (localGeometricFrobenius F) = 1 := by
    rw [localDegreeInt, localGeometricFrobenius_degree]
    rfl
  have hE : localDegreeInt E (localGeometricFrobenius E) = 1 := by
    rw [localDegreeInt, localGeometricFrobenius_degree]
    rfl
  have h := LocalFactor.Inductive.eulerFactorInduction F E g
    (characterLine.{u, u} χ.toMonoidHom) (characterLine_isContinuous χ)
    (localGeometricFrobenius F) (localGeometricFrobenius E) hF hE
  exact h.1

/-- The L-factor `(1 - χ(Fr) X)⁻¹` of a character, or `1` if it is ramified. -/
def characterLFactor (χ : localWeilGroup F →ₜ* ℂˣ) : RatFunc ℂ :=
  (algebraMap ℂ[X] (RatFunc ℂ) (characterEulerPolynomial F χ))⁻¹

/-- The L-factor over `F` of the representation induced from a character `χ` of `W_E`:
`(1 - χ(Fr_E) X^f)⁻¹`, or `1` if `χ` is ramified, with `f` the residue degree of
`E / F`. -/
def inducedLFactor (E : PadicField.{u} p) (g : F.Carrier →ₐ[Padic p] E.Carrier)
    (χ : localWeilGroup E →ₜ* ℂˣ) : RatFunc ℂ :=
  (algebraMap ℂ[X] (RatFunc ℂ)
    (expand ℂ (extensionResidueDegree F E g) (characterEulerPolynomial E χ)))⁻¹

theorem coe_lFactorUnit_characterLine (χ : localWeilGroup F →ₜ* ℂˣ) :
    (lFactorUnit F (characterLine.{u, w} χ.toMonoidHom) : RatFunc ℂ) =
      characterLFactor F χ := by
  rw [coe_lFactorUnit, eulerPolynomial_characterLine, characterLFactor]

theorem coe_lFactorUnit_induceAlong_characterLine (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (χ : localWeilGroup E →ₜ* ℂˣ) :
    (lFactorUnit F (induceAlong (extensionWeilMap F E g).toMonoidHom
        (extensionWeilMap_injective F E g) (characterLine.{u, w} χ.toMonoidHom)) : RatFunc ℂ) =
      inducedLFactor F E g χ := by
  rw [coe_lFactorUnit, eulerPolynomial_induceAlong_characterLine, inducedLFactor]

theorem lFactorHom_characterClass (χ : localWeilGroup F →ₜ* ℂˣ) :
    lFactorHom.{u, w} F (characterClass.{u, w} χ) =
      Additive.ofMul (lFactorUnit F (characterLine.{u, w} χ.toMonoidHom)) :=
  lFactorHom_ofRepresentation F _

theorem lFactorHom_continuousInduceAlong_characterClass (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (χ : localWeilGroup E →ₜ* ℂˣ) :
    lFactorHom.{u, max u w} F (continuousInduceAlong (extensionWeilMap F E g)
        (extensionWeilMap_isOpenEmbedding F E g) (characterClass.{u, w} χ)) =
      Additive.ofMul (lFactorUnit F (induceAlong (extensionWeilMap F E g).toMonoidHom
        (extensionWeilMap_injective F E g) (characterLine.{u, w} χ.toMonoidHom))) :=
  lFactorHom_continuousInduceAlong F E g _

open WeilDeligneRepresentation in
/-- The arithmetic pair L-factor of the zero-monodromy pairs of `V` and `W` is the
L-factor on inertia invariants of any representation equivalent to `V ⊗ W`. -/
theorem arithmeticPairLFactor_zeroMonodromy (V W : LocalWeilRepresentation.{u, uA} F)
    (T : LocalWeilRepresentation.{u, w} F)
    (eT : FiniteRepresentation.Equiv T (FiniteRepresentation.tensor V W)) :
    Correspondence.arithmeticPairLFactor F
        (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom V))
        (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom W)) =
      (lFactorUnit F T : RatFunc ℂ) := by
  rw [Correspondence.arithmeticPairLFactor, LocalFactor.WeilDeligne.pairLFactorClass_classOf,
    LocalFactor.WeilDeligne.pairLFactor,
    LocalFactor.WeilDeligne.rationalLFactor_eq_of_equiv _ (tensorZeroMonodromyEquiv _ V W),
    coe_lFactorUnit, eulerPolynomial_eq_of_equiv F eT]
  change (algebraMap ℂ[X] (RatFunc ℂ) (LocalFactor.WeilDeligne.eulerPolynomial _ _ _))⁻¹ = _
  rw [LocalFactor.WeilDeligne.eulerPolynomial_zeroMonodromy]
  rfl

open WeilDeligneRepresentation in
/-- If a continuous representation `T ≃ V ⊗ W` has virtual class
`d [α₀] + Σ_j n_j Ind_{E_j/F}([α_j] - [β_j])`, then the arithmetic pair L-factor of the
zero-monodromy pairs of `V` and `W` is `L(α₀)^d Π_j (L(Ind α_j) / L(Ind β_j))^{n_j}`. -/
theorem arithmeticPairLFactor_eq_of_virtualIdentity
    (V W : LocalWeilRepresentation.{u, uA} F) (T : LocalWeilRepresentation.{u, max u w} F)
    (hT : T.IsContinuous) (eT : FiniteRepresentation.Equiv T (FiniteRepresentation.tensor V W))
    {J : Type*} [Fintype J] (E : J → PadicField.{u} p)
    (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier)
    (α β : ∀ j, localWeilGroup (E j) →ₜ* ℂˣ) (n : J → ℤ)
    (α₀ : localWeilGroup F →ₜ* ℂˣ) (d : ℤ)
    (h : ofRepresentation _ ⟨T, hT⟩ = d • characterClass.{u, max u w} α₀ +
      ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
        (extensionWeilMap_isOpenEmbedding F (E j) (g j))
        (characterClass.{u, w} (α j) - characterClass.{u, w} (β j))) :
    Correspondence.arithmeticPairLFactor F
        (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom V))
        (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom W)) =
      characterLFactor F α₀ ^ d *
        ∏ j, (inducedLFactor F (E j) (g j) (α j) / inducedLFactor F (E j) (g j) (β j)) ^ n j := by
  rw [arithmeticPairLFactor_zeroMonodromy F V W T eT]
  have hL := congrArg (fun x => Additive.toMul (lFactorHom F x)) h
  simp only [map_add, map_zsmul, map_sum, map_sub, lFactorHom_ofRepresentation,
    lFactorHom_characterClass, lFactorHom_continuousInduceAlong_characterClass, toMul_add,
    toMul_zsmul, toMul_sum, toMul_sub, toMul_ofMul] at hL
  rw [hL]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.coe_prod,
    Units.val_div_eq_div_val, coe_lFactorUnit_characterLine,
    coe_lFactorUnit_induceAlong_characterLine]

open WeilDeligneRepresentation in
/-- The dual form of `arithmeticPairLFactor_eq_of_virtualIdentity`: under the same virtual
identity, the arithmetic pair L-factor of the zero-monodromy pairs of any `Vd ≃ V^∨` and
`Wd ≃ W^∨` is `L(α₀⁻¹)^d Π_j (L(Ind α_j⁻¹) / L(Ind β_j⁻¹))^{n_j}`. -/
theorem arithmeticPairLFactor_dual_eq_of_virtualIdentity
    (V W : LocalWeilRepresentation.{u, uA} F) (T : LocalWeilRepresentation.{u, max u w} F)
    (hT : T.IsContinuous) (eT : FiniteRepresentation.Equiv T (FiniteRepresentation.tensor V W))
    (Vd Wd : LocalWeilRepresentation.{u, uA} F)
    (eV : FiniteRepresentation.Equiv Vd (FiniteRepresentation.dual V))
    (eW : FiniteRepresentation.Equiv Wd (FiniteRepresentation.dual W))
    {J : Type*} [Fintype J] (E : J → PadicField.{u} p)
    (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier)
    (α β : ∀ j, localWeilGroup (E j) →ₜ* ℂˣ) (n : J → ℤ)
    (α₀ : localWeilGroup F →ₜ* ℂˣ) (d : ℤ)
    (h : ofRepresentation _ ⟨T, hT⟩ = d • characterClass.{u, max u w} α₀ +
      ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
        (extensionWeilMap_isOpenEmbedding F (E j) (g j))
        (characterClass.{u, w} (α j) - characterClass.{u, w} (β j))) :
    Correspondence.arithmeticPairLFactor F
        (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom Vd))
        (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom Wd)) =
      characterLFactor F α₀⁻¹ ^ d *
        ∏ j, (inducedLFactor F (E j) (g j) (α j)⁻¹ /
          inducedLFactor F (E j) (g j) (β j)⁻¹) ^ n j := by
  have hTd : (FiniteRepresentation.dual T).IsContinuous := (isContinuous_dual_iff T).mpr hT
  let eTd : FiniteRepresentation.Equiv (FiniteRepresentation.dual T)
      (FiniteRepresentation.tensor Vd Wd) :=
    ((FiniteRepresentation.dualEquiv eT).symm.trans
      (FiniteRepresentation.tensorDualEquiv V W).symm).trans
      (FiniteRepresentation.tensorEquiv eV eW).symm
  apply arithmeticPairLFactor_eq_of_virtualIdentity F Vd Wd _ hTd eTd E g
  have hd := congrArg continuousDual h
  simp only [continuousDual_ofRepresentation, map_add, map_zsmul, map_sum, map_sub,
    continuousDual_continuousInduceAlong, continuousDual_characterClass] at hd
  refine hd.trans ?_
  simp only [map_sub]

end Langlands.Weil.Local.InertiaEuler
