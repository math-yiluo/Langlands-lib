import Langlands.AbelianScheme.Tate.RationalTopology
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof

/-! # Actual full and away adelic geometric Tate representations -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AbelianScheme.Tate.Geometric

universe u
open Langlands.AlgebraicGeometry
open GroupScheme.Tate (Index)

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (s : Spec (.of Ω) ⟶ S) (A : AbelianScheme S)

local notation "Γs" => FiniteEtale.FundamentalGroup s (FiniteEtale.geometricFiberFinite s)

section Full
variable (hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- Full geometric monodromy over the existing finite-adelic scalar action. -/
def finiteAdeleRepresentation :
    let := finiteAdeleModule A (Over.mk s) (fun _ => True) h
    Γs →* (RationalFullAt A s ≃ₗ[Global.FiniteAdeles ℚ] RationalFullAt A s) := by
  let := finiteAdeleModule A (Over.mk s) (fun _ => True) h
  exact {
    toFun := finiteAdeleMonodromy s (FiniteEtale.geometricFiberFinite s)
      torsionFiniteEtale A (fun _ => True) hunit h
    map_one' := LinearEquiv.ext (rationalMonodromyMap_one s
      (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A (fun _ => True) hunit)
    map_mul' := fun g k => LinearEquiv.ext (rationalMonodromyMap_mul s
      (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A (fun _ => True) hunit g k) }

@[simp] theorem finiteAdeleRepresentation_apply (g : Γs) (x : RationalFullAt A s) :
    finiteAdeleRepresentation s A hunit h g x =
      rationalFullMonodromy s (FiniteEtale.geometricFiberFinite s)
        torsionFiniteEtale A hunit g x := rfl

@[simp] theorem finiteAdeleRepresentation_tmul (g : Γs) (q : ℚ) (x : FullAt A s) :
    finiteAdeleRepresentation s A hunit h g (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] integralMonodromy s (FiniteEtale.geometricFiberFinite s)
        torsionFiniteEtale A (fun _ => True) hunit g x := rfl

/-- The compact open integral image carries its original geometric action. -/
@[simp] theorem finiteAdeleRepresentation_toRational (g : Γs) (x : FullAt A s) :
    finiteAdeleRepresentation s A hunit h g
        (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x) =
      GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True)
        (integralMonodromy s (FiniteEtale.geometricFiberFinite s)
          torsionFiniteEtale A (fun _ => True) hunit g x) := rfl

/-- Membership in the actual integral image is invariant under full monodromy. -/
theorem finiteAdeleRepresentation_mem_integral_iff (g : Γs) (x : RationalFullAt A s) :
    finiteAdeleRepresentation s A hunit h g x ∈
        Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True)) ↔
      x ∈ Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True)) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨integralMonodromy s (FiniteEtale.geometricFiberFinite s)
      torsionFiniteEtale A (fun _ => True) hunit g⁻¹ y, ?_⟩
    change rationalMonodromyMap s (FiniteEtale.geometricFiberFinite s)
      torsionFiniteEtale A (fun _ => True) hunit g⁻¹
        (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) y) = x
    change GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) y =
      rationalMonodromyMap s (FiniteEtale.geometricFiberFinite s)
        torsionFiniteEtale A (fun _ => True) hunit g x at hy
    rw [hy]
    exact (rationalMonodromy s (FiniteEtale.geometricFiberFinite s)
      torsionFiniteEtale A (fun _ => True) hunit g).left_inv x
  · rintro ⟨y, rfl⟩
    exact ⟨integralMonodromy s (FiniteEtale.geometricFiberFinite s)
      torsionFiniteEtale A (fun _ => True) hunit g y, rfl⟩

/-- Tensor-linear full monodromy induced by actual rational endomorphisms. -/
abbrev finiteAdeleAlgebraRepresentation {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) :
    let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
    Γs →* (RationalFullAt A s ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] RationalFullAt A s) :=
  finiteAdeleAlgebraMonodromyRepresentation s (FiniteEtale.geometricFiberFinite s)
    torsionFiniteEtale A (fun _ => True) hunit h i

@[simp] theorem finiteAdeleAlgebraRepresentation_apply {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) (g : Γs) (x : RationalFullAt A s) :
    finiteAdeleAlgebraRepresentation s A hunit h i g x =
      finiteAdeleRepresentation s A hunit h g x := rfl

end Full

section Away
variable (m : ℕ)
  (hunit : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Away geometric monodromy over the existing away finite-adelic scalar action. -/
def awayFiniteAdeleRepresentation :
    let := primeToFiniteAdeleModule A (Over.mk s) hAway
    Γs →* (RationalAwayAt A s m ≃ₗ[Global.PrimeToFiniteAdeles m] RationalAwayAt A s m) := by
  let := primeToFiniteAdeleModule A (Over.mk s) hAway
  exact {
    toFun := primeToFiniteAdeleMonodromy s (FiniteEtale.geometricFiberFinite s)
      torsionFiniteEtale A m hunit hAway
    map_one' := LinearEquiv.ext (rationalMonodromyMap_one s
      (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A (fun n => Nat.Coprime n m) hunit)
    map_mul' := fun g k => LinearEquiv.ext (rationalMonodromyMap_mul s
      (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A
        (fun n => Nat.Coprime n m) hunit g k) }

@[simp] theorem awayFiniteAdeleRepresentation_apply (g : Γs) (x : RationalAwayAt A s m) :
    awayFiniteAdeleRepresentation s A m hunit hAway g x =
      rationalAwayMonodromy s (FiniteEtale.geometricFiberFinite s)
        torsionFiniteEtale A m hunit g x := rfl

@[simp] theorem awayFiniteAdeleRepresentation_tmul
    (g : Γs) (q : ℚ) (x : AwayAt A s m) :
    awayFiniteAdeleRepresentation s A m hunit hAway g (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] integralMonodromy s (FiniteEtale.geometricFiberFinite s)
        torsionFiniteEtale A (fun n => Nat.Coprime n m) hunit g x := rfl

/-- Away integral-to-rational inclusion intertwines the actual actions. -/
@[simp] theorem awayFiniteAdeleRepresentation_toRational (g : Γs) (x : AwayAt A s m) :
    awayFiniteAdeleRepresentation s A m hunit hAway g
        (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun n => Nat.Coprime n m) x) =
      GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun n => Nat.Coprime n m)
        (integralMonodromy s (FiniteEtale.geometricFiberFinite s)
          torsionFiniteEtale A (fun n => Nat.Coprime n m) hunit g x) := rfl

/-- Membership in the actual away integral image is invariant under monodromy. -/
theorem awayFiniteAdeleRepresentation_mem_integral_iff (g : Γs) (x : RationalAwayAt A s m) :
    awayFiniteAdeleRepresentation s A m hunit hAway g x ∈
        Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun n => Nat.Coprime n m)) ↔
      x ∈ Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun n => Nat.Coprime n m)) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨integralMonodromy s (FiniteEtale.geometricFiberFinite s)
      torsionFiniteEtale A (fun n => Nat.Coprime n m) hunit g⁻¹ y, ?_⟩
    change rationalMonodromyMap s (FiniteEtale.geometricFiberFinite s)
      torsionFiniteEtale A (fun n => Nat.Coprime n m) hunit g⁻¹
        (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun n => Nat.Coprime n m) y) = x
    change GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun n => Nat.Coprime n m) y =
      rationalMonodromyMap s (FiniteEtale.geometricFiberFinite s)
        torsionFiniteEtale A (fun n => Nat.Coprime n m) hunit g x at hy
    rw [hy]
    exact (rationalMonodromy s (FiniteEtale.geometricFiberFinite s)
      torsionFiniteEtale A (fun n => Nat.Coprime n m) hunit g).left_inv x
  · rintro ⟨y, rfl⟩
    exact ⟨integralMonodromy s (FiniteEtale.geometricFiberFinite s)
      torsionFiniteEtale A (fun n => Nat.Coprime n m) hunit g y, rfl⟩

/-- Tensor-linear away monodromy induced by actual rational endomorphisms. -/
abbrev awayFiniteAdeleAlgebraRepresentation {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) :
    let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
    Γs →* (RationalAwayAt A s m ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] RationalAwayAt A s m) :=
  primeToFiniteAdeleAlgebraMonodromyRepresentation s (FiniteEtale.geometricFiberFinite s)
    torsionFiniteEtale A m hunit hAway i

@[simp] theorem awayFiniteAdeleAlgebraRepresentation_apply
    {D : Type*} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
    (g : Γs) (x : RationalAwayAt A s m) :
    awayFiniteAdeleAlgebraRepresentation s A m hunit hAway i g x =
      awayFiniteAdeleRepresentation s A m hunit hAway g x := rfl

end Away

/-- Full-to-away restriction intertwines the actual adelic representations. -/
theorem finiteAdeleRepresentation_restrictAway
    (hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (h : Global.RationalProfiniteIntegerAdeleComparison) (m : ℕ)
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (g : Γs) (x : RationalFullAt A s) :
    GroupScheme.Tate.rationalRestrictAway A.toGrp (Over.mk s) m
        (finiteAdeleRepresentation s A hunit h g x) =
      awayFiniteAdeleRepresentation s A m
        (fun n => hunit ⟨n.val, n.property.1, trivial⟩) hAway g
        (GroupScheme.Tate.rationalRestrictAway A.toGrp (Over.mk s) m x) :=
  rationalRestrictAway_monodromy s (FiniteEtale.geometricFiberFinite s)
    torsionFiniteEtale A m hunit g x

attribute [local instance] rationalTopology

/-- Joint continuity of full finite-adelic monodromy on the actual rational Tate space. -/
theorem continuous_finiteAdeleRepresentation
    (hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    Continuous (fun z : Γs × RationalFullAt A s => finiteAdeleRepresentation s A hunit h z.1 z.2) :=
  continuous_rationalFullMonodromy A s (FiniteEtale.geometricFiberFinite s)
    torsionFiniteEtale hunit

/-- Joint continuity of the full tensor-linear geometric action. -/
theorem continuous_finiteAdeleAlgebraRepresentation
    (hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {D : Type*} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A) :
    Continuous (fun z : Γs × RationalFullAt A s =>
      finiteAdeleAlgebraRepresentation s A hunit h i z.1 z.2) :=
  continuous_finiteAdeleRepresentation s A hunit h

/-- The actual full integral image is compact and open, with geometry proved. -/
theorem rationalFull_compactOpen_integral
    (hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))) :
    IsCompact (Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True))) ∧
      IsOpen (Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True))) :=
  Tate.rationalFull_compactOpen_integral A s (FiniteEtale.geometricFiberFinite s)
    torsionFiniteEtale hunit

/-- Local compactness of the full rational Tate space at an actual geometric point. -/
theorem rationalFull_locallyCompactSpace
    (hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))) :
    LocallyCompactSpace (RationalFullAt A s) :=
  Tate.rationalFull_locallyCompactSpace A s (FiniteEtale.geometricFiberFinite s)
    torsionFiniteEtale hunit

variable (m : ℕ)
  (hunit : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Joint continuity of away finite-adelic geometric monodromy. -/
theorem continuous_awayFiniteAdeleRepresentation :
    Continuous (fun z : Γs × RationalAwayAt A s m =>
      awayFiniteAdeleRepresentation s A m hunit hAway z.1 z.2) :=
  continuous_rationalAwayMonodromy A s (FiniteEtale.geometricFiberFinite s)
    torsionFiniteEtale m hunit

/-- Joint continuity of the away tensor-linear geometric action. -/
theorem continuous_awayFiniteAdeleAlgebraRepresentation
    {D : Type*} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A) :
    Continuous (fun z : Γs × RationalAwayAt A s m =>
      awayFiniteAdeleAlgebraRepresentation s A m hunit hAway i z.1 z.2) :=
  continuous_awayFiniteAdeleRepresentation s A m hunit hAway

include hunit in
/-- The actual away integral image is compact and open, with geometry proved. -/
theorem rationalAway_compactOpen_integral :
    IsCompact (Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s)
      (fun n => Nat.Coprime n m))) ∧
      IsOpen (Set.range (GroupScheme.Tate.toRational A.toGrp (Over.mk s)
        (fun n => Nat.Coprime n m))) :=
  Tate.rationalAway_compactOpen_integral A s (FiniteEtale.geometricFiberFinite s)
    torsionFiniteEtale m hunit

include hunit in
/-- Local compactness of the actual away rational Tate space. -/
theorem rationalAway_locallyCompactSpace : LocallyCompactSpace (RationalAwayAt A s m) :=
  Tate.rationalAway_locallyCompactSpace A s (FiniteEtale.geometricFiberFinite s)
    torsionFiniteEtale m hunit

end Langlands.AbelianScheme.Tate.Geometric
