import Langlands.Representation.Smooth.IrreducibleGrothendieckStatement
import Langlands.Representation.Smooth.IrreducibleCompositionFactors

/-!
# Irreducibles form the integral basis of exact finite-length smooth K₀

The published composition-factor map and canonical realization are inverse.
Actual invariant-submodule inclusions and quotient projections give the exact
relations needed to telescope any composition series. The generic theorem
retains independent coefficient, group and carrier universes; the actual GL
and product-Levi cases are direct specializations.

Original proof: Worker 320. Preparation and verification: Worker 585.
-/

noncomputable section

open CategoryTheory
open Langlands.VirtualRepresentation
open scoped BigOperators

universe uR uG uV uF

namespace Langlands.SmoothRep.IrreducibleGrothendieckProof

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  {A : SmoothRep.{uR, uG, uV} k G} {n : ℕ}

/-- Actual invariant subrepresentations inherit finite group-algebra length. -/
theorem subrepresentation_hasFiniteLength (hA : A.HasFiniteLength)
    (S : Subrepresentation A.representation) :
    (subrepresentation A S).HasFiniteLength :=
  hA.of_injective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom (subtype A S)))
    (subtype_injective A S)

/-- The class of a zero representation vanishes in the exact quotient. -/
theorem ofRepresentation_eq_zero_of_subsingleton (A : SmoothRep.{uR, uG, uV} k G)
    (hA : A.HasFiniteLength) [Subsingleton A.obj] :
    FiniteLengthGrothendieckGroup.ofRepresentation A hA = 0 := by
  let z : A.representation.IntertwiningMap A.representation := 0
  have hz : IsShortExact z z := by
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun a => ⟨0, Subsingleton.elim _ _⟩, ?_⟩
    ext a
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    exact iff_of_true ⟨0, Subsingleton.elim _ _⟩ (Subsingleton.elim _ _)
  have h := FiniteLengthGrothendieckGroup.ofRepresentation_shortExact hA hA hA hz
  exact add_left_cancel (show
      FiniteLengthGrothendieckGroup.ofRepresentation A hA +
          FiniteLengthGrothendieckGroup.ofRepresentation A hA =
        FiniteLengthGrothendieckGroup.ofRepresentation A hA + 0 by
    simpa only [add_zero] using h.symm)

/-- Inclusion of the full invariant submodule is an actual representation equivalence. -/
def subrepresentationTopEquiv (A : SmoothRep.{uR, uG, uV} k G) :
    (subrepresentation A ⊤).representation.Equiv A.representation :=
  (hom (subtype A ⊤)).ofBijective
    ⟨subtype_injective A ⊤, fun a => ⟨⟨a, Submodule.mem_top⟩, rfl⟩⟩

/-- Successive invariant submodules and their actual quotient form a short exact sequence. -/
theorem filtration_step_shortExact (s : ObjectRepFiltration A.obj n) (i : Fin n) :
    ∃ f : (subrepresentation A (s.subrepresentation i.castSucc)).representation.IntertwiningMap
        (subrepresentation A (s.subrepresentation i.succ)).representation,
      IsShortExact
        (A := subrepresentation A (s.subrepresentation i.castSucc))
        (B := subrepresentation A (s.subrepresentation i.succ))
        (C := gradedSmooth s i) f (s.gradedProjection i).hom := by
  let hle := s.monotone_subrepresentation (Fin.castSucc_le_succ i)
  let f : (subrepresentation A (s.subrepresentation i.castSucc)).representation.IntertwiningMap
      (subrepresentation A (s.subrepresentation i.succ)).representation :=
    { toLinearMap := Submodule.inclusion hle
      isIntertwining' _ := rfl }
  refine ⟨f, ?_, s.gradedProjection_surjective i, ?_⟩
  · change Function.Injective (Submodule.inclusion hle)
    exact Submodule.inclusion_injective hle
  · change LinearMap.range (Submodule.inclusion hle) =
      LinearMap.ker
        (((s.subrepresentation i.castSucc).toSubmodule.comap
          (s.subrepresentation i.succ).toSubmodule.subtype).mkQ)
    rw [Submodule.range_inclusion, Submodule.ker_mkQ]

/-- The integer-linear realization of the labels of a series is its exact class. -/
theorem realize_seriesClass (s : ObjectRepFiltration A.obj n)
    (hs : s.HasSimpleFactors) (hA : A.HasFiniteLength) :
    realizeIrreducibles k G (seriesClass s hs) =
      FiniteLengthGrothendieckGroup.ofRepresentation A hA := by
  let hstep (j : Fin (n + 1)) :
      (subrepresentation A (s.subrepresentation j)).HasFiniteLength :=
    subrepresentation_hasFiniteLength hA _
  let f (j : Fin (n + 1)) : FiniteLengthGrothendieckGroup.{uR, uG, uV} k G :=
    FiniteLengthGrothendieckGroup.ofRepresentation
      (subrepresentation A (s.subrepresentation j)) (hstep j)
  have hgrade (i : Fin n) :
      FiniteLengthGrothendieckGroup.ofRepresentation (gradedSmooth s i)
          (hasFiniteLength_of_isIrreducible (hs i)) = f i.succ - f i.castSucc := by
    obtain ⟨ι, hι⟩ := filtration_step_shortExact s i
    have heq := FiniteLengthGrothendieckGroup.ofRepresentation_shortExact
      (hstep i.castSucc) (hstep i.succ) (hasFiniteLength_of_isIrreducible (hs i)) hι
    change f i.succ = f i.castSucc + _ at heq
    rw [heq]
    abel
  have hzero : f 0 = 0 := by
    change FiniteLengthGrothendieckGroup.ofRepresentation
      (subrepresentation A (s.subrepresentation 0)) _ = 0
    simp only [ObjectRepFiltration.subrepresentation_zero]
    have : Subsingleton (subrepresentation A ⊥).obj := by
      change Subsingleton (⊥ : Submodule k A.obj)
      exact Submodule.subsingleton_iff_eq_bot.mpr rfl
    exact ofRepresentation_eq_zero_of_subsingleton _ _
  have hlast : f (Fin.last n) = FiniteLengthGrothendieckGroup.ofRepresentation A hA := by
    change FiniteLengthGrothendieckGroup.ofRepresentation
      (subrepresentation A (s.subrepresentation (Fin.last n))) _ = _
    simp only [ObjectRepFiltration.subrepresentation_last]
    exact FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv _ hA
      (subrepresentationTopEquiv A)
  calc
    realizeIrreducibles k G (seriesClass s hs) =
        ∑ i : Fin n, (f i.succ - f i.castSucc) := by
      rw [seriesClass, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (realizeIrreducibles_generator_irreducibleIsoClass (gradedSmooth s i)
        (hs i) (hasFiniteLength_of_isIrreducible (hs i))).trans (hgrade i)
    _ = f (Fin.last n) - f 0 := by
      rw [Finset.sum_sub_distrib]
      calc
        (∑ i : Fin n, f i.succ) - ∑ i : Fin n, f i.castSucc =
            (f 0 + ∑ i : Fin n, f i.succ) -
              ((∑ i : Fin n, f i.castSucc) + f 0) := by abel
        _ = ((∑ i : Fin n, f i.castSucc) + f (Fin.last n)) -
            ((∑ i : Fin n, f i.castSucc) + f 0) := by
          rw [← Fin.sum_univ_succ, Fin.sum_univ_castSucc]
        _ = f (Fin.last n) - f 0 := by abel
    _ = FiniteLengthGrothendieckGroup.ofRepresentation A hA := by rw [hzero, hlast, sub_zero]

/-- The factor-count map recovers every irreducible-lattice element. -/
theorem factorMap_comp_realize :
    (factorMap : FiniteLengthGrothendieckGroup.{uR, uG, uV} k G →ₗ[ℤ]
      IrreducibleLattice k G).comp (realizeIrreducibles k G) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro c z
  obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
  have hz : Finsupp.single (irreducibleIsoClass A hA) z =
      z • generator (irreducibleIsoClass A hA) := by simp [generator]
  simp only [hz, LinearMap.comp_apply, map_zsmul, LinearMap.id_apply]
  rw [realizeIrreducibles_generator_irreducibleIsoClass A hA
    (hasFiniteLength_of_isIrreducible hA), factorMap_ofRepresentation,
    compositionFactors_irreducible]

/-- Realization recovers every class in the exact finite-length quotient. -/
theorem realize_comp_factorMap :
    (realizeIrreducibles k G).comp
      (factorMap : FiniteLengthGrothendieckGroup.{uR, uG, uV} k G →ₗ[ℤ]
        IrreducibleLattice k G) = LinearMap.id := by
  apply FiniteLengthGrothendieckGroup.hom_ext_object k G
  intro A
  change realizeIrreducibles k G (factorMap
    (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property)) = _
  rw [factorMap_ofRepresentation]
  exact realize_seriesClass _ _ A.property

end Langlands.SmoothRep.IrreducibleGrothendieckProof

namespace Langlands.SmoothRep

variable (k : Type uR) [Field k] (G : Type uG) [Group G] [TopologicalSpace G]

/-- Genuine irreducible classes form the integral basis of the exact finite-length quotient. -/
theorem irreducibleGrothendieckStatement :
    IrreducibleGrothendieckStatement.{uR, uG, uV} k G := by
  change Function.Bijective (realizeIrreducibles.{uR, uG, uV} k G)
  have hleft : Function.LeftInverse
      (IrreducibleGrothendieckProof.factorMap :
        FiniteLengthGrothendieckGroup.{uR, uG, uV} k G →ₗ[ℤ] IrreducibleLattice k G)
      (realizeIrreducibles k G) := by
    intro v
    exact LinearMap.congr_fun IrreducibleGrothendieckProof.factorMap_comp_realize v
  have hright : Function.RightInverse
      (IrreducibleGrothendieckProof.factorMap :
        FiniteLengthGrothendieckGroup.{uR, uG, uV} k G →ₗ[ℤ] IrreducibleLattice k G)
      (realizeIrreducibles k G) := by
    intro v
    exact LinearMap.congr_fun IrreducibleGrothendieckProof.realize_comp_factorMap v
  exact ⟨hleft.injective, hright.surjective⟩

end Langlands.SmoothRep

namespace Langlands.GeneralLinear

variable (n : ℕ) (F : Type uF) [Field F] [TopologicalSpace F]

/-- The exact finite-length comparison for every actual general linear group. -/
theorem irreducibleGrothendieckStatement :
    IrreducibleGrothendieckStatement.{uV, uF} n F :=
  SmoothRep.irreducibleGrothendieckStatement.{0, uF, max uF uV} ℂ (GeneralLinear n F)

namespace BlockShape

variable {n} (B : BlockShape n)

/-- The comparison for arbitrary representations of an actual product Levi. -/
theorem irreducibleGrothendieckStatement :
    B.IrreducibleGrothendieckStatement.{uV, uF} F :=
  SmoothRep.irreducibleGrothendieckStatement.{0, uF, max uF uV} ℂ (B.Levi F)

end BlockShape
end Langlands.GeneralLinear
