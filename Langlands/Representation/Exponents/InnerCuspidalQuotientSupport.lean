import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Exponents.RealTwistFamilies
import Langlands.Representation.Classification.FineTwistRegularityProof

/-!
# Inner cuspidal support through an actual induction quotient

Actual maps on flattened normalized refined Jacquet modules, surjectivity
and subquotient inheritance. The final adapter reduces support identification
for a quotient to the existing cuspidal-induction constituent statement.
-/

noncomputable section

namespace Langlands.InnerCuspidalQuotientSupport

open GeneralLinear Geometric CuspidalSupport RelativeJacquetMultiplicity
open WeylBranchPieces

universe uF uV uW uM

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (R : BlockRefinement B)

section Maps

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {A : Representation ℂ (B.Levi F.Carrier) V}
  {D : Representation ℂ (B.Levi F.Carrier) W}

/-- Descend an actual coarse-Levi intertwiner to the flattened upper quotient. -/
def flattenedUpperJacquetMap (q : A.IntertwiningMap D) :
    Representation.IntertwiningMap
    ((T.normalizedRefinedJacquet B R A).comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom)
    ((T.normalizedRefinedJacquet B R D).comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom) where
  toLinearMap := (T.normalizedRefinedJacquetMap B R q).toLinearMap
  isIntertwining' m := (T.normalizedRefinedJacquetMap B R q).isIntertwining'
    (flattenedLeviEquiv F.Carrier B R m)

@[simp]
theorem flattenedUpperJacquetMap_mk (q : A.IntertwiningMap D) (v : V) :
    flattenedUpperJacquetMap T B R q (refinedJacquetMk B R A v) =
      refinedJacquetMk B R D (q v) := rfl

/-- Surjectivity of the upper quotient map follows by lifting a representative
through the original surjection. No smoothness or exactness premise is needed. -/
theorem flattenedUpperJacquetMap_surjective (q : A.IntertwiningMap D)
    (hq : Function.Surjective q) :
    Function.Surjective (flattenedUpperJacquetMap T B R q) := by
  intro x
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective D (refinedUnipotent F.Carrier B R) x
  obtain ⟨v, rfl⟩ := hq w
  exact ⟨refinedJacquetMk B R A v, rfl⟩

/-- Descend an actual coarse-Levi intertwiner to the flattened opposite quotient. -/
def flattenedOppositeJacquetMap (q : A.IntertwiningMap D) :
    Representation.IntertwiningMap
    ((T.normalizedRefinedOppositeJacquet B R A).comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom)
    ((T.normalizedRefinedOppositeJacquet B R D).comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom) where
  toLinearMap := (T.normalizedRefinedOppositeJacquetMap B R q).toLinearMap
  isIntertwining' m := (T.normalizedRefinedOppositeJacquetMap B R q).isIntertwining'
    (flattenedLeviEquiv F.Carrier B R m)

@[simp]
theorem flattenedOppositeJacquetMap_mk (q : A.IntertwiningMap D) (v : V) :
    flattenedOppositeJacquetMap T B R q (refinedOppositeJacquetMk B R A v) =
      refinedOppositeJacquetMk B R D (q v) := rfl

/-- The same representative argument proves surjectivity on opposite quotients. -/
theorem flattenedOppositeJacquetMap_surjective (q : A.IntertwiningMap D)
    (hq : Function.Surjective q) :
    Function.Surjective (flattenedOppositeJacquetMap T B R q) := by
  intro x
  obtain ⟨w, rfl⟩ := refinedOppositeJacquetMk_surjective B R D x
  obtain ⟨v, rfl⟩ := hq w
  exact ⟨refinedOppositeJacquetMk B R A v, rfl⟩

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  {ρ : Representation ℂ ((B.flatten R).Levi F.Carrier) M}

/-- A subquotient of the upper Jacquet module of a quotient is a subquotient
of the upper Jacquet module of the source. -/
theorem upper_isSubquotient_of_quotient (q : A.IntertwiningMap D)
    (hq : Function.Surjective q)
    (hρ : IsSubquotient ((T.normalizedRefinedJacquet B R D).comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom) ρ) :
    IsSubquotient ((T.normalizedRefinedJacquet B R A).comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom) ρ :=
  IsSubquotient.of_surjective_left (flattenedUpperJacquetMap T B R q)
    (flattenedUpperJacquetMap_surjective T B R q hq) hρ

/-- The corresponding inheritance for the opposite Jacquet module. -/
theorem opposite_isSubquotient_of_quotient (q : A.IntertwiningMap D)
    (hq : Function.Surjective q)
    (hρ : IsSubquotient ((T.normalizedRefinedOppositeJacquet B R D).comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom) ρ) :
    IsSubquotient ((T.normalizedRefinedOppositeJacquet B R A).comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom) ρ :=
  IsSubquotient.of_surjective_left (flattenedOppositeJacquetMap T B R q)
    (flattenedOppositeJacquetMap_surjective T B R q hq) hρ

end Maps

/-- Reduction to the existing constituent statement, retaining the very same
block-Weyl element that the constituent statement supplies. The constituent
statement remains a separate proof obligation. -/
theorem exists_transport_of_quotient_of_constituent
    (hC : GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uM})
    (hn : 0 < n) (S : BlockRefinement B)
    (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
    (hωi : Representation.IsIrreducible ω.ρ)
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (ρ : Rep.{uM} ℂ ((B.flatten R).Levi F.Carrier))
    (hρi : Representation.IsIrreducible ρ.ρ) :
    letI := T.topology
    IsLeviCuspidal (B.flatten S) ω.ρ →
    IsLeviCuspidal (B.flatten R) ρ.ρ →
    (∃ q : (innerInduced T B S (Rep.of (ω.ρ.comp
      (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom))).ρ.IntertwiningMap π.ρ,
      Function.Surjective q) →
    IsSubquotient ((innerJacquet T B R π).ρ.comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom) ρ.ρ →
    ∃ h ∈ blockWeyl B,
      ∃ hh : ConjugatesLevi (F := F.Carrier) (B.flatten S) (B.flatten R) h,
        Nonempty (ρ.ρ.Equiv (transport (B.flatten S) (B.flatten R) h hh ω.ρ)) := by
  let := T.topology
  intro hωc hρc ⟨q, hq⟩ hρ
  exact hC p F T n hn B S R ω hωi hωc ρ hρi hρc
    (opposite_isSubquotient_of_quotient T B R q hq hρ)

/-- The persistence input's arbitrary fine real twist is still irreducible and
cuspidal. The quotient adapter therefore identifies its inner cuspidal support
without any restriction on the fine parameter. -/
theorem exists_transport_fineTwist_of_quotient_of_constituent
    (hC : GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uM})
    (hn : 0 < n) (S : BlockRefinement B)
    (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
    (hωi : Representation.IsIrreducible ω.ρ)
    (v : Fin (B.flatten S).length → ℝ)
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (ρ : Rep.{uM} ℂ ((B.flatten R).Levi F.Carrier))
    (hρi : Representation.IsIrreducible ρ.ρ) :
    letI := T.topology
    IsLeviCuspidal (B.flatten S) ω.ρ →
    IsLeviCuspidal (B.flatten R) ρ.ρ →
    (∃ q : (innerInduced T B S (fineTwist T B S ω v 0)).ρ.IntertwiningMap π.ρ,
      Function.Surjective q) →
    IsSubquotient ((innerJacquet T B R π).ρ.comp
      (flattenedLeviEquiv F.Carrier B R).toMonoidHom) ρ.ρ →
    ∃ h ∈ blockWeyl B,
      ∃ hh : ConjugatesLevi (F := F.Carrier) (B.flatten S) (B.flatten R) h,
        Nonempty (ρ.ρ.Equiv (transport (B.flatten S) (B.flatten R) h hh
          (T.leviRealPowerTwist (B.flatten S) (-v) ω.ρ))) := by
  let := T.topology
  intro hωc hρc hq hρ
  let Ω := Rep.of (T.leviRealPowerTwist (B.flatten S) (-v) ω.ρ)
  have hΩi : Representation.IsIrreducible Ω.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff (B.flatten S) (-v) ω.ρ).mpr hωi
  have hΩc : IsLeviCuspidal (B.flatten S) Ω.ρ :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff (B.flatten S) (-v) ω.ρ).mpr hωc
  have hfine : fineTwist T B S ω v 0 =
      Rep.of (Ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom) := by
    have hv : (fun k : Fin (B.flatten S).length =>
        -v k + (0 : Fin B.length → ℝ) ((B.flattenBlockEquiv S).symm k).1) = -v := by
      funext k
      simp
    change Rep.of ((T.leviRealPowerTwist (B.flatten S) _ ω.ρ).comp _) = _
    rw [hv]
  have hq' : ∃ q : (innerInduced T B S (Rep.of (Ω.ρ.comp
      (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom))).ρ.IntertwiningMap π.ρ,
      Function.Surjective q := by
    rw [hfine] at hq
    exact hq
  exact exists_transport_of_quotient_of_constituent T B R hC hn S Ω hΩi π ρ hρi
    hΩc hρc hq' hρ

end Langlands.InnerCuspidalQuotientSupport
