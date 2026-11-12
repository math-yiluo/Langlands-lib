import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket
import Langlands.Representation.Twist.SmoothPartDefinitions

/-! # Coefficients bounded by `Ξ` along unitary unramified orbits

For a weight `Ξ : G → ℝ` and a representation `ρ` of `G`, `HasXiBoundedCoefficients Ξ ρ` says
that every smooth coefficient `g ↦ ⟨ℓ, ρ(g) v⟩` is bounded by `c Ξ(g)` for some `c > 0` (the
coefficient bound of a tempered representation used in the proof of Waldspurger's Lemma VI.2.2).

* `HasXiBoundedCoefficients.of_equiv`: the bound is invariant under equivalence;
* `HasXiBoundedCoefficients.twist`: it is invariant under twisting by a unitary character with open
  kernel;
* `HasXiBoundedCoefficients.unitaryOrbitRepresentative`: if `π` has the bound, so does every
  representative `A` of a class in the unitary unramified orbit of `π`
  (`UnitaryOrbitRepresentative ν π`);
* `rationalLeviXi_coefficientBound_unitaryOrbitRepresentative`: the case of the actual Levi
  subgroup `M_I(F)` of a standard parabolic, the weight `Ξ^{M_I}` and the unitary unramified
  characters of `M_I(F)`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

universe u uG uV uW uI

section Bound

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- **Coefficients bounded by `Ξ`**: for every `v ∈ V` and every smooth functional `ℓ` there is
`c > 0` with `‖⟨ℓ, ρ(g) v⟩‖ ≤ c Ξ(g)` for all `g ∈ G`. -/
def HasXiBoundedCoefficients (Ξ : G → ℝ) (ρ : Representation ℂ G V) : Prop :=
  ∀ (v : V) (ℓ : SmoothDual ρ), ∃ c : ℝ, 0 < c ∧ ∀ g, ‖ℓ.val (ρ g v)‖ ≤ c * Ξ g

variable [IsTopologicalGroup G] {Ξ : G → ℝ}

/-- The bound is transported along an equivalence of representations. -/
theorem HasXiBoundedCoefficients.of_equiv {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (Φ : ρ.Equiv σ) (h : HasXiBoundedCoefficients Ξ ρ) :
    HasXiBoundedCoefficients Ξ σ := by
  intro w ℓ
  obtain ⟨c, hc, hb⟩ := h (Φ.toLinearEquiv.symm w) (contragredientMap Φ.toIntertwiningMap ℓ)
  refine ⟨c, hc, fun g => ?_⟩
  have e : σ g w = Φ.toIntertwiningMap (ρ g (Φ.toLinearEquiv.symm w)) := by
    rw [Φ.toIntertwiningMap.isIntertwining]
    change σ g w = σ g (Φ.toLinearEquiv (Φ.toLinearEquiv.symm w))
    rw [LinearEquiv.apply_symm_apply]
  rw [e]
  exact hb g

/-- The bound is preserved by twisting with a unitary character with open kernel. -/
theorem HasXiBoundedCoefficients.twist {ρ : Representation ℂ G V} (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) (hχu : ∀ g, ‖((χ g : ℂˣ) : ℂ)‖ = 1)
    (h : HasXiBoundedCoefficients Ξ ρ) : HasXiBoundedCoefficients Ξ (Langlands.twist χ ρ) := by
  intro v ℓ
  obtain ⟨c, hc, hb⟩ := h v (smoothContragredientTwistEquiv χ ρ hχ ℓ)
  refine ⟨c, hc, fun g => ?_⟩
  have e : ℓ.val (Langlands.twist χ ρ g v) = ((χ g : ℂˣ) : ℂ) * ℓ.val (ρ g v) := by
    change ℓ.val (((χ g : ℂˣ) : ℂ) • ρ g v) = _
    exact ℓ.val.map_smul _ _
  rw [e, norm_mul, hχu, one_mul]
  exact hb g

end Bound

section Orbit

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))

/-- **Coefficient bounds along a unitary unramified orbit**: if the coefficients of `π` are
bounded by `Ξ`, so are those of every representative `A` of a class `π ⊗ χ` with `χ` a unitary
unramified character. -/
theorem HasXiBoundedCoefficients.unitaryOrbitRepresentative {Ξ : M → ℝ}
    (h : HasXiBoundedCoefficients Ξ π.obj.representation) (A : UnitaryOrbitRepresentative ν π) :
    HasXiBoundedCoefficients Ξ A.val.obj.representation := by
  obtain ⟨χ, hχ⟩ := A.property
  have hclass : (Quotient.mk _ (IrreducibleAdmissibleRep.twist
      (unitaryUnramifiedInclusion ν χ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν (unitaryUnramifiedInclusion ν χ)) π) :
        SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) = Quotient.mk _ A.val := hχ
  let Φ := SmoothRep.equivOfIso
    ((irreducibleAdmissibleProperty (k := ℂ) (G := M)).ι.mapIso
      (Classical.choice (Quotient.exact hclass)))
  exact HasXiBoundedCoefficients.of_equiv Φ
    (HasXiBoundedCoefficients.twist _
      (unramifiedCharacter_isOpen_ker ν (unitaryUnramifiedInclusion ν χ)) (fun m => χ.2.2 m) h)

end Orbit

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

/-- **Coefficient bounds along the unitary unramified orbit of a representation of `M_I(F)`**:
for the actual Levi subgroup `M_I(F)` of the standard parabolic `P_I(F)` and its weight
`Ξ^{M_I} = rationalLeviXi hKc hM`, if the coefficients of `π` are bounded by `c Ξ^{M_I}`
(`hcoeff`), then so are those of every representative `A` of a class in the orbit of `π` under
the unitary unramified characters of `M_I(F)`. This is the hypothesis `hcoeffA` of the orbit
results of `RationalInducedConstantTermFourier`, obtained from `hcoeff`. -/
theorem rationalLeviXi_coefficientBound_unitaryOrbitRepresentative
    (hM : IsIwasawaPair
      ((standardParabolicPoints i ν ∅).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
      ((K : Subgroup (rationalPoints G)).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π)
    (v : A.val.obj) (ℓ : SmoothDual A.val.obj.representation) :
    ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (A.val.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m :=
  HasXiBoundedCoefficients.unitaryOrbitRepresentative _ π hcoeff A v ℓ

end Rational

end Langlands.HarishChandraSchwartz
