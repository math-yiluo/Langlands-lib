import Langlands.Representation.Jacquet.CoefficientRestrictedFiltration

/-! Native normal coinvariants and the actual character-one subgroup functor. -/

noncomputable section

namespace Langlands.Jacquet.Localization.Coefficient

universe uR uG uV uW

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]

section Normal

variable (N M : Subgroup G) [N.Normal]
variable (hMN : M ≤ Subgroup.normalizer N)
variable (ρ : Representation R G V)

/-- The original native normal action and character-one localization agree
on their actual quotient representatives. -/
def normalCoinvariantsLocalizationEquiv :
    Representation.Equiv ((ρ.toCoinvariants N).comp M.subtype)
      (action ρ N 1 M hMN (isInvariant_one N M hMN)) where
  toLinearEquiv := (trivialEquiv ρ N M hMN).symm.toLinearEquiv
  isIntertwining' m := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N q
    rfl

@[simp]
theorem normalCoinvariantsLocalizationEquiv_mk (v : V) :
    normalCoinvariantsLocalizationEquiv N M hMN ρ (Jacquet.mk ρ N v) =
      mk ρ N 1 v := rfl

@[simp]
theorem normalCoinvariantsLocalizationEquiv_symm_mk (v : V) :
    (normalCoinvariantsLocalizationEquiv N M hMN ρ).symm (mk ρ N 1 v) =
      Jacquet.mk ρ N v := rfl

/-- The comparison commutes with every native ambient intertwiner. -/
theorem normalCoinvariantsLocalizationEquiv_natural
    {σ : Representation R G W} (T : ρ.IntertwiningMap σ)
    (q : Jacquet.Coinvariants ρ N) :
    normalCoinvariantsLocalizationEquiv N M hMN σ
        (Representation.Coinvariants.map _ _ (Jacquet.restrictMap T N) q) =
      map N 1 M hMN (isInvariant_one N M hMN) T
        (normalCoinvariantsLocalizationEquiv N M hMN ρ q) := by
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N q
  rfl

end Normal

section Nested

variable (U M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
variable (Q : Subgroup G) (hUQ : U ≤ Q) (hMQ : M ≤ Q)
variable [(U.subgroupOf Q).Normal]
variable (ρ : Representation R Q V)

/-- The original output subgroup acts on the native normal quotient through
its actual inclusion in `Q`. This is the concrete carrier of `subgroupFunctor`. -/
def normalCoinvariantsSubgroupEquiv :
    Representation.Equiv
      ((ρ.toCoinvariants (U.subgroupOf Q)).comp (Subgroup.inclusion hMQ))
      (((subgroupFunctor (R := R) U M hMU Q hUQ hMQ).obj (Rep.of ρ)).ρ) where
  toLinearEquiv :=
    (normalCoinvariantsLocalizationEquiv (U.subgroupOf Q) (M.subgroupOf Q)
      (nested_normalizes U M hMU Q hUQ) ρ).toLinearEquiv
  isIntertwining' m := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ (U.subgroupOf Q) q
    rfl

@[simp]
theorem normalCoinvariantsSubgroupEquiv_mk (v : V) :
    normalCoinvariantsSubgroupEquiv U M hMU Q hUQ hMQ ρ
        (Jacquet.mk ρ (U.subgroupOf Q) v) =
      mk ρ (U.subgroupOf Q) 1 v := rfl

@[simp]
theorem normalCoinvariantsSubgroupEquiv_symm_mk (v : V) :
    (normalCoinvariantsSubgroupEquiv U M hMU Q hUQ hMQ ρ).symm
        (mk ρ (U.subgroupOf Q) 1 v) =
      Jacquet.mk ρ (U.subgroupOf Q) v := rfl

/-- The actual nested quotient comparison is natural in every `Q`-intertwiner. -/
theorem normalCoinvariantsSubgroupEquiv_natural
    {σ : Representation R Q W} (T : ρ.IntertwiningMap σ)
    (q : Jacquet.Coinvariants ρ (U.subgroupOf Q)) :
    normalCoinvariantsSubgroupEquiv U M hMU Q hUQ hMQ σ
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap T (U.subgroupOf Q)) q) =
      mapLinear (U.subgroupOf Q) 1 T
        (normalCoinvariantsSubgroupEquiv U M hMU Q hUQ hMQ ρ q) := by
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ (U.subgroupOf Q) q
  rfl

end Nested

end Langlands.Jacquet.Localization.Coefficient
