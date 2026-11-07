import Langlands.VirtualRepresentation.ExactInductionTwist
import Langlands.Weil.Representation.CharacterLine

/-!
# Transitivity of finite-index induction

For subgroups `T ≤ S` of `G`, inducing first from `T` (viewed inside `S`) to `S`
and then from `S` to `G` is equivalent to inducing from `T` to `G`. The
equivalence of the function models evaluates an `S`-equivariant family of
functions at the identity of `S`. It descends to continuous exact virtual groups.
-/

noncomputable section

universe uG uV

namespace Langlands.FiniteRep

variable {k : Type*} [CommRing k] {G : Type*} [Group G] {W : Type*} [AddCommGroup W]
  [Module k W] {S T : Subgroup G} (hTS : T ≤ S) (σ : Representation k T W)

/-- Coinduction in two steps through `S` is coinduction from `T`, by evaluation
at the identity of `S`. -/
def coindTransLinearEquiv :
    Representation.coindV S.subtype
        (Representation.coind (T.subgroupOf S).subtype
          (σ.comp (Subgroup.subgroupOfEquivOfLe hTS).toMonoidHom)) ≃ₗ[k]
      Representation.coindV T.subtype σ where
  toFun F := ⟨fun g => (F.1 g).1 1, by
    intro t g
    have h1 := F.2 ⟨t, hTS t.2⟩ g
    have h2 := (F.1 g).2 ⟨⟨t, hTS t.2⟩, t.2⟩ 1
    change F.1 ((t : G) * g) = _ at h1
    change (F.1 ((t : G) * g)).1 1 = σ t ((F.1 g).1 1)
    rw [h1]
    change (F.1 g).1 (1 * ⟨t, hTS t.2⟩) = _
    rw [one_mul]
    rw [mul_one] at h2
    exact h2⟩
  invFun f := ⟨fun g => ⟨fun s => f.1 ((s : G) * g), by
      intro t s
      have h := f.2 (Subgroup.subgroupOfEquivOfLe hTS t) ((s : G) * g)
      change f.1 ((((t : S) : G) * (s : G)) * g) = _
      rw [mul_assoc]
      exact h⟩, by
    intro s g
    apply Subtype.ext
    funext x
    change f.1 ((x : G) * ((s : G) * g)) = f.1 (((x * s : S) : G) * g)
    rw [Subgroup.coe_mul, mul_assoc]⟩
  left_inv F := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    funext s
    change (F.1 ((s : G) * g)).1 1 = (F.1 g).1 s
    have h := F.2 s g
    change F.1 ((s : G) * g) = _ at h
    rw [h]
    change (F.1 g).1 (1 * s) = _
    rw [one_mul]
  right_inv f := by
    apply Subtype.ext
    funext g
    change f.1 (((1 : S) : G) * g) = f.1 g
    rw [Subgroup.coe_one, one_mul]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Transitivity of coinduction as an equivalence of representations of `G`. -/
def coindTransEquiv :
    Representation.Equiv
      (Representation.coind S.subtype
        (Representation.coind (T.subgroupOf S).subtype
          (σ.comp (Subgroup.subgroupOfEquivOfLe hTS).toMonoidHom)))
      (Representation.coind T.subtype σ) :=
  Representation.Equiv.mk (coindTransLinearEquiv hTS σ) (fun _ => rfl)

end Langlands.FiniteRep

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The identification of `T`, viewed inside `S`, with `T`, as a continuous
homomorphism. -/
def subgroupOfContinuousHom {S T : Subgroup G} (hTS : T ≤ S) : T.subgroupOf S →ₜ* T where
  toMonoidHom := (Subgroup.subgroupOfEquivOfLe hTS).toMonoidHom
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalGroup G] in
theorem isOpen_subgroupOf {S T : Subgroup G} (hT : IsOpen (T : Set G)) :
    IsOpen ((T.subgroupOf S : Subgroup S) : Set S) :=
  hT.preimage continuous_subtype_val

/-- Transitivity of continuous finite-index induction on exact virtual classes:
inducing the restriction of `B` from `T` (inside `S`) to `S` and then to `G`
gives the induction of `B` from `T` to `G`. -/
theorem continuousInduce_continuousInduce_ofRepresentation
    (S T : Subgroup G) [S.FiniteIndex] [T.FiniteIndex] (hS : IsOpen (S : Set G))
    (hT : IsOpen (T : Set G)) (hTS : T ≤ S)
    (B : FiniteRepresentation.{0, uG, uV} ℂ T) (hB : B.IsContinuous) :
    continuousInduce S hS
        (continuousInduce (T.subgroupOf S) (isOpen_subgroupOf hT)
          (ofRepresentation _
            ⟨FiniteRepresentation.restrict (subgroupOfContinuousHom hTS).toMonoidHom B,
              isContinuous_restrict _ (subgroupOfContinuousHom hTS).continuous hB⟩)) =
      continuousInduce T hT (ofRepresentation _ ⟨B, hB⟩) := by
  simp only [continuousInduce, induce_ofRepresentation]
  exact ofRepresentation_eq_of_equiv _ (FiniteRep.coindTransEquiv hTS B.representation)

/-- Transitivity for continuous character lines. -/
theorem continuousInduce_continuousInduce_characterClass
    (S T : Subgroup G) [S.FiniteIndex] [T.FiniteIndex] (hS : IsOpen (S : Set G))
    (hT : IsOpen (T : Set G)) (hTS : T ≤ S) (θ : T →ₜ* ℂˣ) :
    continuousInduce S hS
        (continuousInduce (T.subgroupOf S) (isOpen_subgroupOf hT)
          (characterClass.{uG, uV} (θ.comp (subgroupOfContinuousHom hTS)))) =
      continuousInduce T hT (characterClass.{uG, uV} θ) := by
  have h := continuousInduce_continuousInduce_ofRepresentation.{uG, uV} S T hS hT hTS
    (characterLine θ.toMonoidHom) (characterLine_isContinuous θ)
  exact h

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
