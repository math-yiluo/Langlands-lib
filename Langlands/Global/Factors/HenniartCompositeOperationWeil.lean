import Langlands.Weil.Representation.RestrictionDual
import Langlands.VirtualRepresentation.Weil.GroupTransport
import Langlands.VirtualRepresentation.Weil.UnitaryOperations
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers
import Langlands.Global.Factors.CompletionReciprocityTransport
import Langlands.Global.Factors.RelativeIsometryOperationStatement
import Langlands.HarmonicAnalysis.ConductorTransport

/-!
# Restriction of Weil lattices along a group isomorphism and the operations

For a topological group isomorphism `e : G ≃ₜ* H`, restriction of continuous
irreducible classes along `e` commutes with the contragredient, carries the twist by
a character `χ` of `H` to the twist by `χ ∘ e`, and carries the rank-one class of
`χ` to the rank-one class of `χ ∘ e`.

In completion form, for `f : K ≅ F_v` and `φ = completionWeilEquiv v h K f`, the
pullback `completionWeilLatticeEquiv v h K f` commutes with the contragredient, and
carries the twist and rank-one class of the Weil character of `χ'` along `e'` to
those of `χ` along `e` whenever the first Weil character restricts along `φ` to
the second. This holds when `rec_{F_v} ∘ φ = f ∘ rec_K` and `χ' ∘ f = χ`.
-/

noncomputable section

universe uG uH uV

namespace Langlands.FiniteRepresentation

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

/-- Restriction of a character twist is the twist of the restriction by the
restricted character, through the identity map. -/
def restrictTwistEquiv (φ : G →* H) (χ : H →* ℂˣ) (A : FiniteRepresentation.{0, uH, uV} ℂ H) :
    Equiv (restrict φ (twist χ A)) (twist (χ.comp φ) (restrict φ A)) where
  toLinearEquiv := LinearEquiv.refl ℂ A
  isIntertwining' _ := rfl

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- Restriction along `e` carries the twist by `χ` to the twist by `χ ∘ e`. -/
theorem restrictBasisEquiv_twistBasisEquiv (e : G ≃ₜ* H) (χ : H →ₜ* ℂˣ)
    (b : IrreducibleBasis.{uH, uV} H) :
    restrictBasisEquiv e (twistBasisEquiv χ b) =
      twistBasisEquiv (χ.comp (e : G →ₜ* H)) (restrictBasisEquiv e b) := by
  obtain ⟨n, c, hc⟩ := b
  induction c using Quotient.inductionOn with
  | h A =>
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Quotient.sound
      ⟨restrictTwistEquiv (e : G →ₜ* H).toMonoidHom χ.toMonoidHom A.val⟩)))

/-- Restriction along `e` carries the rank-one class of `χ` to that of `χ ∘ e`. -/
theorem restrictBasisEquiv_characterClass (e : G ≃ₜ* H) (χ : H →ₜ* ℂˣ) :
    restrictBasisEquiv.{uG, uH, uV} e ⟨1, continuousIrreducibleCharacterClass χ⟩ =
      ⟨1, continuousIrreducibleCharacterClass (χ.comp (e : G →ₜ* H))⟩ :=
  Sigma.ext rfl (heq_of_eq (Subtype.ext (Quotient.sound
    ⟨restrictCharacterLineEquiv (e : G →ₜ* H).toMonoidHom χ.toMonoidHom⟩)))

/-- Restriction along `e` commutes with the unitary twist lattice operation. -/
theorem restrictUnitaryLatticeEquiv_unitaryTwistLatticeEquiv (e : G ≃ₜ* H)
    (χ : H →ₜ* ℂˣ) (hχ : ∀ h : H, ‖(χ h : ℂ)‖ = 1)
    (hχe : ∀ g : G, ‖((χ.comp (e : G →ₜ* H)) g : ℂ)‖ = 1)
    (x : UnitaryLattice.{uH, uV} H) :
    restrictUnitaryLatticeEquiv e (unitaryTwistLatticeEquiv χ hχ x) =
      unitaryTwistLatticeEquiv (χ.comp (e : G →ₜ* H)) hχe (restrictUnitaryLatticeEquiv e x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single b m =>
    simp only [unitaryTwistLatticeEquiv_single, restrictUnitaryLatticeEquiv_single]
    congr 1
    exact Subtype.ext (restrictBasisEquiv_twistBasisEquiv e χ b.val)

/-- The unitary twist depends only on the character. -/
theorem unitaryTwistLatticeEquiv_congr {χ₁ χ₂ : G →ₜ* ℂˣ} (hχ : χ₁ = χ₂)
    (h₁ : ∀ g : G, ‖(χ₁ g : ℂ)‖ = 1) (h₂ : ∀ g : G, ‖(χ₂ g : ℂ)‖ = 1) :
    unitaryTwistLatticeEquiv.{uG, uV} χ₁ h₁ = unitaryTwistLatticeEquiv χ₂ h₂ := by
  subst hχ
  rfl

variable [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- Restriction along `e` commutes with the contragredient on basis classes. -/
theorem restrictBasisEquiv_dualBasisEquiv (e : G ≃ₜ* H) (b : IrreducibleBasis.{uH, uV} H) :
    restrictBasisEquiv e (dualBasisEquiv b) = dualBasisEquiv (restrictBasisEquiv e b) := by
  obtain ⟨n, c, hc⟩ := b
  induction c using Quotient.inductionOn with
  | h A =>
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Quotient.sound
      ⟨restrictDualEquiv (e : G →ₜ* H).toMonoidHom A.val⟩)))

/-- Restriction along `e` commutes with the unitary contragredient lattice operation. -/
theorem restrictUnitaryLatticeEquiv_unitaryDualLatticeEquiv (e : G ≃ₜ* H)
    (x : UnitaryLattice.{uH, uV} H) :
    restrictUnitaryLatticeEquiv e (unitaryDualLatticeEquiv x) =
      unitaryDualLatticeEquiv (restrictUnitaryLatticeEquiv e x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single b m =>
    simp only [unitaryDualLatticeEquiv_single, restrictUnitaryLatticeEquiv_single]
    congr 1
    exact Subtype.ext (restrictBasisEquiv_dualBasisEquiv e b.val)

end Langlands.VirtualRepresentation.Weil

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic
open Langlands.VirtualRepresentation

universe u uK uW

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- Every modulus-one field character `χ` of `K` is `χ' ∘ f` for a modulus-one
field character `χ'` of the completion package `padicField v`. -/
theorem exists_completionQuasiCharacter (χ : Correspondence.QuasiCharacter K)
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    letI := (padicFieldAt v h).algebra
    ∃ χ' : Correspondence.QuasiCharacter (padicField v), (∀ b, ‖(χ' b : ℂ)‖ = 1) ∧
      ∀ (a : K.Carrierˣ) (b : (padicField v).Carrierˣ),
        (b : (padicField v).Carrier) = f (a : K.Carrier) → χ' b = χ a := by
  subst h
  let := (padicFieldAt v rfl).algebra
  let : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
  refine ⟨PadicField.ConductorTransport.quasicharacter K (padicFieldAt v rfl) f χ,
    fun b => hχ _, fun a b hab => ?_⟩
  exact (PadicField.ConductorTransport.quasicharacter_apply K (padicFieldAt v rfl) f χ b).trans
    (congrArg χ (Units.ext
      ((PadicField.ConductorTransport.unitsEquiv_symm_apply K (padicFieldAt v rfl) f b).trans
        (f.symm_apply_eq.2 hab))))

/-- If `rec_{F_v} ∘ φ = f ∘ rec_K` and `χ' ∘ f = χ`, then the Weil character of
`χ'` restricted along `φ = completionWeilEquiv v h K f` is the Weil character of
`χ`. -/
theorem weilCharacter_comp_completionWeilEquiv
    (e : Correspondence.ReciprocityCandidate K)
    (e' : Correspondence.ReciprocityCandidate (padicField v))
    (he : letI := (padicFieldAt v h).algebra
      ∀ w : localWeilGroup K,
        (LocalFactor.RankOne.reciprocityUnits (padicField v) e'
            (completionWeilEquiv v h K f w) : (padicField v).Carrier) =
          f (LocalFactor.RankOne.reciprocityUnits K e w : K.Carrier))
    (χ : Correspondence.QuasiCharacter K)
    (χ' : Correspondence.QuasiCharacter (padicField v))
    (hχ : letI := (padicFieldAt v h).algebra
      ∀ (a : K.Carrierˣ) (b : (padicField v).Carrierˣ),
        (b : (padicField v).Carrier) = f (a : K.Carrier) → χ' b = χ a) :
    (LocalFactor.RankOne.weilCharacter (padicField v) e' χ').comp
        (completionWeilEquiv v h K f : localWeilGroup K →ₜ* localWeilGroup (padicField v)) =
      LocalFactor.RankOne.weilCharacter K e χ := by
  ext w
  change ((χ' (LocalFactor.RankOne.reciprocityUnits (padicField v) e'
    (completionWeilEquiv v h K f w)) : ℂˣ) : ℂ) =
      ((χ (LocalFactor.RankOne.reciprocityUnits K e w) : ℂˣ) : ℂ)
  rw [hχ _ _ (he w)]

/-- Pullback along `completionWeilEquiv` commutes with the contragredient. -/
theorem completionWeilLatticeEquiv_unitaryDualLatticeEquiv
    (y : LocalWeil.UnitaryLattice.{u, uW} (padicField v)) :
    completionWeilLatticeEquiv v h K f (LocalWeil.unitaryDualLatticeEquiv (padicField v) y) =
      LocalWeil.unitaryDualLatticeEquiv K (completionWeilLatticeEquiv v h K f y) :=
  Weil.restrictUnitaryLatticeEquiv_unitaryDualLatticeEquiv _ y

/-- Pullback along `completionWeilEquiv` carries the twist by the Weil character of
`χ'` (along `e'`) to the twist by the Weil character of `χ` (along `e`), when
the first restricts to the second. -/
theorem completionWeilLatticeEquiv_unitaryFieldCharacterTwistLatticeEquiv
    (e : Correspondence.ReciprocityCandidate K)
    (e' : Correspondence.ReciprocityCandidate (padicField v))
    (χ : Correspondence.QuasiCharacter K) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)
    (χ' : Correspondence.QuasiCharacter (padicField v)) (hχ' : ∀ b, ‖(χ' b : ℂ)‖ = 1)
    (hcomp : (LocalFactor.RankOne.weilCharacter (padicField v) e' χ').comp
        (completionWeilEquiv v h K f : localWeilGroup K →ₜ* localWeilGroup (padicField v)) =
      LocalFactor.RankOne.weilCharacter K e χ)
    (y : LocalWeil.UnitaryLattice.{u, uW} (padicField v)) :
    completionWeilLatticeEquiv v h K f
        (LocalWeil.unitaryFieldCharacterTwistLatticeEquiv (padicField v) e' χ' hχ' y) =
      LocalWeil.unitaryFieldCharacterTwistLatticeEquiv K e χ hχ
        (completionWeilLatticeEquiv v h K f y) := by
  have key := Weil.restrictUnitaryLatticeEquiv_unitaryTwistLatticeEquiv
    (completionWeilEquiv v h K f) (LocalFactor.RankOne.weilCharacter (padicField v) e' χ')
    (LocalWeil.norm_weilCharacter_eq_one (padicField v) e' χ' hχ')
    (fun w => by rw [hcomp]; exact LocalWeil.norm_weilCharacter_eq_one K e χ hχ w) y
  refine key.trans ?_
  exact LinearEquiv.congr_fun (Weil.unitaryTwistLatticeEquiv_congr hcomp _ _) _

/-- Pullback along `completionWeilEquiv` carries the rank-one class of the Weil
character of `χ'` to that of `χ`, when the first restricts to the second. -/
theorem includeUnitary_completionWeilLatticeEquiv_rankOne
    (e : Correspondence.ReciprocityCandidate K)
    (e' : Correspondence.ReciprocityCandidate (padicField v))
    (χ : Correspondence.QuasiCharacter K)
    (χ' : Correspondence.QuasiCharacter (padicField v))
    (hcomp : (LocalFactor.RankOne.weilCharacter (padicField v) e' χ').comp
        (completionWeilEquiv v h K f : localWeilGroup K →ₜ* localWeilGroup (padicField v)) =
      LocalFactor.RankOne.weilCharacter K e χ)
    (y : LocalWeil.UnitaryLattice.{u, uW} (padicField v))
    (hy : LocalWeil.includeUnitary (padicField v) y =
      generator (⟨1, Correspondence.rankOneWeilCharacterClass.{u, uW}
        (padicField v) e' χ'⟩ : LocalWeil.Basis.{u, uW} (padicField v))) :
    LocalWeil.includeUnitary K (completionWeilLatticeEquiv v h K f y) =
      generator (⟨1, Correspondence.rankOneWeilCharacterClass.{uK, uW} K e χ⟩ :
        LocalWeil.Basis.{uK, uW} K) := by
  change Weil.includeUnitary _ (Weil.restrictUnitaryLatticeEquiv _ y) = _
  rw [Weil.includeUnitary_restrictUnitaryLatticeEquiv]
  change Weil.restrictLatticeEquiv _ (LocalWeil.includeUnitary (padicField v) y) = _
  rw [hy, Weil.restrictLatticeEquiv_generator]
  unfold Correspondence.rankOneWeilCharacterClass
  rw [Weil.restrictBasisEquiv_characterClass, hcomp]

end Langlands.Global
