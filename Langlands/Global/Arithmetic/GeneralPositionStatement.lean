import Langlands.HarmonicAnalysis.Conductor
import Langlands.LocalFactor.CommonClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Characters in general position (Harris 1998, Definition 4.5 and Lemma 4.7)

Mackey constituents of an induced character, Harris's general position of a
character of the Weil group of a finite extension `F'/F`, and his sufficient
condition (4.12), all over the actual subgroups of one local Weil group in the
common algebraic closure. The theorems remain proposition definitions.
-/

noncomputable section

universe uG uV uF

namespace Langlands.Global.GeneralPosition

open FiniteRepresentation

section Mackey

variable {G : Type uG} [Group G]

/-- The conjugate subgroup `g H g⁻¹`, as the preimage of `H` under `x ↦ g⁻¹ x g`. -/
abbrev conjugate (H : Subgroup G) (g : G) : Subgroup G :=
  H.comap (MulAut.conj g⁻¹).toMonoidHom

/-- The canonical map `g H g⁻¹ ∩ K → H`, `x ↦ g⁻¹ x g`, on the subgroup of `K`. -/
def conjugateRestriction (H K : Subgroup G) (g : G) :
    (conjugate H g).subgroupOf K →* H :=
  ((MulAut.conj g⁻¹).toMonoidHom.subgroupComap H).comp
    ((K.subtype.comp ((conjugate H g).subgroupOf K).subtype).codRestrict
      (conjugate H g) fun y => y.2)

/-- Harris's Mackey constituent `Ind_{g H g⁻¹ ∩ K}^K g(σ)` of `Ind_H^G σ`
restricted to `K`, where `g(σ)(x) = σ(g⁻¹ x g)`. It is the actual
finite-index induction of the actual restriction. -/
def mackeyConstituent (H K : Subgroup G) [H.FiniteIndex]
    (A : FiniteRepresentation.{0, uG, uV} ℂ H) (g : G) :
    FiniteRepresentation.{0, uG, max uG uV} ℂ K :=
  induce ((conjugate H g).subgroupOf K) (restrict (conjugateRestriction H K g) A)

end Mackey

open LocalFactor.CommonClosure Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Harris's `F̃`: the normal closure of `F'/F` in the common algebraic closure. -/
def galoisClosure (F' : Extension F) : Extension F :=
  ⟨IntermediateField.normalClosure F.Carrier F'.field (AlgebraicClosure F.Carrier),
    inferInstance⟩

/-- `L/E` is a cyclic extension of prime degree, for fields `E ≤ L` of the
common closure. The relative field is Mathlib's `extendScalars`. -/
def IsCyclicPrimeStep (E L : Extension F) : Prop :=
  ∃ h : E.field ≤ L.field,
    IsGalois E.field (IntermediateField.extendScalars h) ∧
    IsCyclic (IntermediateField.extendScalars h ≃ₐ[E.field]
      IntermediateField.extendScalars h) ∧
    (Module.finrank E.field (IntermediateField.extendScalars h)).Prime

/-- Harris 1998 Definition 4.5: a character `χ` of `W_{F'}` is in general
position relative to `F` if some tower `F̃ = F_0 ⊇ F_1 ⊇ ⋯ ⊇ F_t = F` has
cyclic steps of prime degree and, for every `i ≤ t`, every Mackey constituent
of `Ind_{F'/F} χ` restricted to `W_{F_i}` is irreducible. Constituents are
indexed by all elements of `W_F`, not by chosen double-coset representatives. -/
def IsInGeneralPosition (F' : Extension F) (χ : weilSubgroup F F' →ₜ* ℂˣ) : Prop :=
  ∃ (t : ℕ) (tower : Fin (t + 1) → Extension F),
    (tower 0).field = (galoisClosure F F').field ∧
    (tower (Fin.last t)).field = ⊥ ∧
    (∀ i : Fin t, IsCyclicPrimeStep F (tower i.succ) (tower i.castSucc)) ∧
    ∀ (i : Fin (t + 1)) (g : localWeilGroup F),
      (mackeyConstituent (weilSubgroup F F') (weilSubgroup F (tower i))
        (characterLine.{uF, 0} χ.toMonoidHom) g).IsIrreducible

theorem le_galoisClosure (F' : Extension F) :
    F'.field ≤ (galoisClosure F F').field :=
  IntermediateField.le_normalClosure F'.field

/-- `W_{F̃} ⊆ W_{F'}`. -/
theorem galoisClosure_weilSubgroup_le (F' : Extension F) :
    weilSubgroup F (galoisClosure F F') ≤ weilSubgroup F F' :=
  weilSubgroup_antitone F F' (galoisClosure F F') (le_galoisClosure F F')

/-- `W_{F̃}` is normal in `W_F`, because `F̃/F` is Galois. -/
instance galoisClosure_normal (F' : Extension F) :
    (weilSubgroup F (galoisClosure F F')).Normal := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have : IsGalois F.Carrier (IntermediateField.normalClosure F.Carrier F'.field
      (AlgebraicClosure F.Carrier)) := inferInstance
  exact ((InfiniteGalois.normal_iff_isGalois
    (galoisClosure F F').field).mpr this).comap _

/-- Harris's `χ̃ = χ ∘ N_{F̃/F'}`, read on the Weil side as the restriction of
`χ` to `W_{F̃}`. -/
def closureRestriction (F' : Extension F) (χ : weilSubgroup F F' →ₜ* ℂˣ) :
    weilSubgroup F (galoisClosure F F') →* ℂˣ :=
  χ.toMonoidHom.comp (Subgroup.inclusion (galoisClosure_weilSubgroup_le F F'))

/-- Harris 1998 (4.12): the stabilizer of `χ̃` in `W_F`, acting by
`g(χ̃)(x) = χ̃(g⁻¹ x g)`, is exactly `W_{F'}`. -/
def HasExactWeilStabilizer (F' : Extension F) (χ : weilSubgroup F F' →ₜ* ℂˣ) : Prop :=
  ∀ g : localWeilGroup F,
    (closureRestriction F F' χ).comp (MulAut.conjNormal g⁻¹).toMonoidHom =
        closureRestriction F F' χ ↔
      g ∈ weilSubgroup F F'

end Langlands.Global.GeneralPosition

namespace Langlands.Global

open LocalFactor.CommonClosure GeneralPosition

/-- Harris 1998, proof of Lemma 4.7: condition (4.12) implies general position,
including the existence of the tower of cyclic steps of prime degree. -/
def GeneralPositionOfExactStabilizerStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (χ : weilSubgroup F F' →ₜ* ℂˣ),
    HasExactWeilStabilizer F F' χ → IsInGeneralPosition F F' χ

/-- Harris 1998, proof of Lemma 4.7: for every normalized reciprocity family,
finite-order characters of `F'ˣ` of arbitrarily large conductor satisfy (4.12). -/
def ExactStabilizerCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (e : ReciprocityFamily F), NormalizedReciprocity F e →
    ∀ r : ℕ, ∃ χ : FieldCharacter F F',
      (∃ n : ℕ, 0 < n ∧ χ ^ n = 1) ∧
      r ≤ (fieldData F F').multiplicativeConductor χ ∧
      HasExactWeilStabilizer F F' (weilCharacter F e F' χ)

/-- Harris 1998 Lemma 4.7: for every normalized reciprocity family, there are
finite-order characters of `F'ˣ` of arbitrarily large conductor in general
position relative to `F`. Finite order is part of Harris's proof. -/
def GeneralPositionCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (e : ReciprocityFamily F), NormalizedReciprocity F e →
    ∀ r : ℕ, ∃ χ : FieldCharacter F F',
      (∃ n : ℕ, 0 < n ∧ χ ^ n = 1) ∧
      r ≤ (fieldData F F').multiplicativeConductor χ ∧
      IsInGeneralPosition F F' (weilCharacter F e F' χ)

/-- Harris 1998 Lemma 4.7 together with the two steps of its proof. -/
def HarrisGeneralPositionStatement : Prop :=
  GeneralPositionOfExactStabilizerStatement.{uF} ∧ ExactStabilizerCharacterStatement.{uF} ∧
    GeneralPositionCharacterStatement.{uF}

end Langlands.Global
