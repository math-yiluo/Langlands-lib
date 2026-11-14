import Langlands.Global.Factors.RelativeWeilFunctionalEquationStatement
import Langlands.Global.Factors.RelativeWeilLocalHecke
import Langlands.ClassField.Global.LocalRelativeWeilTransferProof
import Langlands.ClassFieldTheory.Local.CommonClosureGeometricProof
import Langlands.Correspondence.BaseReciprocityCandidate
import Langlands.Correspondence.ArithmeticPairEpsilonExistenceStatement
import Langlands.Weil.Representation.TwistProperties
import Langlands.Weil.Representation.DualClasses

/-!
# Local twisted pair classes of relative Weil representations

Along a local map `ι : W_{F_z} → W_{E/F}`, the twist of `S` by the reciprocity character
`χ ∘ τ_F` depends only on the local component `χ_z`; with the existence of arithmetic pair
epsilon factors, every twisted local pair has arithmetic local factors.
-/

noncomputable section

set_option autoImplicit false

universe u uV uE

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E] {z : FinitePlace F}

/-- Twists by characters agreeing on the image of `ι` have the same local pair class. -/
theorem localPairClass_twist_congr
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    {χ₁ χ₂ : RelativeWeilGroup c F E →* ℂˣ} (h : ∀ g, χ₁ (ι g) = χ₂ (ι g)) :
    localPairClass (FiniteRepresentation.twist χ₁ S) ι =
      localPairClass (FiniteRepresentation.twist χ₂ S) ι := by
  let e : FiniteRepresentation.Equiv (localComponent (FiniteRepresentation.twist χ₁ S) ι)
      (localComponent (FiniteRepresentation.twist χ₂ S) ι) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => by
      change Langlands.twist χ₁ S.representation (ι g) =
        Langlands.twist χ₂ S.representation (ι g)
      ext x
      change ((χ₁ (ι g) : ℂˣ) : ℂ) • S.representation (ι g) x =
        ((χ₂ (ι g) : ℂˣ) : ℂ) • S.representation (ι g) x
      rw [h g])
  apply Quotient.sound
  exact ⟨WeilDeligneRepresentation.Equiv.ofIso
    ((WeilDeligneRepresentation.zeroMonodromyFunctor _).mapIso
      (FiniteRepresentation.isoOfEquiv e))⟩

/-- The same for the duals of the twists. -/
theorem localPairClass_twist_dual_congr
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    {χ₁ χ₂ : RelativeWeilGroup c F E →* ℂˣ} (h : ∀ g, χ₁ (ι g) = χ₂ (ι g)) :
    localPairClass (FiniteRepresentation.twist χ₁ S).dual ι =
      localPairClass (FiniteRepresentation.twist χ₂ S).dual ι := by
  let e : FiniteRepresentation.Equiv
      (localComponent (FiniteRepresentation.twist χ₁ S).dual ι)
      (localComponent (FiniteRepresentation.twist χ₂ S).dual ι) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => by
      change (Langlands.twist χ₁ S.representation ((ι g)⁻¹)).dualMap =
        (Langlands.twist χ₂ S.representation ((ι g)⁻¹)).dualMap
      have hg : χ₁ ((ι g)⁻¹) = χ₂ ((ι g)⁻¹) := by
        rw [← map_inv ι g, h]
      congr 1
      ext x
      change ((χ₁ ((ι g)⁻¹) : ℂˣ) : ℂ) • S.representation ((ι g)⁻¹) x =
        ((χ₂ ((ι g)⁻¹) : ℂˣ) : ℂ) • S.representation ((ι g)⁻¹) x
      rw [hg])
  apply Quotient.sound
  exact ⟨WeilDeligneRepresentation.Equiv.ofIso
    ((WeilDeligneRepresentation.zeroMonodromyFunctor _).mapIso
      (FiniteRepresentation.isoOfEquiv e))⟩

/-- Along a local relative Weil map, the reciprocity character of `χ` depends only on the
local component `χ_z`. -/
theorem reciprocityCharacter_comp_eq_of_finiteComponent_eq
    {w : FinitePlacesAbove E z} {e : LocalFactor.RankOne.ReciprocityCandidate
      (towerPadicField z w.1)}
    {ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E}
    (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC)
    {χ χ' : HeckeCharacter F} (h : χ.finiteComponent z = χ'.finiteComponent z)
    (g : Weil.Local.localWeilGroup (padicField z)) :
    reciprocityCharacter c F E χ (ι g) = reciprocityCharacter c F E χ' (ι g) := by
  have hgeo := (LocalClassField.commonClosureGeometricProof.{u, u} _ _ eC heC).1 _
    (Correspondence.baseReciprocityCandidate_spec _ eC)
  have ht := localTransferReciprocity.{u} c F E z w.1 e ι hι _ hgeo g
  rw [reciprocityCharacter_apply, reciprocityCharacter_apply, ht, map_inv, map_inv, inv_inv,
    inv_inv]
  exact congrArg (fun φ : (FiniteCompletion F z)ˣ →ₜ* ℂˣ =>
    φ (LocalFactor.RankOne.reciprocityUnits (padicField z)
      (Correspondence.baseReciprocityCandidate _ eC) g)) h

/-- The local Weil character `g ↦ χ_z(rec(g))`, along the base candidate of `eC`. -/
def localTwistCharacter (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (χ : HeckeCharacter F) : Weil.Local.localWeilGroup (padicField z) →ₜ* ℂˣ :=
  LocalFactor.RankOne.weilCharacter (padicField z) (Correspondence.baseReciprocityCandidate _ eC)
    (quasicharacterBase z (χ.finiteComponent z))

/-- Along a local relative Weil map, `χ ∘ τ_F` is the local Weil character of `χ_z`. -/
theorem reciprocityCharacter_apply_localMap
    {w : FinitePlacesAbove E z} {e : LocalFactor.RankOne.ReciprocityCandidate
      (towerPadicField z w.1)}
    {ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E}
    (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC)
    (χ : HeckeCharacter F) (g : Weil.Local.localWeilGroup (padicField z)) :
    reciprocityCharacter c F E χ (ι g) = localTwistCharacter eC χ g := by
  have hgeo := (LocalClassField.commonClosureGeometricProof.{u, u} _ _ eC heC).1 _
    (Correspondence.baseReciprocityCandidate_spec _ eC)
  have ht := localTransferReciprocity.{u} c F E z w.1 e ι hι _ hgeo g
  rw [reciprocityCharacter_apply, ht, map_inv, inv_inv]
  rfl

/-- The local pair class of a twist is the class of the twisted local component. -/
theorem localPairClass_twist_eq
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    (χ : RelativeWeilGroup c F E →* ℂˣ) (η : Weil.Local.localWeilGroup (padicField z) →* ℂˣ)
    (h : ∀ g, χ (ι g) = η g) :
    localPairClass (FiniteRepresentation.twist χ S) ι =
      WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy
        (Weil.Local.localNormCharacter (padicField z)).toMonoidHom
        (FiniteRepresentation.twist η (localComponent S ι))) := by
  let e : FiniteRepresentation.Equiv (localComponent (FiniteRepresentation.twist χ S) ι)
      (FiniteRepresentation.twist η (localComponent S ι)) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => by
      change Langlands.twist χ S.representation (ι g) =
        Langlands.twist η (localComponent S ι).representation g
      ext x
      change ((χ (ι g) : ℂˣ) : ℂ) • S.representation (ι g) x =
        ((η g : ℂˣ) : ℂ) • S.representation (ι g) x
      rw [h g])
  apply Quotient.sound
  exact ⟨WeilDeligneRepresentation.Equiv.ofIso
    ((WeilDeligneRepresentation.zeroMonodromyFunctor _).mapIso
      (FiniteRepresentation.isoOfEquiv e))⟩

/-- **Arithmetic local factors exist** for every twisted local pair of continuous
relative Weil representations, given the existence of arithmetic pair epsilon factors. -/
theorem exists_isArithmeticPairLocalFactors
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (hS : S.IsContinuous) (hS' : S'.IsContinuous)
    {w : FinitePlacesAbove E z} {e : LocalFactor.RankOne.ReciprocityCandidate
      (towerPadicField z w.1)}
    {ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E}
    (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (εz : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField z))
    (hε : LocalFactor.NonabelianSystem.IsSystem (padicField z) eC εz)
    (ψz : Correspondence.NontrivialAdditiveCharacter (padicField z)) (χ : HeckeCharacter F) :
    ∃ f : LocalFactors, IsArithmeticPairLocalFactors.{u, uV, uE} (padicField z) eC εz hε ψz
      (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) ι)
      (localPairClass S' ι)
      (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S).dual ι)
      (localPairClass S'.dual ι) f := by
  have hX := localPairClass_twist_eq S ι (reciprocityCharacter c F E χ)
    (localTwistCharacter eC χ).toMonoidHom (reciprocityCharacter_apply_localMap hι eC hε.1 χ)
  have hcont : (FiniteRepresentation.twist (localTwistCharacter eC χ).toMonoidHom
      (localComponent S ι)).IsContinuous :=
    FiniteRepresentation.isContinuous_twist _ (localComponent_isContinuous ι hS)
  obtain ⟨cc, m, hcm⟩ := hEps (padicField z) eC εz hε ψz _ (localPairClass S' ι)
    ⟨_, hX.symm, hcont⟩ ⟨_, rfl, localComponent_isContinuous ι hS'⟩
  exact ⟨⟨_, _, fun s => RankinSelberg.epsilonMonomial
      (padicField z).canonicalTopologicalData.residueCardinality cc m s⟩,
    fun _ => rfl, fun _ => rfl, cc, m, hcm, fun _ => rfl⟩

end Langlands.ClassField.Global.RelativeWeilGroup
