import Langlands.ClassFieldTheory.Local.InertiaNormActualModels
import Langlands.ClassFieldTheory.Local.InertiaFixedFieldNormStatement
import Langlands.ClassFieldTheory.Local.InertiaNormTransport
import Langlands.FieldTheory.SolvableGaloisTowerProof
import Langlands.Galois.Local.TotallyRamifiedSolvabilityProof
import Langlands.ClassFieldTheory.Local.PrimeInertiaNormProof

/-! Finite Galois norm surjectivity above the actual canonical inertia fixed field. -/
noncomputable section
namespace Langlands.ClassFieldTheory.Local.InertiaNormReduction
open Langlands Langlands.LocalClassField IntermediateField
open Langlands.ClassFieldTheory.Local.InertiaNormDescent Langlands.ClassFieldTheory.Local.InertiaNormFieldModels Langlands.ClassFieldTheory.Local.InertiaNormActualModels
universe u

/-- The first step of the published solvable tower is a prime Galois subextension. -/
theorem prime_subextension (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Group.IsSolvable Gal(L/K)]
    (hdeg : Module.finrank K L ≠ 1) :
    ∃ B : IntermediateField K L, IsGalois K B ∧ Nat.Prime (Module.finrank K B) := by
  obtain ⟨n, T, hbot, htop, hstep⟩ := FieldTheory.solvableGaloisPrimeTower K L
  cases n with
  | zero =>
    have hbt : (⊥ : IntermediateField K L) = ⊤ := hbot.symm.trans htop
    exact False.elim (hdeg (IntermediateField.bot_eq_top_iff_finrank_eq_one.mp hbt))
  | succ n =>
    let i : Fin (n + 1) := 0
    obtain ⟨h, hfin, hGal, _, hp⟩ := hstep i
    let A := T i.castSucc
    let B := T i.succ
    let : Algebra A B := (IntermediateField.inclusion h).toAlgebra
    let : FiniteDimensional A B := hfin
    let : IsGalois A B := hGal
    have hA : A = ⊥ := hbot
    let e : A ≃ₐ[K] K := (IntermediateField.equivOfEq hA).trans (IntermediateField.botEquiv K L)
    have hc : (algebraMap K B).comp e.toRingEquiv.toRingHom =
        (RingEquiv.refl B).toRingHom.comp (algebraMap A B) := by
      ext a
      change algebraMap K L (e a) = (a : L)
      have ha := congrArg (fun x : (⊥ : IntermediateField K L) => (x : L))
        ((IntermediateField.botEquiv K L).symm_apply_apply
          ((IntermediateField.equivOfEq hA) a))
      exact ha
    refine ⟨B, IsGalois.of_equiv_equiv (F := A) (E := B)
      (f := e.toRingEquiv) (g := RingEquiv.refl B) hc, ?_⟩
    rwa [← Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl B) hc]

/-- The canonical compositum inclusion has degree one exactly when the other
field was already contained in the base. No finiteness of that base is needed. -/
theorem sup_finrank_eq_one_iff (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    (A B : IntermediateField K Ω) :
    letI : Algebra A (A ⊔ B : IntermediateField K Ω) :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    Module.finrank A (A ⊔ B : IntermediateField K Ω) = 1 ↔ B ≤ A := by
  let : Algebra A (A ⊔ B : IntermediateField K Ω) :=
    (IntermediateField.inclusion le_sup_left).toAlgebra
  rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
  constructor
  · intro h x hx
    obtain ⟨a, ha⟩ := h.2 (⟨x, (show B ≤ A ⊔ B from le_sup_right) hx⟩ :
      (A ⊔ B : IntermediateField K Ω))
    have he : (a : Ω) = x := congrArg (fun y : (A ⊔ B : IntermediateField K Ω) => (y : Ω)) ha
    exact he ▸ a.2
  · intro h
    refine ⟨(algebraMap A (A ⊔ B : IntermediateField K Ω)).injective, ?_⟩
    intro x
    exact ⟨⟨x.1, (show A ⊔ B ≤ A from sup_le le_rfl h) x.2⟩, rfl⟩

/-- A nontrivial totally ramified Galois local model contains a totally ramified
prime Galois subextension, disjoint from the same actual inertia field. -/
theorem prime_local_subextension (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (D : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier D.field]
    (hdisj : D.field.LinearDisjoint (U p F))
    (hram : (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier D.field * F.canonicalTopologicalData.ramificationIndex)
    (hdeg : Module.finrank F.Carrier D.field ≠ 1) :
    ∃ Q : FiniteIntermediateExtension F.Carrier,
      Q.field ≤ D.field ∧ IsGalois F.Carrier Q.field ∧
      Nat.Prime (Module.finrank F.Carrier Q.field) ∧
      Q.field.LinearDisjoint (U p F) ∧
      (Q.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
        Module.finrank F.Carrier Q.field * F.canonicalTopologicalData.ramificationIndex := by
  let : Group.IsSolvable Gal(D.field/F.Carrier) :=
    PadicField.totallyRamifiedGaloisSolvability p F D hram
  obtain ⟨B, hGal, hp⟩ := prime_subextension F.Carrier D.field hdeg
  let : IsGalois F.Carrier B := hGal
  let Q : FiniteIntermediateExtension F.Carrier :=
    ⟨B.map D.field.val, Module.Finite.equiv (IntermediateField.equivMap B D.field.val).toLinearEquiv⟩
  have hQ : Q.field ≤ D.field := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hQdisj := hdisj.of_le_left hQ
  refine ⟨Q, hQ, IsGalois.of_algEquiv (IntermediateField.equivMap B D.field.val), ?_,
    hQdisj, PadicField.inertiaDisjointTotallyRamified p F Q hQdisj⟩
  rwa [← (IntermediateField.equivMap B D.field.val).toLinearEquiv.finrank_eq]

/-- Degree-one norms are surjective on all field units. -/
theorem surjective_norm_degree_one (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (h : Module.finrank K L = 1) :
    Function.Surjective (normUnits K L) := by
  intro x
  refine ⟨Units.map (algebraMap K L) x, ?_⟩
  apply Units.ext
  change Algebra.norm K (algebraMap K L (x : K)) = (x : K)
  rw [Algebra.norm_algebraMap, h, pow_one]

end Langlands.ClassFieldTheory.Local.InertiaNormReduction

namespace Langlands.ClassFieldTheory.Local

open Langlands Langlands.LocalClassField IntermediateField
open InertiaNormDescent InertiaNormFieldModels InertiaNormActualModels InertiaNormReduction

universe u

set_option maxHeartbeats 800000 in
/-- Every finite Galois extension of a finite extension of the actual canonical
inertia fixed field has surjective determinant norm on all field units. -/
theorem inertiaFixedFieldNormSurjectivity :
    Langlands.ClassFieldTheory.Local.InertiaFixedFieldNormSurjectivity.{u} := by
  suffices H : ∀ n (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
      (E L : Type u) [Field E] [Field L]
      [Algebra (U p F) E] [FiniteDimensional (U p F) E]
      [Algebra E L] [FiniteDimensional E L] [IsGalois E L],
      Module.finrank E L = n → Function.Surjective (normUnits E L) by
    intro p _ F
    dsimp only
    intro E L _ _ _ _ _ _ _
    exact H (Module.finrank E L) p F E L rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p _ F E L _ _ _ _ _ _ _ hn
    by_cases hdeg : Module.finrank E L = 1
    · exact surjective_norm_degree_one E L hdeg
    obtain ⟨F', D, hGalD, hdisjD, hramD, eE, eL, hc⟩ := actual_models p F E L
    let V := U p F' ⊔ D.field
    let : Algebra (U p F') V := (IntermediateField.inclusion le_sup_left).toAlgebra
    let : FiniteDimensional (U p F') V := finiteDimensional_sup_left (U p F') D.field
    let : Module.Free (U p F') V := Module.Free.of_divisionRing _ _
    let : IsGalois (U p F') V := IsGalois.of_equiv_equiv (F := E) (E := L)
      (f := eE) (g := eL) hc
    have hdegree : Module.finrank (U p F') V = n :=
      (Algebra.finrank_eq_of_equiv_equiv eE eL hc).symm.trans hn
    have hDne : Module.finrank F'.Carrier D.field ≠ 1 := by
      intro hD
      have hDU : D.field ≤ U p F' := by
        rw [IntermediateField.finrank_eq_one_iff.mp hD]
        exact bot_le
      have hVone := (sup_finrank_eq_one_iff F'.Carrier (AlgebraicClosure F'.Carrier)
        (U p F') D.field).mpr hDU
      apply hdeg
      exact (Algebra.finrank_eq_of_equiv_equiv eE eL hc).trans hVone
    let : IsGalois F'.Carrier D.field := hGalD
    obtain ⟨Q, hQD, hGalQ, hp, hdisjQ, hramQ⟩ :=
      prime_local_subextension p F' D hdisjD hramD hDne
    let : IsGalois F'.Carrier Q.field := hGalQ
    let W := U p F' ⊔ Q.field
    let : Algebra (U p F') W := (IntermediateField.inclusion le_sup_left).toAlgebra
    let : FiniteDimensional (U p F') W := finiteDimensional_sup_left (U p F') Q.field
    let : Module.Free (U p F') W := Module.Free.of_divisionRing _ _
    let : Module.IsTorsionFree (U p F') W := DivisionSemiring.to_moduleIsTorsionFree
    have hWV : W ≤ V := sup_le_sup_left hQD (U p F')
    let : Algebra W V := (IntermediateField.inclusion hWV).toAlgebra
    let : IsScalarTower (U p F') W V := IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional W V := Module.Finite.right (U p F') W V
    let : Module.Free W V := Module.Free.of_divisionRing _ _
    let : Module.IsTorsionFree W V := DivisionSemiring.to_moduleIsTorsionFree
    let : IsGalois W V := IsGalois.tower_top_of_isGalois (U p F') W V
    have hWne : Module.finrank (U p F') W ≠ 1 := by
      intro hW
      have hQU := (sup_finrank_eq_one_iff F'.Carrier (AlgebraicClosure F'.Carrier)
        (U p F') Q.field).mp hW
      have hQbot : Q.field = ⊥ := by
        simpa only [inf_eq_left.mpr hQU] using hdisjQ.inf_eq_bot
      apply hp.ne_one
      rw [hQbot]
      exact IntermediateField.finrank_bot
    have hWgt : 1 < Module.finrank (U p F') W := by
      have hpos := Module.finrank_pos (R := U p F') (M := W)
      omega
    have hsmaller : Module.finrank W V < n := calc
      Module.finrank W V < Module.finrank (U p F') W * Module.finrank W V := by
        simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hWgt
          (Module.finrank_pos (R := W) (M := V))
      _ = n := (Module.finrank_mul_finrank (U p F') W V).trans hdegree
    have hnormW : Function.Surjective (normUnits (U p F') W) := primeNormOverInertiaFixedField p F' Q hp hramQ
    have hnormV : Function.Surjective (normUnits W V) :=
      ih (Module.finrank W V) hsmaller p F' W V rfl
    exact Langlands.ClassFieldTheory.Local.InertiaNormTransport.surjective_norm_of_equiv E L (U p F') V eE eL hc
      (Langlands.ClassFieldTheory.Local.InertiaNormTransport.surjective_norm_trans (U p F') W V hnormW hnormV)

end Langlands.ClassFieldTheory.Local
