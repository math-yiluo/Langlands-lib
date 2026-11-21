import Langlands.Correspondence.HenniartWeilSwanBreak
import Langlands.Representation.CyclicRestriction
import Mathlib.Algebra.Group.Int.TypeTags

/-! # Torsion number one and irreducibility on actual Weil inertia -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence FiniteRepresentation Weil.Local
open Ramification.Padic Ramification.HerbrandBridge CyclicRestriction

universe uK uW
variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- Dividing a Weil element by the geometric Frobenius lift to the power of
its degree leaves an inertia element. -/
theorem mem_localInertia_div_geometricFrobenius (w : localWeilGroup K) :
    w * ((localGeometricFrobenius K) ^ (localDegree K w).toAdd)⁻¹ ∈ localInertia K := by
  change (localDegree K).toMonoidHom _ = 1
  rw [map_mul, map_inv, map_zpow]
  change localDegree K w * (localDegree K (localGeometricFrobenius K) ^
    (localDegree K w).toAdd)⁻¹ = 1
  rw [localGeometricFrobenius_degree]
  have h : Multiplicative.ofAdd (1 : ℤ) ^ (localDegree K w).toAdd = localDegree K w := by
    apply Multiplicative.toAdd.injective
    simp
  rw [h, mul_inv_cancel]

/-- Every algebraic character trivial on actual inertia is the constructed
continuous unramified character of its value at geometric Frobenius. -/
theorem character_eq_unramifiedCharacter_of_ker
    (χ : localWeilGroup K →* ℂˣ) (hχ : localInertia K ≤ χ.ker) :
    χ = (unramifiedCharacter (localDegree K) (χ (localGeometricFrobenius K))).toMonoidHom := by
  apply MonoidHom.ext
  intro w
  have hw : χ (w * ((localGeometricFrobenius K) ^ (localDegree K w).toAdd)⁻¹) = 1 :=
    hχ (mem_localInertia_div_geometricFrobenius K w)
  change χ w = χ (localGeometricFrobenius K) ^ (localDegree K w).toAdd
  rwa [map_mul, map_inv, map_zpow, mul_inv_eq_one] at hw

/-- On an actual representative the restricted action is semisimple. The
presentation map is surjective onto finite Galois inertia. -/
theorem semisimple_localInertiaRepresentation
    (A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)) (hc : A.IsContinuous) :
    Representation.IsSemisimpleRepresentation (localInertiaRepresentation K A) := by
  obtain ⟨P⟩ := continuousWeilFiniteInertiaPresentation K A hc
  let T := (absoluteFiniteExtension K P.extension).canonicalTopologicalData
  have hP := weilInertiaRestriction_surjective K P.extension
  let π := (weilInertiaRestriction K P.extension).toMonoidHom
  let R := P.representation hP
  let : Finite (inertia T K.Carrier) :=
    Finite.of_injective (fun s : inertia T K.Carrier => (s : Gal(P.extension/K.Carrier)))
      Subtype.val_injective
  let : NeZero (Nat.card (inertia T K.Carrier) : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_pos (α := inertia T K.Carrier)).ne'⟩
  have hR : R.comp π = localInertiaRepresentation K A :=
    MonoidHom.ext fun w => P.representation_apply hP w
  have hs : Representation.IsSemisimpleRepresentation R := inferInstance
  rw [← hR]
  exact isSemisimpleRepresentation_comp_of_surjective R π hP hs

/-- The class twist is represented by the actual scalar twist on every
representative. -/
theorem weilTwistRepresentative_classOf {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (hA : classOf A = weilClassForget K σ) (χ : localWeilGroup K →ₜ* ℂˣ) :
    classOf (FiniteRepresentation.twist χ.toMonoidHom A) =
      weilClassForget K (n := k.succPNat) (continuousIrreducibleTwistEquiv χ (k + 1) σ) :=
  (twistClass_classOf χ.toMonoidHom A).symm.trans
    ((congrArg (twistClass χ.toMonoidHom) hA).trans
      (forget_continuousIrreducibleTwistEquiv χ (k + 1) σ).symm)

/-- A stabilizing unramified twist is exactly an equivalence on actual
representatives. -/
theorem weilUnramifiedTwist_eq_iff_equiv {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (hA : classOf A = weilClassForget K σ) (z : ℂˣ) :
    weilUnramifiedTwist K k z σ = σ ↔ Nonempty
      ((Langlands.twist (unramifiedCharacter (localDegree K) z).toMonoidHom A.representation).Equiv
        A.representation) := by
  let χ := unramifiedCharacter (localDegree K) z
  let B := FiniteRepresentation.twist χ.toMonoidHom A
  have hB : classOf B = weilClassForget K (weilUnramifiedTwist K k z σ) :=
    weilTwistRepresentative_classOf K hA χ
  change _ ↔ Nonempty (FiniteRepresentation.Equiv B A)
  rw [← classOf_eq_iff B A, hB, hA]
  constructor
  · exact congrArg (weilClassForget K)
  · intro h
    exact Subtype.ext (forgetPropertyClass_injective _ h)

/-- The torsion number is one exactly when the restriction to actual inertia
is irreducible, on any representative of the class. -/
theorem weilTorsionNumber_eq_one_iff_inertia_irreducible {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (hA : classOf A = weilClassForget K σ) :
    weilTorsionNumber K σ = 1 ↔ (localInertiaRepresentation K A).IsIrreducible := by
  let F := localGeometricFrobenius K
  let S := {z : ℂˣ // weilUnramifiedTwist K k z σ = σ}
  have h1 : weilUnramifiedTwist K k 1 σ = σ := by
    apply (weilUnramifiedTwist_eq_iff_equiv K hA 1).mpr
    have hχ : (unramifiedCharacter (localDegree K) 1).toMonoidHom = 1 := by
      ext w
      simp
    rw [hχ]
    exact ⟨FiniteRepresentation.twistOneEquiv A⟩
  let one : S := ⟨1, h1⟩
  constructor
  · intro ht
    let : Subsingleton S := (Nat.card_eq_one_iff_unique.mp ht).1
    obtain ⟨hc, hi⟩ := weilRepresentative_continuous_irreducible K hA
    exact isIrreducible_comp_of_no_character_self_twist A.representation (localInertia K) hi
      (semisimple_localInertiaRepresentation K A hc) F
      (fun w => ⟨_, mem_localInertia_div_geometricFrobenius K w⟩) (by
        intro χ hχ he
        have hη := character_eq_unramifiedCharacter_of_ker K χ hχ
        rw [hη] at he
        let z : S := ⟨χ F, (weilUnramifiedTwist_eq_iff_equiv K hA _).mpr he⟩
        have hval : χ F = 1 := congrArg (fun z : S => z.val) (Subsingleton.elim z one)
        change χ = (unramifiedCharacter (localDegree K) (χ F)).toMonoidHom at hη
        rw [hη, hval]
        ext w
        simp)
  · intro hi
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨one, fun z => Subtype.ext ?_⟩
    obtain ⟨e⟩ := (weilUnramifiedTwist_eq_iff_equiv K hA z.val).mp z.property
    let χ := unramifiedCharacter (localDegree K) z.val
    have hχ : localInertia K ≤ χ.toMonoidHom.ker := fun _ hw =>
      unramifiedCharacter_on_kernel (localDegree K) z.val hw
    have he := no_character_self_twist_of_irreducible_comp A.representation (localInertia K)
      hi χ.toMonoidHom hχ e
    have h := DFunLike.congr_fun he F
    change χ F = 1 at h
    rwa [show χ F = z.val from unramifiedCharacter_degree_one (localDegree K) z.val
      (localGeometricFrobenius_degree K)] at h

/-- Inertia irreducibility is a property of a Weil class: some actual
representative is irreducible on the local inertia subgroup. -/
def WeilInertiallyIrreducible {k : ℕ} (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) : Prop :=
  ∃ A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K),
    classOf A = weilClassForget K σ ∧ (localInertiaRepresentation K A).IsIrreducible

theorem weilInertiallyIrreducible_iff_torsionNumber_eq_one {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    WeilInertiallyIrreducible K σ ↔ weilTorsionNumber K σ = 1 := by
  constructor
  · rintro ⟨A, hA, hi⟩
    exact (weilTorsionNumber_eq_one_iff_inertia_irreducible K hA).mpr hi
  · intro ht
    obtain ⟨A, hA⟩ := Quotient.exists_rep σ.val
    have h : classOf A.val = weilClassForget K σ := congrArg (forgetPropertyClass _) hA
    exact ⟨A.val, h, (weilTorsionNumber_eq_one_iff_inertia_irreducible K h).mp ht⟩

end Langlands.Henniart.Numerical
