import Langlands.Representation.Exponents.MaximalLeviReducibilityReductionStatements
import Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs
import Langlands.Representation.Exponents.UnramifiedTwistRadicals
import Langlands.Representation.Exponents.PositiveUnramifiedCentralTwist
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement
import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Unitary.AdmissibleSemisimplicityProof
import Mathlib.LinearAlgebra.Projection

/-! # The unitary case of Renard VII.1.3 from its inputs

Renard 2026, VII.1.3 (PDF pp.230–232): for an actual maximal proper rational parabolic
and an irreducible supercuspidal `ρ` of `M(F)` whose induction `i_P^G ρ` is reducible with
a unitary central character, some `g ∈ G(F)` outside the Levi image normalizes the Levi
and `ρ ∘ φ(F)⁻¹ ≃ ρ ψ` for a positive unramified character `ψ`. This module derives
`MaximalLeviSupercuspidalReducibilityUnitaryStatement` from the input statements of
`Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs` and Jacquet's
theorem `RationalPointsIrreducibleAdmissibleStatement`.

* If `ρ` has a unitary central character, `i_P^G ρ` is admissible and unitarizable, hence
  semisimple; the projection onto a proper summand is a non-scalar endomorphism, so the
  endomorphism input gives the Weyl element with `ψ = 1`.
* Otherwise a positive unramified twist `ρ₀ = ρ ψ` has a unitary central character, and
  `i_P^G ρ` has an irreducible unitarizable subrepresentation or quotient `W`. Hermitian
  duality for `i_P^G ρ = i_P^G (ρ₀ ψ⁻¹)` gives a nonzero morphism between `W` and
  `i_P^G (ρ ψ²)`, hence a nonzero morphism between `i_P^G (ρ ψ²)` and `i_P^G ρ`. The
  morphism input then gives either `ρ ψ² ≃ ρ`, which is excluded because it would make
  `ψ` trivial on the center and the central character of `ρ` unitary, or the Weyl element
  with the character `ψ²`.
-/

noncomputable section

universe u v uH uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Abstract

variable {H : Type uH} [Group H] [TopologicalSpace H]

/-- The action of a twisted bundled representation, evaluated. -/
theorem smoothRep_twist_representation_apply (χ : H →* ℂˣ) (hχ : IsOpen (χ.ker : Set H))
    (A : SmoothRep.{0, uH, uV} ℂ H) (h : H) (x : A) :
    (A.twist χ hχ).representation h x = ((χ h : ℂˣ) : ℂ) • A.representation h x :=
  rfl

/-- The underlying map of an isomorphism of smooth representations is injective. -/
theorem smoothRep_hom_injective_of_iso {A B : SmoothRep.{0, uH, uV} ℂ H} (e : A ≅ B) :
    Function.Injective (SmoothRep.hom e.hom) := by
  intro x y hxy
  have h := congrArg (SmoothRep.hom e.inv) hxy
  change SmoothRep.hom (e.hom ≫ e.inv) x = SmoothRep.hom (e.hom ≫ e.inv) y at h
  rwa [e.hom_inv_id] at h

/-- The underlying map of an isomorphism of smooth representations is surjective. -/
theorem smoothRep_hom_surjective_of_iso {A B : SmoothRep.{0, uH, uV} ℂ H} (e : A ≅ B) :
    Function.Surjective (SmoothRep.hom e.hom) := by
  intro y
  refine ⟨SmoothRep.hom e.inv y, ?_⟩
  change SmoothRep.hom (e.inv ≫ e.hom) y = y
  rw [e.inv_hom_id]
  rfl

/-- A nonzero semisimple representation that is not irreducible has a non-scalar
endomorphism: the projection onto a proper nonzero subrepresentation along a complement. -/
theorem exists_nonscalar_endomorphism_of_semisimple (π : SmoothRep.{0, uH, uV} ℂ H)
    [Nontrivial π] (hsem : Representation.IsSemisimpleRepresentation π.representation)
    (hred : ¬ π.IsIrreducible) :
    ∃ f : π ⟶ π, ¬ ∃ c : ℂ, ∀ x, SmoothRep.hom f x = c • x := by
  classical
  obtain ⟨S, hSbot, hStop⟩ :
      ∃ S : Subrepresentation π.representation, S ≠ ⊥ ∧ S ≠ ⊤ := by
    by_contra! hno
    apply hred
    refine { exists_pair_ne := ⟨⊥, ⊤, fun he => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
    · obtain ⟨x, hx⟩ := exists_ne (0 : π)
      apply hx
      have hmem : x ∈ (⊤ : Subrepresentation π.representation) := trivial
      rw [← he] at hmem
      exact hmem
    · by_cases h : S = ⊥
      · exact Or.inl h
      · exact Or.inr (hno S h)
  obtain ⟨C, hC⟩ := exists_isCompl S
  have hSC : IsCompl S.toSubmodule C.toSubmodule :=
    ⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hC.inf_eq_bot),
      codisjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hC.sup_eq_top)⟩
  have hCbot : C ≠ ⊥ := by
    intro h
    apply hStop
    have htop := hC.sup_eq_top
    rwa [h, sup_bot_eq] at htop
  have hne (T : Subrepresentation π.representation) (hT : T ≠ ⊥) : ∃ x ∈ T, x ≠ 0 := by
    by_contra! hno
    apply hT
    apply le_antisymm _ bot_le
    intro x hx
    exact hno x hx
  obtain ⟨s, hs, hs0⟩ := hne S hSbot
  obtain ⟨t, ht, ht0⟩ := hne C hCbot
  let q : π.representation.IntertwiningMap π.representation :=
    { toLinearMap := S.toSubmodule.projection C.toSubmodule hSC
      isIntertwining' := fun g => by
        ext v
        have hv := Submodule.sub_projection_mem hSC v
        have hsum : π.representation g v =
            π.representation g (S.toSubmodule.projection C.toSubmodule hSC v) +
              π.representation g (v - S.toSubmodule.projection C.toSubmodule hSC v) := by
          rw [← map_add, add_sub_cancel]
        simp only [LinearMap.comp_apply]
        rw [hsum, map_add,
          Submodule.projection_apply_of_mem_left hSC
            (S.apply_mem_toSubmodule g (Submodule.projection_apply_mem hSC v)),
          Submodule.projection_apply_of_mem_right hSC (C.apply_mem_toSubmodule g hv),
          add_zero] }
  refine ⟨SmoothRep.ofHom q, ?_⟩
  rintro ⟨c, hc⟩
  have h1 : c • s = s := by
    rw [← hc s]
    exact Submodule.projection_apply_of_mem_left hSC hs
  have h2 : c • t = 0 := by
    rw [← hc t]
    exact Submodule.projection_apply_of_mem_right hSC ht
  have hc0 : c = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h ht0
  rw [hc0, zero_smul] at h1
  exact hs0 h1.symm

/-- If `ρ` is isomorphic to its twist by `ψ²`, where `ψ` takes positive real values and
`ρ ψ` has a unitary central character, then `ψ` is trivial on the center and `ρ` itself
has a unitary central character. -/
theorem nonempty_unitaryCentralCharacter_of_iso_twist_twist (ρ : SmoothRep.{0, uH, uV} ℂ H)
    [Nontrivial ρ] (ψ : H →* ℂˣ) (hψ : IsOpen (ψ.ker : Set H))
    (hpos : ∀ h : H, ∃ t : ℝ, 0 < t ∧ ((ψ h : ℂˣ) : ℂ) = t)
    (c : UnitaryCentralCharacter (ρ.twist ψ hψ).representation)
    (e : ρ ≅ (ρ.twist ψ hψ).twist ψ hψ) :
    Nonempty (UnitaryCentralCharacter ρ.representation) := by
  have hact (z : Subgroup.center H) (x : ρ) :
      ((ψ z : ℂˣ) : ℂ) • ρ.representation z x = (c.character z : ℂ) • x :=
    c.acts z x
  have hone (z : Subgroup.center H) : ((ψ z : ℂˣ) : ℂ) = 1 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : ρ)
    have hEx : SmoothRep.hom e.hom x ≠ 0 := by
      intro h
      apply hx
      apply smoothRep_hom_injective_of_iso e
      rw [h, map_zero]
    have hint := Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom e.hom) (z : H) x
    rw [smoothRep_twist_representation_apply, smoothRep_twist_representation_apply,
      hact z (SmoothRep.hom e.hom x)] at hint
    have hρz : ρ.representation z x = ((ψ z : ℂˣ) : ℂ)⁻¹ • ((c.character z : ℂ) • x) := by
      rw [← hact z x, smul_smul, inv_mul_cancel₀ (ψ z).ne_zero, one_smul]
    rw [hρz, map_smul, map_smul, smul_smul, smul_smul] at hint
    have hcoef := smul_left_injective ℂ hEx hint
    have hc0 : (c.character z : ℂ) ≠ 0 := (c.character z).ne_zero
    have hsq : ((ψ z : ℂˣ) : ℂ)⁻¹ = (ψ z : ℂ) := mul_right_cancel₀ hc0 hcoef
    obtain ⟨t, ht, hψt⟩ := hpos z
    rw [hψt] at hsq ⊢
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have htt : (t : ℂ) * t = 1 :=
      calc (t : ℂ) * t = (t : ℂ)⁻¹ * t := by rw [hsq]
        _ = 1 := inv_mul_cancel₀ ht0
    have htt' : t * t = 1 := by exact_mod_cast htt
    have : t = 1 := by nlinarith
    rw [this, Complex.ofReal_one]
  exact ⟨{ character := c.character
           isOpen_ker := c.isOpen_ker
           norm_eq_one := c.norm_eq_one
           acts := fun z x => by
             rw [← hact z x, hone z, one_smul] }⟩

end Abstract

section PointMap

variable {k : Type u} [Field k] {M : GroupScheme (Spec (CommRingCat.of k))}

/-- Point maps of an automorphism and its inverse cancel. -/
theorem rationalPoints_map_hom_map_inv (φ : M ≅ M) (m : rationalPoints M) :
    rationalPoints.map φ.hom (rationalPoints.map φ.inv m) = m := by
  simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

end PointMap

section Core

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

local instance maximalLeviUnitaryProofPointTopology {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] : TopologicalSpace (rationalPoints H) :=
  RationalPointFamily.pointTopology

variable {G P M U : GroupScheme (Spec (CommRingCat.of k))}

variable [IsAffineHom M.X.hom] [NonarchimedeanGroup (rationalPoints M)]

/-- The conclusion of VII.1.3 from an isomorphism `T : ρ ≃ ρ ψ² ∘ φ(F)` with the twist on the
target. -/
theorem maximalLeviReducibility_conclusion_of_twist_sq (p : P ⟶ G) (l : M ⟶ P)
    (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (ψ : Plancherel.unramifiedCharacters
      (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul))
    (hpos : ∀ m : rationalPoints M, ∃ t : ℝ, 0 < t ∧
      (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) = t)
    (g : rationalPoints G) (φ : M ≅ M)
    (hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom) (hg : g ∉ pointImage (l ≫ p))
    (T : ρ ≃ₗ[ℂ] ((ρ.twist (ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom
        (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).twist
          (ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom
          (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)))
    (hT : ∀ (m : rationalPoints M) (x : ρ),
      T (ρ.representation m x) =
        ((ρ.twist (ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom
          (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).twist
            (ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom
            (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).representation
          (rationalPoints.map φ.hom m) (T x)) :
    ∃ (g : rationalPoints G) (φ : M ≅ M),
      φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom ∧ g ∉ pointImage (l ≫ p) ∧
      ∃ ψ : Plancherel.unramifiedCharacters
          (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
        (∀ m : rationalPoints M, ∃ t : ℝ, 0 < t ∧
          (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) = t) ∧
        ∃ T : ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : ρ),
          T (ρ.representation m x) =
            (((ψ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) : ℂˣ) : ℂ) •
              ρ.representation (rationalPoints.map φ.hom m) (T x) := by
  refine ⟨g, φ, hφ, hg, ψ * ψ, ?_, T, ?_⟩
  · intro m
    obtain ⟨t, ht, hψt⟩ := hpos m
    refine ⟨t * t, mul_pos ht ht, ?_⟩
    simp only [Subgroup.coe_mul, ContinuousMonoidHom.mul_apply, Units.val_mul, hψt,
      Complex.ofReal_mul]
  · intro m x
    rw [hT m x, smoothRep_twist_representation_apply, smoothRep_twist_representation_apply,
      smul_smul]
    simp only [Subgroup.coe_mul, ContinuousMonoidHom.mul_apply, Units.val_mul,
      ContinuousMonoidHom.coe_toMonoidHom]
    rfl

/-- The conclusion of VII.1.3 from an isomorphism `T : ρ ψ² ≃ ρ ∘ φ(F)` with the twist on
the source: invert `g`, `φ` and `T`. -/
theorem maximalLeviReducibility_conclusion_of_twist_sq_symm (p : P ⟶ G) (l : M ⟶ P)
    (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (ψ : Plancherel.unramifiedCharacters
      (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul))
    (hpos : ∀ m : rationalPoints M, ∃ t : ℝ, 0 < t ∧
      (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) = t)
    (g : rationalPoints G) (φ : M ≅ M)
    (hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom) (hg : g ∉ pointImage (l ≫ p))
    (T : ((ρ.twist (ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom
        (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).twist
          (ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom
          (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)) ≃ₗ[ℂ] ρ)
    (hT : ∀ (m : rationalPoints M) (x : ρ),
      T (((ρ.twist (ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom
          (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).twist
            (ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom
            (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).representation m x) =
        ρ.representation (rationalPoints.map φ.hom m) (T x)) :
    ∃ (g : rationalPoints G) (φ : M ≅ M),
      φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom ∧ g ∉ pointImage (l ≫ p) ∧
      ∃ ψ : Plancherel.unramifiedCharacters
          (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
        (∀ m : rationalPoints M, ∃ t : ℝ, 0 < t ∧
          (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) = t) ∧
        ∃ T : ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : ρ),
          T (ρ.representation m x) =
            (((ψ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) : ℂˣ) : ℂ) •
              ρ.representation (rationalPoints.map φ.hom m) (T x) := by
  refine ⟨g⁻¹, φ.symm, ?_, ?_, ψ * ψ, ?_, T.symm, ?_⟩
  · rw [Iso.symm_hom, G.innerIso_inv_hom, Iso.inv_comp_eq]
    simp only [← Category.assoc] at hφ ⊢
    rw [hφ]
    simp
  · intro h
    apply hg
    simpa using (pointImage (l ≫ p)).inv_mem h
  · intro m
    obtain ⟨t, ht, hψt⟩ := hpos m
    refine ⟨t * t, mul_pos ht ht, ?_⟩
    simp only [Subgroup.coe_mul, ContinuousMonoidHom.mul_apply, Units.val_mul, hψt,
      Complex.ofReal_mul]
  · intro m y
    rw [Iso.symm_hom]
    apply T.injective
    rw [LinearEquiv.apply_symm_apply]
    have hT' := hT (rationalPoints.map φ.inv m) (T.symm y)
    rw [rationalPoints_map_hom_map_inv, LinearEquiv.apply_symm_apply,
      smoothRep_twist_representation_apply, smoothRep_twist_representation_apply,
      smul_smul] at hT'
    rw [← hT']
    congr 1

/-- The unitary case of Renard VII.1.3 for a fixed actual maximal proper rational
parabolic and a fixed irreducible supercuspidal `ρ`, from the input statements. -/
theorem maximalLeviReducibilityUnitary_core [T2Space k]
    (hI0 : RationalPointsIrreducibleAdmissibleStatement.{u, v})
    (hI0G : RationalPointsIrreducibleAdmissibleStatement.{u, max u v})
    (hI1 : SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v})
    (hIA : LeviInductionAdmissibleStatement.{u, v})
    (hIU : LeviInductionUnitarizableStatement.{u, v})
    (hN : LeviInductionNontrivialStatement.{u, v})
    (hHd : LeviInductionHermitianDualityStatement.{u, v})
    (hK1 : MaximalLeviSupercuspidalInductionEndomorphismStatement.{u, v})
    (hK2 : MaximalLeviSupercuspidalInductionHomStatement.{u, v})
    (hC : MaximalLeviSupercuspidalUnitarizableConstituentStatement.{u, v})
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom]
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    [LocallyCompactSpace (rationalPoints M)]
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) (hproper : ¬ IsIso p)
    (hmax : ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G) (j : P ⟶ Q),
      IsParabolicSubgroup q → j ≫ q = p → IsIso j ∨ IsIso q)
    (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (hirr : ρ.IsIrreducible)
    (hsc : ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
      (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r')),
      ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ))
    (hred : ¬ ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).IsIrreducible)
    (hπ : Nonempty (UnitaryCentralCharacter
      ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation)) :
    ∃ (g : rationalPoints G) (φ : M ≅ M),
      φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom ∧ g ∉ pointImage (l ≫ p) ∧
      ∃ ψ : Plancherel.unramifiedCharacters
          (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
        (∀ m : rationalPoints M, ∃ t : ℝ, 0 < t ∧
          (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) = t) ∧
        ∃ T : ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : ρ),
          T (ρ.representation m x) =
            (((ψ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) : ℂˣ) : ℂ) •
              ρ.representation (rationalPoints.map φ.hom m) (T x) := by
  classical
  have hM : IsConnectedReductive M := hl.isConnectedReductive
  obtain ⟨x₀, hx₀⟩ :=
    Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible ρ.representation hirr
  have : Nontrivial ρ := ⟨⟨x₀, 0, hx₀⟩⟩
  have hρadm : ρ.IsAdmissible := hI0 k M hM ρ hirr
  by_cases hU : Nonempty (UnitaryCentralCharacter ρ.representation)
  · -- Case A: `i_P^G ρ` is admissible, unitarizable and nonzero, hence semisimple, and
    -- reducibility gives a non-scalar endomorphism.
    have hρunit : IsUnitarizable ρ.representation := hI1 k M hM ρ hirr hsc hU
    have hπadm := hIA k G hG P M U p l r hp hl hr hmul ρ hρadm
    have hπunit := hIU k G hG P M U p l r hp hl hr hmul ρ hρunit
    have := hN k G hG P M U p l r hp hl hr hmul ρ inferInstance
    have hsem := admissibleUnitarySemisimplicity (rationalPoints G)
      (compactOpenCofinal_of_nonarchimedean (rationalPoints G)) _ _ hπadm hπunit
    obtain ⟨f, hf⟩ := exists_nonscalar_endomorphism_of_semisimple _ hsem hred
    rcases hK1 k G hG P M U p l r hp hl hr hmul hproper hmax ρ hirr hsc f with
      hc | ⟨g, φ, hφ, hg, T, hT⟩
    · exact absurd hc hf
    · refine ⟨g, φ, hφ, hg, 1, fun m => ⟨1, one_pos, ?_⟩, T, fun m x => ?_⟩
      · simp
      · rw [hT m x]
        simp
  · -- Case B: twist by a positive unramified `ψ` to a unitary central character.
    have hUe : IsEmpty (UnitaryCentralCharacter ρ.representation) := not_nonempty_iff.mp hU
    obtain ⟨ψ, hpos, ⟨c₀⟩⟩ := exists_positive_unramifiedTwist_unitaryCentralCharacter hM ρ hirr
    have hχ := Plancherel.unramifiedCharacter_isOpen_ker _ ψ
    have hχinv := Langlands.isOpen_ker_inv hχ
    have hρ₀irr : (ρ.twist _ hχ).IsIrreducible :=
      (SmoothRep.isIrreducible_twist_iff _ hχ ρ).mpr hirr
    have hρ₂irr : ((ρ.twist _ hχ).twist _ hχ).IsIrreducible :=
      (SmoothRep.isIrreducible_twist_iff _ hχ _).mpr hρ₀irr
    have hρ₀sc := properJacquet_subsingleton_unramifiedTwist ψ ρ hsc
    have hρ₂sc := properJacquet_subsingleton_unramifiedTwist ψ _ hρ₀sc
    have hρ₀adm : (ρ.twist _ hχ).IsAdmissible := hI0 k M hM _ hρ₀irr
    have hρ₀unit : IsUnitarizable (ρ.twist _ hχ).representation :=
      hI1 k M hM _ hρ₀irr hρ₀sc ⟨c₀⟩
    obtain ⟨W, hWirr, hWunit, hWmap⟩ :=
      hC k G hG P M U p l r hp hl hr hmul hproper hmax ρ hirr hsc hUe hred hπ
    have hWadm : W.IsAdmissible := hI0G k G hG W hWirr
    obtain ⟨w₀, hw₀⟩ :=
      Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible W.representation hWirr
    have : Nontrivial W := ⟨⟨w₀, 0, hw₀⟩⟩
    -- `i_P^G ρ = i_P^G (ρ₀ ψ⁻¹)` and `ψ · conj(ψ⁻¹) = 1`.
    let ε : (ρ.twist _ hχ).twist _ hχinv ≅ ρ :=
      SmoothRep.mkIso (equivOfRepresentationEq (twist_inv_twist _ ρ.representation))
    let E := (leviInductionFunctor p l r hp hr hl hmul).mapIso ε
    have hconj : ∀ m : rationalPoints M,
        (((ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom m : ℂˣ) : ℂ) *
          starRingEnd ℂ ((((ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom⁻¹ m : ℂˣ) : ℂ)) = 1 := by
      intro m
      obtain ⟨t, ht, hψt⟩ := hpos m
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      change (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) *
        starRingEnd ℂ ((((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ))⁻¹ = 1
      rw [hψt, map_inv₀, Complex.conj_ofReal]
      exact mul_inv_cancel₀ (by exact_mod_cast ht.ne')
    have hd := hHd k G hG P M U p l r hp hl hr hmul _ hρ₀adm hρ₀unit _ _ hχinv hχ hconj W
      hWadm hWunit inferInstance
    rcases hWmap with ⟨f, hf⟩ | ⟨f, hf⟩
    · -- `W ⊆ i_P^G ρ`: a nonzero `i_P^G (ρ ψ²) → W → i_P^G ρ`.
      have hf' : Function.Injective (SmoothRep.hom (f ≫ E.inv)) := fun x y hxy =>
        hf (smoothRep_hom_injective_of_iso E.symm hxy)
      obtain ⟨h, x, hx⟩ := hd.1 ⟨f ≫ E.inv, hf'⟩
      have hnz : ∃ x, SmoothRep.hom (h ≫ f) x ≠ 0 :=
        ⟨x, fun h0 => hx (hf (h0.trans (map_zero _).symm))⟩
      rcases hK2 k G hG P M U p l r hp hl hr hmul hproper hmax ρ _ hirr hρ₂irr hsc hρ₂sc
          (h ≫ f) hnz with ⟨e⟩ | ⟨g, φ, hφ, hg, T, hT⟩
      · exact absurd
          (nonempty_unitaryCentralCharacter_of_iso_twist_twist ρ _ hχ hpos c₀ e.some.symm) hU
      · exact maximalLeviReducibility_conclusion_of_twist_sq p l ρ ψ hpos g φ hφ hg T hT
    · -- `i_P^G ρ ↠ W`: a nonzero `i_P^G ρ → W → i_P^G (ρ ψ²)`.
      have hf' : Function.Surjective (SmoothRep.hom (E.hom ≫ f)) := by
        intro y
        obtain ⟨x, rfl⟩ := hf y
        obtain ⟨x', rfl⟩ := smoothRep_hom_surjective_of_iso E x
        exact ⟨x', rfl⟩
      obtain ⟨h, y, hy⟩ := hd.2 ⟨E.hom ≫ f, hf'⟩
      obtain ⟨x, rfl⟩ := hf y
      have hnz : ∃ x, SmoothRep.hom (f ≫ h) x ≠ 0 := ⟨x, hy⟩
      rcases hK2 k G hG P M U p l r hp hl hr hmul hproper hmax _ ρ hρ₂irr hirr hρ₂sc hsc
          (f ≫ h) hnz with ⟨e⟩ | ⟨g, φ, hφ, hg, T, hT⟩
      · exact absurd
          (nonempty_unitaryCentralCharacter_of_iso_twist_twist ρ _ hχ hpos c₀ e.some) hU
      · exact maximalLeviReducibility_conclusion_of_twist_sq_symm p l ρ ψ hpos g φ hφ hg T hT

end Core

/-- **The unitary case of Renard VII.1.3 from its inputs.** -/
theorem maximalLeviSupercuspidalReducibilityUnitary_of_inputs
    (hI0 : RationalPointsIrreducibleAdmissibleStatement.{u, v})
    (hI0G : RationalPointsIrreducibleAdmissibleStatement.{u, max u v})
    (hI1 : SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v})
    (hIA : LeviInductionAdmissibleStatement.{u, v})
    (hIU : LeviInductionUnitarizableStatement.{u, v})
    (hN : LeviInductionNontrivialStatement.{u, v})
    (hHd : LeviInductionHermitianDualityStatement.{u, v})
    (hK1 : MaximalLeviSupercuspidalInductionEndomorphismStatement.{u, v})
    (hK2 : MaximalLeviSupercuspidalInductionHomStatement.{u, v})
    (hC : MaximalLeviSupercuspidalUnitarizableConstituentStatement.{u, v}) :
    MaximalLeviSupercuspidalReducibilityUnitaryStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  intro _ _ P M U p l r hp hl hr hmul hproper hmax
  have := hl.isConnectedReductive.isAffineHom
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hirr hsc hred hπ
  exact maximalLeviReducibilityUnitary_core hI0 hI0G hI1 hIA hIU hN hHd hK1 hK2 hC hG p l r hp
    hl hr hmul hproper hmax ρ hirr hsc hred hπ

end Langlands.Aubert.General.RepresentedParabolic
