import Langlands.Representation.Exponents.MaximalLeviBlockReductionStatements
import Langlands.Representation.Exponents.UnramifiedTwistRadicals
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Exponents.LeviParabolicFunctorsExactProof
import Langlands.Representation.Smooth.RenardIrreducibleExistenceProof
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Filtration.ExactSmoothSubquotients
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.GroupScheme.Rational.SplitComponentLeviPoints
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.CuspidalSupport.LeviInductionEndEmbedding
import Langlands.Representation.CuspidalSupport.RationalSummandEndCenterReduction
import Langlands.Representation.Plancherel.RationalUnramifiedRestriction

/-! # The block corollary of Renard VII.1.3 from two premises

For part (i), a reducible induction of an unramified twist `σ` of `ρ` would give a
normalizing element outside the Levi whose conjugation preserves the inertial class of
`σ`. Transporting the intertwiner to `ρ` contradicts the hypothesis on `ρ`.
For part (ii), each irreducible subquotient `τ` of a block object is isomorphic to the
induction of a twist `σ`. Frobenius reciprocity gives `σ` as a quotient of the normalized
Jacquet module of `τ`, and exactness carries subquotients through the Jacquet functor.
For part (iii), faithfulness follows from `leviInductionFunctor_faithful`. The second
premise supplies block preservation, fullness and essential surjectivity.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Twist

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]

/-- A linear equivalence `T : ρ ≃ σ` with `ψ(m) • T (ρ m x) = σ m (T x)` is an isomorphism
from the twist `ρ ⊗ ψ` to `σ`. -/
private def twistIsoOfRelation (ρ σ : SmoothRep.{0, u, v} ℂ Γ) (ψ : Γ →* ℂˣ)
    (hψ : IsOpen (ψ.ker : Set Γ)) (T : ρ ≃ₗ[ℂ] σ)
    (hT : ∀ (m : Γ) (x : ρ), ((ψ m : ℂˣ) : ℂ) • T (ρ.representation m x) =
      σ.representation m (T x)) :
    ρ.twist ψ hψ ≅ σ :=
  SmoothRep.mkIso (Representation.Equiv.mk T fun m => LinearMap.ext fun x => by
    change T (((ψ m : ℂˣ) : ℂ) • ρ.representation m x) = σ.representation m (T x)
    rw [map_smul]
    exact hT m x)

/-- A subsingleton carrier is transported along an isomorphism. -/
private theorem subsingleton_of_iso {A B : SmoothRep.{0, u, v} ℂ Γ} (e : A ≅ B)
    (h : Subsingleton A) : Subsingleton B :=
  ⟨fun x y => by
    obtain ⟨x', rfl⟩ := SmoothRep.hom_hom_surjective e x
    obtain ⟨y', rfl⟩ := SmoothRep.hom_hom_surjective e y
    rw [Subsingleton.elim x' y']⟩

end Twist

/-- The VII.1.3 reducibility theorem implies parts (i) and (ii) of `MaximalLeviBlockStatements`.
Every unramified twist of `ρ` induces irreducibly. The normalized Jacquet module of any
nonzero object of `InBlockG` has an irreducible subquotient that is an unramified twist of
`ρ`. -/
theorem maximalLeviBlock_irreducible_detection
    (hThm : MaximalLeviSupercuspidalReducibilityStatement.{u, max u v})
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      ¬ IsIso p →
      (∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G) (j : P ⟶ Q),
        IsParabolicSubgroup q → j ≫ q = p → IsIso j ∨ IsIso q) →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), ρ.IsIrreducible →
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
        (¬ ∃ (g : rationalPoints G) (φ : M ≅ M),
          φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom ∧ g ∉ pointImage (l ≫ p) ∧
          ∃ ψ : Plancherel.unramifiedCharacters
              (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
            ∃ T : ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : ρ),
              T (ρ.representation m x) =
                (((ψ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) : ℂˣ) : ℂ) •
                  ρ.representation (rationalPoints.map φ.hom m) (T x)) →
        let IsTwist : SmoothRep.{0, u, max u v} ℂ (rationalPoints M) → Prop := fun σ =>
          ∃ ψ : Plancherel.unramifiedCharacters
              (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
            ∃ T : ρ ≃ₗ[ℂ] σ, ∀ (m : rationalPoints M) (x : ρ),
              (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) • T (ρ.representation m x) =
                σ.representation m (T x)
        let InBlockG : ObjectProperty (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) :=
          fun Y => ∀ τ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
            τ.IsIrreducible → SmoothRep.IsSubquotient τ Y →
              ∃ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), IsTwist σ ∧
                SmoothRep.IsSubquotient τ ((leviInductionFunctor p l r hp hr hl hmul).obj σ)
        (∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), IsTwist σ →
          ((leviInductionFunctor p l r hp hr hl hmul).obj σ).IsIrreducible) ∧
        (∀ Y : SmoothRep.{0, u, max u v} ℂ (rationalPoints G), InBlockG Y → Nontrivial Y →
          ∃ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), σ.IsIrreducible ∧
            SmoothRep.IsSubquotient σ ((leviJacquetFunctor p l r hp hr hl hmul).obj Y) ∧
              IsTwist σ) := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul hproper hmax
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hirr hcusp hw IsTwist InBlockG
  have hI : ∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), IsTwist σ →
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).IsIrreducible := by
    rintro σ ⟨ψ, T, hT⟩
    have hker := Plancherel.unramifiedCharacter_isOpen_ker _ ψ
    let e := twistIsoOfRelation ρ σ (ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom hker T hT
    have hσirr : σ.IsIrreducible :=
      SmoothRep.isIrreducible_of_iso e ((SmoothRep.isIrreducible_twist_iff _ hker ρ).mpr hirr)
    have hσcusp : ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
        (hmul' : IsIso (subgroupMultiplication l' r')),
        ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj σ) := by
      intro P' M' U' p' l' r' hp' hl' hr' hmul' hp'proper
      exact subsingleton_of_iso ((jacquetFunctor p' l' r' hp' hr' hl' hmul').mapIso e)
        (properJacquet_subsingleton_unramifiedTwist ψ ρ hcusp P' M' U' p' l' r' hp' hl' hr'
          hmul' hp'proper)
    by_contra hred
    obtain ⟨g, φ, hφ, hg, ψ', -, T', hT'⟩ :=
      hThm k G hG P M U p l r hp hl hr hmul hproper hmax σ hσirr hσcusp hred
    have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    apply hw
    refine ⟨g, φ, hφ, hg, ψ' * ψ * (Plancherel.rationalUnramifiedCharacterRestrict φ.inv ψ)⁻¹,
      T.trans (T'.trans T.symm), ?_⟩
    intro m x
    have hφφ : rationalPoints.map φ.inv (rationalPoints.map φ.hom m) = m := by
      rw [← pointMap_comp_apply, φ.hom_inv_id]
      rfl
    have h1 : ∀ (m : rationalPoints M) (x : ρ), T (ρ.representation m x) =
        ((((ψ : rationalPoints M →ₜ* ℂˣ) m)⁻¹ : ℂˣ) : ℂ) • σ.representation m (T x) := by
      intro m x
      rw [← hT m x, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    have h2 : ∀ (m : rationalPoints M) (w : σ), σ.representation m w =
        (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) • T (ρ.representation m (T.symm w)) := by
      intro m w
      rw [hT m (T.symm w), LinearEquiv.apply_symm_apply]
    simp only [LinearEquiv.trans_apply]
    rw [h1, map_smul, hT', map_smul, map_smul, h2 (rationalPoints.map φ.hom m), map_smul,
      LinearEquiv.symm_apply_apply, smul_smul, smul_smul]
    congr 1
    change _ = (((ψ' : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) *
      (ψ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) *
      ((Plancherel.rationalUnramifiedCharacterRestrict φ.inv ψ).val
        (rationalPoints.map φ.hom m))⁻¹ : ℂˣ) : ℂ)
    rw [Plancherel.rationalUnramifiedCharacterRestrict_apply, hφφ]
    push_cast
    ring
  refine ⟨hI, ?_⟩
  intro Y hY hnt
  obtain ⟨τ, hτirr, hτY⟩ := SmoothRep.RenardIrreducibleExistence.exists_irreducible_subquotient Y
  obtain ⟨σ, hσ, hτσ⟩ := hY τ hτirr hτY
  have hiσ := hI σ hσ
  obtain ⟨e⟩ := CuspidalSupport.NormalHecke.nonempty_iso_of_isSubquotient hiσ hτirr hτσ
  have hσirr : σ.IsIrreducible := by
    obtain ⟨ψ, T, hT⟩ := hσ
    have hker := Plancherel.unramifiedCharacter_isOpen_ker _ ψ
    exact SmoothRep.isIrreducible_of_iso
      (twistIsoOfRelation ρ σ (ψ : rationalPoints M →ₜ* ℂˣ).toMonoidHom hker T hT)
      ((SmoothRep.isIrreducible_twist_iff _ hker ρ).mpr hirr)
  obtain ⟨E, -⟩ := leviFrobeniusReciprocity.{u, max u v, max u v} k G hG P M U p l r hp hl hr
    hmul ((leviInductionFunctor p l r hp hr hl hmul).obj σ) σ
  have : ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IsIrreducible := hiσ
  have : σ.representation.IsIrreducible := hσirr
  have hF0 : E (Representation.IntertwiningMap.id _) ≠ 0 := by
    intro h0
    have hid : Representation.IntertwiningMap.id
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation = 0 :=
      E.injective (h0.trans (map_zero E).symm)
    have : Nontrivial ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) _
    obtain ⟨x, hx⟩ := exists_ne
      (0 : ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.asModule)
    exact hx (congrArg (fun f => f x) hid)
  have hFsurj :=
    (Representation.IsIrreducible.surjective_or_eq_zero
      (E (Representation.IntertwiningMap.id _))).resolve_right hF0
  have hExact : Derivative.Mirabolic.MapsShortExactIntertwiners
      (leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul) := by
    intro A B C i q hi hq hex
    obtain ⟨h1, h2, h3⟩ :=
      (leviParabolicFunctorsExact.{u, max u v} k G hG P M U p l r hp hl hr hmul).2 i q
        ⟨hi, hq, hex⟩
    exact ⟨h1, h3, h2⟩
  have hq : SmoothRep.IsSubquotient σ ((leviJacquetFunctor p l r hp hr hl hmul).obj
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ)) :=
    SmoothRep.IsQuotient.isSubquotient
      ⟨SmoothRep.ofHom (E (Representation.IntertwiningMap.id _)), hFsurj⟩
  refine ⟨σ, hσirr, ?_, hσ⟩
  exact smoothSubquotientTransitivity ℂ (rationalPoints M) _ _ _
    (hq.of_iso_right ((leviJacquetFunctor p l r hp hr hl hmul).mapIso e.symm))
    (ExactSmoothTransport.map_isSubquotient _ hExact hτY)

/-- The block corollary follows from the VII.1.3 reducibility theorem together with
block preservation, fullness and essential surjectivity of induction. -/
theorem maximalLeviBlockStatementsFromInputs :
    MaximalLeviBlockStatementsFromInputsStatement.{u, v} := by
  intro hThm hIII k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul hproper hmax
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hirr hcusp hw IsTwist InBlockM InBlockG
  obtain ⟨hI, hII⟩ := maximalLeviBlock_irreducible_detection hThm k G hG P M U p l r hp hl hr
    hmul hproper hmax ρ hirr hcusp hw
  obtain ⟨hInto, hFull, hEss⟩ := hIII k G hG P M U p l r hp hl hr hmul hproper hmax ρ hirr hcusp hw
  have : (leviInductionFunctor p l r hp hr hl hmul).Faithful :=
    leviInductionFunctor_faithful p l r hp hr hl hmul
  exact ⟨hI, hII, hInto, hFull, inferInstance, hEss⟩

end Langlands.Aubert.General.RepresentedParabolic
