import Langlands.GroupScheme.Rational.NumberFieldHasseInflation
import Mathlib.GroupTheory.QuotientGroup.Simple
import Mathlib.Order.Atoms.Finite

/-! # From prime-degree to abelian Galois covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IntermediateField
open scoped IsMulCommutative CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
set_option maxRecDepth 1000

private theorem exists_primeIntermediate (F L : Type u) [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L] [IsMulCommutative (L ≃ₐ[F] L)]
    (h : Module.finrank F L ≠ 1) :
    ∃ E : IntermediateField F L, IsGalois F E ∧ Nat.Prime (Module.finrank F E) := by
  let Γ := L ≃ₐ[F] L
  have hΓ : Nontrivial Γ := by
    by_contra hnt
    let : Subsingleton Γ := not_nontrivial_iff_subsingleton.mp hnt
    apply h
    rw [← IsGalois.card_aut_eq_finrank]
    exact Nat.card_unique
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (α := Subgroup Γ)
  let E := IntermediateField.fixedField N
  let : N.Normal := inferInstance
  have hs : IsSimpleGroup (Γ ⧸ N) := CommGroup.isSimpleGroup_iff_isCoatom.mpr hN
  refine ⟨E, inferInstance, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv]
  exact IsSimpleGroup.prime_card

/-- A class of affine number-field groups stable under finite extension with
locally trivial cocycles has abelian-cover vanishing if it has vanishing on
covers of the allowed prime degrees. -/
def NumberFieldAbelianCoverVanishingStatement : Prop :=
  ∀ (P : ∀ (F : Type u) [Field F] [NumberField F], GroupScheme (Spec (CommRingCat.of F)) → Prop)
    (s : Set ℕ),
    (∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E]
      [Algebra F E] [FiniteDimensional F E]
      (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
      P F G → P E ((GroupScheme.baseChange (algebraBaseMap F E)).obj G)) →
    (∀ (F : Type u) [Field F] [NumberField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom], P F G →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial) →
    (∀ (F : Type u) [Field F] [NumberField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom], P F G →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
        Nat.Prime (Module.finrank F L) → Module.finrank F L ∈ s →
        ∀ (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.IsTrivial) →
    ∀ (F : Type u) [Field F] [NumberField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom], P F G →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        [IsMulCommutative (L ≃ₐ[F] L)],
        (∀ q : ℕ, Nat.Prime q → q ∣ Module.finrank F L → q ∈ s) →
        ∀ (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.IsTrivial

open GaloisCocycle in
theorem numberFieldAbelianCoverVanishing : NumberFieldAbelianCoverVanishingStatement.{u} := by
  classical
  intro P s hBase hLocal hPrime F _ _ G _ hG L _ _ _ _ _ hDiv ξ
  generalize hdegree : Module.finrank F L = n
  induction n using Nat.strong_induction_on generalizing F G L with
  | h n ih =>
    by_cases hOne : Module.finrank F L = 1
    · let e := AlgEquiv.ofBijective (Algebra.ofId F L)
        (Module.Free.bijective_algebraMap_of_finrank_eq_one hOne)
      let R := e.toRingEquiv.toCommRingCatIso
      let : IsIso (cover F L).hom := by
        change IsIso (Spec.map R.hom)
        infer_instance
      refine ⟨1, fun {Z} a b => ?_⟩
      have hab : a = b := Over.OverMorphism.ext
        ((cancel_mono (cover F L).hom).mp ((Over.w a).trans (Over.w b).symm))
      subst b
      simp only [Cocycle.toFun_self, MonObj.comp_one, inv_one, mul_one]
    · obtain ⟨E, hE, hp⟩ := exists_primeIntermediate F L hOne
      let : IsGalois F E := hE
      let : NumberField E := NumberField.of_module_finite F E
      let : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite F E L
      let : IsGalois E L := IsGalois.tower_top_of_isGalois F E L
      let : IsMulCommutative (L ≃ₐ[E] L) := by
        let f : (L ≃ₐ[E] L) →* (L ≃ₐ[F] L) := AlgEquiv.restrictScalarsHom F
        refine ⟨⟨fun x y => AlgEquiv.restrictScalarsHom_injective (R := F) (S := E) ?_⟩⟩
        change f (x * y) = f (y * x)
        rw [map_mul, map_mul, mul_comm]
      let G_E := (GroupScheme.baseChange (algebraBaseMap F E)).obj G
      let : IsAffineHom G_E.X.hom := by change IsAffineHom (Limits.pullback.snd G.X.hom _); infer_instance
      have he : Module.finrank F E * Module.finrank E L = Module.finrank F L := Module.finrank_mul_finrank F E L
      have hlt : Module.finrank E L < n := by
        rw [← hdegree, ← he]
        simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hp.one_lt
          (Module.finrank_pos (R := E) (M := L))
      have hdE (q : ℕ) (hq : Nat.Prime q) (hd : q ∣ Module.finrank E L) : q ∈ s :=
        hDiv q hq (hd.trans (he ▸ dvd_mul_left _ _))
      have hTriv := ih (Module.finrank E L) hlt E G_E (hBase F E G hG) L hdE
        (scalarExtension (K := E) (M := L) ξ) rfl
      have hBc := isTrivial_baseChange_of_scalarExtension (M := L) ξ hTriv
      let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      apply Cocycle.isTrivial_of_baseChange_isTrivial_of_kernel L ξ (hLocal F G hG L ξ) hBc
      intro θ _
      exact hPrime F G hG E hp (hDiv _ hp (he ▸ dvd_mul_right _ _)) θ

end Langlands.GroupScheme
