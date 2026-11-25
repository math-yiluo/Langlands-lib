/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.Algebra.Category.ModuleCat.QuotSMulTop
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-!
# Nilpotent coefficient extensions preserve a higher direct-image bound

Source: Stacks Project, Derived Categories, Tag 015B, lemma-higher-derived-functors,
part (1). The nilpotent coefficient application uses an agent-written sheafified
descending I-adic filtration, motivated by Bhatt--Scholze, Lemma 6.5.11.
(blueprint: lem-sf-nilpotent-coefficient-direct-image-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private def idealPowerPresheaf {C : Type*} [Category* C]
    {R : Type*} [CommRing R] (I : Ideal R) (P : C ⥤ ModuleCat R) (j : ℕ) :
    C ⥤ ModuleCat R where
  obj U := ModuleCat.of R ↥(I ^ j • (⊤ : Submodule R (P.obj U)))
  map {U V} f := ModuleCat.ofHom
    ((P.map f).hom.restrict fun x hx ↦ by
      have h : Submodule.map (P.map f).hom
          (I ^ j • (⊤ : Submodule R (P.obj U))) ≤
          I ^ j • (⊤ : Submodule R (P.obj V)) := by
        rw [Submodule.map_smul'']
        exact smul_mono_right _ le_top
      exact h (Submodule.mem_map_of_mem hx))
  map_id U := by
    ext x
    change (P.map (𝟙 U)) x.val = x.val
    simp
  map_comp f g := by
    ext x
    change (P.map (f ≫ g)) x.val = (P.map g) ((P.map f) x.val)
    simp

private theorem idealPower_succ_le {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (j : ℕ) :
    I ^ (j + 1) • (⊤ : Submodule R M) ≤ I ^ j • (⊤ : Submodule R M) :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ j))

private def idealPowerInclusion {C : Type*} [Category* C]
    {R : Type*} [CommRing R] (I : Ideal R) (P : C ⥤ ModuleCat R) (j : ℕ) :
    idealPowerPresheaf I P (j + 1) ⟶ idealPowerPresheaf I P j where
  app U := ModuleCat.ofHom (Submodule.inclusion (idealPower_succ_le I (P.obj U) j))
  naturality _ _ f := by ext x; rfl

private noncomputable def idealPowerProjection {C : Type*} [Category* C]
    {R : Type*} [CommRing R] (I : Ideal R) (P : C ⥤ ModuleCat R) (j : ℕ) :
    idealPowerPresheaf I P j ⟶
      idealPowerPresheaf I P j ⋙ ModuleCat.quotSMulTop I ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk I) where
  app U := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
      ((ModuleCat.quotSMulTop I).obj ((idealPowerPresheaf I P j).obj U)))
    ((ModuleCat.quotSMulTopRestrictScalarsEquiv I _).toLinearMap.comp
      (I • (⊤ : Submodule R ((idealPowerPresheaf I P j).obj U))).mkQ)
  naturality _ _ f := by ext x; rfl

private theorem idealPower_mem {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (j : ℕ)
    (x : ↥(I ^ j • (⊤ : Submodule R M))) :
    x ∈ I • (⊤ : Submodule R ↥(I ^ j • (⊤ : Submodule R M))) ↔
      (x : M) ∈ I ^ (j + 1) • (⊤ : Submodule R M) := by
  rw [Submodule.mem_smul_top_iff, pow_succ', Submodule.mul_smul]

private noncomputable def idealPowerShortComplex {C : Type*} [Category* C]
    {R : Type*} [CommRing R] (I : Ideal R) (P : C ⥤ ModuleCat R) (j : ℕ) :
    ShortComplex (C ⥤ ModuleCat R) :=
  ShortComplex.mk (idealPowerInclusion I P j) (idealPowerProjection I P j) (by
    ext U x
    change Submodule.Quotient.mk _ = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ((idealPower_mem I _ j _).2 x.property))

private theorem idealPowerShortComplex_shortExact {C : Type*} [Category* C]
    {R : Type*} [CommRing R] (I : Ideal R) (P : C ⥤ ModuleCat R) (j : ℕ) :
    (idealPowerShortComplex I P j).ShortExact := by
  let S := idealPowerShortComplex I P j
  have he (U : C) : (S.map ((evaluation C (ModuleCat R)).obj U)).ShortExact := by
    change (ShortComplex.mk ((idealPowerInclusion I P j).app U)
      ((idealPowerProjection I P j).app U) _).ShortExact
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      have hx' : (x.val : P.obj U) ∈ I ^ (j + 1) • (⊤ : Submodule R (P.obj U)) :=
        (idealPower_mem I _ j x).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
      exact ⟨⟨x.val, hx'⟩, Subtype.ext rfl⟩
    · rw [ModuleCat.mono_iff_injective]
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : (idealPowerPresheaf I P j).obj U ↦ z.val) h
    · rw [ModuleCat.epi_iff_surjective]
      exact Submodule.Quotient.mk_surjective _
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.exact_iff_isZero_homology]
    apply Functor.isZero
    intro U
    exact ((S.map ((evaluation C (ModuleCat R)).obj U)).exact_iff_isZero_homology.1
      (he U).exact).of_iso (S.mapHomologyIso ((evaluation C (ModuleCat R)).obj U)).symm
  · let : ∀ U : C, Mono (S.f.app U) := fun U ↦ (he U).mono_f
    exact NatTrans.mono_of_mono_app _
  · let : ∀ U : C, Epi (S.g.app U) := fun U ↦ (he U).epi_g
    exact NatTrans.epi_of_epi_app _

private def idealPowerZeroIso {C : Type*} [Category* C]
    {R : Type*} [CommRing R] (I : Ideal R) (P : C ⥤ ModuleCat R) :
    idealPowerPresheaf I P 0 ≅ P :=
  NatIso.ofComponents (fun U ↦ LinearEquiv.toModuleIso
    { toFun := fun x ↦ x.val
      invFun := fun x ↦ ⟨x, by simp⟩
      left_inv := fun x ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }) (by intros; ext x; rfl)

private theorem idealPowerPresheaf_isZero {C : Type*} [Category* C]
    {R : Type*} [CommRing R] (I : Ideal R) (P : C ⥤ ModuleCat R)
    (t : ℕ) (hI : I ^ t = ⊥) : IsZero (idealPowerPresheaf I P t) := by
  apply Functor.isZero
  intro U
  rw [IsZero.iff_id_eq_zero]
  ext x
  change x = 0
  apply Subtype.ext
  exact (by simpa [hI] using x.property : x.val = 0)

/-- A common higher direct-image vanishing bound for quotient coefficients remains a bound
for the original coefficients when the coefficient ideal is nilpotent. The same integer
`N` is retained for every positive nilpotency exponent and every module sheaf.

Source: Stacks Project, Tag 015B, lemma-higher-derived-functors, part (1), applied to the
agent-written finite coefficient filtration, motivated by Bhatt--Scholze, Lemma 6.5.11.
(blueprint: lem-sf-nilpotent-coefficient-direct-image-bound)

Proof:
1. On the underlying module presheaf of `M`, form `P_j(U) = I^j M(U)`.
Restrictions preserve these submodules. The inclusion `P_(j+1) → P_j` is injective,
and its cokernel is `P_j / I P_j`, with its canonical `R / I`-module structure.
Indeed `I P_j = I^(j+1) M` by associativity of ideal multiplication and scalar action.
The reduction functor `ModuleCat.quotSMulTop` supplies the quotient action and maps.
2. Sheafification is exact, so these presheaf short exact sequences give sheaf short
exact sequences. Restriction of scalars preserves sheafification: it is left adjoint
to coextension of scalars. Thus the third sheaf is the restriction of an actual
`R / I`-module sheaf. The coefficient-change vanishing theorem and the hypothesis
annihilate its higher direct image in every degree under consideration.
3. Identify `higherDirectImage` in nonnegative degree with the classical right derived
functor of `lowerStar`, using the existing single-object comparison. Apply the full
long exact sequence to each sheaf short exact sequence. In a fixed degree, vanishing
of the outer terms implies vanishing of the middle term.
4. The last presheaf `P_t` is zero since `I^t = 0`. Descending induction therefore
annihilates the higher direct image of every sheafified `P_j`. Finally `P_0` is
isomorphic to the underlying presheaf of `M`, whose sheafification is `M`.
The degree remains fixed throughout, including degree zero when `N < 0`. -/
theorem isZero_higherDirectImage_of_nilpotent_quotient_bound
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (R : Type (u + 1)) [CommRing R] (I : Ideal R) (t : ℕ)
    (ht : 1 ≤ t) (hI : I ^ t = ⊥) (N : ℤ)
    (hN : ∀ (Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (R ⧸ I)))
      (q : ℤ), 0 ≤ q → N < q → IsZero (higherDirectImage (R ⧸ I) f q Q)) :
    ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
      (q : ℤ), 0 ≤ q → N < q → IsZero (higherDirectImage R f q M) := by
  intro M q hq hNq
  lift q to ℕ using hq
  let J := X.smallEtaleTopology
  have : J.PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.mk I)) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} (Ideal.Quotient.mk I))
  let A := presheafToSheaf J (ModuleCat.{u + 1} R)
  let F := lowerStar (ModuleCat.{u + 1} R) f
  let D := F.rightDerived q
  let e := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q
  let B (j : ℕ) := A.obj (idealPowerPresheaf I M.obj j)
  have hlast : IsZero (D.obj (B t)) :=
    D.map_isZero (A.map_isZero (idealPowerPresheaf_isZero I M.obj t hI))
  have hstep (j : ℕ) (_hj : j < t) (hz : IsZero (D.obj (B (j + 1)))) :
      IsZero (D.obj (B j)) := by
    let S := (idealPowerShortComplex I M.obj j).map A
    have hS : S.ShortExact := (idealPowerShortComplex_shortExact I M.obj j).map_of_exact A
    let Q : Sheaf J (ModuleCat.{u + 1} (R ⧸ I)) :=
      (presheafToSheaf J (ModuleCat.{u + 1} (R ⧸ I))).obj
        (idealPowerPresheaf I M.obj j ⋙ ModuleCat.quotSMulTop.{u + 1} I)
    let i : S.X₃ ≅ (Sheaf.restrictScalars J (Ideal.Quotient.mk I)).obj Q :=
      (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.mk I))
        (sheafificationAdjunction J (ModuleCat.{u + 1} (R ⧸ I)))
        (sheafificationAdjunction J (ModuleCat.{u + 1} R))).app
          (idealPowerPresheaf I M.obj j ⋙ ModuleCat.quotSMulTop.{u + 1} I)
    have hzQ : IsZero
        (D.obj ((Sheaf.restrictScalars J (Ideal.Quotient.mk I)).obj Q)) :=
      (e.app _).isZero_iff.mp
        ((isZero_higherDirectImage_restrictScalars_iff (Ideal.Quotient.mk I) f
          (q : ℤ) Q).2 (hN Q (q : ℤ) (Int.natCast_nonneg q) hNq))
    have hzQ' : IsZero (D.obj S.X₃) := hzQ.of_iso (D.mapIso i)
    obtain ⟨_, _, he⟩ := hS.exists_rightDerived_full_long_exact F
    exact ((he q).1).isZero_of_both_isZero hz hzQ'
  have hzero : IsZero (D.obj (B 0)) :=
    Nat.decreasingInduction hstep hlast (Nat.le_trans (Nat.zero_le 1) ht)
  have hM : IsZero (D.obj M) := hzero.of_iso
    (D.mapIso ((sheafificationIso M) ≪≫ (A.mapIso (idealPowerZeroIso I M.obj)).symm))
  exact hM.of_iso (e.app M)

end AlgebraicGeometry.Etale
