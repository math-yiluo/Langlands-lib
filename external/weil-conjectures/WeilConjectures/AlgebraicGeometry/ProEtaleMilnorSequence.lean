/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.MilnorTower
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.AlgebraicGeometry.RoosCohomologySequence

/-!
# The Milnor sequence on the small pro-etale site

Source: Weil conjectures blueprint, main-20261015, chap-The-pro-etale-site,
sk-prop-pe-milnor/det-pe-milnor-sequence.md (blueprint: proposition-milnor-sequence--2).

The existing strict Roos construction `WeilConjectures.integralOperationsRoos` is
exactly Cone(1-T)[-1], including its diagonal map on strict tower morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

section Calculation

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableLimits A]

omit [HasCountableLimits A] in
private theorem shortExact_iso_g (S : ShortComplex A) (hS : S.ShortExact)
    (h : IsZero S.X₁) : IsIso S.g :=
  hS.isIso_g_iff.mpr h

omit [HasCountableLimits A] in
private theorem shortExact_iso_f (S : ShortComplex A) (hS : S.ShortExact)
    (h : IsZero S.X₃) : IsIso S.f :=
  hS.isIso_f_iff.mpr h

private def milnorCokernelFunctor : (ℕᵒᵖ ⥤ A) ⥤ A where
  obj := milnorTowerCokernel
  map := milnorTowerCokernelMap
  map_id M := by
    apply (cancel_epi (cokernel.π _)).1
    simp [milnorTowerCokernelMap]
  map_comp f g := by
    apply (cancel_epi (cokernel.π _)).1
    simp [milnorTowerCokernelMap, Category.assoc, ← Limits.Pi.map_comp_map]

private def singleHomologyTowerIso (M : ℕᵒᵖ ⥤ A) :
    milnorCohomologyTower (milnorSingleTower M) 0 ≅ M :=
  NatIso.ofComponents
    (fun n ↦ HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (M.obj n))
    (fun f ↦ HomologicalComplex.singleObjHomologySelfIso_hom_naturality
      (ComplexShape.up ℤ) 0 (M.map f))

omit [HasCountableLimits A] in
private theorem singleHomologyTowerIso_naturality {M N : ℕᵒᵖ ⥤ A} (f : M ⟶ N) :
    Functor.whiskerRight
        (Functor.whiskerRight f (HomologicalComplex.single A (ComplexShape.up ℤ) 0))
        (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0) ≫
        (singleHomologyTowerIso N).hom = (singleHomologyTowerIso M).hom ≫ f := by
  ext n
  exact HomologicalComplex.singleObjHomologySelfIso_hom_naturality
    (ComplexShape.up ℤ) 0 (f.app n)

omit [HasCountableLimits A] in
private theorem singleHomologyTower_isZero (M : ℕᵒᵖ ⥤ A) (p : ℤ) (hp : p ≠ 0) :
    IsZero (milnorCohomologyTower (milnorSingleTower M) p) := by
  apply Functor.isZero
  intro n
  exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 (M.obj n) p hp

private theorem singleLimit_isZero (M : ℕᵒᵖ ⥤ A) (p : ℤ) (hp : p ≠ 0) :
    IsZero (limit (milnorCohomologyTower (milnorSingleTower M) p)) :=
  (limit.isLimit _).isZero_pt (singleHomologyTower_isZero M p hp)

private theorem singleCokernel_isZero (M : ℕᵒᵖ ⥤ A) (p : ℤ) (hp : p ≠ 0) :
    IsZero (milnorTowerCokernel (milnorCohomologyTower (milnorSingleTower M) p)) := by
  have hP : IsZero (∏ᶜ fun n : ℕ ↦
      (milnorCohomologyTower (milnorSingleTower M) p).obj (op n)) := by
    apply (limit.isLimit _).isZero_pt
    apply Functor.isZero
    intro n
    exact HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℤ) 0 (M.obj (op n.as)) p hp
  apply (IsZero.of_epi (cokernel.π _) hP)

end Calculation

private theorem milnor_sequence_of_exact_products
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableLimits A]
    [HasExactLimitsOfShape (Discrete ℕ) A] :
    ∃ (e₀ : ∀ M : ℕᵒᵖ ⥤ A,
        (WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology 0 ≅ limit M)
      (e₁ : ∀ M : ℕᵒᵖ ⥤ A,
        (WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology 1 ≅
          milnorTowerCokernel M),
      (∀ (M : ℕᵒᵖ ⥤ A) (p : ℤ), p ≠ 0 → p ≠ 1 →
        IsZero ((WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology p)) ∧
      (∀ (M N : ℕᵒᵖ ⥤ A) (f : M ⟶ N),
        HomologicalComplex.homologyMap
            (WeilConjectures.integralOperationsRoosMap
              (Functor.whiskerRight f
                (HomologicalComplex.single
                  A (ComplexShape.up ℤ) 0))) 0 ≫
            (e₀ N).hom = (e₀ M).hom ≫ limMap f ∧
        HomologicalComplex.homologyMap
            (WeilConjectures.integralOperationsRoosMap
              (Functor.whiskerRight f
                (HomologicalComplex.single
                  A (ComplexShape.up ℤ) 0))) 1 ≫
            (e₁ N).hom = (e₁ M).hom ≫ milnorTowerCokernelMap f) ∧
      ∀ q : ℤ,
        ∃ (a : ∀ K : ℕᵒᵖ ⥤ CochainComplex A ℤ,
            milnorTowerCokernel (milnorCohomologyTower K (q - 1)) ⟶
              (WeilConjectures.integralOperationsRoos K).homology q)
          (b : ∀ K : ℕᵒᵖ ⥤ CochainComplex A ℤ,
            (WeilConjectures.integralOperationsRoos K).homology q ⟶
              limit (milnorCohomologyTower K q)),
          (∀ K : ℕᵒᵖ ⥤ CochainComplex A ℤ,
            ∃ h : a K ≫ b K = 0, (ShortComplex.mk (a K) (b K) h).ShortExact) ∧
          (∀ (K L : ℕᵒᵖ ⥤ CochainComplex A ℤ) (f : K ⟶ L),
            milnorTowerCokernelMap
                (Functor.whiskerRight f
                  (HomologicalComplex.homologyFunctor A
                    (ComplexShape.up ℤ) (q - 1))) ≫ a L =
              a K ≫ HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap f) q ∧
            HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap f) q ≫ b L =
              b K ≫ limMap (Functor.whiskerRight f
                (HomologicalComplex.homologyFunctor
                  A (ComplexShape.up ℤ) q))) ∧
          ∀ K : ℕᵒᵖ ⥤ CochainComplex A ℤ,
            ∃ h : ((e₁ (milnorCohomologyTower K (q - 1))).hom ≫ a K) ≫ b K = 0,
              (ShortComplex.mk
                ((e₁ (milnorCohomologyTower K (q - 1))).hom ≫ a K) (b K) h).ShortExact  := by
  classical
  obtain ⟨a₀, b₀, hS₀, hN₀⟩ := roos_cohomology_sequence (A := A) 0
  obtain ⟨a₁, b₁, hS₁, hN₁⟩ := roos_cohomology_sequence (A := A) 1
  have hb₀ (M : ℕᵒᵖ ⥤ A) : IsIso (b₀ (milnorSingleTower M)) := by
    obtain ⟨z, hz⟩ := hS₀ (milnorSingleTower M)
    exact shortExact_iso_g (ShortComplex.mk _ _ z) hz
      (singleCokernel_isZero M (0 - 1) (by decide))
  have ha₁ (M : ℕᵒᵖ ⥤ A) : IsIso (a₁ (milnorSingleTower M)) := by
    obtain ⟨z, hz⟩ := hS₁ (milnorSingleTower M)
    exact shortExact_iso_f (ShortComplex.mk _ _ z) hz
      (singleLimit_isZero M 1 (by decide))
  let e₀ (M : ℕᵒᵖ ⥤ A) :
      (WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology 0 ≅
        limit M := asIso (b₀ (milnorSingleTower M)) ≪≫
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapIso (singleHomologyTowerIso M)
  let e₁ (M : ℕᵒᵖ ⥤ A) :
      (WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology 1 ≅
        milnorTowerCokernel M := (asIso (a₁ (milnorSingleTower M))).symm ≪≫
    milnorCokernelFunctor.mapIso (singleHomologyTowerIso M)
  refine ⟨e₀, e₁, ?_, ?_, ?_⟩
  · intro M p hp₀ hp₁
    obtain ⟨a, b, hS, hN⟩ := roos_cohomology_sequence (A := A) p
    exact (hS (milnorSingleTower M)).choose_spec.exact.isZero_X₂
      ((singleCokernel_isZero M (p - 1) (by omega)).eq_of_src _ _)
      ((singleLimit_isZero M p hp₀).eq_of_tgt _ _)
  · intro M N f
    let g := Functor.whiskerRight f (HomologicalComplex.single A (ComplexShape.up ℤ) 0)
    have hlim := congrArg (fun k ↦ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).map k)
      (singleHomologyTowerIso_naturality f)
    have hcok := congrArg (fun k ↦ milnorCokernelFunctor.map k)
      (singleHomologyTowerIso_naturality f)
    constructor
    · change _ ≫ (b₀ (milnorSingleTower N) ≫ _) =
        (b₀ (milnorSingleTower M) ≫ _) ≫ _
      rw [← Category.assoc, (hN₀ _ _ g).2, Category.assoc, Category.assoc]
      congr 1
      exact (Functor.map_comp _ _ _).symm.trans
        (hlim.trans (Functor.map_comp _ _ _))
    · change _ ≫ (inv (a₁ (milnorSingleTower N)) ≫ _) =
        (inv (a₁ (milnorSingleTower M)) ≫ _) ≫ _
      have hn := (hN₁ _ _ g).1
      have hi : HomologicalComplex.homologyMap
          (WeilConjectures.integralOperationsRoosMap g) 1 ≫
          inv (a₁ (milnorSingleTower N)) =
          inv (a₁ (milnorSingleTower M)) ≫
            milnorTowerCokernelMap (Functor.whiskerRight g
              (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0)) := by
        rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
        exact hn.symm
      rw [← Category.assoc, hi, Category.assoc, Category.assoc]
      congr 1
      exact (Functor.map_comp _ _ _).symm.trans
        (hcok.trans (Functor.map_comp _ _ _))
  · intro q
    obtain ⟨a, b, hS, hN⟩ := roos_cohomology_sequence (A := A) q
    refine ⟨a, b, hS, hN, ?_⟩
    intro K
    obtain ⟨h, he⟩ := hS K
    refine ⟨by rw [Category.assoc, h, comp_zero], ?_⟩
    apply ShortComplex.shortExact_of_iso _ he
    exact ShortComplex.isoMk (e₁ (milnorCohomologyTower K (q - 1))).symm
      (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- All three clauses of the natural Milnor sequence, for arbitrary unbounded towers.
The chosen isomorphisms e₀ and e₁ compute the cohomology of the degree-zero Roos
complex. The final short exact complex is the first one with its left endpoint
rewritten by e₁; in particular it uses the same maps, not unrelated exact sequences.

md (blueprint: proposition-milnor-sequence--2).

Proof:
1. In the abelian category of ringedSiteModules, apply the cone long exact
cohomology sequence (proposition-milnor-sequence and
 proposition-milnor-sequence) to 1-T on the termwise product. Exactness
identifies the cokernel in degree q-1 with the kernel of the outgoing map, and
its image with the kernel in degree q. By proposition-exact-products--2, using exact
products from proposition-exact-products--1, the projection-induced product/cohomology
comparison is an isomorphism. Its coordinate formulas identify the induced map
with 1-T on cohomology. The kernel is the sheaf inverse limit by
 proposition-milnor-sequence. The diagonal product map on cone summands commutes
with inclusion and negative projection; factoring through cokernels and kernels
gives both naturality squares below.
2. For modules concentrated in degree zero the shifted cone has only degrees
0 and 1, with differential -(1-T). Negating degree 1 identifies it with the
usual two-term complex. Its cohomology is the kernel in degree 0, the cokernel
in degree 1, and zero in every other integer degree. Identify the kernel with
the sectionwise inverse limit. The constructions commute with tower maps.
3. Apply the degree-1 calculation to the tower of H^(q-1)(K_n). Composing its
isomorphism with the first inclusion gives the last displayed short exact
complex, which is exactly the Milnor sequence in clause 3. -/
theorem milnor_sequence (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)}) :
    ∃ (e₀ : ∀ M : ℕᵒᵖ ⥤ (ringedSiteModules.{max u (t + 1)} R),
        (WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology 0 ≅ limit M)
      (e₁ : ∀ M : ℕᵒᵖ ⥤ (ringedSiteModules.{max u (t + 1)} R),
        (WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology 1 ≅
          milnorTowerCokernel M),
      (∀ (M : ℕᵒᵖ ⥤ (ringedSiteModules.{max u (t + 1)} R)) (p : ℤ), p ≠ 0 → p ≠ 1 →
        IsZero ((WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology p)) ∧
      (∀ (M N : ℕᵒᵖ ⥤ (ringedSiteModules.{max u (t + 1)} R)) (f : M ⟶ N),
        HomologicalComplex.homologyMap
            (WeilConjectures.integralOperationsRoosMap
              (Functor.whiskerRight f
                (HomologicalComplex.single
                  (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) 0))) 0 ≫
            (e₀ N).hom = (e₀ M).hom ≫ limMap f ∧
        HomologicalComplex.homologyMap
            (WeilConjectures.integralOperationsRoosMap
              (Functor.whiskerRight f
                (HomologicalComplex.single
                  (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) 0))) 1 ≫
            (e₁ N).hom = (e₁ M).hom ≫ milnorTowerCokernelMap f) ∧
      ∀ q : ℤ,
        ∃ (a : ∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
            milnorTowerCokernel (milnorCohomologyTower K (q - 1)) ⟶
              (WeilConjectures.integralOperationsRoos K).homology q)
          (b : ∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
            (WeilConjectures.integralOperationsRoos K).homology q ⟶
              limit (milnorCohomologyTower K q)),
          (∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
            ∃ h : a K ≫ b K = 0, (ShortComplex.mk (a K) (b K) h).ShortExact) ∧
          (∀ (K L : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ) (f : K ⟶ L),
            milnorTowerCokernelMap
                (Functor.whiskerRight f
                  (HomologicalComplex.homologyFunctor (ringedSiteModules.{max u (t + 1)} R)
                    (ComplexShape.up ℤ) (q - 1))) ≫ a L =
              a K ≫ HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap f) q ∧
            HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap f) q ≫ b L =
              b K ≫ limMap (Functor.whiskerRight f
                (HomologicalComplex.homologyFunctor
                  (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) q))) ∧
          ∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
            ∃ h : (e₁ (milnorCohomologyTower K (q - 1))).hom ≫ a K ≫ b K = 0,
              (ShortComplex.mk
                ((e₁ (milnorCohomologyTower K (q - 1))).hom ≫ a K) (b K) h).ShortExact  := by
  have : HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{max u (t + 1)} R) := products_exact X R ℕ
  exact milnor_sequence_of_exact_products

end AlgebraicGeometry.Scheme.ProEt
