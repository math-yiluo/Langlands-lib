/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
public import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.ExactAdjointTowerModels.ExactAdjointTowerModels
import WeilConjectures.PoincareDuality.Pod.PodNativeRoosFunctorComparison
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleMittagLeffler

/-!
# The Milnor theorem for arbitrary ring sheaves on the pro-etale site

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-pe-milnor/_section.md; Stacks Tags 0940, 0941, 0947 and 07KW
(blueprint: proposition-milnor-sequence).

The strict cone functor and all module/cohomology towers are the existing constructions
of `IntegralOperationsWellDefined` and `MilnorTower`. No cone is chosen in a bare
triangulated category. The declarations below give the total-derived-functor
comparison and all cohomological, epimorphic and sectionwise Mittag-Leffler clauses.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u w wT

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The functorial strict Roos fibre computes the total right derived inverse limit.
The universal pair is asserted to exist, with its unit invertible on K-injectives;
the displayed natural isomorphism uses the positive `1-T` cone, not its negative.

Source: latest blueprint, proposition-milnor-sequence; Stacks Tags 0940 and 0941
(blueprint: proposition-milnor-sequence).

Proof:
1. Module sheaves over the small site form a Grothendieck abelian category, as does
   their countable diagram category. Resolve strict tower complexes by K-injectives.
   The additive ordinary inverse-limit functor therefore has the universal right-derived
   pair of def-sfb-right-derived-functor, with unit invertible on K-injectives.
2. Exact countable products identify the termwise products with derived products.
   Strict tower maps commute with 1-T, and their diagonal cone maps respect composition.
3. Apply lem-weil-pbc-exact-products-roos-comparison to the universal pair. Its fibre
   uses -(1-T); multiplying the target cone summand by -1 gives a chain isomorphism
   from Cone(1-T) to Cone(-(1-T)), natural in the strict tower. Shift by -1 and compose
   with that comparison to obtain the natural isomorphism asserted here.
4. The universal property on complexes is the universal property on the homotopy
   category in def-sfb-right-derived-functor: the ordinary termwise limit is additive
   and preserves chain homotopies. Localization through the homotopy quotient identifies
   the two sets of natural transformations and their unit-factorization maps. -/
theorem milnor_totalDerived (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)]
    [HasDerivedCategory.{wT} (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R)] :
    ∃ (RF : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ⥤
        DerivedCategory (ringedSiteModules.{max u (t + 1)} R))
      (η : ExactProductsRoos.ordinary ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF),
      (∀ G : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ⥤
          DerivedCategory (ringedSiteModules.{max u (t + 1)} R),
        Function.Bijective (fun β : RF ⟶ G ↦ η ≫ Functor.whiskerLeft DerivedCategory.Q β)) ∧
      (∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ,
        I.IsKInjective → IsIso (η.app I)) ∧
      Nonempty (HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        WeilConjectures.integralOperationsRoosFunctor ⋙ DerivedCategory.Q ≅
          DerivedCategory.Q ⋙ RF) := by
  classical
  let A := ringedSiteModules.{max u (t + 1)} R
  let AT := ℕᵒᵖ ⥤ A
  let _ : IsGrothendieckAbelian.{max u (t + 1)} A :=
    SheafOfModules.isGrothendieckAbelianOfUniverses (topology X) R
  let _ : IsGrothendieckAbelian.{max u (t + 1)} AT := tower_grothendieck A
  let _ := products_exact.{t, u, 0} X R ℕ
  let _ : (lim : AT ⥤ A).Additive := by
    constructor
    intro M N f g
    apply limit.hom_ext
    intro n
    simp only [lim_map, limMap_π, Preadditive.add_comp, NatTrans.app_add,
      Preadditive.comp_add]
  obtain ⟨RF, η, hRF, hI, _⟩ := totalDerivedData (lim : AT ⥤ A)
  let _ := hRF
  refine ⟨RF, η, ?_, hI, ?_⟩
  · intro G
    constructor
    · intro β γ h
      exact RF.rightDerived_ext η (HomologicalComplex.quasiIso AT (.up ℤ)) G β γ h
    · intro α
      exact ⟨RF.rightDerivedDesc η (HomologicalComplex.quasiIso AT (.up ℤ)) G α,
        RF.rightDerived_fac η (HomologicalComplex.quasiIso AT (.up ℤ)) G α⟩
  · let F := CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)} AT
    let q := CochainComplex.toKInjectiveResolution.{max u (t + 1)} AT
    let Q := DerivedCategory.Q.{w} (C := A)
    let QT := DerivedCategory.Q.{wT} (C := AT)
    let α := Functor.whiskerRight q (ExactProductsRoos.fibre ⋙ Q)
    have (N : CochainComplex AT ℤ) : IsIso (α.app N) := by
      have : QuasiIso (q.app N) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app AT N).2
      have : QuasiIso (ExactProductsRoos.fibre.map (q.app N)) :=
        ExactProductsRoos.fibreMap_quasiIso (q.app N)
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso A _).2 inferInstance
    have : IsIso α := NatIso.isIso_of_isIso_app _
    let β := Functor.whiskerLeft F
      (Functor.whiskerRight ExactProductsRoos.comparison Q)
    have (N : CochainComplex AT ℤ) : IsIso (β.app N) := by
      have : QuasiIso (ExactProductsRoos.comparison.app (F.obj N)) :=
        ExactProductsRoos.comparison_quasiIso _
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso A _).2 inferInstance
    have : IsIso β := NatIso.isIso_of_isIso_app _
    let δ := Functor.whiskerRight q QT
    have (N : CochainComplex AT ℤ) : IsIso (δ.app N) := by
      have : QuasiIso (q.app N) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app AT N).2
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso AT _).2 inferInstance
    have : IsIso δ := NatIso.isIso_of_isIso_app _
    let ε := Functor.whiskerLeft F η
    have (N : CochainComplex AT ℤ) : IsIso (ε.app N) := hI _ inferInstance
    have : IsIso ε := NatIso.isIso_of_isIso_app _
    let negative : ExactProductsRoos.fibre ⋙ Q ≅ QT ⋙ RF :=
      asIso α ≪≫ Functor.associator F ExactProductsRoos.fibre Q ≪≫
        (asIso β).symm ≪≫ asIso ε ≪≫ (Functor.associator F QT RF).symm ≪≫
          Functor.isoWhiskerRight (asIso δ).symm RF
    exact ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight WeilConjectures.podNativeRoosIso Q ≪≫
      Functor.isoWhiskerRight ExactAdjointTowerModels.signIso.symm Q ≪≫ negative⟩

/-- The Milnor cohomology formulas, natural exact sequence, epimorphic case, and
sectionwise Mittag-Leffler vanishing, all for the same strict Roos construction.
Here e₁ identifies R¹lim with the cokernel. The left endpoint of the exact sequence
is the actual degree-one derived limit of the cohomology sheaves. The final implication
is tested only on affine weakly contractible objects.

Source: latest blueprint, proposition-milnor-sequence; Stacks Tag 0947 (6),(7), Tag 07KW
(blueprint: proposition-milnor-sequence).

Proof:
1. Apply proposition-milnor-sequence--2 to the strict cone. The long exact cohomology sequence
   and exact products give the natural cokernel/kernel short exact sequence.
   For a module tower in degree zero, its cohomology is lim in degree zero, coker(1-T)
   in degree one, and zero in every other degree; in particular it vanishes for p>1.
   Substituting this e₁ identification in degree q-1 gives the displayed Milnor sequence.
2. If transitions are epimorphisms, their sections on affine weakly contractible W
   are surjective. For any a=(a_n), choose m_0=0 and recursively lift m_n-a_n along t_n
   to m_(n+1). This solves (1-T)m=a on W. Exactness detection makes 1-T an epimorphism
   of sheaves, and proposition-milnor-sequence--3 identifies the canonical ordinary-limit
   comparison with an isomorphism in the derived category.
3. More generally apply the algebraic Mittag-Leffler lemma, Tag 07KW, to M_n(W).
   The finite-prefix exact sequence and ML exactness of inverse limit show that 1-T
   on the full section product is surjective. Evaluation on W preserves products
   and cokernels, so coker(1-T)(W)=0. The affine weakly contractible family detects
   zero sheaves. Thus R¹lim vanishes. Apply this to H^(q-1)(K_n) for the Milnor term.
4. Preservation of cokernels makes every sheaf epimorphism surjective on these
   section modules, explaining why checking the condition on this basis suffices. -/
theorem milnor (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)] :
    ∃ e₁ : ∀ M : ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R,
        (WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology 1 ≅
          milnorTowerCokernel M,
      (∀ (M : ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) (p : ℤ), 1 < p →
        IsZero ((WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology p)) ∧
      (∀ (M N : ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) (f : M ⟶ N),
        HomologicalComplex.homologyMap
            (WeilConjectures.integralOperationsRoosMap
              (Functor.whiskerRight f
                (HomologicalComplex.single
                  (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) 0))) 1 ≫
            (e₁ N).hom = (e₁ M).hom ≫ milnorTowerCokernelMap f) ∧
      (∀ q : ℤ,
        ∃ (a : ∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
            (WeilConjectures.integralOperationsRoos
              (milnorSingleTower (milnorCohomologyTower K (q - 1)))).homology 1 ⟶
                (WeilConjectures.integralOperationsRoos K).homology q)
          (b : ∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
            (WeilConjectures.integralOperationsRoos K).homology q ⟶
              limit (milnorCohomologyTower K q)),
          (∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
            ∃ h : a K ≫ b K = 0, (ShortComplex.mk (a K) (b K) h).ShortExact) ∧
          ∀ (K L : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ)
            (f : K ⟶ L),
            HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap
                  (Functor.whiskerRight
                    (Functor.whiskerRight f
                      (HomologicalComplex.homologyFunctor
                        (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) (q - 1)))
                    (HomologicalComplex.single
                      (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) 0))) 1 ≫
                a L = a K ≫ HomologicalComplex.homologyMap
                  (WeilConjectures.integralOperationsRoosMap f) q ∧
            HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap f) q ≫ b L =
              b K ≫ limMap (Functor.whiskerRight f
                (HomologicalComplex.homologyFunctor
                  (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) q))) ∧
      (∀ M : ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R,
        (∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op)) →
          IsIso (DerivedCategory.Q.map (AlgebraicGeometry.ProEtale.milnorLimitComparison M))) ∧
      ∀ M : ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R,
        (∀ W : X.ProEt, IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
          (M ⋙ SheafOfModules.evaluation R (op W) ⋙ CategoryTheory.forget _).IsMittagLeffler) →
        IsZero ((WeilConjectures.integralOperationsRoos (milnorSingleTower M)).homology 1) := by
  obtain ⟨_, e₁, hzero, hnat, hseq⟩ := Scheme.ProEt.milnor_sequence X R
  refine ⟨e₁, ?_, ?_, ?_, ?_, ?_⟩
  · intro M p hp
    apply hzero M p
    · omega
    · omega
  · intro M N f
    exact (hnat M N f).2
  · intro q
    obtain ⟨a, b, hshort, hnatab, hlast⟩ := hseq q
    let a' : ∀ K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ,
        (WeilConjectures.integralOperationsRoos
          (milnorSingleTower (milnorCohomologyTower K (q - 1)))).homology 1 ⟶
          (WeilConjectures.integralOperationsRoos K).homology q :=
      fun K ↦ (e₁ (milnorCohomologyTower K (q - 1))).hom ≫ a K
    refine ⟨a', b, ?_, ?_⟩
    · intro K
      obtain ⟨h, hK⟩ := hlast K
      exact ⟨h, hK⟩
    · intro K L f
      constructor
      · dsimp [a']
        rw [← Category.assoc, (hnat _ _
            (Functor.whiskerRight f
              (HomologicalComplex.homologyFunctor
                (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) (q - 1)))).2,
          Category.assoc]
        rw [Category.assoc, (hnatab K L f).1]
      · exact (hnatab K L f).2
  · intro M hM
    exact (AlgebraicGeometry.ProEtale.milnor_epimorphic X R M hM).2.2
  · intro M hML
    let F := fun n : ℕ ↦ M.obj (op n)
    let t := fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op
    let S := ShortComplex.mk (towerTransitionEndomorphism (K := F) t)
      (0 : ∏ᶜ F ⟶ ∏ᶜ F) (by simp)
    have ht : Epi (towerTransitionEndomorphism (K := F) t) := by
      apply (S.exact_iff_epi rfl).1
      apply ((sections_conservative X R).1 _ _ _ _ _ _).2
      intro W hW hw
      have := hW
      let ev := SheafOfModules.evaluation.{max u (t + 1)} R (op W)
      have hpres := peSectionsLimitsColimits.{t, max u (t + 1), 0, 0, 0} R W hw
      have := hpres.1
      have := hpres.2
      have hfan := isLimitFanMkObjOfIsLimit ev F (Pi.π F) (productIsProduct F)
      have he : Epi (ev.map (towerTransitionEndomorphism (K := F) t)) := by
        change Epi (ev.map (𝟙 _ - towerProductShift (K := F) t))
        rw [ev.map_sub, ev.map_id]
        apply ModuleCat.epi_one_sub_of_mittagLeffler (F := M ⋙ ev)
          hfan (ev.map (towerProductShift (K := F) t))
        · intro n
          change ev.map (Pi.lift (fun n : ℕ ↦ Pi.π F (n + 1) ≫ t n)) ≫
              ev.map (Pi.π F n) = ev.map (Pi.π F (n + 1)) ≫ ev.map (t n)
          rw [← ev.map_comp, ← ev.map_comp, Pi.lift_comp_π]
        · exact ModuleCat.mittagLeffler_of_isMittagLeffler (hML W hW hw)
      exact ((S.map ev).exact_iff_epi (by simp [S])).2 he
    exact (isZero_cokernel_of_epi (towerTransitionEndomorphism (K := F) t)).of_iso (e₁ M)

/-- The same strict cone represents a homotopy limit in the triangulated sense.
The existential product witness asserts product existence rather than assuming it;
the following use of IsDerivedLimit uses precisely that product structure.

Source: latest blueprint, proposition-milnor-sequence; Stacks Tags 08TC and 0941
(blueprint: proposition-milnor-sequence).

Proof: exact products make Q preserve the termwise product of the representative
complexes. Rotate the mapping-cone triangle and shift it by -1. Its middle map is
1-T, after the standard sign isomorphism. Transport the two product vertices along
the product comparison isomorphism. The resulting distinguished triangle is exactly
IsDerivedLimitTriangle, so its two outside arrows witness IsDerivedLimit. -/
theorem milnor_homotopyLimit (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)]
    (K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ) :
    ∃ hP : HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (K.obj (op n))),
      @IsDerivedLimit _ _ _ _ _ _ _ _ hP
        (fun n : ℕ ↦ DerivedCategory.Q.map (K.map (homOfLE (Nat.le_succ n)).op))
        (DerivedCategory.Q.obj (WeilConjectures.integralOperationsRoos K)) := by
  classical
  let A := ringedSiteModules.{max u (t + 1)} R
  let Q := DerivedCategory.Q.{w} (C := A)
  let F := fun n : ℕ ↦ K.obj (op n)
  let f := WeilConjectures.integralOperationsTowerStep K
  let g := towerTransitionEndomorphism (K := F) f
  let _ := products_exact.{t, u, 0} X R ℕ
  let _ := SheafOfModules.isGrothendieckAbelianOfUniverses (topology X) R
  have hP : Nonempty (IsLimit (Q.mapCone (limit.cone (Discrete.functor F)))) :=
    ⟨isLimitOfPreserves Q (limit.isLimit _)⟩
  obtain ⟨hP⟩ := hP
  have hfan : IsLimit (Fan.mk (Q.obj (∏ᶜ F)) (fun n : ℕ ↦ Q.map (Pi.π F n))) :=
    (Fan.isLimitMapConeEquiv Q F (limit.cone (Discrete.functor F))) hP
  let : HasProduct (fun n : ℕ ↦ Q.obj (F n)) :=
    ⟨⟨Fan.mk (Q.obj (∏ᶜ F)) (fun n : ℕ ↦ Q.map (Pi.π F n)), hfan⟩⟩
  let e := hfan.conePointUniqueUpToIso (productIsProduct (fun n : ℕ ↦ Q.obj (F n)))
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = Q.map (Pi.π F n) :=
    hfan.conePointUniqueUpToIso_hom_comp _ ⟨n⟩
  have hg : Q.map g ≫ e.hom = e.hom ≫ towerTransitionEndomorphism
      (fun n : ℕ ↦ Q.map (f n)) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, he, ← Q.map_comp,
      (towerTransitionEndomorphism_eq_iff (K := F) f _).mp rfl n]
    simp only [Functor.map_sub, Functor.map_comp]
    rw [Category.assoc, (towerTransitionEndomorphism_eq_iff
      (K := fun n : ℕ ↦ Q.obj (F n)) (fun n : ℕ ↦ Q.map (f n)) _).mp rfl n]
    simp only [Preadditive.comp_sub, ← Category.assoc, he]
  let T := Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle g)
  refine ⟨inferInstance, T.mor₁ ≫ e.hom, e.inv ≫ T.mor₃, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk T
      (Pretriangulated.Triangle.mk (T.mor₁ ≫ e.hom)
        (towerTransitionEndomorphism (fun n : ℕ ↦ Q.map (f n))) (e.inv ≫ T.mor₃))
      (Iso.refl _) e e (by simp) hg (by simp))).mp
    (DerivedCategory.mappingCocone_triangle_distinguished g)

end AlgebraicGeometry.Scheme.ProEt
