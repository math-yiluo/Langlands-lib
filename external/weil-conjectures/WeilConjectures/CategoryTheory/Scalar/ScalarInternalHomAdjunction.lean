/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.Scalar.ScalarTensorTowerComparison

/-! # Internal Hom and arbitrary changes of ring-sheaf coefficients

The scalar comparison is constructed from the five canonical Hom bijections.
Its evaluation and uniqueness follow from the scalar triangle identity;
restriction is conservative by its cohomology comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
namespace SheafOfModules
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
variable {J} {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
  [HasDerivedCategory.{w} (scalarModules J R)]
  [HasDerivedCategory.{w} (scalarModules J S)]

private theorem scalarDerivedPair_exists : Nonempty (ScalarDerivedPair a) := by
  classical
  obtain ⟨E, hobj, hmap, hadd, _, _, F, ε, hF, _, hc⟩ :=
    derivedChangeOfRingsIndependentCoefficients a
  have := hadd
  obtain ⟨_, _, h⟩ := sheafRingDerivedCoefficientAdjunction a
  obtain ⟨am, hu, hd⟩ := h E hobj hmap
  obtain ⟨d, hn⟩ := hd F ε hF
  refine ⟨{ extension := E
            extension_obj := hobj
            extension_map := hmap
            extension_additive := hadd
            derived := F
            counit := ε
            isLeftDerived := hF
            computes := ?_
            ordinaryAdjunction := am
            ordinaryUnit := ?_
            adjunction := d
            normalization := ?_ }⟩
  · intro P hP
    have := hc P hP
    dsimp only [scalarPairComplexComparison]
    infer_instance
  · intro M V x
    have hh := hu M (changeOfRings a M) (𝟙 _) V x
    simp only [Category.comp_id] at hh
    have he := am.homEquiv_naturality_right (𝟙 (E.obj M)) (eqToHom (hobj M))
    simp only [Category.id_comp, am.homEquiv_id] at he
    rw [he] at hh
    exact hh
  · intro P hP hflat H g
    let q := HomotopyCategory.quotient (scalarModules J R) (.up ℤ)
    let q' := HomotopyCategory.quotient (scalarModules J S) (.up ℤ)
    have hh := ((hn P hP hflat).2.2 (q'.obj H) (q.map g)).1
    clear h hd hn hu hobj hmap hc hF
    have hfac : (scalarRestriction a).mapDerivedCategoryFactorsh.inv.app (q'.obj H) =
        (scalarRestriction a).mapDerivedCategoryFactors.inv.app H := by
      apply (Iso.inv_eq_inv
        ((scalarRestriction a).mapDerivedCategoryFactorsh.app (q'.obj H))
        ((scalarRestriction a).mapDerivedCategoryFactors.app H)).2
      change (scalarRestriction a).mapDerivedCategoryFactorsh.hom.app (q'.obj H) =
        (scalarRestriction a).mapDerivedCategoryFactors.hom.app H
      rw [Functor.mapDerivedCategoryFactorsh_hom_app]
      change (scalarRestriction a).mapDerivedCategory.map (𝟙 _) ≫
        (scalarRestriction a).mapDerivedCategoryFactors.hom.app H ≫ 𝟙 _ ≫
          DerivedCategory.Qh.map (𝟙 _) = _
      erw [(scalarRestriction a).mapDerivedCategory.map_id (DerivedCategory.Q.obj H),
        DerivedCategory.Qh.map_id ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((scalarRestriction a).mapHomologicalComplex (.up ℤ)).obj H))]
      simp only [Category.id_comp]
      exact Category.comp_id ((scalarRestriction a).mapDerivedCategoryFactors.hom.app H)
    have ht : ((am.mapHomotopyCategory (.up ℤ)).homEquiv (q.obj P) (q'.obj H)).symm
        (q.map g) = q'.map (((am.mapHomologicalComplex (.up ℤ)).homEquiv P H).symm g) := by
      rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
      erw [Adjunction.mapHomotopyCategory_counit_app_quotient]
      rw [Functor.mapHomotopyCategory_map, q'.map_comp]
    rw [hfac, ht] at hh
    change (d.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj H)).symm
        (DerivedCategory.Q.map g ≫ (scalarRestrictionComparison a).inv.app H) =
      ε.app (q.obj P) ≫ DerivedCategory.Q.map
        (scalarChainTranspose a E hadd am P H g) at hh
    have hcP : scalarPairComplexComparison E hadd F ε P = ε.app (q.obj P) := by
      dsimp only [scalarPairComplexComparison]
      change F.map (𝟙 _) ≫ ε.app (q.obj P) ≫ 𝟙 _ = ε.app (q.obj P)
      simp
    rw [hcP]
    exact hh

end SheafOfModules

namespace CategoryTheory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] monoidalCategory derivedInternalHomOfUniverses
  coefficientTotalTensor CoefficientTensorModels.iso
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

private theorem scalarHomModels_exists : Nonempty (ScalarHomModels.{c, v, r, w} J) := by
  classical
  have hmodels (R : Sheaf J CommRingCat.{max c v r}) :
      ∃ S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R),
        Nonempty (CoefficientTensorModels.{r, c, v, w} J R S) := by
    obtain ⟨S, T, _⟩ := ringedDerived_closed_symmetric_monoidal.{c, v, r, w} J R
    exact ⟨S, ⟨T⟩⟩
  choose closed model using hmodels
  refine ⟨{ closed := closed, model := fun R ↦ (model R).some, scalar := ?_ }⟩
  intro R S a
  exact (scalarDerivedPair_exists a).some

variable {J} {R S T : Sheaf J CommRingCat.{max c v r}}

private theorem scalarDerivedRestriction_conservative (a : R ⟶ S)
    {N N' : DerivedCategory (scalarModules J S)} (f : N ⟶ N')
    (hf : IsIso ((scalarDerivedRestriction a).map f)) : IsIso f := by
  let U := scalarRestriction a
  let V := SheafOfModules.toSheaf ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  have : (U ⋙ V).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)).ReflectsIsomorphisms
  have : U.ReflectsIsomorphisms := reflectsIsomorphisms_of_comp U V
  have : IsIso (U.mapDerivedCategory.map f) := hf
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (U.map ((DerivedCategory.homologyFunctor (scalarModules J S) n).map f)) :=
    (NatIso.isIso_map_iff (U.mapDerivedCategoryHomologyFunctorIso n) f).2
      (by change IsIso ((DerivedCategory.homologyFunctor _ n).map
            (U.mapDerivedCategory.map f)); infer_instance)
  exact isIso_of_reflects_iso _ U

/-- The full unbounded scalar internal-Hom adjunction and all its normalizations.
The existential presentations are fixed by the recorded universal derived pairs,
actual pure-tensor formulas and representative evaluation. No arbitrary replacement
of tensor, internal Hom, restriction or the comparison map is admitted.
Source: Bhatt--Scholze, Remark 6.8.15, ambient derived operations;
Stacks Project, sites-cohomology.tex, Tags 07A6, 07A4, 08J9, 08JA and 0D6D;
derived.tex Tag 05RT
(blueprint: lem-sfb-dc-hom-scalar-adjunction).
Proof: obtain the actual tensor-Hom representative model from the ringed-derived
closed-structure theorem. Construct the normalized scalar pair from independent-universe
derived change of rings and the extension-restriction adjunction; quotient comparison
identities identify its homotopy transpose with the recorded chain transpose. Use the
normalized tensor comparisons and their coefficient-tower coherence. The explicit
five-Hom-equivalence construction gives the isomorphism, its representing bijections,
evaluation equation and uniqueness. Finally exact restriction commutes with cohomology,
reflects module-sheaf isomorphisms, and therefore reflects derived isomorphisms by the
unbounded cohomology criterion. -/
theorem scalarInternalHomAdjunction_exists :
    ∃ (M : ScalarHomModels.{c, v, r, w} J)
      (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
        ScalarHomTensorComparison M a), Nonempty (ScalarInternalHomAdjunction M μ) := by
  classical
  obtain ⟨M⟩ := scalarHomModels_exists.{c, v, r, w} J
  obtain ⟨μ, hcomp, hid⟩ := scalarTensorTowerComparison_exists.{c, v, r, w} M
  refine ⟨M, μ, ⟨{
    iso := fun a ↦ scalarHomCanonicalIso.{c, v, r, w} M a (μ a)
    evaluation := ?_
    unique := ?_
    representing := ?_
    composition := hcomp
    identity := hid
    conservative := ?_ }⟩⟩
  · intro R S a K N
    exact ClosedScalarHom.evaluation (M.closed R) (M.closed S)
      (M.scalar a).adjunction (μ a).iso K N
  · intro R S a β hβ
    exact ClosedScalarHom.unique (M.closed R) (M.closed S)
      (M.scalar a).adjunction (μ a).iso β hβ
  · intro R S a A K N t
    exact ClosedScalarHom.representing (M.closed R) (M.closed S)
      (M.scalar a).adjunction (μ a).iso A K N t
  · intro R S a N N' f hf
    exact scalarDerivedRestriction_conservative.{c, v, r, w} a f hf

end CategoryTheory
