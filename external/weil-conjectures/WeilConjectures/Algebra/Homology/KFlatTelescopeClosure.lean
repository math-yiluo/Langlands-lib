/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.KFlatClosure
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-!
# K-flatness and flatness under the telescope construction

Source: Stacks Project, Cohomology on Sites, proof of Lemma 06YS, with Lemmas 06YQ,
06YR and 07A3; Modules on Sites, Lemma 03EU (blueprint: lem-pc-kflat-closure).

The site and module universes are those of the landed `SheafOfModules.IsFlat`
(`C : Type u`, `Category.{u} C`, rings and modules in `u`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

-- Exact coproducts preserve each three-term complex defining acyclicity.
private theorem acyclic_coproduct {A : Type*} [Category.{u} A] [Abelian A]
    {I : Type*} [HasColimitsOfShape (Discrete I) A]
    [HasExactColimitsOfShape (Discrete I) A]
    (K : I → CochainComplex A ℤ) (hK : ∀ i, (K i).Acyclic) : (∐ K).Acyclic := by
  intro n
  let D := Discrete.functor K
  let S := (ShortComplex.functorEquivalence (Discrete I) A).inverse.obj
    (D ⋙ HomologicalComplex.shortComplexFunctor A (.up ℤ) n)
  have hEval : JointlyReflectIsomorphisms
      (fun j : Discrete I ↦ (evaluation (Discrete I) A).obj j) :=
    ⟨fun f h ↦ by
      have (j : Discrete I) : IsIso (f.app j) := h j
      exact NatIso.isIso_of_isIso_app f⟩
  have hS : S.Exact := (hEval.exact_iff S).2 (fun j ↦ hK j.as n)
  have hc (i : ℤ) := isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) i)
    (colimit.isColimit D)
  exact colim.exact_mapShortComplex hS
    (hc ((ComplexShape.up ℤ).prev n)) (hc n) (hc ((ComplexShape.up ℤ).next n))
    ((∐ K).d _ n) ((∐ K).d n _)
    (fun j ↦ (colimit.ι D j).comm _ _)
    (fun j ↦ (colimit.ι D j).comm _ _)

-- Tensor commutes with small coproducts, whose exactness preserves acyclicity.
private theorem isKFlat_coproduct_small
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) {I : Type*} [Small.{u} I]
    (K : I → CochainComplex (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hK : ∀ i : I, (K i).IsKFlatTensor) : (∐ K).IsKFlatTensor := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.tensorClosed R).2.1.some
  let := (SheafOfModules.grothendieckAbelian_with_localized_generator J R).1
  have : HasExactColimitsOfShape (Discrete I)
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) := by
    exact HasExactColimitsOfShape.of_domain_equivalence _
      (Discrete.equivalence (equivShrink.{u} I)).symm
  intro A hA
  let T := ((MonoidalCategory.curriedTensor _).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)).obj A
  have ht : (∐ fun i ↦ T.obj (K i)).Acyclic :=
    acyclic_coproduct _ (fun i ↦ hK i A hA)
  let e : Discrete.functor (fun i ↦ T.obj (K i)) ≅ Discrete.functor K ⋙ T :=
    (Discrete.compNatIsoDiscrete K T).symm
  exact fun n ↦ (ht n).of_iso
    (HasColimit.isoOfNatIso e ≪≫ (preservesColimitIso T (Discrete.functor K)).symm)

/-- Bounded-above flat complexes are K-flat; K-flat complexes are closed under mapping
cones, countable direct sums and sequential homotopy colimits; countable sums of flat
sheaves of modules are flat.
Source: Stacks Project, proof of Tag 06YS, Tags 06YQ, 06YR, 07A3 and 03EU
(blueprint: lem-pc-kflat-closure).

Proof:
1. Apply `lem-pc-bounded-above-flat-kflat-site`: truncate an acyclic test complex above,
tensor with the bounded-above flat complex, and filter the total complex. The graded
pieces are acyclic by flatness. Pass to the filtered colimit using exactness.
2. Apply `lem-pc-kflat-cone-direct-sum`: total tensor commutes with cones and countable
sums, and both constructions preserve acyclicity. For a sequence, its homotopy colimit
is the cone of `1 - shift` on its sum (`lem-pc-complex-hocolim-colimit`), so it is K-flat.
3. The sheaf-module category is Grothendieck abelian
(`prop-pur-kinjective-resolutions-exist`) and its tensor is symmetric monoidal closed
(`lem-pc-sheaf-modules-tensor-closed`). Tensor with a flat sheaf preserves finite limits.
Apply `lem-weil-pbc-flat-coproduct`; right exactness and symmetry then give exactness of
tensor-right with the sum, hence flatness by `def-pc-flat-sheaf-modules`. -/
theorem kFlat_closure
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    (∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) →
      (∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) → K.IsKFlatTensor) ∧
    (∀ (K L : CochainComplex (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (f : K ⟶ L),
      K.IsKFlatTensor → L.IsKFlatTensor → (mappingCone f).IsKFlatTensor) ∧
    (∀ (I : Type u) [Countable I],
      ∀ K : I → CochainComplex (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
      (∀ i : I, (K i).IsKFlatTensor) → (∐ K).IsKFlatTensor) ∧
    (∀ (K : ℕ → CochainComplex (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
        (t : ∀ n : ℕ, K n ⟶ K (n + 1)),
      (∀ n : ℕ, (K n).IsKFlatTensor) →
      (mappingCone (𝟙 (∐ K) -
        Sigma.desc (fun n : ℕ => t n ≫ Sigma.ι K (n + 1)))).IsKFlatTensor) ∧
    (∀ (I : Type u) [Countable I],
      ∀ F : I → SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      (∀ i : I, SheafOfModules.IsFlat (F i)) → SheafOfModules.IsFlat (∐ F)) := by
  refine ⟨fun K hb hf ↦ isKFlat_of_boundedAbove_flat K hb hf,
    fun K L f hK hL ↦ isKFlat_mappingCone f hK hL,
    fun I _ K hK ↦ isKFlat_coproduct_small R K hK, ?_, ?_⟩
  · intro K t hK
    have hsum := isKFlat_coproduct_small R K hK
    exact isKFlat_mappingCone _ hsum hsum
  · intro I _ F hF
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.symmetricCategory R
    let := (SheafOfModules.tensorClosed R).2.1.some
    let := (SheafOfModules.grothendieckAbelian_with_localized_generator J R).1
    have hflat (i : I) : ObjectProperty.flat (F i) := by
      have hi := hF i
      change exactFunctor _ _ (MonoidalCategory.tensorRight (F i)) at hi
      have : PreservesFiniteLimits (MonoidalCategory.tensorRight (F i)) := hi.1
      exact ⟨⟨preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (F i)).symm,
        (inferInstance : PreservesFiniteColimits (MonoidalCategory.tensorLeft (F i)))⟩, hi⟩
    exact (ObjectProperty.flat_coproduct F hflat).2

end CochainComplex
