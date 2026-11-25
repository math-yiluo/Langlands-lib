/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Algebra.Homology.Derived.DerivedScalarTruncationContinuity
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Cohomological bounds for derived extension of ring-sheaf scalars

Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 077J; the bounds are the
agent consequence detailed in the DAG proof, not a verbatim assertion of either tag
(blueprint: lem-weil-pbc-ringed-tensor-cohomological-bounds).

`ringedDerivedScalarExtension` selects the existing universal derived-change-of-rings
functor. Its ordinary functor is fixed on both objects and maps by that dependency;
the derived universal property determines its value up to compatible isomorphism.
No new tensor product, module category, or cohomological-bound predicate is introduced.

`ringedTensorCohomologicalBounds` states both bounds. Higher Tor is written directly
as the negative-degree cohomology of scalar extension of a degree-zero module.
The module universe is independent of both site universes; essential smallness and
the sheafification instances express the size convention for the abelian module category.
-/

@[expose] public section

set_option autoImplicit false

universe w r u v

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- The universal derived scalar-extension functor from the recorded K-flat construction.
Source: Stacks Project, Tag 06YU, using the universal pair of Tag 06YY
(blueprint: lem-weil-pbc-ringed-tensor-cohomological-bounds).
The choice is from `derivedChangeOfRingsIndependentCoefficients`: the ordinary tensor
functor has its objects and maps specified, and the derived pair has the left-derived
universal property and its canonical counit is invertible on K-flat representatives.
Thus this selects a construction determined up to the isomorphism used by cohomology. -/
noncomputable def ringedDerivedScalarExtension
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S))] :
    DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S)) :=
  ((derivedChangeOfRingsIndependentCoefficients φ).choose_spec.choose_spec.choose_spec.choose_spec
    |>.2.2).choose

private theorem bounded_kflat_model
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})
    (G : CochainComplex (SheafOfModules.{r}
      (derivedChangeRingIndependentCoefficients J R)) ℤ)
    (a : ℤ) [G.IsStrictlyLE a] :
    ∃ (P : CochainComplex (SheafOfModules.{r}
        (derivedChangeRingIndependentCoefficients J R)) ℤ) (p : P ⟶ G),
      P.IsStrictlyLE a ∧ P.IsKFlatIndependentCoefficients ∧ QuasiIso p := by
  let A := SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)
  have (I : Type r) : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  have (I : Type r) : HasColimitsOfShape (Discrete I) A :=
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      _ _
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) := by
    have := tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (MonoidalCategory.tensorLeft M)
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  have : HasFiniteBiproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteCoproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
    hasFiniteCoproducts_of_hasFiniteBiproducts _
  let := hasFunctorialFlatResolution_kfi R
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  let K : CochainComplex.Minus A := ⟨G, a, inferInstance⟩
  have : (Λ.bicomplexFunctor.obj G).HasTotal (.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_isStrictlyLE _ a 0
  let P := ((ObjectProperty.flat.ι : _ ⥤ A).mapHomologicalComplex (.up ℤ)).obj
    ((Λ.bicomplexFunctor.obj G).total (.up ℤ))
  have hb : CochainComplex.IsStrictlyLE P a := by
    dsimp [P]
    infer_instance
  have hf (i : ℤ) : IsFlatOnSite (J := J) (R := R) (P.X i) := by
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X i)).symm
      (((Λ.bicomplexFunctor.obj G).total (.up ℤ)).X i).property.2
  exact ⟨P, Λ.totalπ K, hb,
    isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P a hf, inferInstance⟩

private theorem finite_lower_bound
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (G : CochainComplex A ℤ) (a : ℤ) [G.IsGE a]
    (hlayer : ∀ q : ℤ, a ≤ q →
      (F.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor A q).obj (G.homology q)))).IsGE a) :
    ∀ b : ℤ, (F.obj (DerivedCategory.Q.obj (G.truncLE b))).IsGE a := by
  have hzero (b : ℤ) (hb : b < a) :
      IsZero (DerivedCategory.Q.obj (G.truncLE b)) := by
    have : (G.truncLE b).IsGE a :=
      (((DerivedCategory.truncation_triangle A b).2.2 G a).2 inferInstance).2.1
    rw [IsZero.iff_id_eq_zero]
    exact DerivedCategory.TStructure.t.zero (𝟙 _) b a hb
  have key (n : ℕ) :
      (F.obj (DerivedCategory.Q.obj (G.truncLE (a + n - 1)))).IsGE a := by
    induction n with
    | zero =>
      have hz := F.map_isZero (hzero (a - 1) (by omega))
      simpa using DerivedCategory.TStructure.t.isGE_of_isZero hz a
    | succ n ih =>
      obtain ⟨i, j, _, _, k, hk, _⟩ :=
        (DerivedCategory.truncation_triangle A (a + n)).1 G
      have htri := F.map_distinguished _ hk
      have h := DerivedCategory.TStructure.t.isGE₂ _ htri a ih (hlayer _ (by omega))
      convert h using 1
      congr 3
      omega
  intro b
  by_cases hb : b < a
  · exact DerivedCategory.TStructure.t.isGE_of_isZero (F.map_isZero (hzero b hb)) a
  · have hn : a + ((b + 1 - a).toNat : ℤ) - 1 = b := by omega
    simpa only [hn] using key (b + 1 - a).toNat

/-- Derived extension of scalars preserves an upper cohomological bound. It also preserves
any lower bound when the cohomology sheaves in the retained range have zero higher Tor.
Here `Tor_p(N,S)` is exactly `H^(-p)(F(Q(N[0])))`, and `IsLE` and `IsGE` are the standard
bounds, equivalent to cohomology vanishing above and below the stated integer.
Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 077J, agent consequence
(blueprint: lem-weil-pbc-ringed-tensor-cohomological-bounds).

Proof:
1. For the upper bound, choose a good upper-truncated representative of M
(def-sbc-standard-tstructure-derived-category). Apply the same-bound flat replacement
(lem-pc-kflat-bounded-flat-replacement). The replacement is K-flat by
lem-pc-bounded-above-flat-kflat-site; its termwise scalar extension computes F(M) by
lem-pur-derived-change-of-rings. Terms and hence cohomology above a vanish.
2. For a sheaf N with vanishing positive Tor, the definition gives vanishing of F(N[0])
in negative degrees. Step 1 gives vanishing in positive degrees. Exactness and shift
compatibility of lem-pur-derived-change-of-rings show F(N[-q]) is concentrated in degree q,
with the shift convention of def-weil-abstract-derived-category.
3. For b < a, the good upper truncation of M at b is zero, since all its cohomology is
zero. Starting at b = a-1, induct using the successive-truncation triangle
(theorem-pbc-injective-acyclicity). Its third term is H^b(M)[-b]. After applying F,
Step 2 concentrates this term in degree b >= a. The long exact cohomology sequence
(lem-sf-derived-homology-long-exact) and induction give the lower bound for every finite
upper truncation of M.
4. For a representative G, take compatible bounded-above flat resolutions E_n of its
good upper truncations, with maps into G (lem-pc-flat-truncation-tower). Their degreewise
colimit P maps to G. Exact filtered colimits (lem-pc-module-filtered-colimits-tensor)
preserve kernels, images and their quotients, so commute with cohomology. In any fixed
degree i the maps H^i(E_n) -> H^i(G) are compatible isomorphisms once n >= max(0,i).
Their colimit is an isomorphism. Thus P -> G is a quasi-isomorphism.
5. Each E_n is K-flat by lem-pc-bounded-above-flat-kflat-site. Tensor commutes with the
filtered colimit by lem-pc-module-filtered-colimits-tensor, and exactness of that colimit
preserves acyclicity. Therefore P is K-flat (def-pc-kflat-complex). If necessary, exchange
the tensor factors using the signed symmetry (-1)^(rs); the differential formula of
def-pc-tensor-complex-sheaves verifies this chain isomorphism and its inverse.
6. The K-flat computation (lem-pur-derived-change-of-rings) represents F(M) by P tensor S,
which is the degreewise colimit of E_n tensor S. Step 3 makes each of these acyclic below
a, so the exact-colimit cohomology calculation in Step 4 proves the same for F(M).
One may calculate after restricting scalars to R: the kernels and sheafified cokernels
are the same underlying abelian sheaves (situation-conventions), so vanishing
also holds as an S-module sheaf. This uses no upper bound for the second assertion and
no flatness, finite generation, boundedness beyond the stated bounds, or site points. -/
theorem ringedTensorCohomologicalBounds
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S))]
    (a : ℤ) :
    (∀ M : DerivedCategory
      (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)),
      M.IsLE a → ((ringedDerivedScalarExtension φ).obj M).IsLE a) ∧
    (∀ M : DerivedCategory
      (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)),
      M.IsGE a →
      (∀ (q : ℤ), a ≤ q → ∀ (p : ℕ), 0 < p →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S)) (-(p : ℤ))).obj
          ((ringedDerivedScalarExtension φ).obj
            (DerivedCategory.Q.obj
              ((CochainComplex.singleFunctor
                (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) 0).obj
                ((DerivedCategory.homologyFunctor
                  (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) q).obj
                    M)))))) →
      ((ringedDerivedScalarExtension φ).obj M).IsGE a) := by
  let h := derivedChangeOfRingsIndependentCoefficients φ
  let E := h.choose
  let hobj := h.choose_spec.choose
  let hadd := h.choose_spec.choose_spec.choose_spec.choose
  let hrest := h.choose_spec.choose_spec.choose_spec.choose_spec
  let F := hrest.2.2.choose
  let ε := hrest.2.2.choose_spec.choose
  have hspec := hrest.2.2.choose_spec.choose_spec
  have : E.Additive := hadd
  obtain ⟨hshift, htri⟩ := hspec.2.1
  let := hshift
  have : F.IsTriangulated := htri
  change (∀ M, M.IsLE a → (F.obj M).IsLE a) ∧ _
  constructor
  · intro M hM
    obtain ⟨G, hG, ⟨eG⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE M a
    obtain ⟨P, p, hb, hk, hp⟩ := bounded_kflat_model R G a
    have : QuasiIso p := hp
    have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
      hspec.2.2 P hk
    let e₁ : F.obj (DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P) :=
      F.mapIso ((DerivedCategory.quotientCompQhIso _).symm.app P) ≪≫
        asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
        DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
        (DerivedCategory.quotientCompQhIso _).app _
    have : CochainComplex.IsStrictlyLE ((E.mapHomologicalComplex (.up ℤ)).obj P) a := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact E.map_isZero (P.isZero_of_isStrictlyLE a i hi)
    have : (DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).IsLE a :=
      inferInstance
    have : (F.obj (DerivedCategory.Q.obj P)).IsLE a :=
      DerivedCategory.TStructure.t.isLE_of_iso e₁.symm a
    exact DerivedCategory.TStructure.t.isLE_of_iso
      (F.mapIso (asIso (DerivedCategory.Q.map p) ≪≫ eG.symm)) a
  · intro M hM hTor
    let A := SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)
    let B := SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S)
    let G := DerivedCategory.Q.objPreimage M
    let eG : DerivedCategory.Q.obj G ≅ M := DerivedCategory.Q.objObjPreimageIso M
    have : G.IsGE a := by
      rw [← DerivedCategory.isGE_Q_obj_iff]
      exact DerivedCategory.TStructure.t.isGE_of_iso eG.symm a
    have hsingle₀ (q : ℤ) (hq : a ≤ q) :
        (F.obj (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor A 0).obj (G.homology q)))).IsGE 0 := by
      rw [DerivedCategory.isGE_iff]
      intro i hi
      let p := (-i).toNat
      have hp : 0 < p := by dsimp [p]; omega
      have hip : -(p : ℤ) = i := by dsimp [p]; omega
      have hz := hTor q hq p hp
      rw [hip] at hz
      let eH : G.homology q ≅ (DerivedCategory.homologyFunctor A q).obj M :=
        ((DerivedCategory.homologyFunctorFactors A q).app G).symm ≪≫
          (DerivedCategory.homologyFunctor A q).mapIso eG
      exact hz.of_iso ((DerivedCategory.homologyFunctor B i).mapIso
        (F.mapIso (DerivedCategory.Q.mapIso
          ((CochainComplex.singleFunctor A 0).mapIso eH))))
    have hlayer (q : ℤ) (hq : a ≤ q) :
        (F.obj (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor A q).obj (G.homology q)))).IsGE a := by
      have : DerivedCategory.TStructure.t.IsGE
          (F.obj ((CochainComplex.singleFunctor A 0 ⋙ DerivedCategory.Q).obj
            (G.homology q))) 0 := hsingle₀ q hq
      have : (F.obj ((DerivedCategory.singleFunctor A 0).obj (G.homology q))).IsGE 0 :=
        DerivedCategory.TStructure.t.isGE_of_iso
          (F.mapIso ((DerivedCategory.singleFunctorIsoCompQ A 0).app _).symm) 0
      have : DerivedCategory.TStructure.t.IsGE
          ((F.obj ((DerivedCategory.singleFunctor A 0).obj (G.homology q)))⟦-q⟧) q :=
        DerivedCategory.TStructure.t.isGE_shift _ 0 (-q) q (by omega)
      let e : (F.obj ((DerivedCategory.singleFunctor A 0).obj (G.homology q)))⟦-q⟧ ≅
          F.obj ((DerivedCategory.singleFunctor A q).obj (G.homology q)) :=
        (F.commShiftIso (-q)).symm.app _ ≪≫
          F.mapIso (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0 (by omega)).app
            (G.homology q))
      have : (F.obj ((DerivedCategory.singleFunctor A q).obj (G.homology q))).IsGE q :=
        DerivedCategory.TStructure.t.isGE_of_iso e q
      have : (F.obj (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor A q).obj (G.homology q)))).IsGE q :=
        DerivedCategory.TStructure.t.isGE_of_iso
          (F.mapIso ((DerivedCategory.singleFunctorIsoCompQ A q).app _)) q
      exact DerivedCategory.TStructure.t.isGE_of_ge _ a q hq
    have hfinite := finite_lower_bound F G a hlayer
    suffices (F.obj (DerivedCategory.Q.obj G)).IsGE a from
      DerivedCategory.TStructure.t.isGE_of_iso (F.mapIso eG) a
    apply derivedScalar_lower_bound_of_truncations φ E hobj
      h.choose_spec.choose_spec.choose F ?_ G a hfinite
    intro P hk
    have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
      hspec.2.2 P hk
    exact ⟨F.mapIso ((DerivedCategory.quotientCompQhIso _).symm.app P) ≪≫
      asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
      DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _⟩

end SheafOfModules
