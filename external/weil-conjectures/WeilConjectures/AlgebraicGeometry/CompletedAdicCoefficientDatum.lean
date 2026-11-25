/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CompleteCoefficientDatum
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Completed adic coefficient datum

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1239,
node def-weil-pbc-adic-coefficient-datum; Stacks Tags 099L and 099M
(blueprint: def-weil-pbc-adic-coefficient-datum).

The finite coefficient sheaves are exactly the recorded sheafifications of continuous
functions on connected components. The ambient ring is their inverse limit. In particular,
no identification with the discrete constant coefficient category is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t uC vC r

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The Noetherian adic datum, including finiteness of every positive quotient.
The inherited fields give finite generation, additive torsion of A/I and perfectness.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
structure AdicCoefficientDatum (A : Type t) [CommRing A] extends CompleteCoefficientDatum A where
  quotientFinite : ∀ n : ℕ, Finite (A ⧸ ideal ^ (n + 1))

variable {A : Type t} [CommRing A]

/-- The positive quotient in the site's coefficient universe; n denotes exponent n+1.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev completedAdicQuotient (d : AdicCoefficientDatum A) (n : ℕ) :=
  ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))

/-- Quotient coefficients are finite, by the datum, also after changing universe.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicQuotient_finite (d : AdicCoefficientDatum A) (n : ℕ) :
    Finite (completedAdicQuotient d n) :=
  letI := d.quotientFinite n
  inferInstance

/-- Each finite quotient has the discrete topology specified by the datum.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicQuotient_topology (d : AdicCoefficientDatum A) (n : ℕ) :
    TopologicalSpace (completedAdicQuotient d n) := ⊥

/-- The quotient topology is discrete.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicQuotient_discrete (d : AdicCoefficientDatum A) (n : ℕ) :
    DiscreteTopology (completedAdicQuotient d n) := ⟨rfl⟩

/-- The actual finite coefficient sheaf from the recorded continuous-functions construction.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteRing (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :=
  ProEtale.finiteCoefficientRingSheaf T (completedAdicQuotient d n)

/-- Postcomposition by the quotient homomorphism on the coefficient presheaves.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFinitePresheafStep (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    ProEtale.finiteCoefficientPresheaf T (completedAdicQuotient d (n + 1)) ⟶
      ProEtale.finiteCoefficientPresheaf T (completedAdicQuotient d n) where
  app U := RingCat.ofHom
    ((RingHom.ulift (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _))).compLeftContinuous
      (ConnectedComponents U.unop.left) (continuous_of_discreteTopology))
  naturality _ _ _ := by ext s; rfl

/-- Sheafify the specified postcomposition maps, retaining their actual formula.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteStep (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicFiniteRing T d (n + 1) ⟶ completedAdicFiniteRing T d n :=
  (presheafToSheaf (ProEt.topology T) RingCat.{t + 1}).map
    (completedAdicFinitePresheafStep T d n)

/-- The strict inverse sequence of finite coefficient sheaves, with all longer composites.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicRingSystem (T : Scheme.{t}) (d : AdicCoefficientDatum A) :=
  Functor.ofOpSequence (completedAdicFiniteStep T d)

/-- The completed coefficient ring sheaf A_T, the actual sheaf limit of the finite quotients.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicRing (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    Sheaf (ProEt.topology T) RingCat.{t + 1} :=
  limit (completedAdicRingSystem T d)

private theorem finiteRing_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (n : ℕ) (U : T.ProEtᵒᵖ) (x y : (completedAdicFiniteRing T d n).obj.obj U) :
    x * y = y * x := by
  let J := ProEt.topology T
  let F := ProEtale.finiteCoefficientPresheaf T (completedAdicQuotient d n)
  let R := completedAdicFiniteRing T d n
  let η : F ⟶ R.obj := toSheafify J F
  have hs := (isSheaf_iff_isSheaf_of_type J
      (R.obj ⋙ CategoryTheory.forget RingCat.{t + 1})).1
    ((sheafCompose J (CategoryTheory.forget RingCat.{t + 1})).obj R).property
  apply (hs.isSeparated _ (J.intersection_covering
    (Presheaf.imageSieve_mem J η x) (Presheaf.imageSieve_mem J η y))).ext
  rintro V f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  change R.obj.map f.op (x * y) = R.obj.map f.op (y * x)
  rw [map_mul, map_mul, ← ha, ← hb, ← map_mul, ← map_mul]
  change C(ConnectedComponents V.left, completedAdicQuotient d n) at a b
  exact congrArg (η.app (op V)) (mul_comm a b)

/-- The limit ring sheaf is commutative on sections.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: continuous functions into the commutative quotient rings commute pointwise;
sheafification preserves that equation locally. Each limit projection therefore identifies
the images of xy and yx. Evaluate the limit on U: its projections are jointly injective,
so xy=yx. This argument includes the zero ring and the empty site object. -/
theorem completedAdicRing_mul_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (U : T.ProEtᵒᵖ) (x y : (completedAdicRing T d).obj.obj U) : x * y = y * x := by
  let D := completedAdicRingSystem T d
  let ev := sheafToPresheaf (ProEt.topology T) RingCat.{t + 1} ⋙
    (CategoryTheory.evaluation T.ProEtᵒᵖ RingCat.{t + 1}).obj U
  apply Concrete.isLimit_ext (D ⋙ ev)
    (isLimitOfPreserves ev (limit.isLimit D)) (x * y) (y * x)
  intro j
  change ((limit.π D j).hom.app U) (x * y) = ((limit.π D j).hom.app U) (y * x)
  rw [map_mul, map_mul]
  exact finiteRing_comm T d j.unop U _ _

/-- Retain the actual ring data of the limit and supply only its commutativity proof.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev completedAdicCommRingStructure (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (U : T.ProEtᵒᵖ) : CommRing ((completedAdicRing T d).obj.obj U) :=
  { RingCat.ring _ with mul_comm := completedAdicRing_mul_comm T d U }

/-- The same completed coefficient presheaf with commutativity retained.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicCommPresheaf (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    T.ProEtᵒᵖ ⥤ CommRingCat.{t + 1} where
  obj U := @CommRingCat.of ((completedAdicRing T d).obj.obj U)
    (completedAdicCommRingStructure T d U)
  map {U V} f :=
    letI := completedAdicCommRingStructure T d U
    letI := completedAdicCommRingStructure T d V
    CommRingCat.ofHom ((completedAdicRing T d).obj.map f).hom
  map_id U := (forget₂ CommRingCat RingCat).map_injective
    ((completedAdicRing T d).obj.map_id U)
  map_comp f g := (forget₂ CommRingCat RingCat).map_injective
    ((completedAdicRing T d).obj.map_comp f g)

/-- The commutative ring sheaf with precisely the completed limit's underlying ring sheaf.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicCommRing (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    Sheaf (ProEt.topology T) CommRingCat.{t + 1} :=
  ⟨completedAdicCommPresheaf T d,
    Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
      (completedAdicRing T d).property⟩

/-- Module sheaves over A_T, with Mathlib's actual abelian structure.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev CompletedAdicModules (T : Scheme.{t}) (d : AdicCoefficientDatum A) :=
  SheafOfModules.{t + 1} (completedAdicRing T d)

/-- The sheaf tensor structure over the completed commutative ring, not the constant ring.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicModules_monoidal (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    MonoidalCategory (CompletedAdicModules T d) :=
  SheafOfModules.monoidalCategory (completedAdicCommRing T d)

/-- Standard localization of the completed-coefficient module category.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicModules_hasDerived (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    HasDerivedCategory (CompletedAdicModules T d) := HasDerivedCategory.standard _

section DerivedReductionModels

variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (F : B ⥤ C) [F.Additive] (P : CochainComplex B ℤ → Prop)

/-- A left derived functor, its counit, and its computation on the resolving class.
Source: Stacks Tag 06YY (auxiliary; not a blueprint node). -/
structure DerivedReductionModelData where
  reduction : DerivedCategory B ⥤ DerivedCategory C
  counit : DerivedCategory.Qh ⋙ reduction ⟶
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  isLeftDerived : reduction.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso B (.up ℤ))
  isIso_counit : ∀ K : CochainComplex B ℤ, P K →
    IsIso (counit.app ((HomotopyCategory.quotient B (.up ℤ)).obj K))

/-- Retain the universally specified pair in one record, without changing either choice.
Source: Stacks Tag 06YY (auxiliary; not a blueprint node). -/
def derivedReductionModelDataOfExists
    (h : ∃ (LF : DerivedCategory B ⥤ DerivedCategory C)
      (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ)) ∧
        ∀ K : CochainComplex B ℤ, P K →
          IsIso (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj K))) :
    DerivedReductionModelData F P where
  reduction := h.choose
  counit := h.choose_spec.choose
  isLeftDerived := h.choose_spec.choose_spec.1
  isIso_counit := h.choose_spec.choose_spec.2

variable {F P}

/-- The comparison on complexes, including the localization factor isomorphisms.
Source: Stacks Tag 06YY (auxiliary; not a blueprint node). -/
def DerivedReductionModelData.complexCounit (D : DerivedReductionModelData F P)
    (K : CochainComplex B ℤ) :
    D.reduction.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
  D.reduction.map ((DerivedCategory.quotientCompQhIso B).inv.app K) ≫
    D.counit.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
    (DerivedCategory.quotientCompQhIso C).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K)

end DerivedReductionModels

set_option linter.defProp false in
/-- The full normalized scalar-extension witness along a map of coefficient sheaves.
Its object and map equalities fix ordinary tensor; its universal counit fixes the derived
functor. Source: blueprint order 1239; Stacks Tag 06YY
(blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicChangeData (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
      (ProEt.topology T) R))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
      (ProEt.topology T) S))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t} φ

/-- Ordinary scalar extension, fixed on objects and morphisms by the tensor witness.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  (completedAdicChangeData T φ).choose

/-- Additivity from the actual ordinary scalar-extension witness.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicChange_additive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (completedAdicChange T φ).Additive :=
  (completedAdicChangeData T φ).choose_spec.choose_spec.choose_spec.choose

/-- Derived scalar extension, chosen with its universal comparison and K-flat computation.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicDerivedChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  (completedAdicChangeData T φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose

namespace CompletedTensorComparisonProof

open SheafOfModules

set_option hygiene false in
local notation "𝓡" R =>
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local irreducible] monoidalCategory

-- Step 1: the same tensor abelian group, with the two scalar actions identified.
section RestrictionSheafification
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R₀ B₀ : Sheaf J RingCat.{r}}

end RestrictionSheafification

end CompletedTensorComparisonProof

section FiniteReductionComparison

attribute [local irreducible] SheafOfModules.monoidalCategory

end FiniteReductionComparison

/-- A sheafified pure tensor in the normalized ordinary scalar-extension functor.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicChangeTensor (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((completedAdicChange T φ).obj M).val.obj U :=
  (eqToHom ((completedAdicChangeData T φ).choose_spec.choose M).symm).val.app U
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))

end AlgebraicGeometry.Scheme
