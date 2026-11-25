/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists

/-! # Cohomology concentration of reduced shifted comparison units
Source: diagonal tower system proof, step (3), target computation.
(blueprint: lem-sfb-strict-kummer-cohomology-concentration). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  comparisonUpperStar diagonalScalarExtension diagonalScalarAdjunction

private theorem scalar_epi_of_iso {B : Type*} [Category B] [Abelian B]
    (n : ℕ) {X Y : B} (e : X ≅ Y) [Epi (n • 𝟙 Y)] : Epi (n • 𝟙 X) := by
  have : Epi (e.hom ≫ (n • 𝟙 Y) ≫ e.inv) := inferInstance
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
    Category.comp_id, Category.id_comp, Iso.hom_inv_id] using this

private theorem quotient_exact_off_kernel {B : Type*} [Category B] [Abelian B]
    (K Q : CochainComplex B ℤ) (n : ℕ) (g : K ⟶ Q)
    (w : (n • 𝟙 K) ≫ g = 0)
    (hS : (ShortComplex.mk (n • 𝟙 K) g w).ShortExact)
    (hz : ∀ i : ℤ, i ≠ 0 → IsZero (K.homology i))
    (he : Epi (n • 𝟙 (K.homology 0)))
    (i : ℤ) (hi : i ≠ -1) : Q.ExactAt i := by
  apply hS.exactAt_X₃ i ?_ ?_
  · by_cases h : i = 0
    · subst i
      change Epi ((HomologicalComplex.homologyFunctor B (.up ℤ) 0).map (n • 𝟙 K))
      rw [Functor.map_nsmul, (HomologicalComplex.homologyFunctor B (.up ℤ) 0).map_id]
      exact he
    · exact (hz i h).epi _
  · intro j hij
    apply (hz j ?_).mono
    change i + 1 = j at hij
    omega

private theorem exactAt_of_evaluations {B : Type*} [Category B] [Abelian B]
    (K : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (i : ℤ)
    (h : ∀ n : ℕᵒᵖ,
      ((((evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj K).ExactAt i) :
    K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext n
  have he : ((K.sc i).map ((evaluation ℕᵒᵖ B).obj n)).Exact := h n
  have hz := (ShortComplex.exact_iff_isZero_homology _).1 he
  have hz' : IsZero (((evaluation ℕᵒᵖ B).obj n).obj (K.homology i)) :=
    IsZero.of_iso hz ((K.sc i).mapHomologyIso ((evaluation ℕᵒᵖ B).obj n)).symm
  exact hz'.eq_of_src _ _

private theorem reduction_counit_on_class
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (ℓ : ℕ) (L : A ⥤ B) (D : DiagonalDerivedReduction ℓ L)
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (inv : ∀ {P Q : CochainComplex A ℤ} (f : P ⟶ Q), QuasiIso f → good P → good Q →
      QuasiIso ((D.ordinary.E.mapHomologicalComplex (.up ℤ)).map f))
    (P : CochainComplex A ℤ) (hP : good P) : IsIso (D.ε.app P) := by
  obtain ⟨T, ε, hu, _, _, hc⟩ := cochainDerivedFullExists D.ordinary.E good res inv
  let := hu
  let := D.universal
  let c := Functor.leftDerivedNatIso D.T T D.ε ε
    (HomologicalComplex.quasiIso A (.up ℤ)) (Iso.refl _)
  have h : c.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P = D.ε.app P := by
    dsimp only [c, Functor.leftDerivedNatIso]
    simpa only [Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app D.T T D.ε ε
        (HomologicalComplex.quasiIso A (.up ℤ)) (𝟙 _) P
  let := hc P hP
  rw [← h]
  infer_instance

private theorem reduction_of_divisible_concentrated
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (ℓ : ℕ) (L : A ⥤ B) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (D : DiagonalDerivedReduction ℓ L) (M : A)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (p : P ⟶ K),
        (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (L.obj (P.X i)))) ∧ QuasiIso p)
    (he : ∀ n : ℕ, Epi (ℓ ^ (n + 1) • 𝟙 (L.obj M))) :
    (D.T.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj M))).IsGE (-1) ∧
    (D.T.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj M))).IsLE (-1) := by
  let good : CochainComplex A ℤ → Prop := fun P ↦
    ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (L.obj (P.X i)))
  have hinv {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (hf : QuasiIso f)
      (hP : good P) (hQ : good Q) :
      QuasiIso ((D.ordinary.E.mapHomologicalComplex (.up ℤ)).map f) := by
    let := hf
    exact reductionTower_quasiIso ℓ L D.ordinary f hP hQ
  obtain ⟨P, p, hP, hp⟩ := res ((CochainComplex.singleFunctor A 0).obj M)
  let := hp
  let := reduction_counit_on_class ℓ L D good res hinv P hP
  let LP := (L.mapHomologicalComplex (.up ℤ)).obj P
  let es : (L.mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor A 0).obj M) ≅
      (CochainComplex.singleFunctor B 0).obj (L.obj M) :=
    (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app M
  let q : LP ⟶ (CochainComplex.singleFunctor B 0).obj (L.obj M) :=
    (L.mapHomologicalComplex (.up ℤ)).map p ≫ es.hom
  have hq₁ : QuasiIso ((L.mapHomologicalComplex (.up ℤ)).map p) := inferInstance
  have hq₂ : QuasiIso es.hom := quasiIso_of_isIso _
  have : QuasiIso q := quasiIso_comp _ _
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero (LP.homology i) := by
    apply HomologicalComplex.ExactAt.isZero_homology
    apply (exactAt_iff_of_quasiIsoAt q i).2
    exact HomologicalComplex.ExactAt.of_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (L.obj M) i hi)
  let h0 : LP.homology 0 ≅ L.obj M :=
    isoOfQuasiIsoAt q 0 ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (L.obj M)
  let EP : CochainComplex (ℕᵒᵖ ⥤ B) ℤ :=
    (D.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P
  have hex (i : ℤ) (hi : i ≠ -1) : EP.ExactAt i := by
    apply exactAt_of_evaluations
    intro n
    let := he n.unop
    exact quotient_exact_off_kernel LP _ (ℓ ^ (n.unop + 1))
      (reductionComplexSequence ℓ L D.ordinary n.unop P).g
      (reductionComplexSequence ℓ L D.ordinary n.unop P).zero
      (reductionComplexSequence_shortExact ℓ L D.ordinary n.unop P (hP n.unop))
      hz (scalar_epi_of_iso _ h0) i hi
  let : EP.IsGE (-1) := (CochainComplex.isGE_iff EP (-1)).2
    (fun i hi ↦ hex i (by omega))
  let : EP.IsLE (-1) := (CochainComplex.isLE_iff EP (-1)).2
    (fun i hi ↦ hex i (by omega))
  let e : D.T.obj (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor A 0).obj M)) ≅ DerivedCategory.Q.obj EP :=
    (D.T.mapIso (asIso (DerivedCategory.Q.map p))).symm ≪≫ asIso (D.ε.app P)
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e.symm (-1),
    DerivedCategory.TStructure.t.isLE_of_iso e.symm (-1)⟩

/-- Simultaneous reduction of shifted comparison units has cohomology only in
 degree minus two. This assertion specifies no roots identification, comparison
 isomorphism, or unit normalization.

Source: diagonal tower system proof, step (3), target paragraph
(blueprint: lem-sfb-strict-kummer-cohomology-concentration).

Proof: resolve the degree-zero comparison-units complex by a flat-term K-flat
complex P. Nonzero-integer multiplication is mono on the constant integral unit,
hence on every flat term. Exact p-adic scalar extension preserves these monos.
On this resolving class the multiplication/quotient short complexes are short
exact, and their long exact homology sequences show that simultaneous reduction
inverts quasi-isomorphisms. The resolving-class derived construction and
uniqueness of left-derived functors therefore show that the supplied D's counit
is invertible on P. Scalar extension of P resolves the degree-zero scalar
extension of comparison units. Positive prime-power multiplication on units is
epi by the small-etale Kummer exact sequence; comparison pullback and scalar
extension, both left adjoints, preserve it. Consequently multiplication is epi
on every cohomology object of the scalar-extended P: degree zero uses this
Kummer epimorphism, and other degrees are zero. In the long exact sequence of
the level quotient, multiplication is also mono in the next degree except
when that next degree is zero. Thus each level quotient is exact away from
minus one. Exact evaluation commutes with homology and jointly detects zero
objects in the strict-system category, giving both bounds at minus one.
Transport through D's invertible counit and the localized resolution. Finally
use the shift comparison supplied by D.triangulated to shift both bounds to
minus two. No identification of kernels, scalar Tate lines, or boundary maps
is used. The zero sheaf and the first positive prime-power level require no
separate argument. -/
theorem strict_kummer_cohomology_concentration (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) :
    (D.T.obj (((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj
        ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf))⟦(1 : ℤ)⟧)).IsGE (-2) ∧
    (D.T.obj (((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj
        ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf))⟦(1 : ℤ)⟧)).IsLE (-2) := by
  let L := diagonalScalarExtension ℓ W
  let F := comparisonUpperStar AddCommGrpCat.{u + 1} W
  let M := F.obj W.gmSheaf
  let : L.Additive := scalarExtension_additive ℓ W
  let : PreservesFiniteLimits L := scalarExtension_exact ℓ W
  have : PreservesColimits L :=
    (diagonalScalarAdjunction ℓ W).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits L := inferInstance
  have hres : ∀ K : CochainComplex (DiagonalAb W) ℤ,
      ∃ (P : CochainComplex (DiagonalAb W) ℤ) (p : P ⟶ K),
        (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (L.obj (P.X i)))) ∧ QuasiIso p := by
    intro K
    obtain ⟨P, p, hp, hflat, _⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
    refine ⟨P, p, ?_, hp⟩
    intro n i
    have hm := flat_multiplication_mono (ℓ ^ (n + 1))
      (integerUnit_mono W (ℓ ^ (n + 1)) (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)) _ (hflat i)
    let := hm
    have h : Mono (L.map (ℓ ^ (n + 1) • 𝟙 (P.X i))) := inferInstance
    rw [Functor.map_nsmul, L.map_id] at h
    exact h
  have he (n : ℕ) : Epi (ℓ ^ (n + 1) • 𝟙 (L.obj M)) := by
    let : F.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_adjunction
      (comparisonAdjunction AddCommGrpCat.{u + 1} W)
    have hpow : IsUnit ((ℓ ^ (n + 1) : ℕ) : Γ(W, ⊤)) := by
      simpa only [Nat.cast_pow] using hW.pow (n + 1)
    have : Epi (ℓ ^ (n + 1) • 𝟙 W.gmSheaf) :=
      (W.kummerSequence_shortExact (ℓ ^ (n + 1)) hpow).epi_g
    have hF : Epi (F.map (ℓ ^ (n + 1) • 𝟙 W.gmSheaf)) := inferInstance
    have : Epi (ℓ ^ (n + 1) • 𝟙 M) := by
      simpa only [Functor.map_nsmul, F.map_id] using hF
    have hL : Epi (L.map (ℓ ^ (n + 1) • 𝟙 M)) := inferInstance
    simpa only [Functor.map_nsmul, L.map_id] using hL
  obtain ⟨hge, hle⟩ := reduction_of_divisible_concentrated ℓ L D M hres he
  let := hge
  let := hle
  let e : D.T.obj ((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M) ≅
      D.T.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (DiagonalAb W) 0).obj M)) :=
    D.T.mapIso ((DerivedCategory.singleFunctorIsoCompQ (DiagonalAb W) 0).app M)
  let : (D.T.obj ((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M)).IsGE (-1) :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm (-1)
  let : (D.T.obj ((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M)).IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_of_iso e.symm (-1)
  obtain ⟨hc, _⟩ := D.triangulated
  let := hc
  let e' : D.T.obj (((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M)⟦(1 : ℤ)⟧) ≅
      (D.T.obj ((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M))⟦(1 : ℤ)⟧ :=
    (D.T.commShiftIso (1 : ℤ)).app
      ((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M)
  have hge' := DerivedCategory.TStructure.t.isGE_shift
    (D.T.obj ((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M)) (-1) 1 (-2)
  have hle' := DerivedCategory.TStructure.t.isLE_shift
    (D.T.obj ((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M)) (-1) 1 (-2)
  let := hge'
  let := hle'
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e'.symm (-2),
    DerivedCategory.TStructure.t.isLE_of_iso e'.symm (-2)⟩

end AlgebraicGeometry.ProEtale
