/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdRawLocalization.FdRawLocalizationScalarCoherence
import WeilConjectures.FourierTransform.FdIntegralAmbientScalarNormalization
import WeilConjectures.FourierTransform.FdIntegralScalarRestrictionExact
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward
import WeilConjectures.FourierTransform.FdIntegralStageExact

/-! # Integral inputs for raw scalar-comparison descent

Source: trace-definition coefficient-category comparison, integral steps 1--6
(blueprint: lem-fd-integral-scalar-descent-inputs).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FdRawLocalization
namespace WeilConjectures

private theorem heq_composite
    {A : Type*} [Category A] {X X' Y Y' Z : A}
    (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : HEq f g) (q : Y' ⟶ Z) :
    HEq (f ≫ eqToHom hY ≫ q) (g ≫ q) := by
  subst X'
  subst Y'
  cases hf
  simp

private theorem liftIntegralComparison
    {A B : Type*} [Category A] [Category B] (P : ObjectProperty B)
    (F G : A ⥤ P.FullSubcategory) (F' G' : A ⥤ B)
    (hF : F ⋙ P.ι = F') (hG : G ⋙ P.ι = G') (a : F' ≅ G') :
    ∃ b : F ≅ G, ∀ K, HEq (P.ι.map (b.hom.app K)) (a.hom.app K) := by
  let ff := (Functor.FullyFaithful.ofFullyFaithful P.ι).whiskeringRight A
  let e : F ⋙ P.ι ≅ G ⋙ P.ι := eqToIso hF ≪≫ a ≪≫ (eqToIso hG).symm
  let b : F ≅ G := ff.preimageIso e
  refine ⟨b, ?_⟩
  intro K
  have hb : Functor.whiskerRight b.hom P.ι = e.hom := ff.map_preimage e.hom
  have hbK := congrArg (fun t ↦ t.app K) hb
  change HEq ((Functor.whiskerRight b.hom P.ι).app K) (a.hom.app K)
  rw [hbK]
  change HEq ((eqToHom hF ≫ a.hom ≫ eqToHom hG.symm).app K) (a.hom.app K)
  cases hF
  cases hG
  simp

private theorem inverseForwardComparison
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : A} {Z V W : B} (b : X ≅ Y) (c : F.obj Y ≅ Z)
    (a : F.obj X ⟶ V) (d : Z ⟶ W) (e : V ≅ W)
    (h : F.map b.hom ≫ c.hom ≫ d = a ≫ e.hom) :
    c.inv ≫ F.map b.inv ≫ a = d ≫ e.inv := by
  apply e.eq_comp_inv.mpr
  simp only [Category.assoc]
  rw [← h, ← F.map_comp_assoc, b.inv_hom_id, F.map_id, Category.id_comp,
    c.inv_hom_id_assoc]

/-- The integral completion comparison in both coefficient presentations, ready for raw
localization. This statement makes no assertion about rational comparisons or stage systems.
Source: trace-definition final coefficient-category sentence, integral comparison steps 1--6
(blueprint: lem-fd-integral-scalar-descent-inputs).

Proof: Obtain the normalized ordinary transports and ambient comparisons from
fdIntegralAmbientScalarNormalization. The stage integral_identity equations identify
the two endpoint functors after the full PBC inclusion with these ambient functors.
Take the preimage isomorphism under fully faithful right whiskering; map_preimage
and equality elimination give its component HEq. The same equality elimination
inserts the target integral_identity cast in the representative completion equation.
fdIntegralStageExact proves exactness of the supplied stage functors for their
normalized shifts. Apply fdIntegralScalarRestrictionExact for the two shift squares
and exact scalar composites, and fdIntegralScalarPresentationForward for the forward
associator and multiplication/completeness unit laws. For the inverse cocycle,
postcompose with the direct comparison hom, replace the forward associator equation,
and cancel the two comparison inverses. Precomposition of the forward unit equation
with the comparison inverse gives the inverse unit law, including repeated fields.
All maps retain their original coefficient presentations and completion normalization.
-/
theorem fdIntegralScalarDescentInputs
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) :
    ∃ (ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h)
      (comparison : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
            pbcAmbientScalarExtension l Ω T h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T E L h ⋙
          (sfIntegralConstructible l (pbcFiniteField.{u} l Ω L) T).ι ⋙
            integralDetailedTransport T l (pbcFiniteField.{u} l Ω L))
      (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L),
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      HEq ((b h).hom.app K).hom ((comparison h).hom.app K)) ∧
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
      (DerivedCategory.Q.obj P.obj)),
    HEq ((comparison h).hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
        ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
        ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj))
      ((pbcAmbientScalarExtension l Ω T h).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P.obj) ≫
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
          (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map ((ordinary h).completion l Ω P.obj))) ∧
    (∀ E : Padic.FiniteCoefficientFields l Ω, (I l Ω T stage E).IsTriangulated) ∧
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      NatTrans.CommShift (b h).hom ℤ ∧ NatTrans.CommShift (b h).inv ℤ) ∧
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (I l Ω T stage E ⋙ C l Ω T h).IsTriangulated ∧
        (U l Ω T h ⋙ I l Ω T stage L).IsTriangulated) ∧
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
      (V : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
      (hV : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
        (DerivedCategory.Q.obj V.obj)),
      HEq (((b h).hom.app ⟨DerivedCategory.Q.obj V.obj, hV⟩).hom ≫
        eqToHom (congrArg (fun F ↦ F.obj
          ((U l Ω T h).obj ⟨DerivedCategory.Q.obj V.obj, hV⟩))
          (stage L).integral_identity) ≫
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
          ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app V) ≫
        (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
          ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj V.obj))
        ((pbcAmbientScalarExtension l Ω T h).map
          ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app V.obj) ≫
        pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
          (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
            (.up ℤ)).obj V.obj) ≫
        DerivedCategory.Q.map ((ordinary h).completion l Ω V.obj))) ∧
    (∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b k).inv.app ((U l Ω T h).obj K) ≫
        (C l Ω T k).map ((b h).inv.app K) ≫
        (pbcIntegralScalarAssociator l Ω T dT.out iT.out h k).hom.app
          ((I l Ω T stage E).obj K) =
      (I l Ω T stage M).map ((integralAssoc l Ω T h k).hom.app K) ≫
        (b (h.trans k)).inv.app K) ∧
    (∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b (le_refl E)).inv.app K ≫
        (pbcIntegralScalarUnit l Ω T dT.out iT.out E).hom.app ((I l Ω T stage E).obj K) =
      (I l Ω T stage E).map ((integralUnit l Ω T E).hom.app K)) := by
  classical
  have hn := @fdIntegralAmbientScalarNormalization D l _ hl Ω _ _ _ T _ dT iT
  choose ordinary comparison hcomparison using @hn
  have hb (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
      ∃ b : I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L,
        ∀ K, HEq (b.hom.app K).hom ((comparison h).hom.app K) := by
    apply liftIntegralComparison
      (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω L))
      (I l Ω T stage E ⋙ C l Ω T h) (U l Ω T h ⋙ I l Ω T stage L)
      _ _ ?_ ?_ (comparison h)
    · change (I l Ω T stage E ⋙ pbcStageInclusion l Ω T E) ⋙
          pbcAmbientScalarExtension l Ω T h = _
      rw [(stage E).integral_identity]
      rfl
    · change U l Ω T h ⋙ (I l Ω T stage L ⋙ pbcStageInclusion l Ω T L) = _
      rw [(stage L).integral_identity]
      rfl
  choose b hb using hb
  let b' : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L :=
    fun {E L} h ↦ b E L h
  have hI (E : Padic.FiniteCoefficientFields l Ω) : (I l Ω T stage E).IsTriangulated :=
    @fdIntegralStageExact D l _ hl Ω _ _ _ T _ dT iT stage E
  have hlift : fdIntegralScalarLiftProperty l Ω T stage @ordinary @b' := by
    intro E L h V hV
    let K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T :=
      ⟨DerivedCategory.Q.obj V.obj, hV⟩
    have hX := congrArg (fun F ↦ (pbcAmbientScalarExtension l Ω T h).obj (F.obj K))
      (stage E).integral_identity
    have hY := congrArg (fun F ↦ F.obj ((U l Ω T h).obj K))
      (stage L).integral_identity
    exact (heq_composite hX hY _ _ (hb E L h K) _).trans (hcomparison h V hV)
  -- Project the conjunctions directly to avoid case elimination over the large remaining goal.
  have hrestriction := @fdIntegralScalarRestrictionExact D l _ hl Ω _ _ _ T _ dT iT stage
    @ordinary @b' @hlift hI
  have hforward := @fdIntegralScalarPresentationForward D l _ hl Ω _ _ _ T _ dT iT stage
    @ordinary @b' @hlift
  refine ⟨@ordinary, @comparison, @b', (fun {E L} h K ↦ hb E L h K),
    @hcomparison, hI, hrestriction.1, hrestriction.2, @hlift, ?_, ?_⟩
  · intro E L M h k K
    exact inverseForwardComparison (C l Ω T k) ((b' h).app K)
      ((b' k).app ((U l Ω T h).obj K))
      ((pbcIntegralScalarAssociator l Ω T dT.out iT.out h k).hom.app
        ((I l Ω T stage E).obj K))
      ((I l Ω T stage M).map ((integralAssoc l Ω T h k).hom.app K))
      ((b' (h.trans k)).app K) (hforward.1 h k K)
  · intro E K
    exact ((b' (le_refl E)).app K).inv_comp_eq.mpr (hforward.2 E K).symm

end WeilConjectures
