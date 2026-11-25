/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData

import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Scalar extension and continuous coefficient transport -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

structure IntegralMatrixCoefficientTransport (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (g : Y ⟶ X) where
  functor : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) X) ⥤
    Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E))
  additive : functor.Additive
  finiteColimits : PreservesFiniteColimits functor
  regularIso : functor.obj (Mod.regular (condensedRingObj (integralCoeff ℓ E) X)) ≅
    Mod.regular ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E))
  coefficient : ∀ (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X)) (x : Y),
    ((((regularIso.inv ≫ functor.map p ≫ regularIso.hom).hom).hom.app
      (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down x =
      (integralRegularCoefficient ℓ E X p (g x)).val
  freeCokernel : ∀ (n t q : ℕ)
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (_eC : (((ProEtale.upperStar AddCommGrpCat.{u + 1} g).mapMod _).obj
      ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj (cokernel a))) ≅
      Mod.finiteFree ((ProEtale.upperStar AddCommGrpCat.{u + 1} g).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X)) q),
    functor.obj (cokernel a) ≅ Mod.finiteFree
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E)) q

section
variable {X : Scheme.{u}}
variable (R S : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
variable [MonObj R] [MonObj S] [IsCommMonObj R]
variable (φ : R ⟶ S) [IsMonHom φ]

private lemma extension_regular_unit :
    ((Mod.extendRestrictAdjunction φ).unit.app (Mod.regular R)).hom ≫
      (Mod.regularExtensionIso φ).hom.hom = φ := by
  exact Mod.extendUnitHom_extendHom φ (Mod.regularCoefficientMap φ)

private lemma extension_regular_square (p : Mod.regular R ⟶ Mod.regular R) :
    let qh : S ⟶ S := ((Mod.regularExtensionIso φ).inv ≫
      (Mod.extendScalars φ).map p ≫ (Mod.regularExtensionIso φ).hom).hom
    p.hom ≫ φ = φ ≫ qh := by
  dsimp only
  let A := Mod.extendRestrictAdjunction φ
  let e := Mod.regularExtensionIso φ
  let ηR := A.unit.app (Mod.regular R)
  have h := congrArg Mod.Hom.hom (A.unit.naturality p)
  change p.hom ≫ ηR.hom = ηR.hom ≫ ((Mod.extendScalars φ).map p).hom at h
  have he : ηR.hom ≫ e.hom.hom = φ := extension_regular_unit R S φ
  calc
    p.hom ≫ φ = p.hom ≫ ηR.hom ≫ e.hom.hom := by rw [he]
    _ = ηR.hom ≫ ((Mod.extendScalars φ).map p).hom ≫ e.hom.hom := by
      rw [← Category.assoc, h, Category.assoc]
    _ = φ ≫ (e.inv ≫ (Mod.extendScalars φ).map p ≫ e.hom).hom := by
      change _ = φ ≫ e.inv.hom ≫ ((Mod.extendScalars φ).map p).hom ≫ e.hom.hom
      conv_rhs => lhs; rw [← he]
      have hi : e.hom.hom ≫ e.inv.hom = 𝟙 _ := congrArg Mod.Hom.hom e.hom_inv_id
      simp only [Category.assoc, reassoc_of% hi]
end

private lemma integral_extended_regular_coefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [TotallyDisconnectedSpace E] (X : Scheme.{u})
    (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X))
    (q : condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
      condensedRingObj (Profinite.continuousMapRingObj E) X)
    (hq : p.hom ≫ coefficientMap (integralScalarMap ℓ E) X =
      coefficientMap (integralScalarMap ℓ E) X ≫ q) (x : X) :
    (((inv (chartComparison X E) ≫ q ≫ chartComparison X E).hom.app
      (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down x =
      (integralRegularCoefficient ℓ E X p x).val := by
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let eR := chartComparison X (continuousIntegers ℓ E)
  let eS := chartComparison X E
  let I := integralFunctionInclusion ℓ E X
  have hs : φ ≫ eS = eR ≫ I :=
    chartComparison_naturality X (continuousIntegers ℓ E) E
      (continuousIntegers ℓ E).subtype continuous_subtype_val
  have h := conjugated_morphism_square (𝟭 _) eR eS φ I p.hom q hs hq
  exact congrArg (fun k ↦ ((k.hom.app (op (Scheme.ProEt.mk (𝟙 X))))
    (ULift.up 1)).down x) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem field_regular_pullback_coefficient
    (E : Type) [NormedField E] [TotallyDisconnectedSpace E]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (p : condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
      condensedRingObj (Profinite.continuousMapRingObj E) X) (y : Y)
    (e : (ProEtale.upperStar AddCommGrpCat.{u + 1} g).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X) ⟶
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E))
    [IsIso e]
    (hs : ((ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app
        (condensedRingObj (Profinite.continuousMapRingObj E) X)) ≫
      (ProEtale.lowerStar AddCommGrpCat.{u + 1} g).map e =
        chartComparison X E ≫ continuousFunctionPushforward g E) :
    (((inv e ≫ (ProEtale.upperStar AddCommGrpCat.{u + 1} g).map p ≫ e).hom.app
      (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down y =
    (((inv (chartComparison X E) ≫ p ≫ chartComparison X E).hom.app
      (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down (g y) := by
  let adj := ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  apply continuous_function_unit_naturality g E
  apply conjugated_morphism_square (ProEtale.lowerStar AddCommGrpCat.{u + 1} g)
    (chartComparison X E) e (adj.unit.app _) (continuousFunctionPushforward g E)
    p ((ProEtale.upperStar AddCommGrpCat.{u + 1} g).map p) hs
  exact adj.unit.naturality p

private theorem integral_regular_pullback_coefficient_square
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [TotallyDisconnectedSpace E]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X))
    (q : condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
      condensedRingObj (Profinite.continuousMapRingObj E) X)
    (hq : p.hom ≫ coefficientMap (integralScalarMap ℓ E) X =
      coefficientMap (integralScalarMap ℓ E) X ≫ q)
    (e : (ProEtale.upperStar AddCommGrpCat.{u + 1} g).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X) ⟶
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E))
    [IsIso e]
    (hs : ((ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app
        (condensedRingObj (Profinite.continuousMapRingObj E) X)) ≫
      (ProEtale.lowerStar AddCommGrpCat.{u + 1} g).map e =
        chartComparison X E ≫ continuousFunctionPushforward g E) (y : Y) :
    (((inv e ≫ (ProEtale.upperStar AddCommGrpCat.{u + 1} g).map q ≫ e).hom.app
      (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down y =
      (integralRegularCoefficient ℓ E X p (g y)).val := by
  exact (field_regular_pullback_coefficient E g q y e hs).trans
    (integral_extended_regular_coefficient ℓ E X p q hq (g y))

universe uc vc ud vd
private noncomputable def normalizedScalarFunctor
    {C : Type uc} [Category.{vc} C] [MonoidalCategory C]
    {D : Type ud} [Category.{vd} D] [MonoidalCategory D]
    (U : C ⥤ D) [U.LaxMonoidal] (R S : C) [MonObj R] [MonObj S]
    (V : Mod C R ⥤ Mod C S) (A : D) [MonObj A]
    (e : U.obj S ⟶ A) [IsMonHom e] [IsIso e] :=
  (V ⋙ U.mapMod S) ⋙ Mod.comap (inv e)

private noncomputable def normalizedRegularIso
    {C : Type uc} [Category.{vc} C] [MonoidalCategory C]
    {D : Type ud} [Category.{vd} D] [MonoidalCategory D]
    (U : C ⥤ D) [U.LaxMonoidal] (R S : C) [MonObj R] [MonObj S]
    (V : Mod C R ⥤ Mod C S) (A : D) [MonObj A]
    (e : U.obj S ⟶ A) [IsMonHom e] [IsIso e]
    (s : V.obj (Mod.regular R) ≅ Mod.regular S) :
    (normalizedScalarFunctor U R S V A e).obj (Mod.regular R) ≅ Mod.regular A :=
  (Mod.comap (inv e)).mapIso
    ((U.mapMod S).mapIso s ≪≫ Mod.isoMk (Iso.refl _) (by simp [Mod.act])) ≪≫
      Mod.regularIsoOfIsIso e

private theorem normalizedRegularIso_conjugate
    {C : Type uc} [Category.{vc} C] [MonoidalCategory C]
    {D : Type ud} [Category.{vd} D] [MonoidalCategory D]
    (U : C ⥤ D) [U.LaxMonoidal] (R S : C) [MonObj R] [MonObj S]
    (V : Mod C R ⥤ Mod C S) (A : D) [MonObj A]
    (e : U.obj S ⟶ A) [IsMonHom e] [IsIso e]
    (s : V.obj (Mod.regular R) ≅ Mod.regular S)
    (p : Mod.regular R ⟶ Mod.regular R) :
    let L := normalizedScalarFunctor U R S V A e
    let r := normalizedRegularIso U R S V A e s
    let qh : S ⟶ S := (s.inv ≫ V.map p ≫ s.hom).hom
    let ah : A ⟶ A := (r.inv ≫ L.map p ≫ r.hom).hom
    ah = inv e ≫ U.map qh ≫ e := by
  dsimp only
  change (inv e ≫ (𝟙 (U.obj S) ≫ U.map s.inv.hom)) ≫ U.map (V.map p).hom ≫
    ((U.map s.hom.hom ≫ 𝟙 (U.obj S)) ≫ e) =
      inv e ≫ U.map (s.inv.hom ≫ (V.map p).hom ≫ s.hom.hom) ≫ e
  erw [Category.id_comp, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]

attribute [irreducible] normalizedScalarFunctor normalizedRegularIso

private theorem generic_coefficient_transport
    {C : Type uc} [Category.{vc} C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C]
    {D : Type ud} [Category.{vd} D] [MonoidalCategory D]
    [Abelian D] [MonoidalPreadditive D]
    (U : C ⥤ D) [U.LaxMonoidal] (R S : C) [MonObj R] [MonObj S]
    (V : Mod C R ⥤ Mod C S) [V.Additive] [PreservesFiniteColimits V]
    [(U.mapMod S).Additive] [PreservesFiniteColimits (U.mapMod S)]
    (A : D) [MonObj A] (e : U.obj S ⟶ A) [IsMonHom e] [IsIso e]
    [(Mod.comap (D := D) (inv e)).Additive] [PreservesFiniteColimits (Mod.comap (D := D) (inv e))]
    [PreservesFiniteColimits (tensorLeft (U.obj S))]
    [PreservesFiniteColimits (tensorLeft A)]
    [HasFiniteBiproducts (Mod D (U.obj S))] [HasFiniteBiproducts (Mod D A)]
    (s : V.obj (Mod.regular R) ≅ Mod.regular S) :
    ∃ L : Mod C R ⥤ Mod D A, L.Additive ∧ PreservesFiniteColimits L ∧
      ∃ r : L.obj (Mod.regular R) ≅ Mod.regular A,
        (∀ p : Mod.regular R ⟶ Mod.regular R,
          (r.inv ≫ L.map p ≫ r.hom).hom =
            inv e ≫ U.map (s.inv ≫ V.map p ≫ s.hom).hom ≫ e) ∧
        (∀ (M : Mod C R) (q : ℕ),
          Nonempty ((U.mapMod S).obj (V.obj M) ≅ Mod.finiteFree (U.obj S) q) →
            Nonempty (L.obj M ≅ Mod.finiteFree A q)) := by
  let L := normalizedScalarFunctor U R S V A e
  have hLa : L.Additive := by unfold L normalizedScalarFunctor; infer_instance
  have hLc : PreservesFiniteColimits L := by
    unfold L normalizedScalarFunctor
    infer_instance
  refine ⟨L, hLa, hLc, normalizedRegularIso U R S V A e s, ?_, ?_⟩
  · exact normalizedRegularIso_conjugate U R S V A e s
  · intro M q ⟨eM⟩
    let Q := Mod.comap (D := D) (inv e)
    let f : Q.obj (Mod.finiteFree (U.obj S) q) ≅ Mod.finiteFree A q :=
      Q.mapBiproduct (fun _ : Fin q ↦ Mod.regular (U.obj S)) ≪≫
        biproduct.mapIso (fun _ ↦ Mod.regularIsoOfIsIso e)
    unfold L normalizedScalarFunctor
    exact ⟨Q.mapIso eM ≪≫ f⟩

private theorem coefficient_of_abstract_transport
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [TotallyDisconnectedSpace E]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
        ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E)))
    (r : L.obj (Mod.regular (condensedRingObj (integralCoeff ℓ E) X)) ≅
      Mod.regular ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E)))
    (e : (ProEtale.upperStar AddCommGrpCat.{u + 1} g).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X) ⟶
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E))
    [IsIso e]
    (hs : ((ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app
        (condensedRingObj (Profinite.continuousMapRingObj E) X)) ≫
      (ProEtale.lowerStar AddCommGrpCat.{u + 1} g).map e =
        chartComparison X E ≫ continuousFunctionPushforward g E)
    (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X))
    (q : condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
      condensedRingObj (Profinite.continuousMapRingObj E) X)
    (hq : p.hom ≫ coefficientMap (integralScalarMap ℓ E) X =
      coefficientMap (integralScalarMap ℓ E) X ≫ q)
    (hr : (r.inv ≫ L.map p ≫ r.hom).hom =
      inv e ≫ (ProEtale.upperStar AddCommGrpCat.{u + 1} g).map q ≫ e) (y : Y) :
    ((((r.inv ≫ L.map p ≫ r.hom).hom).hom.app
      (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down y =
      (integralRegularCoefficient ℓ E X p (g y)).val := by
  rw [hr]
  exact integral_regular_pullback_coefficient_square ℓ E g p q hq e hs y

/-- Coefficient transport for an integral presentation, before geometric evaluation.

Source: Bhatt--Scholze, Section 6.8, continuous coefficient realization and scalar
extension of integral coefficients. The construction is the standard inverse-image
and scalar-extension construction for internal module objects.
(auxiliary; not a blueprint node)

Proof: put R = O_E,X, S = E_X, U = g* and let A be the abelian sheaf underlying
continuous E-valued functions on Y. The canonical comparison e : U(S) → A is an
isomorphism of monoids: E is ultrametric as a normed Q_l-algebra and hence totally
disconnected. Use the functor L = extendScalars(R → S) followed by U.mapMod(S),
then restriction along e inverse. Each factor is additive and preserves finite
colimits. The scalar-extension adjunction identifies the extension of the regular
R-module with the regular S-module: the forward map is adjoint to R → S, and the
inverse is the regular lift of the unit of the adjunction evaluated at 1. The two
inverse laws follow by the regular-module universal property and preservation of 1.
The underlying scalar-extension unit is natural in each regular endomorphism p;
thus its conjugate q satisfies p composed with R → S equals R → S composed with q.
Combine this regular isomorphism with the identity underlying U's regular-module
comparison and the regular-module isomorphism for restriction along e inverse.
This supplies regularIso. To check coefficient, conjugate the preceding square
by the canonical charts, whose naturality in the scalar inclusion identifies the
coefficient of q with the E-valued integral coefficient of p. Scheme naturality
of the charts identifies the coefficient of U(q), conjugated by e, at y with the
coefficient of q at g(y). This is exactly the stated formula after the regular
comparisons cancel. For freeCokernel, apply restriction along e inverse to the
provided free-cokernel isomorphism. Its canonical biproduct comparison and its
regular-module isomorphism identify the result with A^q. These arguments work for
zero ranks and the empty scheme; the coefficient formula only quantifies over
actual points. No rank or geometric-evaluation assertion is used. -/
theorem nonempty_integralMatrixCoefficientTransport (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (g : Y ⟶ X) : Nonempty (IntegralMatrixCoefficientTransport ℓ E g) := by
  classical
  have : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj E) X
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let U := ProEtale.upperStar AddCommGrpCat.{u + 1} g
  let B := U.obj S
  let A := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (continuousMapRingSheaf Y E)
  let e : B ⟶ A :=
    condensedPullbackHom (Profinite.continuousMapRingObj E) g ≫ chartComparison Y E
  have heIso : IsIso e := inferInstance
  have heMon : IsMonHom e := inferInstance
  have heSquare : ((ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app S) ≫
      (ProEtale.lowerStar AddCommGrpCat.{u + 1} g).map e =
        chartComparison X E ≫ continuousFunctionPushforward g E := by
    simpa only [e, S, A, Functor.map_comp, ← Category.assoc,
      ← unitAlgHom_comp_map_condensedPullbackHom, Adjunction.unitAlgHom, condensedRingObj,
      upperStarFromPoint, Functor.comp_obj] using
        continuousChart_scheme_naturality g E
  clear_value e
  let eX := Mod.regularExtensionIso φ
  have heX : ∀ p : Mod.regular R ⟶ Mod.regular R,
      let qh : S ⟶ S := (eX.inv ≫ (Mod.extendScalars φ).map p ≫ eX.hom).hom
      p.hom ≫ φ = φ ≫ qh :=
    extension_regular_square R S φ
  clear_value eX
  obtain ⟨L, hLa, hLc, r, hr, hfree⟩ :=
    generic_coefficient_transport U R S (Mod.extendScalars φ) A e eX
  refine ⟨⟨L, hLa, hLc, r, ?_, ?_⟩⟩
  · intro p x
    exact coefficient_of_abstract_transport ℓ E g L r e heSquare p _ (heX p) (hr p) x
  · intro n t q a eC
    exact Classical.choice (hfree (cokernel a) q ⟨eC⟩)

end AlgebraicGeometry.ProEtale.CondensedRing
