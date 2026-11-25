/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientQuotientLine
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteEncodingUnit
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Quotient.DiagonalQuotientRootEndpoint
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientRestriction

/-! # Finite quotient coefficient models and normalized functor comparisons

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-uniformizer-finite-models).
 -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization

/-- The norm-ball argument of integralModel_residue_discrete in
WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators, specialized to the present
quotient. -/
private theorem finiteModels_residue_discrete (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ) : DiscreteTopology (completedResidue ℓ E π n) := by
  have hp : π ≠ 0 := by
    intro h
    apply PadicAlgCl.maximalIdeal_integers_ne_bot ℓ E.1
    rw [← hπ, h, Ideal.span_singleton_zero]
  let q := π ^ (n + 1)
  have hq : (q.val : E.1) ≠ 0 := by
    exact_mod_cast pow_ne_zero (n + 1) hp
  let I : Ideal (PadicAlgCl.integers ℓ E.1) := (Ideal.span {π}) ^ (n + 1)
  have hopen : IsOpen (I : Set (PadicAlgCl.integers ℓ E.1)) := by
    apply I.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    have ho : IsOpen ((fun x : PadicAlgCl.integers ℓ E.1 ↦ (x : E.1)) ⁻¹'
        Metric.ball 0 ‖(q : E.1)‖) :=
      Metric.isOpen_ball.preimage continuous_subtype_val
    apply Filter.mem_of_superset (ho.mem_nhds (by
      change dist (0 : E.1) 0 < ‖(q : E.1)‖
      simpa only [dist_self] using norm_pos_iff.mpr hq))
    intro x hx
    have hx' : ‖(x : E.1)‖ < ‖(q : E.1)‖ := by
      change dist (x : E.1) 0 < ‖(q : E.1)‖ at hx
      simpa only [dist_zero_right] using hx
    have hdiv : (x : E.1) / q ∈ PadicAlgCl.integers ℓ E.1 := by
      change ‖(x : E.1) / q‖₊ ≤ 1
      rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, norm_div]
      exact (div_le_one (norm_pos_iff.mpr hq)).2 hx'.le
    change x ∈ (Ideal.span {π}) ^ (n + 1)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨⟨(x : E.1) / q, hdiv⟩, ?_⟩
    apply Subtype.ext
    change (x : E.1) = (q : E.1) * ((x : E.1) / q)
    exact (mul_div_cancel₀ _ hq).symm
  exact QuotientAddGroup.discreteTopology hopen

private theorem finiteEncoding_realizations
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    [IsMonHom eR.hom] :
    ∃ e : ∀ X : Scheme.{u}, FiniteRealization
        (Profinite.continuousMapRingObj.{u} B) (ULift.{u + 1} B) X,
      ∀ (X S : Scheme.{u}) (f : X ⟶ S),
        Nonempty (FiniteOrdinaryPushSquare
          (Profinite.continuousMapRingObj.{u} B) (ULift.{u + 1} B) f (e X) (e S)) := by
  let G := CategoryTheory.internalToModule (ULift.{u + 1} B)
  have hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)) := rfl
  have hregular : ∃ j : G.obj (Mod.regular (AddCommGrpCat.of (ULift.{u + 1} B))) ≅
        ModuleCat.of (ULift.{u + 1} B) (ULift.{u + 1} B),
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}).map j.hom =
        (eqToIso hG).hom.app (Mod.regular (AddCommGrpCat.of (ULift.{u + 1} B))) := by
    refine ⟨ModuleCat.isoMk (Iso.refl _) ?_, rfl⟩
    intro a
    ext b
    rfl
  have hu (X : Scheme.{u}) := by
    letI : (Scheme.ProEt.topology X).PreservesSheafification
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) :=
      Sheaf.preservesSheafification_of_adjunction (Scheme.ProEt.topology X)
        (ModuleCat.forget₂CoinduceAdj (ULift.{u + 1} B))
    exact finiteEncoding_unitComparison B eR G hG hregular X
  choose i hi using hu
  let e (X : Scheme.{u}) : FiniteRealization
      (Profinite.continuousMapRingObj.{u} B) (ULift.{u + 1} B) X :=
    { F := finiteEncoding B eR G hG X
      additive := Functor.additive_of_preserves_binary_products _
      underlying := finiteEncodingUnderlying B eR G hG X
      unitIso := i X
      coefficient := by
        let d := (finiteDiscreteSchemeRingIso B X eR).symm
        haveI : IsMonHom d.hom := by
          exact inferInstanceAs (IsMonHom (finiteDiscreteSchemeRingIso B X eR).inv)
        have hd := IsMonHom.of_eq d.hom rfl
          (constantSheafRingMonObj (Scheme.ProEt.topology X) (ULift.{u + 1} B)).symm
          (hf := inferInstance)
        exact Mon.mkIso d hd.one_hom hd.mul_hom
      unit_normalization := by
        dsimp only [finiteConstantAbComparison, finiteConstantAbRing, sfbConstantRing,
          Mon.mkIso, Mon.mkIso', Iso.symm_hom]
        exact hi X }
  refine ⟨e, fun X S f ↦ ⟨⟨?_, ?_⟩⟩⟩
  · exact CondensedRing.encodingPushforwardNatIso B eR G hG S X f
  · intro M
    exact heq_of_eq (CondensedRing.encodingPushforward_underlying B eR G hG S X f M)

private theorem finiteDiscrete_realizations
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Finite B] [DiscreteTopology B] :
    ∃ e : ∀ X : Scheme.{u}, FiniteRealization
        (Profinite.continuousMapRingObj.{u} B) (ULift.{u + 1} B) X,
      ∀ (X S : Scheme.{u}) (f : X ⟶ S),
        Nonempty (FiniteOrdinaryPushSquare
          (Profinite.continuousMapRingObj.{u} B) (ULift.{u + 1} B) f (e X) (e S)) := by
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  exact @finiteEncoding_realizations.{u} B inferInstance inferInstance inferInstance eR heR

private theorem inverse_square {C : Type*} [Category C] {X Y Z : C}
    (a : X ≅ Y) (b : Z ≅ Y) (t : X ⟶ Z) (h : t ≫ b.hom = a.hom) :
    a.inv ≫ t = b.inv := by
  apply (cancel_mono b.hom).mp
  simp only [Category.assoc, h, Iso.inv_hom_id]

private theorem uniformizer_realizations
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    [Finite (ULift.{u + 1} (completedResidue l E π n))] :
    ∃ e : ∀ X : Scheme.{u}, FiniteRealization
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
        (ULift.{u + 1} (completedResidue l E π n)) X,
      ∀ (X S : Scheme.{u}) (f : X ⟶ S),
        Nonempty (FiniteOrdinaryPushSquare
          (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
          (ULift.{u + 1} (completedResidue l E π n)) f (e X) (e S)) := by
  have : Finite (completedResidue l E π n) :=
    Finite.of_injective (fun b ↦ (ULift.up b : ULift.{u + 1} (completedResidue l E π n)))
      ULift.up_injective
  let : DiscreteTopology (completedResidue l E π n) :=
    finiteModels_residue_discrete l E π hπ n
  exact finiteDiscrete_realizations.{u} (completedResidue l E π n)

private theorem finiteSource_of_pushSquare
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (eP : FiniteRealization R A (ProjectiveLine Y))
    (eW : FiniteRealization R A (diagonalSurface Y))
    (s : FiniteOrdinaryPushSquare R A (diagonalImmersion Y) eP eW) :
    Nonempty (FiniteSourceComparison R A Y eP eW) := by
  refine ⟨⟨s.ordinary.app _ ≪≫
    (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).mapIso eP.unitIso, ?_⟩⟩
  have h := eq_of_heq (s.normalization
    (Mod.regular (condensedRingObj R (ProjectiveLine Y))))
  apply heq_of_eq
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [Functor.map_comp, ← Category.assoc]
  have h' : eW.underlying.inv.app (source R Y) ≫
      (sheafCompose (Scheme.ProEt.topology (diagonalSurface Y))
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map
          (s.ordinary.hom.app (Mod.regular (condensedRingObj R (ProjectiveLine Y)))) =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (Mod.regular (condensedRingObj R (ProjectiveLine Y)))) := by
    exact inverse_square (eW.underlying.app (source R Y))
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).mapIso
        (eP.underlying.app (Mod.regular (condensedRingObj R (ProjectiveLine Y))))) _ h
  erw [h']
  exact ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map_comp
    (eP.underlying.inv.app (Mod.regular (condensedRingObj R (ProjectiveLine Y))))
    ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map eP.unitIso.hom)).symm

set_option linter.unusedVariables false in
/-- Finite coefficient models, endpoints and direct-image squares, without any
assertion about a cycle class or a trace arrow.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), expected finite reductions.
(blueprint: lem-diagonal-uniformizer-finite-models).

Proof: The quotient is a finite discrete ring. Identify its condensed ring with
its sheafified constant ring using the unital constant-function map, and pull
this comparison to each scheme. Transport internal modules across that ring
isomorphism, then use the equivalence with sheaves of modules over the ordinary
quotient ring. Retain the underlying-sheaf comparison and the regular-module
unit; unitality gives its normalization. The integral twist is the inverse
limit of its coefficient/root tensor systems. Since l is invertible, the root
tower is a locally free rank-one Tate module. Extension to the quotient killed
by l^(n+1) is its n-th finite root line tensored with the quotient. The integral
root projections and the kernel inclusions in the supplied FiniteRoots fix the
line endpoints, including the sign. Use the ordinary direct-image comparison
on underlying sheaves to identify the supported coefficient source. Its unit
component gives exactly the displayed source normalization. For q, the same
sectionwise realization commutes with ordinary direct image, with the displayed
underlying-sheaf normalization. No right derivation is part of this statement.
This constructs only coefficient and ordinary-functor comparisons,
independently of all completed classes, scalar-compatible diagrams and traces.
The exponent is n+1 throughout, also for n=0; no unramifiedness is assumed. -/
theorem diagonalUniformizer_finiteModels
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    [hfinite : Finite (ULift.{u + 1} (completedResidue l E π n))]
    (hA : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (hYpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤)))
    (hWpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(diagonalSurface Y, ⊤)))
    (rootsP : FiniteRoots (ProjectiveLine Y) (l ^ (n + 1)))
    (rootsW : FiniteRoots (diagonalSurface Y) (l ^ (n + 1))) :
    ∃ (eY : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) Y)
    (eP : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (ProjectiveLine Y))
    (eW : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (diagonalSurface Y))
      (lineP : QuotientLineRealization l E π n n hA (ProjectiveLine Y) eP)
      (lineW : QuotientLineRealization l E π n n hA (diagonalSurface Y) eW),
    Nonempty (FiniteSourceComparison
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) Y eP eW) ∧
    Nonempty (FiniteOrdinaryPushSquare
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (ProjectiveLine Y ↘ Y) eP eY) := by
  obtain ⟨e, push⟩ := uniformizer_realizations.{u} l E π hπ n
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hW : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [map_natCast] using
      hP.map (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)).appTop.hom
  have lines (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (l : Γ(X, ⊤)))
      (roots : FiniteRoots X (l ^ (n + 1))) :
      Nonempty (QuotientLineRealization l E π n n hA X (e X)) := by
    exact diagonalQuotientRootEndpoint l X hX E π hπ n hA (e X) roots
  let lineP := Classical.choice (lines (ProjectiveLine Y) hP rootsP)
  let lineW := Classical.choice (lines (diagonalSurface Y) hW rootsW)
  refine ⟨e Y, e (ProjectiveLine Y), e (diagonalSurface Y), lineP, lineW, ?_, push _ _ _⟩
  obtain ⟨s⟩ := push _ _ (diagonalImmersion Y)
  exact finiteSource_of_pushSquare _ _ Y _ _ s

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
