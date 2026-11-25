/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.RamificationInertia.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
public import WeilConjectures.AlgebraicGeometry.Curve.FiniteMapToLine
public import WeilConjectures.AlgebraicGeometry.Curve.FiniteDuality
public import WeilConjectures.AlgebraicGeometry.Curve.SeparatingFunction
public import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
public import WeilConjectures.AlgebraicGeometry.Modules.PushforwardHom
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Duality
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Birational.RationalMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.OrderOfVanishing
public import WeilConjectures.Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Order.CompletePartialOrder

/-!
# Local theory of smooth curves and finite morphisms to the projective line

Let `X` be a smooth curve over a field `k`, i.e. `X ⟶ Spec k` is smooth of relative dimension
one. This file collects the inputs of the proof of Serre duality on `X`
(`AlgebraicGeometry.Scheme.serreDuality`): the local rings of `X` at closed points are discrete
valuation rings and closed points are effective Cartier divisors; a rational function `t` on a
proper `X`, transcendental over `k`, defines a finite flat morphism `X ⟶ ℙ¹_k`; along a finite
flat morphism `f : X ⟶ ℙ¹_k` one has the duality `Hom(f_* ℳ, ω_{ℙ¹}) ≅ H⁰(X, ℳᵛ ⊗ ω_X)`; and the
degree of a principal divisor is zero.

## Main statements

- `AlgebraicGeometry.Scheme.isDiscreteValuationRing_stalk_of_isClosed`: the local rings at closed
  points are discrete valuation rings.
- `AlgebraicGeometry.Scheme.isInvertible_vanishingIdeal_of_isClosed`: closed points are effective
  Cartier divisors.
- `AlgebraicGeometry.Scheme.exists_hom_projectiveLine_of_functionField` and
  `AlgebraicGeometry.Scheme.isFinite_flat_of_hom_projectiveLine_of_functionField`: a rational
  function transcendental over `k` is a finite flat morphism to `ℙ¹_k`.
- `AlgebraicGeometry.Scheme.exists_isFinite_flat_hom_projectiveLine`: every smooth proper curve
  has a finite flat morphism to `ℙ¹_k`.
- `AlgebraicGeometry.Scheme.nonempty_homObj_pushforward_iso`: duality along a finite flat
  morphism to `ℙ¹_k`.
- `AlgebraicGeometry.Scheme.nonempty_dual_H_one_iso` and
  `AlgebraicGeometry.Scheme.nonempty_dual_H_zero_iso`: Serre duality on a smooth proper curve in
  degrees `1` and `0`, assembled from the above; they make up
  `AlgebraicGeometry.Scheme.serreDuality`.
- `AlgebraicGeometry.Scheme.finsum_ord_eq_finrank` and
  `AlgebraicGeometry.Scheme.finsum_ord_eq_zero`: degrees of pulled back points and of principal
  divisors.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite IsLocalRing

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

section Local

variable (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f]

include f

/-- The local ring of a smooth curve at a closed point has dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_isClosed {x : X} (hx : IsClosed {x}) :
    ringKrullDim (X.presheaf.stalk x) = 1 :=
  ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one f hx

/-- The local ring of a smooth curve at a closed point is a discrete valuation ring: it is a
regular local ring (`AlgebraicGeometry.IsRegular.of_smooth`), in particular a domain, of
dimension one. -/
theorem isDiscreteValuationRing_stalk_of_isClosed {x : X} (hx : IsClosed {x}) :
    ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
  have := SmoothOfRelativeDimension.smooth 1 f
  have := IsRegular.of_smooth f
  ⟨inferInstance, IsRegularLocalRing.isDiscreteValuationRing _
    (ringKrullDim_stalk_eq_one_of_isClosed f hx)⟩

/-- **Local regularity of smooth curves.** The local rings of a smooth curve over a field are
regular local rings, hence domains, and at closed points they are discrete valuation rings.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem isRegularLocalRing_stalk_and_isDiscreteValuationRing (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) ∧ ∃ _ : IsDomain (X.presheaf.stalk x),
      IsClosed {x} → IsDiscreteValuationRing (X.presheaf.stalk x) :=
  have := SmoothOfRelativeDimension.smooth 1 f
  have := IsRegular.of_smooth f
  ⟨inferInstance, inferInstance, fun hx ↦ by
    obtain ⟨_, h⟩ := isDiscreteValuationRing_stalk_of_isClosed f hx
    exact h⟩

/-- **Closed points are Cartier divisors on smooth curves.** A closed point `x` of a smooth
curve, with its reduced structure, is an effective Cartier divisor: its ideal sheaf is locally
generated by one non-zerodivisor, a uniformizer of the discrete valuation ring `𝒪_{X,x}`.
Consequently every effective divisor, a finite sum of closed points, is an effective Cartier
divisor.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem isInvertible_vanishingIdeal_of_isClosed {x : X} (hx : IsClosed {x}) :
    (IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).IsInvertible :=
  isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one f hx

/-- **Closed points of curves are Cartier divisors.** A closed point `x` of a smooth curve has
invertible ideal sheaf, and `𝒪_{X,x}` is a discrete valuation ring.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem isInvertible_vanishingIdeal_and_isDiscreteValuationRing {x : X} (hx : IsClosed {x}) :
    (IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).IsInvertible ∧
      ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
  ⟨isInvertible_vanishingIdeal_of_isClosed f hx, isDiscreteValuationRing_stalk_of_isClosed f hx⟩

/-- The local rings of a smooth curve over a field are valuation rings: discrete valuation rings
at closed points and fields at generic points. -/
theorem valuationRing_stalk [IsIntegral X] (x : X) : ValuationRing (X.presheaf.stalk x) := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := IsRegular.of_smooth f
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
    (ringKrullDim_stalk_le_topologicalKrullDim x).trans
      (by exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension f 1)
  by_cases h1 : ringKrullDim (X.presheaf.stalk x) = 1
  · have := IsRegularLocalRing.isDiscreteValuationRing _ h1
    infer_instance
  · have h0 : ringKrullDim (X.presheaf.stalk x) ≤ 0 := by
      generalize ringKrullDim (X.presheaf.stalk x) = d at *
      induction d using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe n =>
        induction n using ENat.recTopCoe with
        | top => exact absurd hle (by decide)
        | coe m =>
          have : m ≤ 1 := by exact_mod_cast hle
          have : m ≠ 1 := fun h ↦ h1 (by rw [h]; rfl)
          have : m = 0 := by omega
          subst this; rfl
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := ⟨by exact_mod_cast h0⟩
    let := (Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk x)).toField
    infer_instance

end Local

/-- The ring map `k →+* k(X)` of an integral `k`-scheme `X`. -/
noncomputable abbrev functionFieldRingHom (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsIntegral X] : k →+* X.functionField :=
  (X.germToFunctionField ⊤ (h := ⟨⟨genericPoint X, trivial⟩⟩)).hom.comp
    (globalSectionsRingHom k (X := X))

/-- An integral scheme over a field `k` with a point whose local ring is not a field has a
rational function transcendental over `k`. -/
theorem exists_transcendental_functionField [X.Over (Spec (.of k))] [IsIntegral X] (x : X)
    (hx : ringKrullDim (X.presheaf.stalk x) ≠ 0) :
    ∃ t : X.functionField, letI := (functionFieldRingHom k X).toAlgebra; Transcendental k t := by
  let := (functionFieldRingHom k X).toAlgebra
  let : Algebra k (X.presheaf.stalk x) :=
    ((X.presheaf.germ ⊤ x trivial).hom.comp (globalSectionsRingHom k (X := X))).toAlgebra
  by_contra! h
  have : Algebra.IsAlgebraic k X.functionField := ⟨fun t ↦ not_not.mp (h t)⟩
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
    IsFractionRing.injective _ _
  have : Algebra.IsAlgebraic k (X.presheaf.stalk x) :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq (RingHom.id k)
      (algebraMap (X.presheaf.stalk x) X.functionField) Function.surjective_id hinj (by
        ext a
        simp only [RingHom.algebraMap_toAlgebra, functionFieldRingHom, RingHom.coe_comp,
          RingHom.coe_coe, RingHom.coe_id, Function.comp_apply, id_eq]
        rw [← CommRingCat.comp_apply]
        erw [TopCat.Presheaf.germ_stalkSpecializes])
  have hfield : IsField (X.presheaf.stalk x) :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap k _).injective).mp (Field.toIsField k)
  exact hx (ringKrullDim_eq_zero_of_isField hfield)

/-- In an irreducible scheme of dimension at most one, a point which is not closed is the
generic point. -/
theorem eq_genericPoint_of_not_isClosed {Z : Scheme.{u}} [IrreducibleSpace Z]
    (h : topologicalKrullDim Z ≤ 1) {z : Z} (hz : ¬ IsClosed {z}) : z = genericPoint Z := by
  have : closure {z} = (Set.univ : Set Z) := by
    by_contra hne
    exact hz (IsOpen.isClosed_singleton_of_mem_compl h isClosed_closure.isOpen_compl
      (Set.nonempty_compl.mpr hne) fun hmem ↦ hmem (subset_closure rfl))
  exact (show IsGenericPoint z ⊤ from this).eq (genericPoint_spec Z)

/-- The stalk maps of an integral scheme along specializations are injective. -/
theorem injective_stalkSpecializes {Z : Scheme.{u}} [IsIntegral Z] {a b : Z} (h : a ⤳ b) :
    Function.Injective (Z.presheaf.stalkSpecializes h) := by
  have hinj := IsFractionRing.injective (Z.presheaf.stalk b) Z.functionField
  have e := TopCat.Presheaf.stalkSpecializes_comp Z.presheaf
    ((genericPoint_spec Z).specializes trivial) h
  refine fun u v huv ↦ hinj ?_
  change Z.presheaf.stalkSpecializes _ u = Z.presheaf.stalkSpecializes _ v
  rw [← e, CommRingCat.comp_apply, CommRingCat.comp_apply, huv]

section ProjectiveLine

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

/-- The homogeneous coordinates `[1 : t]` of a rational function `t`, as global sections of
`Spec k(X)`: the `k(X)`-point of `ℙ¹` with affine coordinate `t`. -/
noncomputable abbrev functionFieldCoordinates [IsIntegral X] (t : X.functionField) :
    ULift.{u} (Fin 2) → Γ(Spec X.functionField, ⊤) :=
  fun i ↦ (Scheme.ΓSpecIso X.functionField).inv (![1, t] i.down)

set_option linter.unusedSectionVars false in
/-- **Rational functions define morphisms to `ℙ¹`.** Let `X` be a proper smooth integral curve
over `k` and `t ∈ k(X)` transcendental over `k`. Then there is a morphism `π_t : X ⟶ ℙ¹_k` over
`k` with `π_t^* (x₁ / x₀) = t`: at the generic point it is the point `[1 : t]` of `ℙ¹(k(X))`.
The local rings of `X` are discrete valuation rings or fields (`valuationRing_stalk`), so by the
valuative criterion for the proper `ℙ¹_k` this point extends over every point of `X`
(`exists_hom_of_valuationRing_stalk`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem exists_hom_projectiveLine_of_functionField [IsIntegral X] (t : X.functionField)
    (_ht : letI := (functionFieldRingHom k X).toAlgebra; Transcendental k t) :
    ∃ π : X ⟶ ProjectiveLine (Spec (.of k)), π.IsOver (Spec (.of k)) ∧
      ∀ hs, X.fromSpecFunctionField ≫ π = ProjectiveSpace.homOfSections
        (X.fromSpecFunctionField ≫ X ↘ Spec (.of k)) (functionFieldCoordinates t) hs := by
  have hs : Ideal.span (Set.range (functionFieldCoordinates (X := X) t)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨0⟩, rfl⟩) (by simp)
  have : (ProjectiveLine (Spec (.of k))).IsSeparated :=
    ⟨by rw [← terminal.comp_from (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))]
        infer_instance⟩
  obtain ⟨π, hπ, h⟩ := exists_hom_of_valuationRing_stalk (S := Spec (.of k))
    (valuationRing_stalk (X ↘ Spec (.of k)))
    (ProjectiveSpace.homOfSections (X.fromSpecFunctionField ≫ X ↘ Spec (.of k))
      (functionFieldCoordinates t) hs) (ProjectiveSpace.homOfSections_over _ _ _)
  exact ⟨π, hπ, fun _ ↦ h⟩

/-- **Rational functions define finite morphisms to `ℙ¹`.** Let `X` be a proper smooth integral
curve over `k`, `t ∈ k(X)` transcendental over `k`, and `π_t : X ⟶ ℙ¹_k` the morphism of
`exists_hom_projectiveLine_of_functionField`. Then `π_t` is finite, surjective and flat, of
degree `[k(X) : k(t)]`. It is surjective since its image is closed and not a point; its fibres
are finite, so it is finite; and `π_* 𝒪_X` is torsion free on the smooth curve `ℙ¹_k`, hence
locally free, so `π_t` is flat.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem isFinite_flat_of_hom_projectiveLine_of_functionField [IsIntegral X]
    (t : X.functionField) (ht : letI := (functionFieldRingHom k X).toAlgebra; Transcendental k t)
    (π : X ⟶ ProjectiveLine (Spec (.of k))) [π.IsOver (Spec (.of k))]
    (hπ : ∀ hs, X.fromSpecFunctionField ≫ π = ProjectiveSpace.homOfSections
      (X.fromSpecFunctionField ≫ X ↘ Spec (.of k)) (functionFieldCoordinates t) hs) :
    IsFinite π ∧ Surjective π ∧ Flat π ∧
      ∀ y, π.finrank y = Module.finrank
        (Subfield.closure (Set.range (functionFieldRingHom k X) ∪ {t})) X.functionField := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let P := ProjectiveLine (Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  have hdimX : topologicalKrullDim X ≤ 1 := by
    exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) 1
  have hdimP : topologicalKrullDim P ≤ 1 := topologicalKrullDim_projectiveLine_le_one k
  have hover : π ≫ P ↘ Spec (.of k) = X ↘ Spec (.of k) :=
    HomIsOver.comp_over (f := π) (S := Spec (.of k))
  have : IsProper π := by
    have : IsProper (π ≫ P ↘ Spec (.of k)) := by rw [hover]; infer_instance
    exact IsProper.of_comp π (P ↘ Spec (.of k))
  -- `π` maps the generic point of `X` to the generic point of `ℙ¹`.
  have hg₀ : X.fromSpecFunctionField ≫ X ↘ Spec (.of k) =
      Spec.map (CommRingCat.ofHom (functionFieldRingHom k X)) := by
    refine ext_of_isAffine ?_
    rw [← cancel_epi (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
    ext a
    simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, functionFieldRingHom,
      globalSectionsRingHom]
    rfl
  have hs : Ideal.span (Set.range (functionFieldCoordinates (X := X) t)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨0⟩, rfl⟩) (by simp)
  have hpt : ProjectiveSpace.homOfSections (Spec.map (CommRingCat.ofHom (functionFieldRingHom k X)))
      (fun i : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of X.functionField)).inv (![1, t] i.down)) hs
      (IsLocalRing.closedPoint X.functionField) = π (genericPoint X) := by
    have e := hπ hs
    rw [hg₀] at e
    refine (congrArg (fun f ↦ f (IsLocalRing.closedPoint X.functionField)) e).symm.trans ?_
    exact congrArg π Scheme.fromSpecStalk_closedPoint
  have hηc : ¬ IsClosed {π (genericPoint X)} := by
    rw [← hpt]
    exact ProjectiveLine.not_isClosed_homOfSections (functionFieldRingHom k X) t ht hs _
  have hηP : π (genericPoint X) = genericPoint P := eq_genericPoint_of_not_isClosed hdimP hηc
  -- the points of `X` and `ℙ¹` are closed or generic
  have hptX (x : X) (hx : ¬ IsClosed {x}) : x = genericPoint X :=
    eq_genericPoint_of_not_isClosed hdimX hx
  have hptP (y : P) (hy : ¬ IsClosed {y}) : y = genericPoint P :=
    eq_genericPoint_of_not_isClosed hdimP hy
  have hPgen : ¬ IsClosed ({genericPoint P} : Set P) := hηP ▸ hηc
  have hsurj : Surjective π := by
    refine ⟨fun y ↦ ?_⟩
    have hclosed : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have : closure {genericPoint P} ⊆ Set.range π :=
      closure_minimal (by rintro _ rfl; exact ⟨_, hηP⟩) hclosed
    rw [show closure ({genericPoint P} : Set P) = Set.univ from genericPoint_spec P] at this
    exact this trivial
  have hfib (y : P) : (π ⁻¹' {y}).Finite := by
    by_cases hy : IsClosed ({y} : Set P)
    · have hc : IsClosed (π ⁻¹' {y}) := hy.preimage π.continuous
      have hη : genericPoint X ∉ π ⁻¹' {y} := by
        intro h
        rw [Set.mem_preimage, Set.mem_singleton_iff, hηP] at h
        exact hPgen (h ▸ hy)
      have := IsOpen.finite_compl_of_topologicalKrullDim_le_one hdimX hc.isOpen_compl
        ⟨_, hη⟩
      simpa using this
    · refine (Set.finite_singleton (genericPoint X)).subset fun x hx ↦ ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      refine hptX x fun hxc ↦ hy ?_
      rw [← hx, ← Set.image_singleton]
      exact π.isClosedMap _ hxc
  have : LocallyQuasiFinite π := (locallyQuasiFinite_iff_finite_preimage_singleton).mpr hfib
  have hfin : IsFinite π := IsFinite.of_isProper_of_locallyQuasiFinite π
  have hflat : Flat π := by
    refine Flat.of_stalkMap π fun x ↦ ?_
    have hval := valuationRing_stalk (P ↘ Spec (.of k)) (π x)
    have hinj : Function.Injective (π.stalkMap x) := by
      have h₁ := Scheme.Hom.stalkSpecializes_stalkMap π (genericPoint X) x
        ((genericPoint_spec X).specializes (Set.mem_univ x))
      have hF : IsField (P.presheaf.stalk (π (genericPoint X))) :=
        hηP ▸ Field.toIsField P.functionField
      have h₂ : Function.Injective (P.presheaf.stalkSpecializes
          (π.base.hom.map_specializes ((genericPoint_spec X).specializes (Set.mem_univ x))) ≫
            π.stalkMap (genericPoint X)) := by
        let := hF.toField
        exact (RingHom.injective (π.stalkMap (genericPoint X)).hom).comp
          (injective_stalkSpecializes _)
      rw [h₁] at h₂
      exact fun a b hab ↦ h₂ (by rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hab])
    algebraize [(π.stalkMap x).hom]
    change Module.Flat (P.presheaf.stalk (π x)) (X.presheaf.stalk x)
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    refine eq_bot_iff.mpr fun m ⟨⟨r, hr⟩, hrm⟩ ↦ ?_
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have : algebraMap (P.presheaf.stalk (π x)) (X.presheaf.stalk x) r ≠ 0 := by
      exact fun h ↦ hr0 (hinj (h.trans (π.stalkMap x).hom.map_zero.symm))
    rw [Submonoid.smul_def, Algebra.smul_def] at hrm
    exact (mul_eq_zero.mp hrm).resolve_left this
  refine ⟨hfin, hsurj, hflat, fun y ↦ ?_⟩
  have : IsLocallyNoetherian P :=
    LocallyOfFiniteType.isLocallyNoetherian (P ↘ Spec (.of k))
  have : LocallyOfFinitePresentation π :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  -- the rank is constant, so it is the rank at `π η`
  rw [π.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace y (π (genericPoint X))]
  -- the rank at `π η` is the degree of the residue field extension `κ(η) / κ(π η)`
  have hrank : π.finrank (π (genericPoint X)) =
      letI := (π.residueFieldMap (genericPoint X)).hom.toAlgebra
      Module.finrank (P.residueField (π (genericPoint X)))
        (X.residueField (genericPoint X)) := by
    have h₁ := (Scheme.Hom.finrank_pullback_snd π (P.fromSpecResidueField (π (genericPoint X)))
      (IsLocalRing.closedPoint _)).trans (congrArg π.finrank (P.fromSpecResidueField_apply _ _))
    rw [← h₁]
    change (π.fiberToSpecResidueField _).finrank _ = _
    rw [← Scheme.Hom.finrank_comp_left_of_isIso (π.asFiberHom (genericPoint X))]
    have h₂ : π.asFiberHom (genericPoint X) ≫ π.fiberToSpecResidueField (π (genericPoint X)) =
        Spec.map (π.residueFieldMap (genericPoint X)) := by simp
    have hfin' : IsFinite (Spec.map (π.residueFieldMap (genericPoint X))) := by
      rw [← h₂]; infer_instance
    rw [h₂]
    let := (π.residueFieldMap (genericPoint X)).hom.toAlgebra
    have : Module.Finite (P.residueField (π (genericPoint X)))
        (X.residueField (genericPoint X)) := (IsFinite.SpecMap_iff _).mp hfin'
    rw [show π.residueFieldMap (genericPoint X) = CommRingCat.ofHom (algebraMap
      (P.residueField (π (genericPoint X))) (X.residueField (genericPoint X))) from rfl,
      Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [hrank]
  -- the image of `κ(π η)` in `κ(η) = k(X)` is `k(t)`
  let g := X.fromSpecFunctionField
  have key : ∀ x : X, x = g (IsLocalRing.closedPoint X.functionField) →
      (letI := (π.residueFieldMap x).hom.toAlgebra
      Module.finrank (P.residueField (π x)) (X.residueField x)) =
        Module.finrank (Subfield.closure (Set.range (functionFieldRingHom k X) ∪ {t}))
          X.functionField := by
    rintro x rfl
    let a := π.residueFieldMap (g (IsLocalRing.closedPoint X.functionField))
    let b := Scheme.descResidueField (K := X.functionField) (Scheme.stalkClosedPointTo g)
    have hc := Scheme.descResidueField_stalkClosedPointTo_comp π g
    have hrange : (a ≫ b).hom.fieldRange =
        Subfield.closure (Set.range (functionFieldRingHom k X) ∪ {t}) := by
      erw [← hc]
      have e := hπ hs
      rw [hg₀] at e
      have key' : ∀ h : Spec X.functionField ⟶ P, h = ProjectiveSpace.homOfSections
          (Spec.map (CommRingCat.ofHom (functionFieldRingHom k X)))
          (fun i : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of X.functionField)).inv
            (![1, t] i.down)) hs →
          (Scheme.descResidueField (Scheme.stalkClosedPointTo h)).hom.fieldRange =
            Subfield.closure (Set.range (functionFieldRingHom k X) ∪ {t}) := by
        rintro h rfl
        exact ProjectiveLine.fieldRange_descResidueField_homOfSections _ t hs
      exact key' _ e
    have hb : Function.Bijective b := by
      refine ⟨b.hom.injective, ?_⟩
      have hres : X.residue _ ≫ b = Scheme.stalkClosedPointTo g :=
        Scheme.residue_descResidueField _
      rw [Scheme.stalkClosedPointTo_fromSpecStalk] at hres
      have : Function.Surjective (X.residue _ ≫ b) := by
        rw [hres]
        exact (ConcreteCategory.bijective_of_isIso _).2
      intro y
      obtain ⟨z, hz⟩ := this y
      exact ⟨X.residue _ z, by rw [← CommRingCat.comp_apply]; exact hz⟩
    let := a.hom.toAlgebra
    refine Algebra.finrank_eq_of_equiv_equiv
      (((a ≫ b).hom.rangeRestrictFieldEquiv).trans (RingEquiv.subfieldCongr hrange))
      (RingEquiv.ofBijective b.hom hb) ?_
    ext z
    rfl
  exact key _ Scheme.fromSpecStalk_closedPoint.symm

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- The rational function `t` lies in the image of the stalk map of `π_t` at the generic point
of `X`: it is the pullback of the affine coordinate `x₁ / x₀` of `ℙ¹_k`. -/
theorem mem_range_stalkMap_genericPoint_of_functionField [IsIntegral X] (t : X.functionField)
    (π : X ⟶ ProjectiveLine (Spec (.of k)))
    (hπ : ∀ hs, X.fromSpecFunctionField ≫ π = ProjectiveSpace.homOfSections
      (X.fromSpecFunctionField ≫ X ↘ Spec (.of k)) (functionFieldCoordinates t) hs) :
    t ∈ Set.range (π.stalkMap (genericPoint X)) := by
  have hg₀ : X.fromSpecFunctionField ≫ X ↘ Spec (.of k) =
      Spec.map (CommRingCat.ofHom (functionFieldRingHom k X)) := by
    refine ext_of_isAffine ?_
    rw [← cancel_epi (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
    ext a
    simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, functionFieldRingHom,
      globalSectionsRingHom]
    rfl
  have hs : Ideal.span (Set.range (functionFieldCoordinates (X := X) t)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨0⟩, rfl⟩) (by simp)
  let g := X.fromSpecFunctionField
  have hrange : (Scheme.descResidueField (Scheme.stalkClosedPointTo (g ≫ π))).hom.fieldRange =
      Subfield.closure (Set.range (functionFieldRingHom k X) ∪ {t}) := by
    have e := hπ hs
    rw [hg₀] at e
    have key' : ∀ h : Spec X.functionField ⟶ ProjectiveLine (Spec (.of k)),
        h = ProjectiveSpace.homOfSections
          (Spec.map (CommRingCat.ofHom (functionFieldRingHom k X)))
          (fun i : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of X.functionField)).inv
            (![1, t] i.down)) hs →
          (Scheme.descResidueField (Scheme.stalkClosedPointTo h)).hom.fieldRange =
            Subfield.closure (Set.range (functionFieldRingHom k X) ∪ {t}) := by
      rintro h rfl
      exact ProjectiveLine.fieldRange_descResidueField_homOfSections _ t hs
    exact key' _ e
  have htmem : t ∈ (Scheme.descResidueField (Scheme.stalkClosedPointTo (g ≫ π))).hom.fieldRange :=
    hrange ▸ Subfield.subset_closure (Or.inr rfl)
  obtain ⟨r, hr⟩ := RingHom.mem_fieldRange.mp htmem
  obtain ⟨s, rfl⟩ := (ProjectiveLine (Spec (.of k))).residue_surjective _ r
  rw [← CommRingCat.comp_apply, Scheme.residue_descResidueField, Scheme.stalkClosedPointTo_comp,
    CommRingCat.comp_apply, Scheme.stalkClosedPointTo_fromSpecStalk] at hr
  have key (x : X) (h : x = genericPoint X)
      (s : (ProjectiveLine (Spec (.of k))).presheaf.stalk (π x))
      (hi : Inseparable x (genericPoint X)) :
      (X.presheaf.stalkCongr hi).hom (π.stalkMap x s) ∈
        Set.range (π.stalkMap (genericPoint X)) := by
    subst h
    exact ⟨s, by simp⟩
  exact hr ▸ key _ Scheme.fromSpecStalk_closedPoint s _

omit [IsProper (X ↘ Spec (.of k))] in
/-- **Separating functions give generically unramified morphisms.** Let `X` be a proper smooth
integral curve over `k`, `t ∈ k(X)` with `dt ≠ 0` in `Ω[k(X)⁄k]`, and `π_t : X ⟶ ℙ¹_k` the
morphism with `π_t^* (x₁ / x₀) = t`. Then the stalk map of `π_t` at the generic point, the field
extension `k(t) ⊆ k(X)`, is formally unramified: `Ω[k(X)⁄k]` is spanned by `dt`
(`finrank_kaehlerDifferential_functionField`), and `t` comes from `k(t)`. -/
theorem formallyUnramified_stalkMap_genericPoint_of_functionField [IsIntegral X]
    (t : X.functionField)
    (ht : letI := ((X ↘ Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
      KaehlerDifferential.D Γ(Spec (.of k), ⊤) X.functionField t ≠ 0)
    (π : X ⟶ ProjectiveLine (Spec (.of k))) [π.IsOver (Spec (.of k))]
    (hπ : ∀ hs, X.fromSpecFunctionField ≫ π = ProjectiveSpace.homOfSections
      (X.fromSpecFunctionField ≫ X ↘ Spec (.of k)) (functionFieldCoordinates t) hs) :
    (π.stalkMap (genericPoint X)).hom.FormallyUnramified := by
  let P := ProjectiveLine (Spec (.of k))
  let := ((X ↘ Spec (.of k)).appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  let := ((P ↘ Spec (.of k)).appTop ≫
    P.presheaf.germ ⊤ (π (genericPoint X)) trivial).hom.toAlgebra
  let := (π.stalkMap (genericPoint X)).hom.toAlgebra
  have : IsScalarTower Γ(Spec (.of k), ⊤) (P.presheaf.stalk (π (genericPoint X)))
      X.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((X ↘ Spec (.of k)).appTop ≫ X.presheaf.germ ⊤ _ trivial).hom =
      (((P ↘ Spec (.of k)).appTop ≫ P.presheaf.germ ⊤ _ trivial) ≫ π.stalkMap _).hom
    congr 1
    rw [Category.assoc, Scheme.Hom.germ_stalkMap, ← Category.assoc]
    rw [← HomIsOver.comp_over (f := π) (S := Spec (.of k))]
    rfl
  exact Algebra.FormallyUnramified.of_finrank_kaehlerDifferential_eq_one
    (finrank_kaehlerDifferential_functionField (X ↘ Spec (.of k)) 1 (.refl _) rfl) ht
    (mem_range_stalkMap_genericPoint_of_functionField t π hπ)

/-- **Finite flat morphisms to the projective line.** Every smooth proper curve `X` over `k` has
a finite flat morphism `X ⟶ ℙ¹_k` over `k`, unramified at the generic points of `X`. Each
connected component of `X` is integral (`AlgebraicGeometry.IsRegular.irreducibleSpace`) of
dimension one, so its function field has a transcendental element `t` with `dt ≠ 0`
(`exists_transcendental_and_D_ne_zero`), and `π_t` is finite flat
(`isFinite_flat_of_hom_projectiveLine_of_functionField`) and generically unramified
(`formallyUnramified_stalkMap_genericPoint_of_functionField`); there are finitely many
components, and the morphisms on the components glue. -/
theorem exists_isFinite_flat_hom_projectiveLine :
    ∃ f : X ⟶ ProjectiveLine (Spec (.of k)), f.IsOver (Spec (.of k)) ∧ IsFinite f ∧ Flat f ∧
      LocallyOfFinitePresentation f ∧
        ∀ x : X, IsField (X.presheaf.stalk x) → (f.stalkMap x).hom.FormallyUnramified := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let U : ConnectedComponents X → X.Opens := fun c ↦ ⟨ConnectedComponents.mk ⁻¹' {c}, by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have hUc (c) : IsClosed (U c : Set X) :=
    isClosed_singleton.preimage ConnectedComponents.continuous_coe
  have key (c) : ∃ g : (U c).toScheme ⟶ ProjectiveLine (Spec (.of k)),
      g ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = (U c).ι ≫ X ↘ Spec (.of k) ∧
        IsFinite g ∧ Flat g ∧ ∀ y : (U c).toScheme, IsField ((U c).toScheme.presheaf.stalk y) →
          (g.stalkMap y).hom.FormallyUnramified := by
    let : (U c).toScheme.Over (Spec (.of k)) := ⟨(U c).ι ≫ X ↘ Spec (.of k)⟩
    have : SmoothOfRelativeDimension 1 ((U c).toScheme ↘ Spec (.of k)) := by
      exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) ((U c).ι ≫ X ↘ Spec (.of k)))
    have : IsClosedImmersion (U c).ι :=
      .of_isPreimmersion _ ((U c).range_ι ▸ hUc c)
    have : IsProper ((U c).toScheme ↘ Spec (.of k)) := by
      change IsProper ((U c).ι ≫ X ↘ Spec (.of k))
      infer_instance
    have : ConnectedSpace (U c) := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      have h : (U (ConnectedComponents.mk x) : Set X) = connectedComponent x :=
        connectedComponents_preimage_singleton
      exact isConnected_iff_connectedSpace.mp (h ▸ isConnected_connectedComponent)
    have := SmoothOfRelativeDimension.smooth 1 ((U c).toScheme ↘ Spec (.of k))
    have : CompactSpace (U c) := isCompact_iff_compactSpace.mp (hUc c).isCompact
    have := IsRegular.of_smooth ((U c).toScheme ↘ Spec (.of k))
    have := IsRegular.irreducibleSpace (U c).toScheme
    have : IsReduced (U c).toScheme := isReduced_of_isReduced_stalk _
    have : Nonempty (U c) := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      exact ⟨⟨x, rfl⟩⟩
    have : IsIntegral (U c).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    obtain ⟨x, -, hx⟩ := isClosed_univ.exists_closed_singleton (X := (U c).toScheme)
      Set.univ_nonempty
    obtain ⟨s, hs⟩ := exists_transcendental_functionField (k := k) x (by
      rw [ringKrullDim_stalk_eq_one_of_isClosed ((U c).toScheme ↘ Spec (.of k)) hx]
      exact one_ne_zero)
    -- choose a separating `t`, i.e. with `dt ≠ 0`
    let := (functionFieldRingHom k (U c).toScheme).toAlgebra
    let := (((U c).toScheme ↘ Spec (.of k)).appTop ≫
      (U c).toScheme.presheaf.germ ⊤ (genericPoint (U c).toScheme) trivial).hom.toAlgebra
    obtain ⟨t, ht, hDt⟩ := exists_transcendental_and_D_ne_zero (k := k)
      (finrank_kaehlerDifferential_functionField ((U c).toScheme ↘ Spec (.of k)) 1 (.refl _) rfl)
      hs
    obtain ⟨π, hπ, hπ'⟩ := exists_hom_projectiveLine_of_functionField t ht
    obtain ⟨h₁, -, h₂, -⟩ := isFinite_flat_of_hom_projectiveLine_of_functionField t ht π hπ'
    have hunr := formallyUnramified_stalkMap_genericPoint_of_functionField t hDt π hπ'
    have hdim : topologicalKrullDim (U c).toScheme ≤ 1 := by
      exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension
        ((U c).toScheme ↘ Spec (.of k)) 1
    refine ⟨π, hπ.comp_over, h₁, h₂, fun y hy ↦ ?_⟩
    obtain rfl : y = genericPoint (U c).toScheme := eq_genericPoint_of_not_isClosed hdim
      fun hyc ↦ by
        have := ringKrullDim_stalk_eq_one_of_isClosed ((U c).toScheme ↘ Spec (.of k)) hyc
        rw [ringKrullDim_eq_zero_of_isField hy] at this
        exact zero_ne_one this
    exact hunr
  choose g hg hfin hflat hunr using key
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover U <| eq_top_iff.2 fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.2 ⟨ConnectedComponents.mk x, rfl⟩
  have hcompat (c d) : pullback.fst (𝒰.f c) (𝒰.f d) ≫ g c = pullback.snd _ _ ≫ g d := by
    by_cases hcd : c = d
    · subst hcd
      have : pullback.fst (𝒰.f c) (𝒰.f c) = pullback.snd _ _ :=
        (cancel_mono (𝒰.f c)).1 pullback.condition
      rw [this]
    · have : IsEmpty (Limits.pullback (𝒰.f c) (𝒰.f d) : Scheme) := by
        refine ⟨fun z ↦ hcd ?_⟩
        have h₁ := ((pullback.fst (𝒰.f c) (𝒰.f d)) z).2
        have h₂ := ((pullback.snd (𝒰.f c) (𝒰.f d)) z).2
        have h : 𝒰.f c (pullback.fst (𝒰.f c) (𝒰.f d) z) =
            𝒰.f d (pullback.snd (𝒰.f c) (𝒰.f d) z) := by
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
        simp only [𝒰, Scheme.openCoverOfIsOpenCover_f] at h
        exact h₁.symm.trans ((congrArg ConnectedComponents.mk h).trans h₂)
      exact isInitialOfIsEmpty.hom_ext _ _
  let f := 𝒰.glueMorphisms g hcompat
  have hf (c) : (U c).ι ≫ f = g c := 𝒰.ι_glueMorphisms g hcompat c
  have hover : f ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = X ↘ Spec (.of k) :=
    𝒰.hom_ext _ _ fun c ↦ by
      simp only [𝒰, Scheme.openCoverOfIsOpenCover_f]
      rw [reassoc_of% (hf c), hg]
  have : IsProper (f ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := by
    rw [hover]; infer_instance
  have : IsProper f := IsProper.of_comp f (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : LocallyQuasiFinite f :=
    IsZariskiLocalAtSource.of_openCover 𝒰 fun c ↦ by
      simp only [𝒰, Scheme.openCoverOfIsOpenCover_f]
      rw [hf]; infer_instance
  have : Flat f :=
    IsZariskiLocalAtSource.of_openCover 𝒰 fun c ↦ by
      simp only [𝒰, Scheme.openCoverOfIsOpenCover_f]
      rw [hf]; infer_instance
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  refine ⟨f, ⟨hover⟩, inferInstance, inferInstance,
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance, fun x hx ↦ ?_⟩
  -- the stalk map of `f` at `x` is that of `g c` on the component `U c` of `x`
  let c := ConnectedComponents.mk x
  let y : U c := ⟨x, rfl⟩
  let e := asIso ((U c).ι.stalkMap y)
  have hy : IsField ((U c).toScheme.presheaf.stalk y) :=
    MulEquiv.isField hx e.symm.commRingCatIsoToRingEquiv.toMulEquiv
  have h₁ : ∀ φ : (U c).toScheme ⟶ ProjectiveLine (Spec (.of k)), φ = g c →
      (φ.stalkMap y).hom.FormallyUnramified := by
    rintro _ rfl
    exact hunr c y hy
  have h₂ := h₁ _ (hf c)
  rw [Scheme.Hom.stalkMap_comp] at h₂
  have h₃ : f.stalkMap x = (f.stalkMap ((U c).ι y) ≫ (U c).ι.stalkMap y) ≫ e.inv := by
    simp [e]
    rfl
  rw [h₃, CommRingCat.hom_comp]
  exact .comp h₂ (.of_surjective (ConcreteCategory.bijective_of_isIso e.inv).2)


end ProjectiveLine

section FiniteDuality

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

/-- **Duality along a finite flat morphism to `ℙ¹`, comparison map.** Let `X` be a smooth curve
over `k` and `f : X ⟶ ℙ¹_k` a finite flat morphism over `k`. There is a trace map
`τ : f_* Ω¹_{X/k} ⟶ Ω¹_{ℙ¹_k/k}` such that `f_* Hom(ℳ, Ω¹_{X/k}) ⟶ Hom(f_* ℳ, Ω¹_{ℙ¹_k/k})`,
`φ ↦ τ ∘ f_* φ`, is an isomorphism for every finite locally free `ℳ`. For `ℳ = 𝒪_X` this is the
trace identification `exists_isIso_pushforwardHomObjComparison_unit`; the general case follows
since `ℳ` is a direct summand of a free module of finite rank over the affine opens `f⁻¹V`
(`Modules.isIso_pushforwardHomObjComparison_of_isIso_unit`).

The hypothesis `hf` (`f` generically unramified, i.e. `k(X)/k(t)` separable) is not in the
blueprint statement; it is needed since the trace of differentials vanishes for inseparable `f`,
see `exists_isIso_pushforwardHomObjComparison_unit`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`, the sheaf-level statement) -/
theorem exists_isIso_pushforwardHomObjComparison (f : X ⟶ ProjectiveLine (Spec (.of k)))
    [f.IsOver (Spec (.of k))] [IsFinite f] [Flat f]
    (hf : ∀ x : X, IsField (X.presheaf.stalk x) → (f.stalkMap x).hom.FormallyUnramified) :
    ∃ τ : (Modules.pushforward f).obj (X ↘ Spec (.of k)).relativeDifferentials ⟶
        (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials,
      ∀ ℳ : X.Modules, ℳ.IsFiniteLocallyFree →
        IsIso (Modules.pushforwardHomObjComparison f τ ℳ) := by
  obtain ⟨τ, hτ⟩ := exists_isIso_pushforwardHomObjComparison_unit f hf
  exact ⟨τ, fun ℳ _ ↦ Modules.isIso_pushforwardHomObjComparison_of_isIso_unit hτ ℳ⟩

/-- **Duality along a finite flat morphism to `ℙ¹`, sheaf-level.** Let `X` be a smooth curve
over `k` and `f : X ⟶ ℙ¹_k` a finite flat morphism over `k`. Then
`Hom_{𝒪_{ℙ¹}}(f_* ℳ, Ω¹_{ℙ¹_k/k}) ≅ f_* Hom_{𝒪_X}(ℳ, Ω¹_{X/k})` as sheaves of modules on `ℙ¹_k`,
naturally in finite locally free `ℳ`: the isomorphism `φ ↦ τ ∘ f_* φ` of
`exists_isIso_pushforwardHomObjComparison`. The hypothesis `hf` (`f` generically unramified)
is not in the blueprint statement; see `exists_isIso_pushforwardHomObjComparison_unit`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`, the sheaf-level statement) -/
theorem nonempty_homObj_pushforward_iso_pushforward_homObj (f : X ⟶ ProjectiveLine (Spec (.of k)))
    [f.IsOver (Spec (.of k))] [IsFinite f] [Flat f]
    (hf : ∀ x : X, IsField (X.presheaf.stalk x) → (f.stalkMap x).hom.FormallyUnramified) :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.pushforward f).op ⋙
        (SheafOfModules.homFunctor (ProjectiveLine (Spec (.of k))).sheaf).flip.obj
          (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (SheafOfModules.homFunctor X.sheaf).flip.obj (X ↘ Spec (.of k)).relativeDifferentials ⋙
          Modules.pushforward f) := by
  obtain ⟨τ, hτ⟩ := exists_isIso_pushforwardHomObjComparison f hf
  have (ℳ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategoryᵒᵖ) :
      IsIso ((Functor.whiskerLeft (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op
        (Modules.pushforwardHomObjComparisonNatTrans f τ)).app ℳ) :=
    hτ ℳ.unop.obj ℳ.unop.property
  have := NatIso.isIso_of_isIso_app (Functor.whiskerLeft
    (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op
    (Modules.pushforwardHomObjComparisonNatTrans f τ))
  exact ⟨(asIso (Functor.whiskerLeft (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op
    (Modules.pushforwardHomObjComparisonNatTrans f τ))).symm⟩

/-- **Duality along a finite flat morphism to `ℙ¹`.** Let `X` be a smooth curve over `k` and
`f : X ⟶ ℙ¹_k` a finite flat morphism over `k`. Then
`Hom_{𝒪_{ℙ¹}}(f_* ℳ, Ω¹_{ℙ¹_k/k}) ≅ H⁰(X, ℳᵛ ⊗ Ω¹_{X/k})`, naturally in finite locally free
`ℳ`. Taking global sections in `nonempty_homObj_pushforward_iso_pushforward_homObj` gives
`Hom(f_* ℳ, Ω¹_{ℙ¹}) ≅ H⁰(ℙ¹, f_* Hom(ℳ, Ω¹_{X/k})) = H⁰(X, Hom(ℳ, Ω¹_{X/k}))`
(`Modules.pushforwardCompCohomologyFunctorZeroIso`), and `Hom(ℳ, Ω¹_{X/k}) ≅ ℳᵛ ⊗ Ω¹_{X/k}`
since `Ω¹_{X/k}` is invertible (`Modules.dualTensorHomIso`).

The hypothesis `hf` (`f` generically unramified, i.e. `k(X)/k(t)` separable) is not in the
blueprint statement; it is needed since the isomorphism is induced by the trace of differentials,
which vanishes for inseparable `f` (see `exists_isIso_pushforwardHomObjComparison_unit`). The
blueprint's proof uses this separability too, and downstream a separable `f` is always chosen
(`exists_isFinite_flat_hom_projectiveLine`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
theorem nonempty_homObj_pushforward_iso (f : X ⟶ ProjectiveLine (Spec (.of k)))
    [f.IsOver (Spec (.of k))] [IsFinite f] [Flat f]
    (hf : ∀ x : X, IsField (X.presheaf.stalk x) → (f.stalkMap x).hom.FormallyUnramified) :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.pushforward f).op ⋙
        (SheafOfModules.homFunctor (ProjectiveLine (Spec (.of k))).sheaf).flip.obj
          (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ⋙
        Modules.cohomologyFunctor k 0 ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        tensorRight (X ↘ Spec (.of k)).relativeDifferentials ⋙ Modules.cohomologyFunctor k 0) := by
  obtain ⟨E⟩ := nonempty_homObj_pushforward_iso_pushforward_homObj f hf
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  have := Modules.IsInvertible.of_sheafOfModules (X ↘ Spec (.of k)).relativeDifferentials
  exact ⟨Functor.isoWhiskerRight E (Modules.cohomologyFunctor k 0) ≪≫
    Functor.isoWhiskerLeft ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
      (SheafOfModules.homFunctor X.sheaf).flip.obj (X ↘ Spec (.of k)).relativeDifferentials)
      (Modules.pushforwardCompCohomologyFunctorZeroIso k f) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op
      (Functor.isoWhiskerRight (Modules.dualTensorHomIso (X ↘ Spec (.of k)).relativeDifferentials)
        (Modules.cohomologyFunctor k 0)).symm⟩

end FiniteDuality

section Divisors

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsAlgClosed k]

/-- For an open immersion `χ : Spec R ⟶ Y`, a point `w` and `a ∈ R`, the germ at `χ w` of the
section of `Y` over the image of `χ` given by `a` corresponds to `a` in the localization `R_w`. -/
theorem stalkMap_germ_appIso_inv_of_isOpenImmersion {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (χ : Spec R ⟶ Y) [IsOpenImmersion χ] (w : Spec R) (a : R) :
    (Spec.stalkIso R w).hom (χ.stalkMap w (Y.presheaf.germ (χ ''ᵁ ⊤) (χ w) ⟨w, trivial, rfl⟩
      ((χ.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv a)))) = algebraMap R _ a := by
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (χ.appIso ⊤).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]
  have h := congrArg (fun f ↦ (Spec.stalkIso R w).hom (f a))
    (Spec.algebraMap_stalkIso_inv (R := R) (x := w))
  simp only [CommRingCat.comp_apply] at h
  exact h.symm.trans (Iso.inv_hom_id_apply (Spec.stalkIso R w) _)

/-- For an open immersion `χ : Spec R ⟶ Y` and a point `w` whose prime ideal is `(a)`, the
maximal ideal of `𝒪_{Y, χ w}` is generated by the germ of `a`. -/
theorem maximalIdeal_stalk_eq_span_germ_of_isOpenImmersion {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (χ : Spec R ⟶ Y) [IsOpenImmersion χ] (w : Spec R) (a : R)
    (hw : w.asIdeal = Ideal.span {a}) :
    maximalIdeal (Y.presheaf.stalk (χ w)) = Ideal.span
      {Y.presheaf.germ (χ ''ᵁ ⊤) (χ w) ⟨w, trivial, rfl⟩
        ((χ.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv a))} := by
  have : w.asIdeal.IsPrime := PrimeSpectrum.isPrime w
  let e : Y.presheaf.stalk (χ w) ≃+* Localization.AtPrime w.asIdeal :=
    (asIso (χ.stalkMap w) ≪≫ Spec.stalkIso R w).commRingCatIsoToRingEquiv
  have hg : e (Y.presheaf.germ (χ ''ᵁ ⊤) (χ w) ⟨w, trivial, rfl⟩
      ((χ.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv a))) = algebraMap R _ a :=
    stalkMap_germ_appIso_inv_of_isOpenImmersion χ w a
  have hmax : maximalIdeal (Localization.AtPrime w.asIdeal) = Ideal.span {algebraMap R _ a} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal w.asIdeal,
      congrArg (Ideal.map (algebraMap R (Localization.AtPrime w.asIdeal))) hw, Ideal.map_span,
      Set.image_singleton]
  have : (maximalIdeal (Y.presheaf.stalk (χ w))).map e = maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
  rw [hmax, ← hg, ← Set.image_singleton, ← Ideal.map_span] at this
  have h := congrArg (Ideal.comap e) this
  rwa [Ideal.comap_map_of_bijective _ e.bijective,
    Ideal.comap_map_of_bijective _ e.bijective] at h

/-- For an open immersion `χ : Spec R ⟶ Y`, a point `w` and `a ∈ R` outside `w`, the germ of
`a` at `χ w` is a unit. -/
theorem isUnit_germ_of_isOpenImmersion {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (χ : Spec R ⟶ Y) [IsOpenImmersion χ] (w : Spec R) (a : R) (ha : a ∉ w.asIdeal) :
    IsUnit (Y.presheaf.germ (χ ''ᵁ ⊤) (χ w) ⟨w, trivial, rfl⟩
      ((χ.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv a))) := by
  have : w.asIdeal.IsPrime := PrimeSpectrum.isPrime w
  let e : Y.presheaf.stalk (χ w) ≃+* Localization.AtPrime w.asIdeal :=
    (asIso (χ.stalkMap w) ≪≫ Spec.stalkIso R w).commRingCatIsoToRingEquiv
  have hg : e (Y.presheaf.germ (χ ''ᵁ ⊤) (χ w) ⟨w, trivial, rfl⟩
      ((χ.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv a))) = algebraMap R _ a :=
    stalkMap_germ_appIso_inv_of_isOpenImmersion χ w a
  rw [← isUnit_map_iff e, hg]
  exact IsLocalization.map_units (Localization.AtPrime w.asIdeal) (⟨a, ha⟩ : w.asIdeal.primeCompl)

/-- The ideal `(X)` of a polynomial ring in one variable over a field is maximal. -/
theorem _root_.MvPolynomial.isMaximal_span_X_of_unique {K : Type*} [Field K] {σ : Type*}
    [Unique σ] : (Ideal.span {MvPolynomial.X (R := K) (default : σ)}).IsMaximal := by
  let e := MvPolynomial.uniqueAlgEquiv (R := K) σ
  have h : Ideal.span {MvPolynomial.X (R := K) (default : σ)} =
      Ideal.comap e.toRingEquiv (Ideal.span {Polynomial.X}) := by
    rw [← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
    congr 2
    change _ = Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X default) Polynomial.X
    rw [Polynomial.eval₂_X]
  have : (Ideal.span {(Polynomial.X : Polynomial K)}).IsMaximal := by
    rw [← Polynomial.ker_constantCoeff]
    exact RingHom.ker_isMaximal_of_surjective _ Polynomial.constantCoeff_surjective
  rw [h]
  infer_instance

set_option linter.unusedSectionVars false in
/-- **Degree of pullbacks of divisors.** Let `π : X ⟶ Y` be a finite flat morphism of proper
smooth integral curves over an algebraically closed field `k`, of degree `d`, so that `π_* 𝒪_X`
is locally free of rank `d`. Let `y` be a closed point of `Y` with uniformizer `t`, a section on
an open `V ∋ y` whose germ generates the maximal ideal of `𝒪_{Y,y}`. Then the pullback divisor
`π^*[y] = ∑_{π(x) = y} v_x(π^* t) [x]` has degree `d`. By linearity `deg π^* D = d · deg D` for
every divisor `D` on `Y`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem finsum_ord_eq_finrank [IsIntegral X] [IsLocallyNoetherian X] {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]
    [IsProper (Y ↘ Spec (.of k))] [IsIntegral Y] (π : X ⟶ Y) [π.IsOver (Spec (.of k))]
    [IsFinite π] [Flat π] {y : Y} (hy : IsClosed {y}) {V : Y.Opens} (hyV : y ∈ V)
    (t : Γ(Y, V))
    (ht : maximalIdeal (Y.presheaf.stalk y) = Ideal.span {Y.presheaf.germ V y hyV t}) :
    ∑ᶠ (x : X) (hx : π.base x = y), X.ord (algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ (π ⁻¹ᵁ V) x (show π.base x ∈ V from hx ▸ hyV) (π.app V t))) x =
      π.finrank (genericPoint Y) := by
  classical
  have := SmoothOfRelativeDimension.smooth 1 (Y ↘ Spec (.of k))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyV V.2
  replace hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have := hW.isOpenImmersion_fromSpec
  have := hU.isOpenImmersion_fromSpec
  let φ : Γ(Y, W) ⟶ Γ(X, π ⁻¹ᵁ W) := π.appLE W (π ⁻¹ᵁ W) le_rfl
  let : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := φ.hom.toAlgebra
  have : Module.Finite Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := by
    have := π.finite_app W hW
    rwa [← Scheme.Hom.appLE_eq_app] at this
  have : Module.Flat Γ(Y, W) Γ(X, π ⁻¹ᵁ W) :=
    HasRingHomProperty.appLE @Flat π inferInstance ⟨W, hW⟩ ⟨_, hU⟩ le_rfl
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  let p := (hW.primeIdealOf ⟨y, hyW⟩).asIdeal
  have : Fintype (p.primesOver Γ(X, π ⁻¹ᵁ W)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p Γ(X, π ⁻¹ᵁ W)
  -- the rank of `π` is the rank of `Γ(X, π⁻¹ W)` over `Γ(Y, W)`
  have hpb : IsPullback hU.fromSpec (Spec.map φ) π hW.fromSpec :=
    (IsOpenImmersion.isPullback (Spec.map φ) hU.fromSpec hW.fromSpec π
      (IsAffineOpen.SpecMap_appLE_fromSpec π hW hU le_rfl).symm
      (by rw [hU.opensRange_fromSpec, hW.opensRange_fromSpec])).flip
  have hrank : π.finrank (genericPoint Y) = Module.finrank Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := by
    have hη : genericPoint Y ∈ W :=
      (genericPoint_spec Y).mem_open_set_iff W.2 |>.mpr ⟨y, trivial, hyW⟩
    have h₁ := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb (hW.primeIdealOf ⟨_, hη⟩)
    rw [hW.fromSpec_primeIdealOf] at h₁
    rw [← h₁, show φ = CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(X, π ⁻¹ᵁ W)) from rfl,
      Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq,
      Ideal.finrank_fiber_eq_finrank]
  rw [hrank, ← hsum]
  -- reindex the points over `y` by the primes over `p`
  let G : X → ℤ := fun x ↦ if h : π x ∈ V then X.ord (algebraMap (X.presheaf.stalk x)
    X.functionField (X.presheaf.germ (π ⁻¹ᵁ V) x h (π.app V t))) x else 0
  have hLHS : (∑ᶠ (x : X) (hx : π.base x = y), X.ord (algebraMap (X.presheaf.stalk x)
      X.functionField (X.presheaf.germ (π ⁻¹ᵁ V) x (show π.base x ∈ V from hx ▸ hyV)
        (π.app V t))) x) = ∑ᶠ x ∈ {x | π x = y}, G x :=
    finsum_congr fun x ↦ finsum_congr fun hx ↦ by
      simp only [G, dite_eq_left (show π x ∈ V from hx ▸ hyV)]
  let e : p.primesOver Γ(X, π ⁻¹ᵁ W) → X := fun q ↦ hU.fromSpec ⟨q.1, q.2.1⟩
  have he : Function.Injective e := fun q q' h ↦
    Subtype.ext (congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective h))
  have hπe (q : p.primesOver Γ(X, π ⁻¹ᵁ W)) : π (e q) = y := by
    have hq : Spec.map φ ⟨q.1, q.2.1⟩ = hW.primeIdealOf ⟨y, hyW⟩ :=
      PrimeSpectrum.ext (Ideal.LiesOver.over (P := q.1) (p := p)).symm
    calc π (e q) = hW.fromSpec (Spec.map φ ⟨q.1, q.2.1⟩) :=
          (congrArg (fun f ↦ f ⟨q.1, q.2.1⟩)
            (IsAffineOpen.SpecMap_appLE_fromSpec π hW hU le_rfl)).symm
      _ = y := by rw [hq]; exact hW.fromSpec_primeIdealOf _
  have hrange : Set.range e = {x | π x = y} := by
    ext x
    refine ⟨fun ⟨q, hq⟩ ↦ hq ▸ hπe q, fun hx ↦ ?_⟩
    have hxU : x ∈ π ⁻¹ᵁ W := by
      change π x ∈ W
      rw [show π x = y from hx]; exact hyW
    have hc := IsAffineOpen.comap_primeIdealOf_appLE W hW (π ⁻¹ᵁ W) hU le_rfl hxU
    refine ⟨⟨(hU.primeIdealOf ⟨x, hxU⟩).asIdeal, inferInstance, ⟨?_⟩⟩, ?_⟩
    · change p = Ideal.comap φ.hom (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      have := congrArg PrimeSpectrum.asIdeal hc
      simp only [PrimeSpectrum.comap_asIdeal] at this
      rw [this]
      exact congrArg (fun z : W ↦ (hW.primeIdealOf z).asIdeal)
        (Subtype.ext (show π x = y from hx).symm)
    · exact hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  rw [hLHS, ← hrange, finsum_mem_range he, finsum_eq_sum_of_fintype]
  push_cast
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  -- the point `x` of `X` corresponding to `q`
  have hxy : π (e q) = y := hπe q
  have hxV : π (e q) ∈ V := hxy ▸ hyV
  have hxU : e q ∈ π ⁻¹ᵁ W := show π (e q) ∈ W from hxy ▸ hyW
  have hpq : hU.primeIdealOf ⟨e q, hxU⟩ = ⟨q.1, q.2.1⟩ := by
    generalize hr : (⟨q.1, q.2.1⟩ : PrimeSpectrum Γ(X, π ⁻¹ᵁ W)) = r
    have h : (⟨e q, hxU⟩ : (π ⁻¹ᵁ W : X.Opens)) = hU.isoSpec.inv r := by
      apply Subtype.ext
      change hU.fromSpec ⟨q.1, q.2.1⟩ = (π ⁻¹ᵁ W).ι (hU.isoSpec.inv r)
      rw [hr]
      exact (congrArg (fun f ↦ f r) hU.isoSpec_inv_ι).symm
    rw [IsAffineOpen.primeIdealOf, h]
    exact congrArg (fun f ↦ f r) hU.isoSpec.inv_hom_id
  -- `x` is a closed point: the fibre of `π` over the closed point `y` is discrete
  have hxc : IsClosed {e q} := by
    have := (π.isDiscrete_preimage_singleton y).to_subtype
    have hc := (isClosed_discrete ({⟨e q, hxy⟩} : Set (π ⁻¹' {y}))).trans
      (hy.preimage π.continuous)
    simpa using hc
  obtain ⟨_, hdvr⟩ := isDiscreteValuationRing_stalk_of_isClosed (X ↘ Spec (.of k)) hxc
  have hcoh : Order.coheight (e q) = 1 := by
    have := ringKrullDim_stalk_eq_one_of_isClosed (X ↘ Spec (.of k)) hxc
    rw [ringKrullDim_stalk_eq_coheight] at this
    exact_mod_cast this
  -- `π^* t` does not vanish at `x`
  have hinjx : Function.Injective (π.stalkMap (e q)) := by
    algebraize [(π.stalkMap (e q)).hom]
    have : Module.Flat (Y.presheaf.stalk (π (e q))) (X.presheaf.stalk (e q)) :=
      Flat.stalkMap π (e q)
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (π (e q))) (X.presheaf.stalk (e q))) :=
      inferInstanceAs (IsLocalHom (π.stalkMap (e q)).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom
      (A := Y.presheaf.stalk (π (e q))) (B := X.presheaf.stalk (e q))
    exact FaithfulSMul.algebraMap_injective _ _
  have key : ∀ (z : Y) (_ : z = y) (hzV : z ∈ V),
      maximalIdeal (Y.presheaf.stalk z) = Ideal.span {Y.presheaf.germ V z hzV t} := by
    rintro z rfl hzV
    exact ht
  have ht' := key _ hxy hxV
  have hy' : IsClosed {π (e q)} := hxy ▸ hy
  obtain ⟨_, hdvrY⟩ := isDiscreteValuationRing_stalk_of_isClosed (Y ↘ Spec (.of k)) hy'
  have hgt : Y.presheaf.germ V _ hxV t ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at ht'
    exact IsDiscreteValuationRing.not_a_field _ ht'
  have hs0 : X.presheaf.germ (π ⁻¹ᵁ V) (e q) hxV (π.app V t) ≠ 0 := by
    rw [← Scheme.Hom.germ_stalkMap_apply]
    exact (map_ne_zero_iff _ hinjx).mpr hgt
  simp only [G, dite_eq_left hxV]
  rw [Scheme.ord_algebraMap_stalk hcoh hs0]
  -- the inertia degree is `1`
  let κA : k →+* Γ(Y, W) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appLE ⊤ W le_top).hom
  let : Algebra k Γ(Y, W) := κA.toAlgebra
  let : Algebra k Γ(X, π ⁻¹ᵁ W) := (φ.hom.comp κA).toAlgebra
  have : IsScalarTower k Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType k Γ(Y, W) := by
    have h := HasRingHomProperty.appLE @LocallyOfFiniteType (Y ↘ Spec (.of k)) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
    have h₂ : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact h.comp h₂
  have : Algebra.FiniteType k Γ(X, π ⁻¹ᵁ W) := Algebra.FiniteType.trans (S := Γ(Y, W))
    inferInstance inferInstance
  have hpmax : p.IsMaximal := hW.primeIdealOf_isMaximal_of_isClosed ⟨y, hyW⟩ hy
  have : q.1.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Γ(Y, W)) _
    ((Ideal.LiesOver.over (P := q.1) (p := p)) ▸ hpmax)
  rw [Ideal.inertiaDeg_eq_one_of_isAlgClosed (k := k) p q.1, Nat.cast_one, mul_one]
  -- the ramification index is the order of vanishing
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨e q, hxU⟩
  have hloc := hU.isLocalization_stalk ⟨e q, hxU⟩
  rw [hpq] at hloc
  let : Algebra Γ(Y, W) (X.presheaf.stalk (e q)) :=
    ((algebraMap Γ(X, π ⁻¹ᵁ W) (X.presheaf.stalk (e q))).comp φ.hom).toAlgebra
  have : IsScalarTower Γ(Y, W) Γ(X, π ⁻¹ᵁ W) (X.presheaf.stalk (e q)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨π (e q), show π (e q) ∈ W from hxU⟩
  have hlocY := hW.isLocalization_stalk ⟨π (e q), show π (e q) ∈ W from hxU⟩
  have hpy : hW.primeIdealOf ⟨π (e q), show π (e q) ∈ W from hxU⟩ =
      hW.primeIdealOf ⟨y, hyW⟩ := congrArg _ (Subtype.ext hxy)
  rw [hpy] at hlocY
  have hcomp : algebraMap Γ(Y, W) (X.presheaf.stalk (e q)) =
      (π.stalkMap (e q)).hom.comp (algebraMap Γ(Y, W) (Y.presheaf.stalk (π (e q)))) := by
    ext a
    change X.presheaf.germ (π ⁻¹ᵁ W) (e q) hxU (π.appLE W (π ⁻¹ᵁ W) le_rfl a) =
      π.stalkMap (e q) (Y.presheaf.germ W (π (e q)) hxU a)
    rw [Scheme.Hom.appLE_eq_app]
    exact (Scheme.Hom.germ_stalkMap_apply π W (e q) hxU a).symm
  have hs : p.map (algebraMap Γ(Y, W) (X.presheaf.stalk (e q))) =
      Ideal.span {X.presheaf.germ (π ⁻¹ᵁ V) (e q) hxV (π.app V t)} := by
    rw [hcomp, ← Ideal.map_map, IsLocalization.AtPrime.map_eq_maximalIdeal, ht',
      Ideal.map_span, Set.image_singleton, Scheme.Hom.germ_stalkMap_apply]
  rw [Ideal.ramificationIdx_eq_ord p q.1 _ hs]

/-- **The order of a rational function along a chart of `ℙ¹`.** Let `π : X ⟶ ℙ¹_k` be finite
flat, and let `χ : Spec k[T] ⟶ ℙ¹_k` be an open immersion through which the generic point
`Spec k(X) ⟶ ℙ¹_k` of `π` factors as `Spec` of `T ↦ u`. Then at the point `y = χ(T = 0)` the
function `u` has total order `deg π` over `y`, it vanishes at every point over `y`, and it is a
unit at every other point over the image of `χ`. -/
theorem exists_finsum_ord_chart [IsIntegral X] [IsLocallyNoetherian X]
    (π : X ⟶ ProjectiveLine (Spec (.of k))) [π.IsOver (Spec (.of k))] [IsFinite π] [Flat π]
    {σ : Type u} [Unique σ] (χ : Spec (.of (MvPolynomial σ k)) ⟶ ProjectiveLine (Spec (.of k)))
    [IsOpenImmersion χ] (ψ : MvPolynomial σ k →+* X.functionField) (u : X.functionField)
    (hu : ψ (MvPolynomial.X default) = u)
    (hχ : X.fromSpecFunctionField ≫ π = Spec.map (CommRingCat.ofHom ψ) ≫ χ) :
    ∃ y : ProjectiveLine (Spec (.of k)),
      (∑ᶠ (x : X) (_ : π x = y), X.ord u x) = π.finrank (genericPoint _) ∧
      (∀ x, π x = y → 0 < X.ord u x) ∧
      (∀ x, π x ∈ χ.opensRange → π x ≠ y → X.ord u x = 0) := by
  let A := MvPolynomial σ k
  let a : A := MvPolynomial.X default
  have hmaxa : (Ideal.span {a}).IsMaximal := MvPolynomial.isMaximal_span_X_of_unique
  let w : Spec (.of A) := ⟨Ideal.span {a}, hmaxa.isPrime⟩
  let V := χ ''ᵁ ⊤
  let c := (χ.appIso ⊤).inv ((Scheme.ΓSpecIso (.of A)).inv a)
  have hyV : χ w ∈ V := ⟨w, trivial, rfl⟩
  have hmax := maximalIdeal_stalk_eq_span_germ_of_isOpenImmersion χ w a rfl
  have hyc : IsClosed {χ w} := by
    have : JacobsonSpace (ProjectiveLine (Spec (.of k))) :=
      LocallyOfFiniteType.jacobsonSpace (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
    have hw : w ∈ closedPoints (Spec (.of A)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal w).mpr hmaxa
    rw [← χ.isOpenEmbedding.preimage_closedPoints] at hw
    exact hw
  -- the pullback of the coordinate `c` is `u`
  have hK (x : X) (hx : π x ∈ V) : algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ (π ⁻¹ᵁ V) x hx (π.app V c)) = u := by
    have : Nonempty (π ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩
    refine (Scheme.algebraMap_germ_eq_germToFunctionField X (U := π ⁻¹ᵁ V) (x := x) hx
      (π.app V c)).trans ?_
    let z : Spec X.functionField := IsLocalRing.closedPoint X.functionField
    let F := X.fromSpecFunctionField ≫ π
    have hηV : genericPoint X ∈ π ⁻¹ᵁ V :=
      ((genericPoint_spec X).mem_open_set_iff (π ⁻¹ᵁ V).2).mpr ⟨x, trivial, hx⟩
    have hz : z ∈ F ⁻¹ᵁ V := by
      change F z ∈ V
      rw [show F = _ from hχ]
      exact ⟨_, trivial, rfl⟩
    have hz' : z ∈ (Spec.map (CommRingCat.ofHom ψ) ≫ χ) ⁻¹ᵁ V := ⟨_, trivial, rfl⟩
    -- evaluate both descriptions of `F` on `c` and take germs at the closed point
    have h₁ : (Spec X.functionField).presheaf.germ _ z hz (F.app V c) =
        (Spec X.functionField).presheaf.germ ⊤ z trivial
          ((Scheme.ΓSpecIso X.functionField).inv (X.germToFunctionField _ (π.app V c))) := by
      change (Spec X.functionField).presheaf.germ _ z hz
        (X.fromSpecFunctionField.app (π ⁻¹ᵁ V) (π.app V c)) = _
      rw [Scheme.fromSpecStalk_app hηV]
      erw [TopCat.Presheaf.germ_res_apply]
      rfl
    have h₂ : (Spec X.functionField).presheaf.germ _ z hz (F.app V c) =
        (Spec X.functionField).presheaf.germ _ z hz'
          ((Spec.map (CommRingCat.ofHom ψ) ≫ χ).app V c) := by
      rw [ConcreteCategory.congr_hom (Scheme.Hom.congr_app hχ V) c]
      erw [TopCat.Presheaf.germ_res_apply]
      rfl
    have h₃ : (Spec X.functionField).presheaf.germ _ z hz'
          ((Spec.map (CommRingCat.ofHom ψ) ≫ χ).app V c) =
        (Spec X.functionField).presheaf.germ ⊤ z trivial
          ((Scheme.ΓSpecIso X.functionField).inv (ψ a)) := by
      have hc : χ.app V c = (Spec (.of A)).presheaf.map
          (eqToHom (χ.preimage_image_eq ⊤)).op ((Scheme.ΓSpecIso (.of A)).inv a) := by
        change ((χ.appIso ⊤).inv ≫ χ.app (χ ''ᵁ ⊤)) _ = _
        rw [Scheme.Hom.appIso_inv_app]
      have hn := ConcreteCategory.congr_hom (Scheme.Hom.naturality (Spec.map (CommRingCat.ofHom ψ))
        (eqToHom (χ.preimage_image_eq ⊤)).op) ((Scheme.ΓSpecIso (.of A)).inv a)
      simp only [CommRingCat.comp_apply] at hn
      change (Spec X.functionField).presheaf.germ _ z hz'
        ((Spec.map (CommRingCat.ofHom ψ)).app (χ ⁻¹ᵁ V) (χ.app V c)) = _
      rw [hc]
      erw [hn, TopCat.Presheaf.germ_res_apply]
      erw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (.of A)).inv,
        ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    have hinj : Function.Injective ((Scheme.ΓSpecIso X.functionField).inv ≫
        (Spec X.functionField).presheaf.germ ⊤ z trivial) := RingHom.injective _
    rw [← hu]
    exact hinj (h₁.symm.trans (h₂.trans h₃))
  refine ⟨χ w, ?_, ?_, ?_⟩
  · rw [← finsum_ord_eq_finrank (k := k) π hyc hyV c hmax]
    exact finsum_congr fun x ↦ finsum_congr fun hx ↦ by rw [hK]
  · intro x hxy
    have hxV : π x ∈ V := hxy ▸ hyV
    have hxc : IsClosed {x} := by
      have := (π.isDiscrete_preimage_singleton (χ w)).to_subtype
      have hc := (isClosed_discrete ({⟨x, hxy⟩} : Set (π ⁻¹' {χ w}))).trans
        (hyc.preimage π.continuous)
      simpa using hc
    obtain ⟨_, hdvr⟩ := isDiscreteValuationRing_stalk_of_isClosed (X ↘ Spec (.of k)) hxc
    have hcoh : Order.coheight x = 1 := by
      have := ringKrullDim_stalk_eq_one_of_isClosed (X ↘ Spec (.of k)) hxc
      rw [ringKrullDim_stalk_eq_coheight] at this
      exact_mod_cast this
    have key : ∀ (z : ProjectiveLine (Spec (.of k))) (_ : z = χ w) (hz : z ∈ V),
        Ideal.span {(ProjectiveLine (Spec (.of k))).presheaf.germ V z hz c} =
          maximalIdeal _ := by
      rintro z rfl hz
      exact hmax.symm
    have hm := key _ hxy hxV
    obtain ⟨_, hdvrY⟩ := isDiscreteValuationRing_stalk_of_isClosed
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) (hxy ▸ hyc)
    have hg0 : (ProjectiveLine (Spec (.of k))).presheaf.germ V (π x) hxV c ≠ 0 := by
      intro h
      rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at hm
      exact IsDiscreteValuationRing.not_a_field _ hm.symm
    have hgm : (ProjectiveLine (Spec (.of k))).presheaf.germ V (π x) hxV c ∈ maximalIdeal _ :=
      hm ▸ Ideal.subset_span rfl
    have hinjx : Function.Injective (π.stalkMap x) := by
      algebraize [(π.stalkMap x).hom]
      have : Module.Flat ((ProjectiveLine (Spec (.of k))).presheaf.stalk (π x))
          (X.presheaf.stalk x) := Flat.stalkMap π x
      have : IsLocalHom (algebraMap ((ProjectiveLine (Spec (.of k))).presheaf.stalk (π x))
          (X.presheaf.stalk x)) := inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
      have := Module.FaithfullyFlat.of_flat_of_isLocalHom
        (A := (ProjectiveLine (Spec (.of k))).presheaf.stalk (π x)) (B := X.presheaf.stalk x)
      exact FaithfulSMul.algebraMap_injective _ _
    have hs0 : X.presheaf.germ (π ⁻¹ᵁ V) x hxV (π.app V c) ≠ 0 := by
      rw [← Scheme.Hom.germ_stalkMap_apply]
      exact (map_ne_zero_iff _ hinjx).mpr hg0
    have hsm : X.presheaf.germ (π ⁻¹ᵁ V) x hxV (π.app V c) ∈ maximalIdeal _ := by
      rw [← Scheme.Hom.germ_stalkMap_apply]
      exact map_nonunit (π.stalkMap x).hom _ hgm
    rw [← hK x hxV, Scheme.ord_algebraMap_stalk hcoh hs0]
    have hne : Ring.ord (X.presheaf.stalk x) (X.presheaf.germ (π ⁻¹ᵁ V) x hxV (π.app V c)) ≠ 0 := by
      rw [Ring.ord, ne_eq, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial,
        Ideal.Quotient.nontrivial_iff]
      exact fun h ↦ (mem_maximalIdeal _).mp hsm ((Ideal.span_singleton_eq_top).mp h)
    have hfin := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hs0)
    have : 0 < (Ring.ord (X.presheaf.stalk x)
        (X.presheaf.germ (π ⁻¹ᵁ V) x hxV (π.app V c))).toNat :=
      ENat.toNat_pos hne hfin
    exact_mod_cast this
  · rintro x ⟨w', hw'⟩ hne
    have hxV : π x ∈ V := ⟨w', trivial, hw'⟩
    have hww : w' ≠ w := fun h ↦ hne (hw' ▸ h ▸ rfl)
    have ha : a ∉ w'.asIdeal := by
      intro h
      have := hmaxa.eq_of_le (PrimeSpectrum.isPrime w').ne_top
        ((Ideal.span_singleton_le_iff_mem _).mpr h)
      exact hww (PrimeSpectrum.ext this.symm)
    have key : ∀ (z : ProjectiveLine (Spec (.of k))) (_ : z = χ w') (hz : z ∈ V),
        IsUnit ((ProjectiveLine (Spec (.of k))).presheaf.germ V z hz c) := by
      rintro z rfl hz
      exact isUnit_germ_of_isOpenImmersion χ w' a ha
    have hu' := key _ hw'.symm hxV
    have hsu : IsUnit (X.presheaf.germ (π ⁻¹ᵁ V) x hxV (π.app V c)) := by
      rw [← Scheme.Hom.germ_stalkMap_apply]
      exact hu'.map _
    rw [← hK x hxV]
    by_cases hcoh : Order.coheight x = 1
    · rw [Scheme.ord_eq_iff hcoh ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
        hsu.ne_zero)]
      have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hcoh.le
      exact Ring.ordFrac_of_isUnit hsu
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hcoh _

variable (k X) in
include k in
/-- **Principal divisors have degree zero.** For a nonzero rational function `f` on a proper
smooth integral curve over an algebraically closed field `k`,
`deg div(f) = ∑_x v_x(f) = 0`. For `f ∉ k` this is `div(f) = π_f^*([0] - [∞])` for the finite
flat morphism `π_f : X ⟶ ℙ¹_k` of degree `d`, whose degree is `d - d = 0`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem finsum_ord_eq_zero [IsIntegral X] [IsLocallyNoetherian X] {f : X.functionField}
    (hf : f ≠ 0) : ∑ᶠ x : X, X.ord f x = 0 := by
  classical
  let := (functionFieldRingHom k X).toAlgebra
  by_cases ht : Transcendental k f
  swap
  · -- `f` is algebraic over the algebraically closed `k`, so it is a nonzero constant
    rw [Transcendental, not_not] at ht
    obtain ⟨c, rfl⟩ := minpoly.mem_range_of_degree_eq_one k f
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible ht.isIntegral))
    have hc : c ≠ 0 := by rintro rfl; exact hf (map_zero _)
    have hu : IsUnit (globalSectionsRingHom k (X := X) c) := (Ne.isUnit hc).map _
    have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    refine (finsum_congr fun x ↦ ?_).trans finsum_zero
    exact Scheme.ord_of_isUnit hu trivial
  -- `f` defines a finite flat morphism `π : X ⟶ ℙ¹`
  obtain ⟨π, hπo, hπ⟩ := exists_hom_projectiveLine_of_functionField (k := k) f ht
  have := hπo
  obtain ⟨hfin, -, hflat, -⟩ := isFinite_flat_of_hom_projectiveLine_of_functionField f ht π hπ
  have hg₀ : X.fromSpecFunctionField ≫ X ↘ Spec (.of k) =
      Spec.map (CommRingCat.ofHom (functionFieldRingHom k X)) := by
    refine ext_of_isAffine ?_
    rw [← cancel_epi (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
    ext a
    simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, functionFieldRingHom,
      globalSectionsRingHom]
    rfl
  have hs : Ideal.span (Set.range (functionFieldCoordinates (X := X) f)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨0⟩, rfl⟩) (by simp)
  let v : ULift.{u} (Fin 2) → X.functionField := fun j ↦ ![1, f] j.down
  have hπ' := hπ hs
  rw [hg₀] at hπ'
  -- the two charts
  let _ : Unique {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} :=
    ⟨⟨⟨⟨1⟩, by decide⟩⟩, fun ⟨⟨a⟩, ha⟩ ↦ by
      have : a = 1 := by grind
      subst this; rfl⟩
  let _ : Unique {j : ULift.{u} (Fin 2) // j ≠ ⟨1⟩} :=
    ⟨⟨⟨⟨0⟩, by decide⟩⟩, fun ⟨⟨a⟩, ha⟩ ↦ by
      have : a = 0 := by grind
      subst this; rfl⟩
  obtain ⟨y₀, h₀, h₀pos, h₀zero⟩ := exists_finsum_ord_chart π
    ((ProjectiveSpace.standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩ ≪≫
      AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).inv ≫
      (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩).ι)
    (MvPolynomial.eval₂Hom (functionFieldRingHom k X)
      (fun j : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦ v j / v ⟨0⟩)) f
    (by
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, v]
      change ![1, f] 1 / ![1, f] 0 = f
      simp) (hπ'.trans
      (ProjectiveLine.homOfSections_eq_SpecMap_comp_of_ne_zero _ v ⟨0⟩ (by simp [v]) hs))
  obtain ⟨y₁, h₁, h₁pos, h₁zero⟩ := exists_finsum_ord_chart π
    ((ProjectiveSpace.standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨1⟩ ≪≫
      AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨1⟩} (.of k)).inv ≫
      (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨1⟩).ι)
    (MvPolynomial.eval₂Hom (functionFieldRingHom k X)
      (fun j : {j : ULift.{u} (Fin 2) // j ≠ ⟨1⟩} ↦ v j / v ⟨1⟩)) f⁻¹
    (by
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, v]
      change ![1, f] 0 / ![1, f] 1 = f⁻¹
      simp) (hπ'.trans
      (ProjectiveLine.homOfSections_eq_SpecMap_comp_of_ne_zero _ v ⟨1⟩ (by simpa [v]) hs))
  -- the order of `f⁻¹`
  have hinv (x : X) : X.ord f⁻¹ x = - X.ord f x := by
    have h := Scheme.ord_mul (x := x) hf (inv_ne_zero hf)
    have h1 := Scheme.ord_mul (x := x) (one_ne_zero (α := X.functionField))
      (one_ne_zero (α := X.functionField))
    rw [mul_inv_cancel₀ hf] at h
    rw [mul_one] at h1
    omega
  -- every point of `ℙ¹` lies in one of the two charts
  have hcover (z : ProjectiveLine (Spec (.of k))) :
      z ∈ (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩) ∨
        z ∈ (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨1⟩) := by
    have : z ∈ (⊤ : (ProjectiveLine (Spec (.of k))).Opens) := trivial
    rw [← ProjectiveSpace.iSup_standardOpen, TopologicalSpace.Opens.mem_iSup] at this
    obtain ⟨⟨i⟩, hi⟩ := this
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  have hsupp (x : X) (hx : X.ord f x ≠ 0) : x ∈ π ⁻¹' {y₀} ∪ π ⁻¹' {y₁} := by
    rcases hcover (π x) with h | h
    · by_contra hn
      refine hx (h₀zero x ?_ fun e ↦ hn (Or.inl e))
      rwa [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
    · by_contra hn
      refine hx ?_
      have := h₁zero x (by rwa [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι])
        fun e ↦ hn (Or.inr e)
      rw [hinv] at this
      omega
  have hdisj : Disjoint (π ⁻¹' {y₀}) (π ⁻¹' {y₁}) := by
    rw [Set.disjoint_left]
    intro x hx₀ hx₁
    have a₀ := h₀pos x hx₀
    have a₁ := h₁pos x hx₁
    rw [hinv] at a₁
    omega
  have e₁ : ∑ᶠ x ∈ π ⁻¹' {y₁}, X.ord f x = -(π.finrank (genericPoint _) : ℤ) := by
    rw [← h₁, ← finsum_neg_distrib]
    refine finsum_congr fun x ↦ ?_
    rw [← finsum_neg_distrib]
    exact finsum_congr fun _ ↦ by rw [hinv, neg_neg]
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (π ⁻¹' {y₀} ∪ π ⁻¹' {y₁})
      (fun x hx ↦ ⟨fun _ ↦ hsupp x hx, fun _ ↦ trivial⟩),
    finsum_mem_union hdisj (π.finite_preimage_singleton _) (π.finite_preimage_singleton _), e₁]
  change (∑ᶠ (x : X) (_ : π x = y₀), X.ord f x) + _ = _
  rw [h₀]
  ring

end Divisors

section Duality

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

/-- **Serre duality on a curve, `q = 1`.** On a smooth proper curve `X` over `k`, with
`ω = Ω¹_{X/k}`, there is an isomorphism `H¹(X, ℳ)^∨ ≅ H⁰(X, ℳᵛ ⊗ ω)`, natural in finite locally
free `ℳ`. Choose a finite flat `f : X ⟶ ℙ¹_k` (`exists_isFinite_flat_hom_projectiveLine`); then
`H¹(X, ℳ) ≅ H¹(ℙ¹_k, f_* ℳ)` since `f` is affine, `H¹(ℙ¹_k, f_* ℳ)^∨ ≅ Hom(f_* ℳ, ω_{ℙ¹})` by
duality on `ℙ¹_k` (`f_* ℳ` is finite locally free, hence coherent), and
`Hom(f_* ℳ, ω_{ℙ¹}) ≅ H⁰(X, ℳᵛ ⊗ ω)` by duality along `f`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`, case `q = n = 1`) -/
theorem nonempty_dual_H_one_iso :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.cohomologyFunctor k 1).op ⋙ ModuleCat.dualFunctor k ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        tensorRight (X ↘ Spec (.of k)).relativeDifferentials ⋙ Modules.cohomologyFunctor k 0) := by
  obtain ⟨f, _, _, _, _, hf⟩ := exists_isFinite_flat_hom_projectiveLine (k := k) (X := X)
  obtain ⟨T⟩ := Modules.nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom k f 1
  obtain ⟨D⟩ := ProjectiveLine.nonempty_dual_H_one_iso k
  obtain ⟨E⟩ := nonempty_homObj_pushforward_iso f hf
  let L₁ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    ObjectProperty.lift _ (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι fun ℱ ↦ by
      have : ℱ.obj.IsFiniteLocallyFree := ℱ.property
      exact inferInstanceAs ℱ.obj.IsQuasicoherent
  let L₂ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory ⥤
      (Modules.isCoherent (ProjectiveLine (Spec (.of k)))).FullSubcategory :=
    ObjectProperty.lift _
      ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι ⋙ Modules.pushforward f)
      fun ℱ ↦ by
        have : ℱ.obj.IsFiniteLocallyFree := ℱ.property
        let 𝒢 := (Modules.pushforward f).obj ℱ.obj
        have := Modules.isFiniteLocallyFree_pushforward f ℱ.obj
        exact ⟨SheafOfModules.instIsQuasicoherentOfIsLocallyFree 𝒢,
          SheafOfModules.IsFiniteLocallyFree.isFinitePresentation 𝒢⟩
  -- `H¹(X, ℳ)^∨ ≅ H¹(ℙ¹, f_* ℳ)^∨ ≅ Hom(f_* ℳ, ω_{ℙ¹}) ≅ H⁰(X, ℳᵛ ⊗ ω)`
  exact ⟨Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerLeft L₁ T).symm)
    (ModuleCat.dualFunctor k) ≪≫ Functor.isoWhiskerLeft L₂.op D ≪≫ E⟩

/-- **Serre duality on a curve, `q = 0`.** On a smooth proper curve `X` over `k`, with
`ω = Ω¹_{X/k}`, there is an isomorphism `H⁰(X, ℳ)^∨ ≅ H¹(X, ℳᵛ ⊗ ω)`, natural in finite locally
free `ℳ`. Apply `nonempty_dual_H_one_iso` to `𝒩 = ℳᵛ ⊗ ω` and use `(ℳᵛ ⊗ ω)ᵛ ⊗ ω ≅ ℳ` (`ω` is
invertible) to get `H¹(X, 𝒩)^∨ ≅ H⁰(X, ℳ)`; then dualise, `H¹(X, 𝒩)` being finite-dimensional.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`, reduction to `q = n`) -/
theorem nonempty_dual_H_zero_iso :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.cohomologyFunctor k 0).op ⋙ ModuleCat.dualFunctor k ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        tensorRight (X ↘ Spec (.of k)).relativeDifferentials ⋙ Modules.cohomologyFunctor k 1) := by
  obtain ⟨E⟩ := nonempty_dual_H_one_iso (k := k) (X := X)
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  obtain ⟨B⟩ := Modules.nonempty_iso_dual_tensorObj_dual_tensorObj
    (X ↘ Spec (.of k)).relativeDifferentials
  let D := Modules.dualTensorFunctor (X ↘ Spec (.of k)).relativeDifferentials
  -- `H¹(ℱᵛ ⊗ ω)^∨ ≅ H⁰(ℱ)`, naturally in `ℱ`.
  let G : opOp _ ⋙ D.op ⋙ ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
      (Modules.cohomologyFunctor k 1).op ⋙ ModuleCat.dualFunctor k) ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι ⋙ Modules.cohomologyFunctor k 0 :=
    Functor.isoWhiskerLeft (opOp _ ⋙ D.op) E ≪≫
      (Functor.isoWhiskerRight B (Modules.cohomologyFunctor k 0)).symm
  have hfin (ℱ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategoryᵒᵖ) :
      FiniteDimensional k ((D ⋙ (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι ⋙
        Modules.cohomologyFunctor k 1).obj ℱ) := by
    have : (D.obj ℱ).obj.IsFiniteLocallyFree := (D.obj ℱ).property
    have := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation (D.obj ℱ).obj
    have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree (D.obj ℱ).obj
    exact Modules.finiteDimensional_H_of_isProper (D.obj ℱ).obj 1
  exact ⟨Functor.isoWhiskerRight (NatIso.op G) (ModuleCat.dualFunctor k) ≪≫
    ModuleCat.dualDualIso (D ⋙ (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι ⋙
      Modules.cohomologyFunctor k 1)⟩

end Duality

end AlgebraicGeometry.Scheme
