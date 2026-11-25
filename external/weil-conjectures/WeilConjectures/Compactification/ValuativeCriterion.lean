/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring
public import WeilConjectures.Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The dense-source valuative criterion

Let `f : X ⟶ S` be a morphism of schemes and let `h : U ⟶ X` be quasi-compact and
dominant. To check the valuative criterion for `f` it suffices to check it against those
valuative squares whose generic point factors through `h`.

## Main results

- `AlgebraicGeometry.ValuativeCommSqWithPt` and
  `AlgebraicGeometry.ValuativeCommSqWithPt.ofIsDominant`: the **valuation probe through a
  dense source** (Stacks Project Tag 02JQ; blueprint: `def:nagata-dense-valuation-probe`,
  `lemma:nagata-dense-valuation-probe`).
- `AlgebraicGeometry.ValuativeCriterion.RelativeTo`: the dense-source lifting hypothesis.
- `AlgebraicGeometry.ValuativeCriterion.RelativeTo.existence_of_isDominant`: the
  **dense-source valuative criterion** (Stacks Project Tag 0894; blueprint:
  `lemma:nagata-dense-source-valuative`), in the form of the existence part
  `AlgebraicGeometry.ValuativeCriterion.Existence`.
- `AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion_of_isDominant` and
  `AlgebraicGeometry.IsSeparated.of_valuativeCriterion_of_isDominant`: the two consequences
  of the criterion.

The valuation-theoretic inputs live in the Mathlib helper files: the composite of two
valuation rings `ValuationSubring.comapResidue` (blueprint:
`lemma:nagata-composite-valuation-ring`), the intersection with a dominating valuation
ring `ValuationSubring.comap_eq_of_toLocalSubring_le` (Stacks Tag 052K; blueprint:
`lemma:nagata-valuation-intersection`) and the extension of a valuation ring along a field
extension `ValuationSubring.exists_comap_eq` (Stacks Tag 00IA).

## Implementation notes

The criterion is proved in the form `ValuativeCriterion.Existence f`, which applies more
widely than `UniversallyClosed f`: Mathlib's `UniversallyClosed.eq_valuativeCriterion` reads
`UniversallyClosed = ValuativeCriterion.Existence ⊓ QuasiCompact`, so the existence form
needs no quasi-compactness of `f`, and it is stable under base change. The two named
consequences are read off from it.

Two reductions differ from the Stacks Project text. Instead of replacing `U`, `X` and `S`
by their reductions, `h` is factored through its scheme-theoretic image — `h.toImage` is
scheme-theoretically dominant with no reducedness hypothesis, and morphisms from reduced
schemes factor through the image by
`Scheme.IdealSheafData.le_ker_iff_range_subset_support`. And the base is localized to an
affine chart using that `ValuativeCriterion.Existence` is local at the target, rather than
by hand.

## References

* [Stacks Project, Tags 02JQ and 0894](https://stacks.math.columbia.edu/tag/0894)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

/-- A **valuative commutative square centred at a point** `z ∈ P` of a morphism
`h : T ⟶ P`: a valuative commutative square for `h` whose valuation-ring leg takes the
closed point of `Spec R` to `z`. It is the *valuation probe* of Stacks Project Tag 02JQ.
(Blueprint: `def:nagata-dense-valuation-probe`.) -/
structure ValuativeCommSqWithPt {T P : Scheme.{u}} (h : T ⟶ P) (z : P) extends
    ValuativeCommSq h where
  /-- The valuation-ring leg of the square is centred at `z`. -/
  closedPoint_eq : i₂ (closedPoint R) = z

/-- **A specialization of a point of the range gives a square centred at that point**: if
`h t` specializes to `z`, then `h` admits a valuative commutative square centred at `z`.

The square is the one Mathlib builds in `ValuativeCriterion.Existence.specializingMap`: the
stalk composite `𝒪_{P,z} ⟶ 𝒪_{T,t} ⟶ κ(t)` factors through a valuation subring `A ⊆ κ(t)`
by the Chevalley extension theorem `IsLocalRing.exists_factor_valuationRing`. -/
def ValuativeCommSqWithPt.ofSpecializes {T P : Scheme.{u}} (h : T ⟶ P) {t : T}
    {z : P} (ht : h t ⤳ z) : ValuativeCommSqWithPt h z := by
  let ρ : P.presheaf.stalk z ⟶ T.residueField t :=
    P.presheaf.stalkSpecializes ht ≫ h.stalkMap t ≫ T.residue t
  choose A hA hA_local using IsLocalRing.exists_factor_valuationRing ρ.hom
  let toA : P.presheaf.stalk z ⟶ .of A := CommRingCat.ofHom (ρ.hom.codRestrict _ hA)
  have w : T.fromSpecResidueField t ≫ h =
      Spec.map (CommRingCat.ofHom (algebraMap A (T.residueField t))) ≫
        Spec.map toA ≫ P.fromSpecStalk z := by
    rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk ht]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  have hclosed : Spec.map toA (closedPoint A) = closedPoint (P.presheaf.stalk z) :=
    IsLocalRing.comap_closedPoint (S := A) (ρ.hom.codRestrict A.toSubring hA)
  exact { R := A
          K := T.residueField t
          i₁ := T.fromSpecResidueField t
          i₂ := Spec.map toA ≫ P.fromSpecStalk z
          commSq := ⟨w⟩
          closedPoint_eq := by
            rw [Scheme.Hom.comp_apply, hclosed, Scheme.fromSpecStalk_closedPoint] }

/-- **A valuative commutative square through a dense source** (Stacks Project Tag 02JQ):
every point of the target of a quasi-compact dominant morphism is the centre of a valuative
commutative square.
(Blueprint: `lemma:nagata-dense-valuation-probe`.) -/
@[stacks 02JQ]
def ValuativeCommSqWithPt.ofIsDominant {T P : Scheme.{u}} (h : T ⟶ P)
    [QuasiCompact h] [IsDominant h] (z : P) : ValuativeCommSqWithPt h z := by
  have hz : z ∈ closure (Set.range h) := by
    rw [h.denseRange.closure_range]
    trivial
  choose t ht using exists_specializes_of_mem_closure_range h hz
  exact .ofSpecializes h ht

namespace ValuativeCriterion

variable {U X S : Scheme.{u}}

/-- `f : X ⟶ S` satisfies the **valuative criterion relative to `h : U ⟶ X`** if every
valuative commutative square for `f` whose generic point factors through `h` has a unique
lift. This is the hypothesis of the dense-source valuative criterion (Stacks Project
Tag 0894; blueprint: `lemma:nagata-dense-source-valuative`). -/
def RelativeTo (f : X ⟶ S) (h : U ⟶ X) : Prop :=
  ∀ (sq : ValuativeCommSq f) (ηU : Spec (CommRingCat.of sq.K) ⟶ U),
    ηU ≫ h = sq.i₁ → Nonempty (Unique sq.commSq.LiftStruct)

/-- The unique lift provided by `ValuativeCriterion.RelativeTo`, in `∃!` form. -/
theorem RelativeTo.existsUnique {f : X ⟶ S} {h : U ⟶ X} (H : RelativeTo f h)
    (sq : ValuativeCommSq f) {ηU : Spec (CommRingCat.of sq.K) ⟶ U} (hηU : ηU ≫ h = sq.i₁) :
    ∃! l : Spec (CommRingCat.of sq.R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁ ∧ l ≫ f = sq.i₂ := by
  obtain ⟨u⟩ := H sq ηU hηU
  refine ⟨u.default.l, ⟨u.default.fac_left, u.default.fac_right⟩, fun l hl ↦ ?_⟩
  exact congrArg CommSq.LiftStruct.l (u.uniq ⟨l, hl.1, hl.2⟩)

/-- `ValuativeCriterion.RelativeTo` from the `∃!` form of the lifting hypothesis. -/
theorem RelativeTo.of_existsUnique {f : X ⟶ S} {h : U ⟶ X}
    (H : ∀ (sq : ValuativeCommSq f) (ηU : Spec (CommRingCat.of sq.K) ⟶ U), ηU ≫ h = sq.i₁ →
      ∃! l : Spec (CommRingCat.of sq.R) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁ ∧ l ≫ f = sq.i₂) :
    RelativeTo f h := by
  intro sq ηU hηU
  obtain ⟨l, hl, huniq⟩ := H sq ηU hηU
  exact ⟨{ default := ⟨l, hl.1, hl.2⟩
           uniq := fun s ↦ CommSq.LiftStruct.ext (huniq s.l ⟨s.fac_left, s.fac_right⟩) }⟩

/-- The relative valuative criterion is unchanged by composing the base with an
isomorphism. -/
theorem RelativeTo.postcomp_iso {S' : Scheme.{u}} {f : X ⟶ S} {h : U ⟶ X}
    (H : RelativeTo f h) (e : S ⟶ S') [IsIso e] : RelativeTo (f ≫ e) h := by
  refine RelativeTo.of_existsUnique fun sq ηU hηU ↦ ?_
  obtain ⟨l, ⟨hl₁, hl₂⟩, huniq⟩ := H.existsUnique
    { R := sq.R
      K := sq.K
      i₁ := sq.i₁
      i₂ := sq.i₂ ≫ inv e
      commSq := ⟨by rw [← Category.assoc, ← sq.commSq.w, Category.assoc, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]⟩ } hηU
  have hl₂' : l ≫ f = sq.i₂ ≫ inv e := hl₂
  have huniq' (y : Spec (CommRingCat.of sq.R) ⟶ X)
      (hy : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ y = sq.i₁ ∧
        y ≫ f = sq.i₂ ≫ inv e) : y = l := huniq y hy
  refine ⟨l, ⟨hl₁, ?_⟩, fun y hy ↦ huniq' y ⟨hy.1, ?_⟩⟩
  · rw [← Category.assoc, hl₂', Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · rw [← hy.2, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The relative valuative criterion restricts to the preimage of an open of the base. -/
theorem RelativeTo.restrict {f : X ⟶ S} {h : U ⟶ X} (H : RelativeTo f h) (V : S.Opens) :
    RelativeTo (f ∣_ V) (h ∣_ (f ⁻¹ᵁ V)) := by
  refine RelativeTo.of_existsUnique fun sq ηU hηU ↦ ?_
  have hηU' : (ηU ≫ (h ⁻¹ᵁ f ⁻¹ᵁ V).ι) ≫ h = sq.i₁ ≫ (f ⁻¹ᵁ V).ι := by
    rw [Category.assoc, ← morphismRestrict_ι h (f ⁻¹ᵁ V), ← Category.assoc, hηU]
  obtain ⟨l, ⟨hl₁, hl₂⟩, huniq⟩ := H.existsUnique
    { R := sq.R
      K := sq.K
      i₁ := sq.i₁ ≫ (f ⁻¹ᵁ V).ι
      i₂ := sq.i₂ ≫ V.ι
      commSq := ⟨by
        rw [Category.assoc, ← morphismRestrict_ι f V, ← Category.assoc, sq.commSq.w,
          Category.assoc]⟩ }
    (ηU := ηU ≫ (h ⁻¹ᵁ f ⁻¹ᵁ V).ι) hηU'
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l =
      sq.i₁ ≫ (f ⁻¹ᵁ V).ι := hl₁
  have hl₂' : l ≫ f = sq.i₂ ≫ V.ι := hl₂
  have huniq' (y : Spec (CommRingCat.of sq.R) ⟶ X)
      (hy : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ y = sq.i₁ ≫ (f ⁻¹ᵁ V).ι ∧
        y ≫ f = sq.i₂ ≫ V.ι) : y = l := huniq y hy
  -- the lift lands in `f ⁻¹ᵁ V`, because its composite with `f` factors through `V`
  have hrange : Set.range l ⊆ ((f ⁻¹ᵁ V) : Set X) := by
    rintro - ⟨y, rfl⟩
    have hmem : f (l y) ∈ V := by
      rw [← Scheme.Hom.comp_apply, hl₂', Scheme.Hom.comp_apply]
      exact (sq.i₂ y).2
    exact hmem
  let l₂ : Spec (CommRingCat.of sq.R) ⟶ (f ⁻¹ᵁ V).toScheme :=
    IsOpenImmersion.lift (f ⁻¹ᵁ V).ι l (by rwa [Scheme.Opens.range_ι])
  have hl₂ι : l₂ ≫ (f ⁻¹ᵁ V).ι = l := IsOpenImmersion.lift_fac _ _ _
  refine ⟨l₂, ⟨?_, ?_⟩, fun y hy ↦ ?_⟩
  · refine (cancel_mono (f ⁻¹ᵁ V).ι).mp ?_
    rw [Category.assoc, hl₂ι, hl₁']
  · refine (cancel_mono V.ι).mp ?_
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl₂ι, hl₂']
  · refine (cancel_mono (f ⁻¹ᵁ V).ι).mp ?_
    rw [hl₂ι]
    refine huniq' _ ⟨?_, ?_⟩
    · rw [← Category.assoc, hy.1]
    · rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy.2]

variable (h : U ⟶ X) [QuasiCompact h] [IsDominant h]

/-- **A morphism from a reduced scheme factors through the scheme-theoretic image of a
quasi-compact dominant morphism**: its kernel contains the kernel of the image. -/
theorem ker_imageι_le_ker {Z : Scheme.{u}} [IsReduced Z] (l : Z ⟶ X) :
    h.imageι.ker ≤ l.ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.le_ker_iff_range_subset_support,
    Scheme.Hom.support_ker h, h.denseRange.closure_range]
  exact Set.subset_univ _

/-- The existence part of the valuative criterion descends from the scheme-theoretic image
of a quasi-compact dominant morphism. -/
theorem Existence.of_imageι {f : X ⟶ S} (H : Existence (h.imageι ≫ f)) : Existence f := by
  intro sq
  let i₁' := IsClosedImmersion.lift h.imageι sq.i₁ (ker_imageι_le_ker h sq.i₁)
  have hi₁' : i₁' ≫ h.imageι = sq.i₁ := IsClosedImmersion.lift_fac _ _ _
  obtain ⟨l, hl₁, hl₂⟩ := (H { R := sq.R
                               K := sq.K
                               i₁ := i₁'
                               i₂ := sq.i₂
                               commSq := ⟨by
                                 rw [← Category.assoc, hi₁', sq.commSq.w]⟩ }).exists_lift
  refine ⟨⟨⟨l ≫ h.imageι, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, hl₁, hi₁']
  · rw [Category.assoc, hl₂]

/-- The relative valuative criterion transfers to the scheme-theoretic image of a
quasi-compact dominant morphism. -/
theorem RelativeTo.toImage {f : X ⟶ S} (H : RelativeTo f h) :
    RelativeTo (h.imageι ≫ f) h.toImage := by
  refine RelativeTo.of_existsUnique fun sq ηU hηU ↦ ?_
  have hηU' : ηU ≫ h = sq.i₁ ≫ h.imageι := by
    rw [← hηU, Category.assoc, Scheme.Hom.toImage_imageι]
  obtain ⟨l, ⟨hl₁, hl₂⟩, huniq⟩ := H.existsUnique
    { R := sq.R
      K := sq.K
      i₁ := sq.i₁ ≫ h.imageι
      i₂ := sq.i₂
      commSq := ⟨by rw [Category.assoc, sq.commSq.w]⟩ } (ηU := ηU) hηU'
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l =
      sq.i₁ ≫ h.imageι := hl₁
  have hl₂' : l ≫ f = sq.i₂ := hl₂
  have huniq' (y : Spec (CommRingCat.of sq.R) ⟶ X)
      (hy : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ y = sq.i₁ ≫ h.imageι ∧
        y ≫ f = sq.i₂) : y = l := huniq y hy
  let l' := IsClosedImmersion.lift h.imageι l (ker_imageι_le_ker h l)
  have hl' : l' ≫ h.imageι = l := IsClosedImmersion.lift_fac _ _ _
  refine ⟨l', ⟨?_, ?_⟩, fun y hy ↦ ?_⟩
  · refine (cancel_mono h.imageι).mp ?_
    rw [Category.assoc, hl', hl₁']
  · rw [← Category.assoc, hl', hl₂']
  · refine (cancel_mono h.imageι).mp ?_
    rw [hl']
    refine huniq' _ ⟨?_, ?_⟩
    · rw [← Category.assoc, hy.1]
    · rw [Category.assoc, hy.2]

end ValuativeCriterion

/-- **Flat polynomial presentation of a morphism from the spectrum of a field**: every
morphism `Spec K ⟶ X` with `K` a field factors as a surjection `P ↠ K` followed by a flat
morphism `Spec P ⟶ X`.

The presentation takes for `P` the polynomial `Γ(X, V)`-algebra on variables indexed by the
underlying set of `K`, where `V` is an affine open containing the image of the point. The
surjection `P ↠ K` sends a variable `X k` to `k` and acts on coefficients through the ring map
`Γ(X, V) ⟶ K` defining the point, and the flatness is that of `algebraMap Γ(X, V) P`. -/
theorem exists_flat_polynomial_presentation {X : Scheme.{u}} {K : Type u} [Field K]
    (i₁ : Spec (CommRingCat.of K) ⟶ X) :
    ∃ (P : CommRingCat.{u}) (π : P ⟶ CommRingCat.of K) (p : Spec P ⟶ X),
      Function.Surjective π.hom ∧ Flat p ∧ Spec.map π ≫ p = i₁ := by
  -- the field structure on the bundled ring is needed for `closedPoint` and for
  -- `Subsingleton (Spec (CommRingCat.of K))`
  let : Field (CommRingCat.of K) := inferInstanceAs (Field K)
  obtain ⟨V, hV, hx₀V, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := i₁ (closedPoint (CommRingCat.of K))) trivial
  have hrange : Set.range i₁ ⊆ (V : Set X) := by
    rintro - ⟨y, rfl⟩
    rw [Subsingleton.elim y (closedPoint (CommRingCat.of K))]
    exact hx₀V
  let j : Spec (CommRingCat.of K) ⟶ V :=
    IsOpenImmersion.lift V.ι i₁ (by rwa [Scheme.Opens.range_ι])
  have hj : j ≫ V.ι = i₁ := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(X, V) ⟶ CommRingCat.of K := Spec.preimage (j ≫ hV.isoSpec.hom)
  have hφ : Spec.map φ ≫ hV.isoSpec.inv ≫ V.ι = i₁ := by
    rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc, hj]
  refine ⟨CommRingCat.of (MvPolynomial K ↥Γ(X, V)),
    CommRingCat.ofHom (MvPolynomial.eval₂Hom φ.hom id),
    Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(X, V) (MvPolynomial K ↥Γ(X, V)))) ≫
      hV.isoSpec.inv ≫ V.ι, fun k ↦ ⟨MvPolynomial.X k, ?_⟩, ?_, ?_⟩
  · simp
  · have : Flat (Spec.map (CommRingCat.ofHom
        (algebraMap ↥Γ(X, V) (MvPolynomial K ↥Γ(X, V))))) :=
      Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
    infer_instance
  · have hcomp : (MvPolynomial.eval₂Hom φ.hom id).comp
        (algebraMap ↥Γ(X, V) (MvPolynomial K ↥Γ(X, V))) = φ.hom :=
      MvPolynomial.eval₂Hom_comp_C _ _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp,
      CommRingCat.ofHom_hom, hφ]

/-- **Stalk comparison at a generic point**: let `B` be a valuation subring of a field `L`,
let `g : Spec B ⟶ X` and let `i₁ : Spec K ⟶ X` be a field point such that the generic
point of `Spec B` is `i₁` base-changed along `τ : K →+* L`. Then the closed-point stalk
map of `i₁`, transported along the resulting specialization, is a map `𝒪_{X, g(𝔪_B)} ⟶ K`
inducing `i₁`, and `τ` carries it into `B`. -/
theorem exists_stalkClosedPointTo_of_generic_eq {X : Scheme.{u}} {K L : Type u} [Field K]
    [Field L] (B : ValuationSubring L) (τ : K →+* L) (i₁ : Spec (CommRingCat.of K) ⟶ X)
    (g : Spec (CommRingCat.of ↥B) ⟶ X)
    (hI : Spec.map (CommRingCat.ofHom B.subtype) ≫ g =
      Spec.map (CommRingCat.ofHom τ) ≫ i₁) :
    ∃ κ : X.presheaf.stalk (g (closedPoint ↥B)) ⟶ CommRingCat.of K,
      Spec.map κ ≫ X.fromSpecStalk (g (closedPoint ↥B)) = i₁ ∧ ∀ s, τ (κ.hom s) ∈ B := by
  -- the field structures on the bundled rings are needed for `closedPoint`
  let : Field (CommRingCat.of K) := inferInstanceAs (Field K)
  let : Field (CommRingCat.of L) := inferInstanceAs (Field L)
  have : IsLocalHom (CommRingCat.ofHom τ).hom := inferInstanceAs (IsLocalHom τ)
  -- the generic point of `Spec B` is carried by `g` to the `K`-point
  have hgen : g (Spec.map (CommRingCat.ofHom B.subtype) (closedPoint (CommRingCat.of L))) =
      i₁ (closedPoint (CommRingCat.of K)) := by
    rw [← Scheme.Hom.comp_apply, hI, Scheme.Hom.comp_apply, Spec_closedPoint]
  have hspec : i₁ (closedPoint (CommRingCat.of K)) ⤳ g (closedPoint ↥B) := by
    rw [← hgen]
    exact (specializes_closedPoint _).map g.continuous
  refine ⟨X.presheaf.stalkSpecializes hspec ≫ Scheme.stalkClosedPointTo i₁, ?_, fun s ↦ ?_⟩
  · rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk hspec,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk i₁]
  set κ : X.presheaf.stalk (g (closedPoint ↥B)) ⟶ CommRingCat.of K :=
    X.presheaf.stalkSpecializes hspec ≫ Scheme.stalkClosedPointTo i₁ with hκdef
  have hκSpec : Spec.map κ ≫ X.fromSpecStalk (g (closedPoint ↥B)) = i₁ := by
    rw [hκdef, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hspec,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk i₁]
  clear_value κ
  -- the master identity: `τ ∘ κ` is the closed-point stalk map of `g`
  have hMspec : Spec.map (κ ≫ CommRingCat.ofHom τ) ≫
        X.fromSpecStalk (g (closedPoint ↥B)) =
      Spec.map (Scheme.stalkClosedPointTo g ≫ CommRingCat.ofHom B.subtype) ≫
        X.fromSpecStalk (g (closedPoint ↥B)) := by
    simp only [Spec.map_comp, Category.assoc]
    rw [hκSpec, Scheme.Spec_stalkClosedPointTo_fromSpecStalk g]
    exact hI.symm
  have hM : κ ≫ CommRingCat.ofHom τ =
      Scheme.stalkClosedPointTo g ≫ CommRingCat.ofHom B.subtype :=
    Spec.map_injective ((cancel_mono _).mp hMspec)
  have hs : τ (κ.hom s) = B.subtype ((Scheme.stalkClosedPointTo g).hom s) := by
    have hM' := congrArg
      (fun (u : X.presheaf.stalk (g (closedPoint ↥B)) ⟶ CommRingCat.of L) ↦ u.hom s) hM
    simpa using hM'
  rw [hs]
  exact ((Scheme.stalkClosedPointTo g).hom s).2

namespace ValuativeCriterion

variable {U X : Scheme.{u}}

/-- **The dense-source valuative criterion over an affine base** (Stacks Project Tag 0894):
if `h : U ⟶ X` is quasi-compact and scheme-theoretically dominant and `f : X ⟶ Spec R`
satisfies the valuative criterion relative to `h`, then `f` satisfies the existence part of
the valuative criterion. -/
theorem RelativeTo.existence_of_isSchemeTheoreticallyDominant_of_isAffine
    {R : CommRingCat.{u}} {f : X ⟶ Spec R} {h : U ⟶ X} [QuasiCompact h]
    [IsSchemeTheoreticallyDominant h] (H : RelativeTo f h) : Existence f := by
  intro sqf
  obtain ⟨A, K, i₁, i₂, ⟨w⟩⟩ := sqf
  -- `obtain` loses the field instance on the bundled ring, which `closedPoint` needs
  let : Field (CommRingCat.of K) := inferInstanceAs (Field K)
  -- Step 1: a flat polynomial presentation `p : Spec P ⟶ X` of the `K`-point `i₁`
  obtain ⟨P, π, p, hπ, hpflat, hi₁p⟩ := exists_flat_polynomial_presentation i₁
  have : Flat p := hpflat
  -- Step 2: a valuative square for `U ×_X Spec P ⟶ Spec P` centred at the image of `i₁`
  have : QuasiCompact (pullback.snd h p) := MorphismProperty.pullback_snd _ _ inferInstance
  let pr := ValuativeCommSqWithPt.ofIsDominant (pullback.snd h p)
    (Spec.map π (closedPoint (CommRingCat.of K)))
  clear_value pr
  -- Step 3: replace the abstract valuation ring of `pr` by its image in `pr.K`
  let VA' : ValuationSubring pr.K := (ValuationRing.valuation pr.R pr.K).valuationSubring
  let e' : pr.R ≃+* ↥VA' := ValuationRing.equivInteger pr.R pr.K
  have : IsLocalHom (e' : pr.R →+* ↥VA') := ⟨fun a ha ↦ by
    simpa using ha.map e'.symm.toRingHom⟩
  let αV : Spec (CommRingCat.of ↥VA') ⟶ Spec P :=
    Spec.map (CommRingCat.ofHom (e' : pr.R →+* ↥VA')) ≫ pr.i₂
  have halg : CommRingCat.ofHom (e' : pr.R →+* ↥VA') ≫
      CommRingCat.ofHom (algebraMap ↥VA' pr.K) =
      CommRingCat.ofHom (algebraMap pr.R pr.K) := by
    ext a
    rfl
  have hprobe : pr.i₁ ≫ pullback.snd h p =
      Spec.map (CommRingCat.ofHom (algebraMap ↥VA' pr.K)) ≫ αV := by
    rw [pr.commSq.w, ← Category.assoc, ← Spec.map_comp, halg]
  have hclosed : αV (closedPoint ↥VA') = Spec.map π (closedPoint (CommRingCat.of K)) := by
    have hcp : Spec.map (CommRingCat.ofHom (e' : pr.R →+* ↥VA')) (closedPoint ↥VA') =
        closedPoint pr.R := IsLocalRing.comap_closedPoint _
    rw [Scheme.Hom.comp_apply, hcp, pr.closedPoint_eq]
  -- Step 4: descend the residue map of `VA'` to a field embedding `τ : K → κ(VA')`
  let ρ : P ⟶ CommRingCat.of ↥VA' := Spec.preimage αV
  have hρ : Spec.map ρ = αV := Spec.map_preimage _
  have hker (a : P) (ha : a ∈ RingHom.ker π.hom) : ρ.hom a ∈ maximalIdeal ↥VA' := by
    have hmem : Spec.map π (closedPoint (CommRingCat.of K)) ∈
        PrimeSpectrum.zeroLocus {a} := by
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      refine Ideal.mem_comap.mpr ?_
      rw [RingHom.mem_ker] at ha
      rw [ha]
      exact zero_mem _
    rw [← hclosed, ← hρ] at hmem
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hmem
    exact hmem
  obtain ⟨τ, hτπ⟩ := IsLocalRing.exists_comp_eq_residue_comp hπ ρ.hom hker
  -- Step 5: extend the valuation ring `A ⊆ K` along `τ` and form the composite
  let VA : ValuationSubring K := (ValuationRing.valuation A K).valuationSubring
  obtain ⟨A'', hA''⟩ := ValuationSubring.exists_comap_eq τ VA
  let C : ValuationSubring pr.K := VA'.comapResidue A''
  let ιC : ↥C →+* ↥VA' := ValuationSubring.inclusion _ _ (VA'.comapResidue_le A'')
  -- Step 6: the square through `U` for the composite valuation ring `C`
  let ψ : R ⟶ CommRingCat.of A := Spec.preimage i₂
  have hψ : Spec.map ψ = i₂ := Spec.map_preimage _
  let pre : R ⟶ P := Spec.preimage (p ≫ f)
  have hpre : Spec.map pre = p ≫ f := Spec.map_preimage _
  let θ : ↥R →+* ↥VA' := ρ.hom.comp pre.hom
  have hπpre : pre ≫ π = ψ ≫ CommRingCat.ofHom (algebraMap A K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hpre, hψ, ← Category.assoc, hi₁p, w]
  have hθmem (r : ↥R) : residue ↥VA' (θ r) ∈ A'' := by
    have hres : residue ↥VA' (θ r) = τ (π.hom (pre.hom r)) := by
      have hτ := congrArg (fun u : ↑P →+* ResidueField ↥VA' ↦ u (pre.hom r)) hτπ
      simpa [θ] using hτ.symm
    have hval : π.hom (pre.hom r) = algebraMap A K (ψ.hom r) :=
      congrArg (fun (u : R ⟶ CommRingCat.of K) ↦ u.hom r) hπpre
    have hmem : algebraMap A K (ψ.hom r) ∈ VA :=
      (ValuationRing.mem_integer_iff A K _).mpr ⟨ψ.hom r, rfl⟩
    rw [← hA''] at hmem
    rw [hres, hval]
    exact hmem
  let γ : ↥R →+* ↥C := ((algebraMap ↥VA' pr.K).comp θ).codRestrict C
    (fun r ↦ (VA'.mem_comapResidue A'').mpr ⟨(θ r).2, hθmem r⟩)
  have hγθ : Spec.map (CommRingCat.ofHom (algebraMap ↥C pr.K)) ≫
      Spec.map (CommRingCat.ofHom γ) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥VA' pr.K)) ≫
        Spec.map (CommRingCat.ofHom θ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
  have hθspec : Spec.map (CommRingCat.ofHom θ) = αV ≫ p ≫ f := by
    have hθdef : CommRingCat.ofHom θ = pre ≫ ρ := rfl
    rw [hθdef, Spec.map_comp, hρ, hpre]
  have hηθ : Spec.map (CommRingCat.ofHom (algebraMap ↥VA' pr.K)) ≫
      Spec.map (CommRingCat.ofHom θ) = (pr.i₁ ≫ pullback.fst h p ≫ h) ≫ f := by
    rw [hθspec, ← reassoc_of% hprobe, ← pullback.condition_assoc]
    simp only [Category.assoc]
  let sqC : ValuativeCommSq f :=
    { R := ↥C
      K := pr.K
      i₁ := pr.i₁ ≫ pullback.fst h p ≫ h
      i₂ := Spec.map (CommRingCat.ofHom γ)
      commSq := ⟨by rw [hγθ, hηθ]⟩ }
  obtain ⟨gC, ⟨hgC1, hgC2⟩, -⟩ :=
    H.existsUnique sqC (ηU := pr.i₁ ≫ pullback.fst h p) (Category.assoc _ _ _)
  -- Step 7: uniqueness over `VA'` identifies the two maps `Spec VA' ⟶ X`
  let sq' : ValuativeCommSq f :=
    { R := ↥VA'
      K := pr.K
      i₁ := pr.i₁ ≫ pullback.fst h p ≫ h
      i₂ := αV ≫ p ≫ f
      commSq := ⟨by rw [← hηθ, hθspec]⟩ }
  obtain ⟨l', -, hl'uniq⟩ :=
    H.existsUnique sq' (ηU := pr.i₁ ≫ pullback.fst h p) (Category.assoc _ _ _)
  have hE : Spec.map (CommRingCat.ofHom ιC) ≫ gC = αV ≫ p := by
    have halgιC : (algebraMap ↥VA' pr.K).comp ιC = algebraMap ↥C pr.K := rfl
    have hιCγ : ιC.comp γ = θ := RingHom.ext fun _ ↦ rfl
    have hαp : αV ≫ p = l' := hl'uniq (αV ≫ p) ⟨by
      rw [← Category.assoc, ← hprobe, Category.assoc, ← pullback.condition], rfl⟩
    have hCl : Spec.map (CommRingCat.ofHom ιC) ≫ gC = l' := by
      refine hl'uniq _ ⟨?_, ?_⟩
      · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, halgιC]
        exact hgC1
      · rw [Category.assoc, hgC2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιCγ, hθspec]
    rw [hCl, ← hαp]
  -- Step 8: restrict `gC` along the closed immersion `Spec A'' ⟶ Spec C`
  let rr : ↥C →+* ↥A'' := VA'.residueRestrict A''
  let g'' : Spec (CommRingCat.of ↥A'') ⟶ X := Spec.map (CommRingCat.ofHom rr) ≫ gC
  have hcomm : ρ ≫ CommRingCat.ofHom (residue ↥VA') = π ≫ CommRingCat.ofHom τ := by
    apply CommRingCat.hom_ext
    simpa using hτπ.symm
  have hI : Spec.map (CommRingCat.ofHom A''.subtype) ≫ g'' =
      Spec.map (CommRingCat.ofHom τ) ≫ i₁ := by
    have hg''def : g'' = Spec.map (CommRingCat.ofHom rr) ≫ gC := rfl
    have hsubrr : (A''.subtype).comp rr = (residue ↥VA').comp ιC := rfl
    rw [hg''def, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hsubrr,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hE, ← hρ, ← Category.assoc,
      ← Spec.map_comp, hcomm, Spec.map_comp, Category.assoc, hi₁p]
  -- from here on only the established equations matter, so the constructed data is made
  -- opaque to keep unification from unfolding it
  clear_value g'' rr ιC C γ θ pre ψ ρ αV e' VA'
  -- Step 9: the stalk comparison produces a map `𝒪_{X, g''(𝔪)} ⟶ K` landing in `A`
  obtain ⟨κ, hκSpec, hκmem⟩ := exists_stalkClosedPointTo_of_generic_eq A'' τ i₁ g'' hI
  -- `VA` is by definition the valuation subring of `valuation A K`, but bridging to
  -- `.integer` pointwise rather than at the `∀` is a prohibitively expensive defeq check
  have hκVA : ∀ s, κ.hom s ∈ VA := fun s ↦ by
    rw [← hA'']
    exact hκmem s
  have hκint : ∀ s, κ.hom s ∈ (ValuationRing.valuation A K).integer := hκVA
  let φl : X.presheaf.stalk (g'' (closedPoint ↥A'')) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom ((ValuationRing.equivInteger A K).symm.toRingHom.comp
      (κ.hom.codRestrict (ValuationRing.valuation A K).integer hκint))
  have hφκ : φl ≫ CommRingCat.ofHom (algebraMap A K) = κ := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun s ↦ ?_
    have hcoe := ValuationRing.coe_equivInteger_apply A K
      ((ValuationRing.equivInteger A K).symm ⟨κ.hom s, hκint s⟩)
    rw [RingEquiv.apply_symm_apply] at hcoe
    exact hcoe.symm
  clear_value φl
  have hl1 : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫
      (Spec.map φl ≫ X.fromSpecStalk (g'' (closedPoint ↥A''))) = i₁ := by
    rw [← Category.assoc, ← Spec.map_comp, hφκ, hκSpec]
  have hl2 : (Spec.map φl ≫ X.fromSpecStalk (g'' (closedPoint ↥A''))) ≫ f = i₂ := by
    have hmono : Mono (CommRingCat.ofHom (algebraMap A K)) :=
      (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr
        (IsFractionRing.injective A K)
    have hpreeq : Spec.preimage
        ((Spec.map φl ≫ X.fromSpecStalk (g'' (closedPoint ↥A''))) ≫ f) = ψ := by
      refine (cancel_mono (CommRingCat.ofHom (algebraMap A K))).mp (Spec.map_injective ?_)
      rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, hψ, ← Category.assoc, hl1, w]
    rw [← Spec.map_preimage
      ((Spec.map φl ≫ X.fromSpecStalk (g'' (closedPoint ↥A''))) ≫ f), hpreeq, hψ]
  exact ⟨⟨⟨_, hl1, hl2⟩⟩⟩

variable {S : Scheme.{u}}

/-- **The dense-source valuative criterion, scheme-theoretically dominant source** (Stacks
Project Tag 0894): the affine-base case
`ValuativeCriterion.RelativeTo.existence_of_isSchemeTheoreticallyDominant_of_isAffine`
globalizes, since `ValuativeCriterion.Existence` is local at the target. -/
theorem RelativeTo.existence_of_isSchemeTheoreticallyDominant {f : X ⟶ S} {h : U ⟶ X}
    [QuasiCompact h] [IsSchemeTheoreticallyDominant h] (H : RelativeTo f h) :
    Existence f := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := Existence)
    (fun V : S.affineOpens ↦ V.1) (iSup_affineOpens_eq_top S) fun V ↦ ?_
  have : IsAffine V.1.toScheme := V.2
  have : QuasiCompact (h ∣_ (f ⁻¹ᵁ V.1)) :=
    IsZariskiLocalAtTarget.restrict (P := @QuasiCompact) inferInstance _
  have : IsSchemeTheoreticallyDominant (h ∣_ (f ⁻¹ᵁ V.1)) :=
    .of_isPullback (isPullback_morphismRestrict h (f ⁻¹ᵁ V.1)).flip
  rw [← MorphismProperty.cancel_right_of_respectsIso Existence _ V.2.isoSpec.hom]
  exact ((H.restrict V.1).postcomp_iso
    V.2.isoSpec.hom).existence_of_isSchemeTheoreticallyDominant_of_isAffine

/-- **The dense-source valuative criterion** (Stacks Project Tag 0894): if `h : U ⟶ X` is
quasi-compact and dominant and every valuative square for `f : X ⟶ S` whose generic point
factors through `h` has a unique lift, then `f` satisfies the existence part of the
valuative criterion.
(Blueprint: `lemma:nagata-dense-source-valuative`.) -/
@[stacks 0894]
theorem RelativeTo.existence_of_isDominant {f : X ⟶ S} {h : U ⟶ X} [QuasiCompact h]
    [IsDominant h] (H : RelativeTo f h) : Existence f :=
  Existence.of_imageι h H.toImage.existence_of_isSchemeTheoreticallyDominant

end ValuativeCriterion

/-- **The dense-source valuative criterion, universal closedness** (Stacks Project
Tag 0894): a quasi-compact morphism satisfying the valuative criterion relative to a
quasi-compact dominant `h : U ⟶ X` is universally closed.
(Blueprint: `lemma:nagata-dense-source-valuative`.) -/
@[stacks 0894]
theorem UniversallyClosed.of_valuativeCriterion_of_isDominant {U X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] (h : U ⟶ X) [QuasiCompact h] [IsDominant h]
    (H : ValuativeCriterion.RelativeTo f h) : UniversallyClosed f :=
  UniversallyClosed.of_valuativeCriterion _ H.existence_of_isDominant

/-- **The dense-source valuative criterion, separatedness** (Stacks Project Tag 0894;
blueprint: `lemma:nagata-dense-source-valuative`).

The uniqueness half of the hypothesis makes the diagonal satisfy the dense-source criterion
for universal closedness, and a universally closed immersion is a closed immersion. -/
@[stacks 0894]
theorem IsSeparated.of_valuativeCriterion_of_isDominant {U X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiSeparated f] (h : U ⟶ X) [QuasiCompact h] [IsDominant h]
    (H : ValuativeCriterion.RelativeTo f h) : IsSeparated f := by
  constructor
  have : UniversallyClosed (pullback.diagonal f) := by
    refine UniversallyClosed.of_valuativeCriterion_of_isDominant (pullback.diagonal f) h ?_
    refine ValuativeCriterion.RelativeTo.of_existsUnique fun sq ηU hηU ↦ ?_
    -- a square for the diagonal is a pair of maps to `X` agreeing over `S`; the
    -- uniqueness hypothesis for `f` forces the pair to coincide
    have hfst : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫
        (sq.i₂ ≫ pullback.fst f f) = sq.i₁ := by
      rw [← Category.assoc, ← sq.commSq.w, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    have hsnd : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫
        (sq.i₂ ≫ pullback.snd f f) = sq.i₁ := by
      rw [← Category.assoc, ← sq.commSq.w, Category.assoc, pullback.diagonal_snd,
        Category.comp_id]
    obtain ⟨l₀, -, hl₀uniq⟩ := H.existsUnique
      { R := sq.R
        K := sq.K
        i₁ := sq.i₁
        i₂ := sq.i₂ ≫ pullback.fst f f ≫ f
        commSq := ⟨by
          rw [← hfst]
          simp only [Category.assoc]⟩ } hηU
    have hl₀uniq' (y : Spec (CommRingCat.of sq.R) ⟶ X)
        (hy : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ y = sq.i₁ ∧
          y ≫ f = sq.i₂ ≫ pullback.fst f f ≫ f) : y = l₀ := hl₀uniq y hy
    have hfst' : sq.i₂ ≫ pullback.fst f f = l₀ := hl₀uniq' _ ⟨hfst, Category.assoc _ _ _⟩
    have hsnd' : sq.i₂ ≫ pullback.snd f f = l₀ := by
      refine hl₀uniq' _ ⟨hsnd, ?_⟩
      rw [Category.assoc, ← pullback.condition]
    refine ⟨sq.i₂ ≫ pullback.fst f f, ⟨hfst, ?_⟩, fun y hy ↦ ?_⟩
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hfst', hsnd']
    · rw [← hy.2, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  exact IsClosedImmersion.of_isPreimmersion _
    (pullback.diagonal f).isClosedMap.isClosed_range

/-- **The dense-source valuative criterion, properness** (Stacks Project Tag 0894;
blueprint: `proposition-compactifying-union-two-opens--1`):
a quasi-compact, quasi-separated morphism locally of finite type satisfying the valuative
criterion relative to a quasi-compact dominant `h : U ⟶ X` is proper. -/
@[stacks 0894]
theorem IsProper.of_valuativeCriterion_of_isDominant {U X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f] (h : U ⟶ X) [QuasiCompact h]
    [IsDominant h] (H : ValuativeCriterion.RelativeTo f h) : IsProper f :=
  have := IsSeparated.of_valuativeCriterion_of_isDominant f h H
  have := UniversallyClosed.of_valuativeCriterion_of_isDominant f h H
  { }

end AlgebraicGeometry
