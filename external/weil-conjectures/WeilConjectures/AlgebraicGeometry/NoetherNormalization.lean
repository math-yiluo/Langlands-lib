/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization

/-!
# Generic relative Noether normalization

Noether normalization says that a finitely generated algebra over a field is finite over a
polynomial subalgebra. This file states the relative, generic form of that statement for schemes: a
dominant affine morphism `f : X ⟶ Y` of finite type between integral schemes whose generic fibre
has dimension `r` becomes, after shrinking `Y` to a dense open `V` and replacing `X` by `f ⁻¹ᵁ V`, a
finite surjective morphism to the `r`-fold relative affine line over `V` followed by the projection
to `V`.

Recording the target as `AlgebraicGeometry.iteratedAffineLine V r` rather than as the relative
affine space `𝔸(ULift (Fin r); V)` is what makes the statement usable in the Deligne–Laumon
reduction: the projection is then literally a composition of `r` affine-line projections, each of
which can be fed to the relative affine-line bound one at a time, as the blueprint node requires.

## Implementation notes

The blueprint derives this statement from a purely ring-theoretic one,
`lemma-relative-noether-normalization-over-stratification--1` ("spreading affine normalization to a
principal open"): for a domain `A` and a finitely generated `A`-algebra `B` there are `0 ≠ s ∈ A`,
`d ≥ 0` and coordinates `t ∈ (B_s)^d` making `A_s[t] → B_s` finite. It is
`Algebra.FiniteType.exists_finite_aeval_away` in
`WeilConjectures/Mathlib/RingTheory/NoetherNormalization.lean`; the coordinates map of blueprint
`lemma-relative-noether-normalization-over-stratification--1` is
`AlgebraicGeometry.Scheme.Hom.toIteratedAffineLine`.

## Main statements

- `AlgebraicGeometry.exists_isFinite_toIteratedAffineLine_basicOpen`: Noether normalization over a
  principal open of an affine open of an integral base.
- `AlgebraicGeometry.exists_dense_isFinite_toIteratedAffineLine`: the generic relative Noether
  normalization (blueprint `lemma-relative-noether-normalization-over-stratification`).
- `AlgebraicGeometry.Scheme.exists_partition_isImmersion_isAffine_isReduced`: a quasi-compact
  scheme has a finite partition by reduced affine locally closed subschemes (blueprint
  `lemma-relative-noether-normalization-over-stratification--1`).
- `AlgebraicGeometry.exists_partition_isFinite_toIteratedAffineLine`: relative Noether
  normalization over finite partitions of source and target (blueprint
  `lemma-relative-noether-normalization-over-stratification--1`).

## References

- [Stacks, Tag 07NA](https://stacks.math.columbia.edu/tag/07NA): for an injective finite-type ring
  map out of a domain `R`, a factorization `R → R[y₁, …, y_d] → S' → S` with `S'` finite over the
  polynomial ring and `S'_f ≅ S_f` for some nonzero `f ∈ R`. This is the ring-theoretic statement
  the lemma below globalises.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry

section Affine

variable {X S : Scheme.{u}} (g : X ⟶ S) [IsAffine X] [IsAffine S]

set_option backward.isDefEq.respectTransparency.types false in
/-- Coordinates `t` for which `Γ(X, ⊤)` is finite over `Γ(S, ⊤)[t]` give a finite morphism to the
iterated affine line. -/
lemma Scheme.Hom.isFinite_toIteratedAffineLine {r : ℕ} (t : Fin r → Γ(X, ⊤))
    (h : (eval₂Hom g.appTop.hom t).Finite) : IsFinite (g.toIteratedAffineLine t) := by
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
  refine ⟨inferInstance, ?_⟩
  rw [← toIteratedAffineLine_appTop_comp_evalCoord] at h
  exact RingHom.Finite.of_comp_finite h

/-- If moreover the coordinates `t` are algebraically independent over `Γ(S, ⊤)`, the morphism to
the iterated affine line is surjective (lying over). -/
lemma Scheme.Hom.surjective_toIteratedAffineLine {r : ℕ} (t : Fin r → Γ(X, ⊤))
    (hfin : (eval₂Hom g.appTop.hom t).Finite)
    (hinj : Function.Injective (eval₂Hom g.appTop.hom t)) :
    Surjective (g.toIteratedAffineLine t) := by
  set ν := g.toIteratedAffineLine t
  have hcomp := toIteratedAffineLine_appTop_comp_evalCoord g t
  have hνinj : Function.Injective ν.appTop.hom := by
    intro a b hab
    obtain ⟨p, rfl⟩ := iteratedAffineLine.evalCoord_surjective S r a
    obtain ⟨q, rfl⟩ := iteratedAffineLine.evalCoord_surjective S r b
    congr 1
    apply hinj
    rw [← hcomp]
    exact hab
  have hνfin : ν.appTop.hom.Finite := by
    rw [← hcomp] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hs := hνfin.to_isIntegral.comap_surjective hνinj
  have hν : ν = X.isoSpec.hom ≫ Spec.map ν.appTop ≫ (iteratedAffineLine S r).isoSpec.inv := by
    rw [Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have : Surjective (Spec.map ν.appTop) := ⟨hs⟩
  rw [hν]
  infer_instance

/-- The generic fibre of a morphism of affine schemes which is finite and injective over a
polynomial ring in `r` variables over the base has dimension `r`. -/
lemma Scheme.Hom.topologicalKrullDim_fiber_genericPoint [IsIntegral S]
    {r : ℕ} (t : Fin r → Γ(X, ⊤)) (hfin : (eval₂Hom g.appTop.hom t).Finite)
    (hinj : Function.Injective (eval₂Hom g.appTop.hom t)) :
    topologicalKrullDim (g.fiber (genericPoint S)) = r := by
  have hsq : IsPullback X.isoSpec.hom g (Spec.map g.appTop) S.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality g⟩
  rw [topologicalKrullDim_fiber_of_isPullback hsq, genericPoint_eq_of_isOpenImmersion,
    genericPoint_eq_bot_of_affine]
  let _ := g.appTop.hom.toAlgebra
  let e := Spec.fiberToSpecResidueFieldIso Γ(S, ⊤) Γ(X, ⊤) ⊥
  refine (IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.Hom.homeomorph e.hom.left).isHomeomorph).trans ?_
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans ?_
  have : IsFractionRing Γ(S, ⊤) (⊥ : PrimeSpectrum Γ(S, ⊤)).asIdeal.ResidueField :=
    inferInstanceAs (IsFractionRing Γ(S, ⊤) (⊥ : Ideal Γ(S, ⊤)).ResidueField)
  exact_mod_cast ringKrullDim_tensorProduct_eq_of_finite_inj_algHom_mvPolynomial _
    (aeval (R := Γ(S, ⊤)) t) hinj hfin

/-- Finiteness and injectivity of the evaluation of polynomials transfer along an isomorphism of
ring maps. -/
private lemma finite_injective_eval₂Hom_of_arrowIso {R S R' S' : CommRingCat.{u}} {φ : R ⟶ S}
    {φ' : R' ⟶ S'} (e : Arrow.mk φ' ≅ Arrow.mk φ) {r : ℕ} (t : Fin r → S)
    (hfin : (eval₂Hom φ.hom t).Finite) :
    (eval₂Hom φ'.hom fun i ↦ e.inv.right (t i)).Finite ∧
      (Function.Injective (eval₂Hom φ.hom t) →
        Function.Injective (eval₂Hom φ'.hom fun i ↦ e.inv.right (t i))) := by
  have hφ' : φ' = e.hom.left ≫ φ ≫ e.inv.right := by
    have := Arrow.w e.hom
    simp only [Arrow.mk_hom] at this
    rw [← Category.assoc, this, Category.assoc, Arrow.hom_inv_id_right, Category.comp_id]
  have key : eval₂Hom φ'.hom (fun i ↦ e.inv.right (t i)) =
      e.inv.right.hom.comp ((eval₂Hom φ.hom t).comp (MvPolynomial.map e.hom.left.hom)) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · change eval₂Hom φ'.hom _ (C a) =
        e.inv.right.hom (eval₂Hom φ.hom t (MvPolynomial.map e.hom.left.hom (C a)))
      rw [map_C, eval₂Hom_C]
      erw [eval₂Hom_C]
      exact congrArg (fun g ↦ g.hom a) hφ'
    · simp
  have hl : Function.Bijective e.hom.left.hom :=
    ConcreteCategory.bijective_of_isIso (Arrow.leftFunc.mapIso e).hom
  have hr : Function.Bijective e.inv.right.hom :=
    ConcreteCategory.bijective_of_isIso (Arrow.rightFunc.mapIso e).inv
  rw [key]
  refine ⟨RingHom.Finite.comp (RingHom.Finite.of_surjective _ hr.2)
    (RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ (map_surjective _ hl.2))),
    fun hinj ↦ hr.1.comp (hinj.comp (map_injective _ hl.1))⟩

end Affine

/-- Generic relative Noether normalization over a principal open of an affine open.

Let `f : X ⟶ Y` be an affine morphism locally of finite type to an integral scheme and `U` a
nonempty affine open of `Y`. Then there are `s₀ ≠ 0` in `Γ(Y, U)` and `d` such that over every
principal open `D(s) ⊆ U` with `s₀ ∣ s`, `s ≠ 0`, the restriction of `f` factors through a finite
morphism to the `d`-fold relative affine line. If `Γ(Y, U) → Γ(X, f⁻¹ U)` is injective, this finite
morphism is surjective and `d` is the dimension of the generic fibre.

This is the geometric form of `Algebra.FiniteType.exists_finite_aeval_away`
(blueprint `lemma-relative-noether-normalization-over-stratification--1`), using the coordinates of
blueprint `lemma-relative-noether-normalization-over-stratification--1`. -/
theorem exists_isFinite_toIteratedAffineLine_basicOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] [IsAffineHom f] [LocallyOfFiniteType f] {U : Y.Opens} (hU : IsAffineOpen U)
    [Nonempty U] :
    ∃ s₀ : Γ(Y, U), s₀ ≠ 0 ∧ ∃ d : ℕ, ∀ s : Γ(Y, U), s₀ ∣ s → s ≠ 0 →
      ∃ ν : (f ⁻¹ᵁ Y.basicOpen s).toScheme ⟶ iteratedAffineLine (Y.basicOpen s).toScheme d,
        IsFinite ν ∧ ν ≫ iteratedAffineLineProj (Y.basicOpen s).toScheme d = f ∣_ Y.basicOpen s ∧
        (Function.Injective (f.app U).hom → Surjective ν ∧
          topologicalKrullDim (f.fiber (genericPoint Y)) = d) := by
  classical
  have hfU : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let _ : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
    have := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance ⟨U, hU⟩
      ⟨_, hfU⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  obtain ⟨s₀, hs₀, d, t, H⟩ := Algebra.FiniteType.exists_finite_aeval_away Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
  refine ⟨s₀, hs₀, d, fun s hs₀s hs ↦ ?_⟩
  have hsY : (Y.basicOpen s : Set Y).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, Ne, TopologicalSpace.Opens.coe_eq_empty, basicOpen_eq_bot_iff]
    exact hs
  have hV : IsAffineOpen (Y.basicOpen s) := hU.basicOpen s
  have : Nonempty (Y.basicOpen s) := hsY.to_subtype
  have : IsAffine (f ⁻¹ᵁ Y.basicOpen s) := hV.preimage f
  have : IsAffine (Y.basicOpen s) := hV
  -- The rings of `V = D(s)` and `f ⁻¹ V` are the localizations `A_s` and `B_s`.
  let _ : Algebra Γ(Y, Y.basicOpen s) Γ(X, f ⁻¹ᵁ Y.basicOpen s) :=
    (f.app (Y.basicOpen s)).hom.toAlgebra
  have : IsLocalization.Away s Γ(Y, Y.basicOpen s) := hU.isLocalization_basicOpen s
  let inst : Algebra Γ(X, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ Y.basicOpen s) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le s))).op).hom.toAlgebra
  have : IsLocalization.Away (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U) s)
      Γ(X, f ⁻¹ᵁ Y.basicOpen s) := by
    let : Algebra Γ(X, f ⁻¹ᵁ U) Γ(X, X.basicOpen (f.app _ s)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst]
    rw! (castMode := .all) [f.preimage_basicOpen s]
    exact hfU.isLocalization_basicOpen (f.app _ s)
  let _ : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ Y.basicOpen s) :=
    (f.appLE _ _ (f.preimage_mono (Y.basicOpen_le _))).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ Y.basicOpen s) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U) Γ(Y, Y.basicOpen s) Γ(X, f ⁻¹ᵁ Y.basicOpen s) :=
    .of_algebraMap_eq' <| by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.map_appLE]
  obtain ⟨hfin, hinj⟩ := H s hs₀s hs Γ(Y, Y.basicOpen s) Γ(X, f ⁻¹ᵁ Y.basicOpen s)
  -- Transport to the global sections of the restriction `f ∣_ V`.
  let e := arrowResLEAppIso f (Y.basicOpen s) (f ⁻¹ᵁ Y.basicOpen s) le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at e
  obtain ⟨hfin', hinj'⟩ := finite_injective_eval₂Hom_of_arrowIso e
    (fun i ↦ algebraMap Γ(X, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ Y.basicOpen s) (t i)) hfin
  set g := f.resLE (Y.basicOpen s) (f ⁻¹ᵁ Y.basicOpen s) le_rfl with hg
  refine ⟨g.toIteratedAffineLine _, g.isFinite_toIteratedAffineLine _ hfin', ?_, fun hAB ↦ ?_⟩
  · rw [Scheme.Hom.toIteratedAffineLine_proj, hg, Scheme.Hom.resLE_eq_morphismRestrict]
  replace hinj' := hinj' (hinj hAB)
  refine ⟨g.surjective_toIteratedAffineLine _ hfin' hinj', ?_⟩
  -- The number of coordinates is the dimension of the generic fibre.
  have h := g.topologicalKrullDim_fiber_genericPoint _ hfin' hinj'
  rwa [hg, Scheme.Hom.resLE_eq_morphismRestrict,
    topologicalKrullDim_fiber_of_isPullback (isPullback_morphismRestrict f _).flip,
    genericPoint_eq_of_isOpenImmersion] at h

/-- Let `f : X ⟶ Y` be a dominant affine morphism of finite type between integral schemes whose
generic fibre has dimension `r`. Then there is a dense open `V ⊆ Y` over which `f` factors as a
finite surjective morphism `ν` to the `r`-fold relative affine line over `V` followed by its
projection to `V`:

```
f ⁻¹ᵁ V ----- ν -----> iteratedAffineLine V r
      \                        |
       \                       | iteratedAffineLineProj V r
    f ∣_ V                     |
         \                     v
          `----------------->  V
```

(blueprint: `lemma-relative-noether-normalization-over-stratification`). -/
@[stacks 07NA]
theorem exists_dense_isFinite_toIteratedAffineLine {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X]
    [IsIntegral Y] [IsAffineHom f] [LocallyOfFiniteType f] [IsDominant f] (r : ℕ)
    (hr : topologicalKrullDim (f.fiber (genericPoint Y)) = r) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧
      ∃ ν : (f ⁻¹ᵁ V).toScheme ⟶ iteratedAffineLine V.toScheme r,
        IsFinite ν ∧ Surjective ν ∧ ν ≫ iteratedAffineLineProj V.toScheme r = f ∣_ V := by
  classical
  -- A nonempty affine open `U = Spec A` of `Y`, with preimage `f ⁻¹ U = Spec B`.
  obtain ⟨U, hU, hηU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := genericPoint Y) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  -- `A → B` is injective since `f` is dominant.
  have hAB : Function.Injective (f.app U).hom := by
    refine (injective_iff_map_eq_zero _).mpr fun a ha ↦ ?_
    by_contra ha0
    have hne : (Y.basicOpen a : Set Y).Nonempty := by
      rw [Set.nonempty_iff_ne_empty, Ne, TopologicalSpace.Opens.coe_eq_empty,
        basicOpen_eq_bot_iff]
      exact ha0
    obtain ⟨x, hx⟩ := f.denseRange.exists_mem_open (Y.basicOpen a).isOpen hne
    have : x ∈ f ⁻¹ᵁ Y.basicOpen a := hx
    rw [Scheme.preimage_basicOpen, ha, Scheme.basicOpen_zero] at this
    exact this
  obtain ⟨s, hs, d, H⟩ := exists_isFinite_toIteratedAffineLine_basicOpen f hU
  obtain ⟨ν, hfin, hν, H'⟩ := H s dvd_rfl hs
  obtain ⟨hsurj, hdim⟩ := H' hAB
  -- The number of coordinates is the dimension of the generic fibre.
  rw [hr] at hdim
  obtain rfl : d = r := by exact_mod_cast hdim.symm
  have hsY : (Y.basicOpen s : Set Y).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, Ne, TopologicalSpace.Opens.coe_eq_empty, basicOpen_eq_bot_iff]
    exact hs
  exact ⟨Y.basicOpen s, (Y.basicOpen s).isOpen.dense hsY, ν, hfin, hsurj, hν⟩

/-- Blueprint `lemma-relative-noether-normalization-over-stratification--1`: a quasi-compact (e.g.
Noetherian) scheme `X` has a finite partition by locally closed reduced affine subschemes.

Choose a finite affine open cover `U₁, …, Uₙ` and take the `i`-th piece to be
`Uᵢ ∖ ⋃_{j < i} Uⱼ` with its reduced closed subscheme structure inside `Uᵢ`. Every point lies in
the piece indexed by the first `Uᵢ` containing it. -/
theorem Scheme.exists_partition_isImmersion_isAffine_isReduced (X : Scheme.{u})
    [CompactSpace X] :
    ∃ (n : ℕ) (Z : Fin n → Scheme.{u}) (ι : ∀ i, Z i ⟶ X),
      (∀ i, IsImmersion (ι i) ∧ IsAffine (Z i) ∧ IsReduced (Z i)) ∧
        ∀ x : X, ∃! i, x ∈ Set.range (ι i) := by
  classical
  -- A finite affine open cover `U₁, …, Uₙ` of `X`.
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U : Set X))
    (fun U ↦ U.1.isOpen) (by
      intro x _
      have : x ∈ (⨆ i : X.affineOpens, (i : X.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this)
  let n := s.card
  let U : Fin n → X.affineOpens := fun i ↦ (s.equivFin.symm i).1
  have hcov (x : X) : ∃ i, x ∈ (U i : X.Opens) := by
    obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨s.equivFin ⟨V, hV⟩, by simpa [U] using hx⟩
  -- The `i`-th piece is `Uᵢ ∖ ⋃_{j < i} Uⱼ`, with its reduced structure inside `Uᵢ`.
  let C : Fin n → Set X := fun i ↦ ⋂ j : Fin n, ⋂ (_ : j < i), ((U j : X.Opens) : Set X)ᶜ
  let F (i : Fin n) : Spec Γ(X, (U i : X.Opens)) ⟶ X := (U i).2.fromSpec
  let T (i : Fin n) : Set (Spec Γ(X, (U i : X.Opens))) := F i ⁻¹' C i
  have hT (i : Fin n) : IsClosed (T i) :=
    (isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
      (U j).1.isOpen.isClosed_compl).preimage (F i).continuous
  let I (i : Fin n) : Ideal Γ(X, (U i : X.Opens)) := PrimeSpectrum.vanishingIdeal (T i)
  refine ⟨n, fun i ↦ Spec (.of (Γ(X, (U i : X.Opens)) ⧸ I i)),
    fun i ↦ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I i))) ≫ F i, fun i ↦ ⟨?_, ?_, ?_⟩, ?_⟩
  · infer_instance
  · infer_instance
  · have : _root_.IsReduced (Γ(X, (U i : X.Opens)) ⧸ I i) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (PrimeSpectrum.isRadical_vanishingIdeal _)
    infer_instance
  -- The range of the `i`-th piece is `Uᵢ ∖ ⋃_{j < i} Uⱼ`.
  have hrange (i : Fin n) : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I i))) ≫
      F i) = ((U i : X.Opens) : Set X) ∩ C i := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    have : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I i)))) = T i := by
      change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I i))) = T i
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, (hT i).closure_eq]
    rw [this]
    change F i '' (F i ⁻¹' C i) = _
    rw [Set.image_preimage_eq_inter_range, IsAffineOpen.range_fromSpec, Set.inter_comm]
  refine fun x ↦ ?_
  simp only [hrange]
  obtain ⟨i₀, hi₀⟩ := hcov x
  let i := Finset.min' {j | x ∈ (U j : X.Opens)} ⟨i₀, by simpa using hi₀⟩
  have hi : x ∈ (U i : X.Opens) := by
    simpa using Finset.min'_mem {j | x ∈ (U j : X.Opens)} ⟨i₀, by simpa using hi₀⟩
  refine ⟨i, ⟨hi, ?_⟩, fun j ⟨hj, hjC⟩ ↦ ?_⟩
  · simp only [C, Set.mem_iInter, Set.mem_compl_iff]
    intro j hji hj
    exact absurd (Finset.min'_le _ j (by simpa using hj)) (not_le.mpr hji)
  · simp only [C, Set.mem_iInter, Set.mem_compl_iff] at hjC
    refine le_antisymm ?_ (Finset.min'_le _ j (by simpa using hj))
    by_contra h
    exact hjC i (not_le.mp h) hi

section RelativeNoether

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The conclusion of blueprint `lemma-relative-noether-normalization-over-stratification--1` over a
subset `Z` of the target `Y`: there are finite partitions of `Z` and of `f ⁻¹ Z` into reduced
locally closed subschemes such that every source piece maps into a target piece `T` through a finite
morphism to an iterated relative affine line over `T`. -/
def Scheme.Hom.HasNoetherPartitionOver (Z : Set Y) : Prop :=
  ∃ (ιT : Type) (_ : Finite ιT) (T : ιT → Scheme.{u}) (j : ∀ b, T b ⟶ Y),
    (∀ b, IsImmersion (j b) ∧ IsReduced (T b) ∧ Set.range (j b) ⊆ Z) ∧
    (∀ y ∈ Z, ∃! b, y ∈ Set.range (j b)) ∧
  ∃ (ιS : Type) (_ : Finite ιS) (S : ιS → Scheme.{u}) (i : ∀ a, S a ⟶ X),
    (∀ a, IsImmersion (i a) ∧ IsReduced (S a) ∧ Set.range (i a) ⊆ f ⁻¹' Z) ∧
    (∀ x ∈ f ⁻¹' Z, ∃! a, x ∈ Set.range (i a)) ∧
  ∃ (σ : ιS → ιT) (d : ιS → ℕ) (ν : ∀ a, S a ⟶ iteratedAffineLine (T (σ a)) (d a)),
    ∀ a, IsFinite (ν a) ∧ ν a ≫ iteratedAffineLineProj _ _ ≫ j (σ a) = i a ≫ f

/-- The empty set has the empty partition. -/
lemma Scheme.Hom.hasNoetherPartitionOver_empty : f.HasNoetherPartitionOver ∅ :=
  ⟨Empty, inferInstance, Empty.elim, fun b ↦ b.elim, fun b ↦ b.elim, by simp,
    Empty, inferInstance, Empty.elim, fun a ↦ a.elim, fun a ↦ a.elim, by simp,
    Empty.elim, Empty.elim, fun a ↦ a.elim, fun a ↦ a.elim⟩

/-- Partitions over disjoint subsets combine to a partition over their union. -/
lemma Scheme.Hom.HasNoetherPartitionOver.union {Z₁ Z₂ : Set Y} (h : Disjoint Z₁ Z₂)
    (h₁ : f.HasNoetherPartitionOver Z₁) (h₂ : f.HasNoetherPartitionOver Z₂) :
    f.HasNoetherPartitionOver (Z₁ ∪ Z₂) := by
  obtain ⟨ιT₁, _, T₁, j₁, hj₁, hu₁, ιS₁, _, S₁, i₁, hi₁, hv₁, σ₁, d₁, ν₁, hν₁⟩ := h₁
  obtain ⟨ιT₂, _, T₂, j₂, hj₂, hu₂, ιS₂, _, S₂, i₂, hi₂, hv₂, σ₂, d₂, ν₂, hν₂⟩ := h₂
  have hX : Disjoint (f ⁻¹' Z₁) (f ⁻¹' Z₂) := h.preimage f
  refine ⟨ιT₁ ⊕ ιT₂, inferInstance, Sum.elim T₁ T₂, fun | .inl b => j₁ b | .inr b => j₂ b,
    ?_, ?_, ιS₁ ⊕ ιS₂, inferInstance, Sum.elim S₁ S₂, fun | .inl a => i₁ a | .inr a => i₂ a,
    ?_, ?_, Sum.map σ₁ σ₂, Sum.elim d₁ d₂, fun | .inl a => ν₁ a | .inr a => ν₂ a, ?_⟩
  · rintro (b | b)
    · exact ⟨(hj₁ b).1, (hj₁ b).2.1, (hj₁ b).2.2.trans Set.subset_union_left⟩
    · exact ⟨(hj₂ b).1, (hj₂ b).2.1, (hj₂ b).2.2.trans Set.subset_union_right⟩
  · rintro y (hy | hy)
    · obtain ⟨b, hb, hb'⟩ := hu₁ y hy
      refine ⟨.inl b, hb, ?_⟩
      rintro (c | c) hc
      · exact congrArg _ (hb' c hc)
      · exact (h.ne_of_mem hy ((hj₂ c).2.2 hc) rfl).elim
    · obtain ⟨b, hb, hb'⟩ := hu₂ y hy
      refine ⟨.inr b, hb, ?_⟩
      rintro (c | c) hc
      · exact (h.ne_of_mem ((hj₁ c).2.2 hc) hy rfl).elim
      · exact congrArg _ (hb' c hc)
  · rintro (a | a)
    · exact ⟨(hi₁ a).1, (hi₁ a).2.1, (hi₁ a).2.2.trans (Set.preimage_mono Set.subset_union_left)⟩
    · exact ⟨(hi₂ a).1, (hi₂ a).2.1,
        (hi₂ a).2.2.trans (Set.preimage_mono Set.subset_union_right)⟩
  · rintro x (hx | hx)
    · obtain ⟨b, hb, hb'⟩ := hv₁ x hx
      refine ⟨.inl b, hb, ?_⟩
      rintro (c | c) hc
      · exact congrArg _ (hb' c hc)
      · exact (hX.ne_of_mem hx ((hi₂ c).2.2 hc) rfl).elim
    · obtain ⟨b, hb, hb'⟩ := hv₂ x hx
      refine ⟨.inr b, hb, ?_⟩
      rintro (c | c) hc
      · exact (hX.ne_of_mem ((hi₁ c).2.2 hc) hx rfl).elim
      · exact congrArg _ (hb' c hc)
  · rintro (a | a)
    · exact hν₁ a
    · exact hν₂ a

/-- The induction step of blueprint `lemma-relative-noether-normalization-over-stratification--1`: a
nonempty closed subset `Z` of the target contains a nonempty subset `Z₁` with closed complement
`Z ∖ Z₁` over which the partition exists.

Take an irreducible component of `Z ∩ V` for an affine open `V = Spec A`, i.e. a minimal prime
`p` over the ideal of `Z ∩ V`, and a function `f₀` vanishing on the other components only. Cover
the base change of `f` to the integral scheme `Spec (A ⧸ p)` by finitely many reduced affine pieces
(blueprint `lemma-relative-noether-normalization-over-stratification--1`), spread out Noether
normalization for each of them (blueprint
`lemma-relative-noether-normalization-over-stratification--1`) and shrink to a common principal open
`D(s)`. -/
lemma Scheme.Hom.exists_hasNoetherPartitionOver_nonempty [IsNoetherian Y] [QuasiCompact f]
    [LocallyOfFiniteType f] {Z : Set Y} (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ Z₁ ⊆ Z, Z₁.Nonempty ∧ IsClosed (Z \ Z₁) ∧ f.HasNoetherPartitionOver Z₁ := by
  classical
  -- An affine open `V = Spec A` meeting `Z`.
  obtain ⟨z, hz⟩ := hne
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) trivial
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  set F := hV.fromSpec
  let T : Set (Spec Γ(Y, V)) := F ⁻¹' Z
  have hT : IsClosed T := hZ.preimage F.continuous
  let I := PrimeSpectrum.vanishingIdeal T
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Spec Γ(Y, V), F P₀ = z := by
    rw [← Set.mem_range, IsAffineOpen.range_fromSpec]; exact hzV
  have hIP₀ : I ≤ P₀.asIdeal := fun a ha ↦
    (PrimeSpectrum.mem_vanishingIdeal T a).mp ha P₀ (by simpa [T, hP₀] using hz)
  -- A minimal prime `p` over `I`, i.e. an irreducible component of `Z ∩ V`, and a function `f₀`
  -- vanishing on the other components but not on `p`.
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le hIP₀
  have : p.IsPrime := hp.1.1
  have hIp : I ≤ p := hp.1.2
  obtain ⟨f₀, hf₀, hf₀p⟩ : ∃ f₀ ∈ ((I.finite_minimalPrimes_of_isNoetherianRing).toFinset.erase
      p).inf id, f₀ ∉ p := by
    refine IsConcreteLE.not_le_iff_exists.mp fun hle ↦ ?_
    obtain ⟨p', hp', hp'p⟩ := (Ideal.IsPrime.inf_le' this).mp hle
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hp'
    exact hp'.1 (le_antisymm hp'p (hp.2 ⟨hp'.2.1.1, hp'.2.1.2⟩ hp'p))
  -- The integral closed subscheme `Spec (A ⧸ p)` and the base change of `f` to it.
  let A' := CommRingCat.of (Γ(Y, V) ⧸ p)
  let q : Spec A' ⟶ Spec Γ(Y, V) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))
  let h : Spec A' ⟶ Y := q ≫ F
  obtain ⟨n, W, w, hw, hpart⟩ :=
    Scheme.exists_partition_isImmersion_isAffine_isReduced (pullback f h)
  let g (k : Fin n) : W k ⟶ Spec A' := w k ≫ pullback.snd f h
  have : Nonempty (⊤ : (Spec A').Opens) := ⟨⟨⟨⊥, Ideal.isPrime_bot⟩, trivial⟩⟩
  choose s₀ hs₀ d H using fun k ↦
    have := (hw k).1
    have := (hw k).2.1
    exists_isFinite_toIteratedAffineLine_basicOpen (g k) (isAffineOpen_top (Spec A'))
  -- Shrink to a principal open `D(s)` of `Spec (A ⧸ p)` with `s = f₀ ∏ₖ s₀ₖ`.
  obtain ⟨t₁, ht₁⟩ := Ideal.Quotient.mk_surjective (I := p) ((Scheme.ΓSpecIso A').hom (∏ k, s₀ k))
  let s : Γ(Spec A', ⊤) := (Scheme.ΓSpecIso A').inv (Ideal.Quotient.mk p f₀) * ∏ k, s₀ k
  have hs : (Scheme.ΓSpecIso A').hom s = Ideal.Quotient.mk p (f₀ * t₁) := by
    rw [map_mul, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_mul, ht₁]
  have hs0 : s ≠ 0 := by
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun k _ ↦ hs₀ k)
    intro h0
    apply hf₀p
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using congr((Scheme.ΓSpecIso A').hom $h0)
  have hdvd (k : Fin n) : s₀ k ∣ s := (Finset.dvd_prod_of_mem s₀ (Finset.mem_univ k)).mul_left _
  set D := (Spec A').basicOpen s
  choose ν hνfin hν _ using fun k ↦ H k s (hdvd k) hs0
  have hD (x : Spec A') : x ∈ D ↔ Ideal.Quotient.mk p (f₀ * t₁) ∉ x.asIdeal := by
    change x ∈ (Spec A').basicOpen s ↔ _
    rw [basicOpen_eq_of_affine', hs]
    rfl
  -- The target piece `Z₁ = h(D(s))` is `Z ∩ O` for the open `O = F(D(f₀ t₁))` of `Y`.
  have hTz (P : Spec Γ(Y, V)) (hP : I ≤ P.asIdeal) : P ∈ T := by
    rw [← hT.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hP
  have hqp (y : Spec A') : p ≤ (q y).asIdeal := fun a ha ↦ by
    change Ideal.Quotient.mk p a ∈ y.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact zero_mem _
  let O : Set Y := F '' {P : Spec Γ(Y, V) | f₀ * t₁ ∉ P.asIdeal}
  have hO : IsOpen O :=
    F.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen (f₀ * t₁)).isOpen
  have hZ₁Z : Set.range (D.ι ≫ h) ⊆ Z := by
    rintro _ ⟨x, rfl⟩
    exact hTz _ (hIp.trans (hqp _))
  have hZ₁O : Set.range (D.ι ≫ h) ⊆ O := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact ⟨q x, fun hmem ↦ (hD x).mp hx hmem, rfl⟩
  have hZO : Z ∩ O ⊆ Set.range (D.ι ≫ h) := by
    rintro y ⟨hyZ, P, hP, rfl⟩
    have hIP : I ≤ P.asIdeal := fun a ha ↦
      (PrimeSpectrum.mem_vanishingIdeal T a).mp ha P (by simpa [T] using hyZ)
    have hpP : p ≤ P.asIdeal := by
      obtain ⟨p', hp', hp'P⟩ := Ideal.exists_minimalPrimes_le hIP
      by_cases hpp' : p' = p
      · exact hpp' ▸ hp'P
      have hmem : p' ∈ (I.finite_minimalPrimes_of_isNoetherianRing).toFinset.erase p := by
        rw [Finset.mem_erase, Set.Finite.mem_toFinset]
        exact ⟨hpp', hp'⟩
      exact absurd (P.asIdeal.mul_mem_right t₁ (hp'P (Finset.inf_le (f := id) hmem hf₀))) hP
    have hker : RingHom.ker (Ideal.Quotient.mk p) ≤ P.asIdeal := by rwa [Ideal.mk_ker]
    let Q : Spec A' := ⟨P.asIdeal.map (Ideal.Quotient.mk p),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩
    have hQ : q Q = P := by
      apply PrimeSpectrum.ext
      change Ideal.comap _ (Ideal.map _ _) = _
      erw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective]
      exact sup_eq_left.mpr hker
    have hQD : Q ∈ D := by
      rw [hD]
      intro hmem
      apply hP
      rw [← hQ]
      exact hmem
    exact ⟨⟨Q, hQD⟩, by simp [h, hQ]⟩
  have hZ₁ne : (Set.range (D.ι ≫ h)).Nonempty := by
    have : (D : Set (Spec A')).Nonempty := by
      rw [Set.nonempty_iff_ne_empty, Ne, TopologicalSpace.Opens.coe_eq_empty,
        basicOpen_eq_bot_iff]
      exact hs0
    obtain ⟨x, hx⟩ := this
    exact ⟨_, ⟨x, hx⟩, rfl⟩
  refine ⟨Set.range (D.ι ≫ h), hZ₁Z, hZ₁ne, ?_, ?_⟩
  · have : Z \ Set.range (D.ι ≫ h) = Z ∩ Oᶜ := by
      ext y
      refine ⟨fun ⟨hyZ, hy⟩ ↦ ⟨hyZ, fun hyO ↦ hy (hZO ⟨hyZ, hyO⟩)⟩,
        fun ⟨hyZ, hy⟩ ↦ ⟨hyZ, fun hy' ↦ hy (hZ₁O hy')⟩⟩
    rw [this]
    exact hZ.inter hO.isClosed_compl
  -- The pieces: `D(s)` in the target and the `g ⁻¹ D(s)` in the source.
  have e1 (k : Fin n) : ((g k ⁻¹ᵁ D).ι ≫ w k ≫ pullback.fst f h) ≫ f =
      (g k ∣_ D) ≫ D.ι ≫ h := by
    rw [← Category.assoc (g k ∣_ D), morphismRestrict_ι]
    simp [g, pullback.condition]
  have hfst : Function.Injective (pullback.fst f h) := (pullback.fst f h).isEmbedding.injective
  refine ⟨Unit, inferInstance, fun _ ↦ D.toScheme, fun _ ↦ D.ι ≫ h,
    fun _ ↦ ⟨inferInstance, inferInstance, subset_rfl⟩, fun y hy ↦ ⟨(), hy, fun _ _ ↦ rfl⟩,
    Fin n, inferInstance, fun k ↦ (g k ⁻¹ᵁ D).toScheme,
    fun k ↦ (g k ⁻¹ᵁ D).ι ≫ w k ≫ pullback.fst f h, fun k ↦ ⟨?_, ?_, ?_⟩, ?_,
    fun _ ↦ (), d, ν, fun k ↦ ⟨hνfin k, ?_⟩⟩
  · have := (hw k).1
    infer_instance
  · have := (hw k).2.2
    infer_instance
  · rintro _ ⟨u, rfl⟩
    refine ⟨(g k ∣_ D) u, ?_⟩
    change _ = ((((g k ⁻¹ᵁ D).ι ≫ w k ≫ pullback.fst f h) ≫ f) u)
    rw [e1 k]
    rfl
  · rintro x ⟨⟨v, hv⟩, hx⟩
    have hx' : f x = h v := by rw [← hx]; rfl
    obtain ⟨P, hPx, hPv⟩ := Scheme.Pullback.exists_preimage_pullback x v hx'
    obtain ⟨k, ⟨u, hu⟩, -⟩ := hpart P
    have hgu : g k u ∈ D := by
      simp only [g, Scheme.Hom.comp_apply, hu, hPv]
      exact hv
    refine ⟨k, ⟨⟨u, hgu⟩, by simp [hu, hPx]⟩, fun l ⟨⟨u', hu'⟩, hl⟩ ↦ ?_⟩
    obtain ⟨k', -, hk'⟩ := hpart P
    have h1 : w l u' = P := hfst (by simpa [hPx] using hl)
    exact (hk' l ⟨u', h1⟩).trans (hk' k ⟨u, hu⟩).symm
  · change (ν k ≫ iteratedAffineLineProj D (d k)) ≫ D.ι ≫ h = _
    rw [hν k]
    exact (e1 k).symm

/-- Noetherian induction on the closed subsets of the target. -/
lemma Scheme.Hom.hasNoetherPartitionOver_of_isClosed [IsNoetherian Y] [QuasiCompact f]
    [LocallyOfFiniteType f] (Z : TopologicalSpace.Closeds Y) :
    f.HasNoetherPartitionOver Z := by
  induction Z using WellFoundedLT.induction with
  | _ Z ih =>
  rcases (Z : Set Y).eq_empty_or_nonempty with hZ | hZ
  · rw [hZ]
    exact f.hasNoetherPartitionOver_empty
  obtain ⟨Z₁, hZ₁Z, hZ₁, hcl, hP⟩ := f.exists_hasNoetherPartitionOver_nonempty Z.isClosed hZ
  let Z₂ : TopologicalSpace.Closeds Y := ⟨Z \ Z₁, hcl⟩
  have hlt : Z₂ < Z := by
    refine lt_of_le_of_ne (fun y hy ↦ hy.1) fun heq ↦ ?_
    obtain ⟨y, hy⟩ := hZ₁
    have : y ∈ (Z₂ : Set Y) := by rw [heq]; exact hZ₁Z hy
    exact this.2 hy
  have := Scheme.Hom.HasNoetherPartitionOver.union f Set.disjoint_sdiff_right hP (ih Z₂ hlt)
  rwa [Set.union_sdiff_cancel hZ₁Z] at this

/-- Blueprint `lemma-relative-noether-normalization-over-stratification--1`: relative Noether
normalization.

Let `f : X ⟶ Y` be a morphism of finite type to a Noetherian scheme (for instance a separated
morphism of finite type between separated schemes of finite type over a field). There are finite
partitions of `Y` and of `X` into reduced locally closed subschemes `T b ⟶ Y` and `S a ⟶ X` such
that each source piece `S a` maps to the target piece `T (σ a)`, through a finite morphism
`ν a : S a ⟶ 𝔸^{d a}_{T (σ a)}` followed by the `d a` coordinate projections
`AlgebraicGeometry.iteratedAffineLineProj`. For `d a = 0` this is just a finite morphism
`S a ⟶ T (σ a)`. -/
theorem exists_partition_isFinite_toIteratedAffineLine [IsNoetherian Y] [QuasiCompact f]
    [LocallyOfFiniteType f] :
    ∃ (ιT : Type) (_ : Finite ιT) (T : ιT → Scheme.{u}) (j : ∀ b, T b ⟶ Y),
      (∀ b, IsImmersion (j b) ∧ IsReduced (T b)) ∧ (∀ y, ∃! b, y ∈ Set.range (j b)) ∧
    ∃ (ιS : Type) (_ : Finite ιS) (S : ιS → Scheme.{u}) (i : ∀ a, S a ⟶ X),
      (∀ a, IsImmersion (i a) ∧ IsReduced (S a)) ∧ (∀ x, ∃! a, x ∈ Set.range (i a)) ∧
    ∃ (σ : ιS → ιT) (d : ιS → ℕ) (ν : ∀ a, S a ⟶ iteratedAffineLine (T (σ a)) (d a)),
      ∀ a, IsFinite (ν a) ∧ ν a ≫ iteratedAffineLineProj _ _ ≫ j (σ a) = i a ≫ f := by
  obtain ⟨ιT, _, T, j, hj, hu, ιS, _, S, i, hi, hv, σ, d, ν, hν⟩ :=
    f.hasNoetherPartitionOver_of_isClosed ⊤
  exact ⟨ιT, inferInstance, T, j, fun b ↦ ⟨(hj b).1, (hj b).2.1⟩, fun y ↦ hu y trivial,
    ιS, inferInstance, S, i, fun a ↦ ⟨(hi a).1, (hi a).2.1⟩, fun x ↦ hv x trivial, σ, d, ν, hν⟩

end RelativeNoether

end AlgebraicGeometry
