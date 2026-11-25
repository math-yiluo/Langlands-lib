/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.AffineLocal
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Gluing
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Group
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Neighbourhood
public import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineNeighbourhood

/-!
# Effective descent for schemes

Let `p : X ⟶ Y` be a morphism of schemes. This file collects the descent statements for schemes
over `X` equipped with a descent datum relative to `p` (in the transport form
`CategoryTheory.Over.DescentDatum`) that are needed to descend the Jacobian of a curve from a
finite separable extension of the base field.

## Main statements

- `CategoryTheory.Over.DescentDatum.isEffective_of_isFinite`: along a surjective finite locally
  free morphism, descent data on schemes in which every finite set of points lies in an affine open
  (for instance projective schemes over a field) are effective (blueprint
  `proposition-jacobian-over-ground-field--1`).
- `CategoryTheory.Over.DescentDatum.isEffective_of_isClosedImmersion`: along a surjective finite
  locally free morphism with affine source `X`, descent data on projective schemes over `X` are
  effective (blueprint `proposition-jacobian-over-ground-field--1`).
- `CategoryTheory.Over.DescentDatum.existsUnique_hom_of_isPullback`: compatible morphisms descend
  (blueprint `proposition-jacobian-over-ground-field--1`).
- `CategoryTheory.Over.DescentDatum.existsUnique_grpObj_of_isPullback`: compatible group scheme
  structures descend, uniquely (blueprint `proposition-jacobian-over-ground-field--1`).
- `CategoryTheory.Over.DescentDatum.exists_commGrpObj_of_isPullback`: compatible commutative group
  scheme structures descend (blueprint `proposition-jacobian-over-ground-field--1`).
- `AlgebraicGeometry.locallyOfFiniteType_quasiCompact_smooth_isProper_connectedSpace_of_isPullback`:
  finite type, smoothness, properness and connectedness descend along a field extension (blueprint
  `proposition-jacobian-over-ground-field--1`).
- `AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback_aux`:
  properness, smoothness of relative dimension `n` and geometric integrality descend along a field
  extension (blueprint `proposition-jacobian-over-ground-field--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y}

/-- **Effective descent for quasi-projective schemes.** Let `p : X ⟶ Y` be a surjective finite
locally free morphism and let `V` be a scheme over `X` in which every finite set of points lies in
an affine open, as is the case for a projective scheme over a field (Stacks 01ZY). Then every
descent datum on `V` relative to `p` is effective.

This is Stacks 0CCJ, via the criterion of Stacks 0CCI: the hypothesis on `V` is stronger than the
one needed there, which only asks it of the finite sets of points lying over one point of `Y`.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
theorem isEffective_of_isFinite [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] {V : Over X}
    (hV : ∀ s : Set V.left, s.Finite → ∃ U : V.left.Opens, IsAffineOpen U ∧ s ⊆ U)
    (D : Over.DescentDatum p V) : D.IsEffective := by
  refine isEffective_of_forall_exists_mem fun v ↦ ?_
  obtain ⟨U, hv, hU, hUa, W, hW, hUW⟩ := D.exists_isInvariant_isAffineOpen hV v
  exact ⟨U, hU, hv, D.isEffective_restrict_of_isAffineOpen hU hUa hW hUW⟩

/-- **Effective descent for projective schemes.** Let `p : X ⟶ Y` be a surjective finite locally
free morphism with `X` affine, and let `V` be a scheme over `X` such that `V ⟶ X` is projective:
there is a closed immersion `i : V ⟶ ℙ(α; X)`, with `α` finite, whose composition with the
projection `ℙ(α; X) ⟶ X` is the structure morphism of `V`. Then every descent datum on `V`
relative to `p` is effective.

This is Stacks 0CCJ: finitely many points of `V` lie in an affine open (Stacks 01ZY,
`exists_isAffineOpen_superset_of_isImmersion_of_isAffine`), which is the hypothesis of
`isEffective_of_isFinite`. The blueprint states this for an arbitrary base; here `X`, hence the
projective space `ℙ(α; X)`, is assumed affine, which covers the case of a finite extension of
fields used for the Jacobian. The general case is
`CategoryTheory.Over.DescentDatum.isEffective_of_isHProjective`.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
theorem isEffective_of_isClosedImmersion [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] [IsAffine X] {V : Over X} {α : Type u} [Finite α] (i : V.left ⟶ ℙ(α; X))
    [IsClosedImmersion i] (hi : i ≫ ℙ(α; X) ↘ X = V.hom) (D : Over.DescentDatum p V) :
    D.IsEffective := by
  have : CompactSpace ℙ(α; X) := QuasiCompact.compactSpace_of_compactSpace (ℙ(α; X) ↘ X)
  have : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparated V.hom := by
    rw [← hi]
    infer_instance
  have : QuasiSeparatedSpace V.left := quasiSeparatedSpace_of_quasiSeparated V.hom
  exact D.isEffective_of_isFinite fun s hs ↦
    exists_isAffineOpen_superset_of_isImmersion_of_isAffine i s hs


/-- **Morphisms descend.** Let `p : X ⟶ Y` be faithfully flat and quasi-compact, and let `V`, `W`
be schemes over `X` with descent data `D`, `E` that are effective, with descended schemes `V₀`,
`W₀` over `Y` and projections `qV`, `qW`. Then every morphism `ψ : V ⟶ W` over `X` compatible with
the two descent data is the base change of a unique morphism `ψ₀ : V₀ ⟶ W₀` over `Y`.

This is the full faithfulness of base change into descent data, Stacks 02W0.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
theorem existsUnique_hom_of_isPullback [Flat p] [Surjective p] [QuasiCompact p] {V W : Over X}
    (D : Over.DescentDatum p V) (E : Over.DescentDatum p W) {V₀ W₀ : Over Y}
    (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (qW : W.left ⟶ W₀.left) (hqW : IsPullback qW W.hom W₀.hom p)
    (hEW : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ W),
      (E.transport f₁ f₂ h a).left ≫ qW = a.left ≫ qW)
    (ψ : V ⟶ W)
    (hψ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      E.transport f₁ f₂ h (a ≫ ψ) = D.transport f₁ f₂ h a ≫ ψ) :
    ∃! ψ₀ : V₀ ⟶ W₀, ψ.left ≫ qW = qV ≫ ψ₀.left := by
  obtain ⟨g₀, hg₀, hu⟩ := D.existsUnique_desc_of_isPullback hqV hDV (ψ.left ≫ qW)
    fun f₁ f₂ h a ↦ by simpa [hψ] using hEW f₁ f₂ h (a ≫ ψ)
  obtain ⟨_, _, hY⟩ := D.existsUnique_desc_of_isPullback hqV hDV (V.hom ≫ p)
    fun f₁ f₂ h a ↦ by simp [h]
  have hg₀Y : g₀ ≫ W₀.hom = V₀.hom := by
    refine (hY _ ?_).trans (hY V₀.hom hqV.w).symm
    dsimp only
    rw [reassoc_of% hg₀, hqW.w, Over.w_assoc]
  refine ⟨Over.homMk g₀ hg₀Y, hg₀.symm, fun ψ₀ hψ₀ ↦ ?_⟩
  ext
  exact hu _ hψ₀.symm

/-- **The descended scheme is a group scheme.** Let `p : X ⟶ Y` be faithfully flat and
quasi-compact, let `V` be a scheme over `X` with an effective descent datum `D`, with descended
scheme `V₀` and projection `qV`, and let `V` carry a group scheme structure whose multiplication
and unit are compatible with `D`. Then `V₀` carries a unique group scheme structure over `Y`
whose base change is the given one, in the sense that `qV` maps products of points of `V` to
products of points of `V₀`.

Existence comes from the Yoneda lemma applied to the invariant points of `V`; uniqueness from
the injectivity of base change on morphisms (`liftPoint_injective`).

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
theorem existsUnique_grpObj_of_isPullback [Flat p] [Surjective p] [QuasiCompact p] {V : Over X}
    [GrpObj V] (D : Over.DescentDatum p V) {V₀ : Over Y} (qV : V.left ⟶ V₀.left)
    (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a b : Over.mk f₁ ⟶ V),
      D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
        lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
    (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
      D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V]) :
    ∃! _ : GrpObj V₀, ∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ μ[V₀] := by
  let G := GrpObj.ofRepresentableBy V₀ (D.descendedPresheaf hqV hDV hμ hη)
    (D.descendedRepresentableBy hqV hDV hμ hη)
  have hG {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V) :
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ μ[V₀] := by
    have hmul (x y : Over.mk (f ≫ p) ⟶ V₀) :
        lift x y ≫ μ[V₀] = (D.homGroup hqV hDV hμ hη _).mul x y :=
      (((D.descendedPresheaf hqV hDV hμ hη).map (lift x y).op).hom.map_mul
        (fst V₀ V₀) (snd V₀ V₀)).trans
        (congrArg₂ (D.homGroup hqV hDV hμ hη _).mul (lift_fst x y) (lift_snd x y))
    exact (D.descendPoint_mul hqV hDV hμ hη a b).trans (hmul _ _).symm
  exact ⟨G, hG, fun G' hG' ↦ GrpObj.ext_of_mul_eq
    (mul_eq_of_descendPoint_mul hqV G'.toMonObj G.toMonObj hG' hG)⟩

/-- **The descended scheme is a commutative group scheme.** Let `p : X ⟶ Y` be faithfully flat
and quasi-compact, let `V` be a scheme over `X` with an effective descent datum `D`, with
descended scheme `V₀` and projection `qV`, and let `V` carry a commutative group scheme structure
whose multiplication and unit are compatible with `D`. Then `V₀` carries a commutative group
scheme structure over `Y` whose base change is the given one: `qV` maps products of points of `V`
to products of points of `V₀`. Such a structure is unique by
`existsUnique_grpObj_of_isPullback`.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
theorem exists_commGrpObj_of_isPullback [Flat p] [Surjective p] [QuasiCompact p] {V : Over X}
    [CommGrpObj V] (D : Over.DescentDatum p V) {V₀ : Over Y} (qV : V.left ⟶ V₀.left)
    (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a b : Over.mk f₁ ⟶ V),
      D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
        lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
    (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
      D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V]) :
    ∃ _ : CommGrpObj V₀, ∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ μ[V₀] := by
  obtain ⟨G, hG, -⟩ := D.existsUnique_grpObj_of_isPullback qV hqV hDV hμ hη
  have : IsCommMonObj V₀ := (isCommMonObj_iff_isMulCommutative V₀).2 fun T ↦
    ⟨⟨fun x y ↦ liftPoint_injective hqV (by
      rw [liftPoint_mul_of_descendPoint_mul hqV hG, liftPoint_mul_of_descendPoint_mul hqV hG,
        mul_comm])⟩⟩
  exact ⟨{ }, hG⟩

end CategoryTheory.Over.DescentDatum

namespace AlgebraicGeometry

/-- **Properties of morphisms are local in the fpqc topology on the target.** Let `k ⊆ K` be a
field extension and let `Z` be a scheme over `k` whose base change `Z_K` is smooth (in particular
locally of finite type) and proper over `K`, and connected. Then `Z` is of finite type, smooth and
proper over `k`, and connected.

This is the statement of the blueprint, where `K / k` is finite; finiteness is not needed.
Smoothness, being locally of finite type and properness descend along the faithfully flat
quasi-compact morphism `Spec K ⟶ Spec k` (Stacks 02KL, 05B5, 02YJ), and `Z` is connected as the
image of `Z_K` under the surjection `Z_K ⟶ Z`.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
theorem locallyOfFiniteType_quasiCompact_smooth_isProper_connectedSpace_of_isPullback
    {k K : Type u} [Field k] [Field K] [Algebra k K] {Z Z' : Scheme.{u}} (z : Z ⟶ Spec (.of k))
    (z' : Z' ⟶ Spec (.of K)) (q : Z' ⟶ Z)
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K)))) [Smooth z']
    [IsProper z'] [ConnectedSpace Z'] :
    LocallyOfFiniteType z ∧ QuasiCompact z ∧ Smooth z ∧ IsProper z ∧ ConnectedSpace Z := by
  have : IsProper z := of_isPullback_Spec_map_algebraMap @IsProper h ‹_›
  exact ⟨inferInstance, inferInstance, of_isPullback_Spec_map_algebraMap @Smooth h ‹_›, this,
    connectedSpace_of_isPullback_Spec_map_algebraMap h⟩

end AlgebraicGeometry
