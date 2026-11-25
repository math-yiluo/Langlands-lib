/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import WeilConjectures.AlgebraicGeometry.GenericFiber.CoordinateDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# The geometric generic fibre of a coordinate

This file provides the geometric glue of the dimension induction in the proof of
`theorem-verdier-biduality--1` (third and fourth paragraphs). Let `k` be a field, `V` an
affine scheme over `Spec k` and `x ∈ V` a nonclosed point.

1. Some global section of `V` has transcendental image in `κ(x)`, so the induced coordinate
   `p : V ⟶ 𝔸¹_k` sends `x` to the generic point of `𝔸¹_k`
   (`AlgebraicGeometry.exists_hom_affineLine_over_apply_eq_genericPoint`). If `V` is of finite
   type over `k`, any such `p` is a closed immersion into some `𝔸ⁿ_{𝔸¹_k}` followed by the
   projection (`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_affineLine`).
2. Let `K̄` be the algebraic closure of the function field `κ(η)` of `𝔸¹_k` and
   `V' = V ×_{𝔸¹_k} Spec K̄` the geometric generic fibre of `p`
   (`AlgebraicGeometry.geometricGenericFiber`). Then `V'` is affine and of finite type over
   `Spec K̄`, and `dim V' + 1 ≤ dim V`
   (`AlgebraicGeometry.topologicalKrullDim_geometricGenericFiber_add_one_le`): the generic fibre
   over `κ(η)` loses one dimension by `lemma-coordinate-projections--1`, and the base change
   to the algebraic extension `K̄` is an integral morphism onto it, which does not raise the
   dimension.
3. The geometric point `V.algClosurePoint x` factors through the projection `V' ⟶ V`
   (`AlgebraicGeometry.exists_comp_geometricGenericFiber_fst_eq_algClosurePoint`), after
   embedding `K̄` into the algebraic closure of `κ(x)`. Hence the stalk of an étale sheaf `F`
   on `V` at `x` vanishes as soon as its pullback to `V'` vanishes
   (`AlgebraicGeometry.isZero_sheafFiber_algClosurePoint_of_isZero_upperStar`).

The field `k` need not be algebraically closed for these statements.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

/-- In an algebra `R` over a field `k`, a prime ideal `P` which is not maximal admits an element
whose image in `R ⧸ P` is transcendental over `k`: otherwise the domain `R ⧸ P` would be algebraic
over `k`, hence a field. -/
theorem Ideal.exists_transcendental_mk_of_not_isMaximal {k R : Type*} [Field k] [CommRing R]
    [Algebra k R] (P : Ideal R) [P.IsPrime] (hP : ¬ P.IsMaximal) :
    ∃ t : R, Transcendental k (Ideal.Quotient.mk P t) := by
  by_contra! h
  have : Algebra.IsAlgebraic k (R ⧸ P) := ⟨fun y ↦ by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    simpa [Transcendental] using h t⟩
  exact hP (Ideal.Quotient.maximal_of_isField _
    ((Algebra.IsIntegral.isField_iff_isField (algebraMap k (R ⧸ P)).injective).mp
      (Field.toIsField k)))

/-- If `a + 1 ≤ d` in `WithBot ℕ∞` for a natural number `d`, then `a ≤ d - 1`. -/
lemma WithBot.ENat.le_natCast_sub_one_of_add_one_le {a : WithBot ℕ∞} {d : ℕ}
    (h : a + 1 ≤ d) : a ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe m =>
    have h' : m + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
    induction m using ENat.recTopCoe with
    | top => simp at h'
    | coe n =>
      have : n + 1 ≤ d := by exact_mod_cast h'
      have h2 : (n : ℕ∞) ≤ ((d - 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : n ≤ d - 1)
      exact (WithBot.coe_le_coe.mpr h2).trans_eq (by norm_cast)

namespace AlgebraicGeometry

/-- An isomorphism of irreducible schemes maps the generic point to the generic point. -/
lemma Scheme.Hom.apply_genericPoint_of_isIso {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) [IsIso f] : f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ_of_surjective f.surjective, closure_univ] at h
  exact h.eq (genericPoint_spec Y)

/-- A morphism `f` with `f x = y` induces a morphism of residue fields `κ(y) ⟶ κ(x)`
compatible with the canonical morphisms from the spectra of the residue fields. -/
lemma Scheme.Hom.exists_residueField_hom_of_apply_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    {y : Y} (h : f x = y) : ∃ φ : Y.residueField y ⟶ X.residueField x,
      Spec.map φ ≫ Y.fromSpecResidueField y = X.fromSpecResidueField x ≫ f := by
  subst h
  exact ⟨f.residueFieldMap x, f.SpecMap_residueFieldMap_fromSpecResidueField x⟩

variable {k : Type u} [Field k]

/-- Blueprint `theorem-verdier-biduality--1`, proof, third paragraph: **a coordinate
through a nonclosed point.** Let `V` be an affine scheme over a field `k` and `x ∈ V` a nonclosed
point. Some global section `t` of `V` has transcendental image in `κ(x)`; the induced morphism
`p : V ⟶ 𝔸¹_k` over `k` sends `x` to the generic point of `𝔸¹_k`. -/
theorem exists_hom_affineLine_over_apply_eq_genericPoint {V : Scheme.{u}} [IsAffine V]
    (aV : V ⟶ Spec (.of k)) {x : V} (hx : ¬ IsClosed ({x} : Set V)) :
    ∃ p : V ⟶ 𝔸(PUnit; Spec (.of k)), p ≫ 𝔸(PUnit; Spec (.of k)) ↘ Spec (.of k) = aV ∧
      p x = genericPoint 𝔸(PUnit; Spec (.of k)) := by
  let σ : k →+* Γ(V, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ aV.appTop).hom
  let := σ.toAlgebra
  let P : PrimeSpectrum Γ(V, ⊤) := V.isoSpec.hom x
  have hP : ¬ P.asIdeal.IsMaximal := by
    rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    intro h
    apply hx
    have hpre : V.isoSpec.hom ⁻¹' {P} = {x} := by
      ext y
      simp [P, V.isoSpec.hom.isOpenEmbedding.injective.eq_iff]
    rw [← hpre]
    exact h.preimage V.isoSpec.hom.continuous
  obtain ⟨t, ht⟩ := P.asIdeal.exists_transcendental_mk_of_not_isMaximal (k := k) hP
  let φ : MvPolynomial PUnit.{u + 1} k →+* Γ(V, ⊤) := MvPolynomial.eval₂Hom σ fun _ ↦ t
  let p : V ⟶ 𝔸(PUnit; Spec (.of k)) := V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫
    (AffineSpace.SpecIso PUnit (.of k)).inv
  have hφ : CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom φ =
      (Scheme.ΓSpecIso (.of k)).inv ≫ aV.appTop := by
    ext a
    simp [φ, σ]
  refine ⟨p, ?_, ?_⟩
  · simp only [p, Category.assoc, AffineSpace.SpecIso_inv_over]
    rw [← Spec.map_comp, hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  · have hinj : Function.Injective
        (MvPolynomial.aeval (R := k) fun _ : PUnit.{u + 1} ↦ Ideal.Quotient.mk P.asIdeal t) :=
      algebraicIndependent_iff_injective_aeval.mp (algebraicIndependent_unique_type_iff.mpr ht)
    have hgen : Spec.map (CommRingCat.ofHom φ) (V.isoSpec.hom x) =
        genericPoint (Spec (.of (MvPolynomial PUnit.{u + 1} k))) := by
      rw [genericPoint_eq_bot_of_affine]
      refine PrimeSpectrum.ext (Ideal.ext fun f ↦ ?_)
      change φ f ∈ P.asIdeal ↔ f ∈ (⊥ : Ideal _)
      rw [Ideal.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem]
      have : Ideal.Quotient.mk P.asIdeal (φ f) =
          MvPolynomial.aeval (fun _ : PUnit.{u + 1} ↦ Ideal.Quotient.mk P.asIdeal t) f := by
        exact MvPolynomial.comp_aeval_apply (R := k) (f := fun _ : PUnit.{u + 1} ↦ t)
          (Ideal.Quotient.mkₐ k P.asIdeal) f
      rw [this, ← map_zero (MvPolynomial.aeval (R := k) fun _ : PUnit.{u + 1} ↦
        Ideal.Quotient.mk P.asIdeal t), hinj.eq_iff]
    simp only [p, Scheme.Hom.comp_apply]
    exact (congrArg (fun z ↦ (AffineSpace.SpecIso PUnit (.of k)).inv z) hgen).trans
      (Scheme.Hom.apply_genericPoint_of_isIso _)

/-- Blueprint `theorem-verdier-biduality--1`, proof, third paragraph: a coordinate
`p : V ⟶ 𝔸¹_k` over `k` on an affine scheme `V` of finite type over `k` is a closed immersion into
a relative affine space `𝔸ⁿ_{𝔸¹_k}` of finite rank followed by the projection. -/
theorem exists_isClosedImmersion_affineSpace_affineLine {V : Scheme.{u}} [IsAffine V]
    (aV : V ⟶ Spec (.of k)) [LocallyOfFiniteType aV] (p : V ⟶ 𝔸(PUnit; Spec (.of k)))
    (hp : p ≫ 𝔸(PUnit; Spec (.of k)) ↘ Spec (.of k) = aV) :
    ∃ (n : Type u) (_ : Finite n) (i : V ⟶ 𝔸(n; 𝔸(PUnit; Spec (.of k)))),
      IsClosedImmersion i ∧ i ≫ 𝔸(n; 𝔸(PUnit; Spec (.of k))) ↘ 𝔸(PUnit; Spec (.of k)) = p := by
  have hft : aV.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let := aV.appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s, inferInstance, AffineSpace.homOfVector p (Subtype.val : s → Γ(V, ⊤)), ?_,
    AffineSpace.homOfVector_over _ _⟩
  refine AffineSpace.isClosedImmersion_homOfVector _ _ ?_
  have h := congrArg Subalgebra.toSubring hs
  rw [Algebra.adjoin_eq_ring_closure, Algebra.top_toSubring] at h
  rw [eq_top_iff, ← h]
  refine Subring.closure_mono ?_
  rintro y (⟨a, rfl⟩ | hy)
  · refine Or.inl ⟨(𝔸(PUnit; Spec (.of k)) ↘ Spec (.of k)).appTop a, ?_⟩
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hp]
    rfl
  · exact Or.inr ⟨⟨y, hy⟩, rfl⟩

/-- The geometric generic point `Spec K̄ ⟶ 𝔸¹_k` of the affine line, where `K̄` is the algebraic
closure of the function field `κ(η)` of `𝔸¹_k`. -/
noncomputable abbrev affineLineGeometricGenericPoint (k : Type u) [Field k] :
    Spec (.of (AlgebraicClosure
      ((𝔸(PUnit; Spec (.of k))).residueField (genericPoint 𝔸(PUnit; Spec (.of k)))))) ⟶
      𝔸(PUnit; Spec (.of k)) :=
  Scheme.algClosurePoint _ (genericPoint 𝔸(PUnit; Spec (.of k)))

/-- The geometric generic fibre `V ×_{𝔸¹_k} Spec K̄` of a morphism `p : V ⟶ 𝔸¹_k`, where `K̄` is
the algebraic closure of the function field of `𝔸¹_k`. Its structure morphism to `Spec K̄` is
`pullback.snd p (affineLineGeometricGenericPoint k)` and its projection to `V` is
`pullback.fst p (affineLineGeometricGenericPoint k)`. -/
noncomputable abbrev geometricGenericFiber {V : Scheme.{u}} (p : V ⟶ 𝔸(PUnit; Spec (.of k))) :
    Scheme.{u} :=
  pullback p (affineLineGeometricGenericPoint k)

/-- Blueprint `theorem-verdier-biduality--1`, proof, third paragraph: the geometric generic
fibre of a coordinate `p : V ⟶ 𝔸¹_k` on an affine scheme `V` of finite type over `k` is affine
and of finite type over the algebraic closure `K̄` of `k(t)`; in particular its structure
morphism is separated and quasi-compact. -/
theorem geometricGenericFiber_properties {V : Scheme.{u}} [IsAffine V]
    (aV : V ⟶ Spec (.of k)) [LocallyOfFiniteType aV] (p : V ⟶ 𝔸(PUnit; Spec (.of k)))
    (hp : p ≫ 𝔸(PUnit; Spec (.of k)) ↘ Spec (.of k) = aV) :
    IsAffine (geometricGenericFiber p) ∧
      IsAffineHom (pullback.snd p (affineLineGeometricGenericPoint k)) ∧
      IsSeparated (pullback.snd p (affineLineGeometricGenericPoint k)) ∧
      QuasiCompact (pullback.snd p (affineLineGeometricGenericPoint k)) ∧
      LocallyOfFiniteType (pullback.snd p (affineLineGeometricGenericPoint k)) := by
  have : LocallyOfFiniteType p := by
    have : LocallyOfFiniteType (p ≫ 𝔸(PUnit; Spec (.of k)) ↘ Spec (.of k)) := hp ▸ ‹_›
    exact locallyOfFiniteType_of_comp p (𝔸(PUnit; Spec (.of k)) ↘ Spec (.of k))
  have h1 : IsAffineHom (pullback.snd p (affineLineGeometricGenericPoint k)) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  have h2 : LocallyOfFiniteType (pullback.snd p (affineLineGeometricGenericPoint k)) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  exact ⟨isAffine_of_isAffineHom (pullback.snd p _), h1, inferInstance, inferInstance, h2⟩

/-- Blueprint `theorem-verdier-biduality--1`, proof, third paragraph: **the geometric
generic fibre of a coordinate loses one dimension.** Let `V` be locally of finite type over a
field `k` and `p : V ⟶ 𝔸¹_k` a morphism over `k`. Then the geometric generic fibre `V'` of `p`
satisfies `dim V' + 1 ≤ dim V`.

By `lemma-coordinate-projections--1` the generic fibre of `p` over the function field `κ(η)`
of `𝔸¹_k` has dimension at most `dim V - 1`, and `V'` is its base change along the integral
morphism `Spec K̄ ⟶ Spec κ(η)`, which does not raise the dimension (incomparability). -/
theorem topologicalKrullDim_geometricGenericFiber_add_one_le {V : Scheme.{u}}
    (aV : V ⟶ Spec (.of k)) [LocallyOfFiniteType aV] (p : V ⟶ 𝔸(PUnit; Spec (.of k)))
    (hp : p ≫ 𝔸(PUnit; Spec (.of k)) ↘ Spec (.of k) = aV) :
    topologicalKrullDim (geometricGenericFiber p) + 1 ≤ topologicalKrullDim V := by
  let Y := 𝔸(PUnit; Spec (.of k))
  let η := genericPoint Y
  let ι : Y.residueField η ⟶ .of (AlgebraicClosure (Y.residueField η)) :=
    CommRingCat.ofHom (algebraMap (Y.residueField η) (AlgebraicClosure (Y.residueField η)))
  have hι : IsIntegralHom (Spec.map ι) := by
    rw [IsIntegralHom.SpecMap_iff]
    exact fun a ↦ Algebra.IsIntegral.isIntegral (R := Y.residueField η) a
  have h1 : topologicalKrullDim (geometricGenericFiber p) ≤ topologicalKrullDim (p.fiber η) := by
    let e := pullback.congrHom (f₁ := p) (g₁ := affineLineGeometricGenericPoint k) rfl
      (show _ = Spec.map ι ≫ Y.fromSpecResidueField η from rfl) ≪≫
      (pullbackLeftPullbackSndIso p (Y.fromSpecResidueField η) (Spec.map ι)).symm
    have : IsIntegralHom (pullback.fst (pullback.snd p (Y.fromSpecResidueField η)) (Spec.map ι)) :=
      MorphismProperty.pullback_fst (P := @IsIntegralHom) _ _ hι
    refine (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).trans_le ?_
    exact topologicalKrullDim_le_of_continuous
      (pullback.fst (pullback.snd p (Y.fromSpecResidueField η)) (Spec.map ι)).continuous
      fun _ _ ↦ (pullback.fst (pullback.snd p (Y.fromSpecResidueField η))
        (Spec.map ι)).eq_of_specializes_of_apply_eq_of_isIntegralHom
  have h2 := topologicalKrullDim_fiber_genericPoint_add_one_le aV p hp
  have h3 : topologicalKrullDim (aV.fiber (genericPoint (Spec (.of k)))) ≤
      topologicalKrullDim V :=
    (IsPreimmersion.isEmbedding (aV.fiberι _)).isInducing.topologicalKrullDim_le
  calc topologicalKrullDim (geometricGenericFiber p) + 1
      ≤ topologicalKrullDim (p.fiber η) + 1 := by gcongr
    _ ≤ topologicalKrullDim V := h2.trans h3

/-- The form of `topologicalKrullDim_geometricGenericFiber_add_one_le` used in the dimension
induction: if `dim V ≤ d`, then the geometric generic fibre of a coordinate has dimension at most
`d - 1`. -/
theorem topologicalKrullDim_geometricGenericFiber_le {V : Scheme.{u}}
    (aV : V ⟶ Spec (.of k)) [LocallyOfFiniteType aV] (p : V ⟶ 𝔸(PUnit; Spec (.of k)))
    (hp : p ≫ 𝔸(PUnit; Spec (.of k)) ↘ Spec (.of k) = aV) {d : ℕ}
    (hd : topologicalKrullDim V ≤ d) :
    topologicalKrullDim (geometricGenericFiber p) ≤ ((d - 1 : ℕ) : WithBot ℕ∞) :=
  WithBot.ENat.le_natCast_sub_one_of_add_one_le
    ((topologicalKrullDim_geometricGenericFiber_add_one_le aV p hp).trans hd)

/-- Blueprint `theorem-verdier-biduality--1`, proof, fourth paragraph: **geometric points
over `x` factor through the geometric generic fibre.** If `p : V ⟶ 𝔸¹_k` sends `x` to the
generic point, the geometric point `V.algClosurePoint x` factors through the projection
`V' ⟶ V` of the geometric generic fibre: embed the algebraic closure `K̄` of `κ(η)` into the
algebraic closure of `κ(x)` over `κ(η)`. -/
theorem exists_comp_geometricGenericFiber_fst_eq_algClosurePoint {V : Scheme.{u}}
    (p : V ⟶ 𝔸(PUnit; Spec (.of k))) {x : V} (hx : p x = genericPoint 𝔸(PUnit; Spec (.of k))) :
    ∃ s' : Spec (.of (AlgebraicClosure (V.residueField x))) ⟶ geometricGenericFiber p,
      s' ≫ pullback.fst p (affineLineGeometricGenericPoint k) = V.algClosurePoint x := by
  let Y := 𝔸(PUnit; Spec (.of k))
  let η := genericPoint Y
  obtain ⟨φ, hφ⟩ := p.exists_residueField_hom_of_apply_eq hx
  let : Algebra (Y.residueField η) (AlgebraicClosure (V.residueField x)) :=
    (φ ≫ CommRingCat.ofHom (algebraMap (V.residueField x) _)).hom.toAlgebra
  let j : AlgebraicClosure (Y.residueField η) →ₐ[Y.residueField η]
      AlgebraicClosure (V.residueField x) := IsAlgClosed.lift
  refine ⟨pullback.lift (V.algClosurePoint x) (Spec.map (CommRingCat.ofHom j.toRingHom)) ?_,
    pullback.lift_fst _ _ _⟩
  change (Spec.map (CommRingCat.ofHom (algebraMap (V.residueField x) _)) ≫
      V.fromSpecResidueField x) ≫ p =
    Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField η) _)) ≫ Y.fromSpecResidueField η
  rw [Category.assoc, ← hφ, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext a
  exact (j.commutes a).symm

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Blueprint `theorem-verdier-biduality--1`, proof, fourth paragraph: if `p : V ⟶ 𝔸¹_k`
sends `x` to the generic point and the pullback of an étale sheaf `F` on `V` to the geometric
generic fibre `V'` of `p` has zero stalks at all geometric points, then the stalk of `F` at the
geometric point `V.algClosurePoint x` is zero. -/
theorem isZero_sheafFiber_algClosurePoint_of_isZero_sheafFiber_upperStar {V : Scheme.{u}}
    (p : V ⟶ 𝔸(PUnit; Spec (.of k))) {x : V} (hx : p x = genericPoint 𝔸(PUnit; Spec (.of k)))
    (F : Sheaf V.smallEtaleTopology A)
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ geometricGenericFiber p),
      IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj
        ((Etale.upperStar A (pullback.fst p (affineLineGeometricGenericPoint k))).obj F))) :
    IsZero ((Scheme.pointSmallEtale (V.algClosurePoint x)).sheafFiber.obj F) := by
  obtain ⟨s', hs'⟩ := exists_comp_geometricGenericFiber_fst_eq_algClosurePoint p hx
  rw [← hs']
  exact IsZero.of_iso (h _ s') ((Etale.upperStarCompSheafFiberIso A _ s').app F).symm

/-- Blueprint `theorem-verdier-biduality--1`, proof, fourth paragraph: if `p : V ⟶ 𝔸¹_k`
sends `x` to the generic point and the pullback of an étale sheaf `F` on `V` to the geometric
generic fibre of `p` is zero, then the stalk of `F` at the geometric point `V.algClosurePoint x`
is zero. -/
theorem isZero_sheafFiber_algClosurePoint_of_isZero_upperStar {V : Scheme.{u}}
    (p : V ⟶ 𝔸(PUnit; Spec (.of k))) {x : V} (hx : p x = genericPoint 𝔸(PUnit; Spec (.of k)))
    (F : Sheaf V.smallEtaleTopology A)
    (h : IsZero ((Etale.upperStar A (pullback.fst p (affineLineGeometricGenericPoint k))).obj F)) :
    IsZero ((Scheme.pointSmallEtale (V.algClosurePoint x)).sheafFiber.obj F) :=
  isZero_sheafFiber_algClosurePoint_of_isZero_sheafFiber_upperStar A p hx F
    fun _ _ _ s ↦ (Scheme.pointSmallEtale s).sheafFiber.map_isZero h

end AlgebraicGeometry
