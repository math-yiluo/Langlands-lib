/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLimitAux
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLimitDimension
public import WeilConjectures.AlgebraicGeometry.DimensionFiniteTypeField
public import WeilConjectures.RingTheory.HenselianSepClosedSubfield
public import WeilConjectures.RingTheory.KrullDimensionAdjoinTranscendental
public import WeilConjectures.RingTheory.FiniteTypeSubalgebraUnion
public import WeilConjectures.AlgebraicGeometry.ClosedPointResidueField
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension

/-!
# The strict henselization at a non-closed point as a limit of smaller schemes

Let `K` be a field, `X` a scheme of finite type over `K` and `s : Spec Ω ⟶ X` a geometric point
lying over a point `x` with `trdeg_K κ(x) > 0`, equivalently a non-closed point `x`. Let
`X' = Spec 𝒪^{sh}_{X,s}` be the strict localization (`AlgebraicGeometry.Scheme.strictLocalization`;
recall that it is also the limit of the affine pointed étale neighbourhoods of `s`,
`AlgebraicGeometry.Scheme.isLimitStrictLocalizationConeOver`). Then there is a separably closed
field `L` over `K` such that `X'` is an `L`-scheme and a cofiltered limit, with affine transition
maps, of affine schemes `X_i` of finite type over `L` with `dim X_i < dim X`
(blueprint `corollary-open-direct-image-over-field--2`, Stacks 0F0U).

## References

- Stacks Project, Lemma 0F0U, <https://stacks.math.columbia.edu/tag/0F0U>
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry.Scheme

/-- Blueprint `corollary-open-direct-image-over-field--2`: the strict henselization as a limit.

Let `K` be a field, `aX : X ⟶ Spec K` of finite type and `s : Spec Ω ⟶ X` a geometric point
(`Ω` separably closed) lying over a non-closed point `x` of `X` (for `X` of finite type over `K`
this is equivalent to `trdeg_K κ(x) > 0`). Then there are

* a separably closed field `L` over `K` and a morphism `ℓ : X' ⟶ Spec L` from the strict
  localization `X' = Spec 𝒪^{sh}_{X,s}`, compatible with `X' ⟶ X ⟶ Spec K` and
  `Spec L ⟶ Spec K`;
* a small cofiltered category `I`, a diagram `D : I ⥤ Scheme` and a limit cone `π` from `X'`
  to `D`;
* structure morphisms `q i : D i ⟶ Spec L`, locally of finite type, compatible with the
  transition maps and with `ℓ`,

such that every `D i` is affine, all transition maps are affine, and `dim D i < dim X`. -/
@[stacks 0F0U]
theorem exists_isLimit_strictLocalization_of_not_isClosed {K Ω : Type u} [Field K] [Field Ω]
    [IsSepClosed Ω] {X : Scheme.{u}} (aX : X ⟶ Spec (.of K)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] (s : Spec (.of Ω) ⟶ X) (hs : ¬ IsClosed {s (IsLocalRing.closedPoint Ω)}) :
    ∃ (L : Type u) (_ : Field L) (_ : IsSepClosed L) (_ : Algebra K L)
      (ℓ : strictLocalization s ⟶ Spec (.of L))
      (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u}) (π : (Functor.const I).obj (strictLocalization s) ⟶ D)
      (q : ∀ i, D.obj i ⟶ Spec (.of L)),
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      ℓ ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = strictLocalizationToBase s ≫ aX ∧
      (∀ i, IsAffine (D.obj i)) ∧ (∀ ⦃i j : I⦄ (f : i ⟶ j), IsAffineHom (D.map f)) ∧
      (∀ i, LocallyOfFiniteType (q i)) ∧ (∀ i, π.app i ≫ q i = ℓ) ∧
      (∀ ⦃i j : I⦄ (f : i ⟶ j), D.map f ≫ q j = q i) ∧
      ∀ i, topologicalKrullDim (D.obj i) < topologicalKrullDim X := by
  classical
  let κR : K →+* strictHenselization s := (Spec.preimage (strictLocalizationToBase s ≫ aX)).hom
  let : Algebra K (strictHenselization s) := κR.toAlgebra
  let : Algebra K Ω := (Spec.preimage (s ≫ aX)).hom.toAlgebra
  obtain ⟨N₀, c₀, hc₀⟩ := exists_transcendental_pt aX hs
  let ev : strictHenselization s →ₐ[K] Ω :=
    { (strictHenselizationEval s).hom with
      commutes' k := congr($(preimage_comp_strictHenselizationEval aX) k) }
  let tR := N₀.ι c₀
  have hunit (g : nonZeroDivisors K[X]) : IsUnit (aeval tR (g : K[X])) := by
    refine isUnit_of_strictHenselizationEval_ne_zero fun h ↦
      hc₀ ⟨g, nonZeroDivisors.ne_zero g.2, ?_⟩
    have hev : ev tR = N₀.pt c₀ := SpecPointedEtaleNeighborhood.strictHenselizationEval_ι N₀ c₀
    have : ev (aeval tR (g : K[X])) = 0 := h
    rwa [← Polynomial.aeval_algHom_apply, hev] at this
  let F := FractionRing K[X]
  let φ : F →+* strictHenselization s :=
    IsLocalization.lift (M := nonZeroDivisors K[X]) (g := (aeval tR).toRingHom) hunit
  have hφ (p : K[X]) : φ (algebraMap K[X] F p) = aeval tR p := IsLocalization.lift_eq _ _
  obtain ⟨L, _, _, ψ, ρ, hψρ⟩ := HenselianLocalRing.exists_isSepClosed_factor φ
  let : Algebra K L := (ρ.comp ((algebraMap K[X] F).comp Polynomial.C)).toAlgebra
  let : Algebra L (strictHenselization s) := ψ.toAlgebra
  have hψK (k : K) : ψ (algebraMap K L k) = κR k := by
    change (ψ.comp ρ) _ = _
    rw [hψρ, RingHom.comp_apply, hφ, aeval_C]
    rfl
  have : IsScalarTower K L (strictHenselization s) :=
    .of_algebraMap_eq fun k ↦ (hψK k).symm
  let t : L := ρ (algebraMap K[X] F Polynomial.X)
  have hψt : algebraMap L (strictHenselization s) t = tR := by
    change (ψ.comp ρ) _ = _
    rw [hψρ, hφ, aeval_X]
  have ht : Transcendental K t := by
    rintro ⟨p, hp, hpt⟩
    have h := hunit ⟨p, mem_nonZeroDivisors_of_ne_zero hp⟩
    rw [← hψt] at h
    have : algebraMap L _ (aeval t p) = aeval (algebraMap L (strictHenselization s) t) p :=
      (Polynomial.aeval_algebraMap_apply _ _ _).symm
    rw [← this, hpt, map_zero] at h
    exact not_isUnit_zero h
  -- the index set: the `L`-subalgebras generated by neighbourhoods containing `tR`
  let Dset : Set (Subalgebra L (strictHenselization s)) :=
    {D | ∃ N : SpecPointedEtaleNeighborhood s, tR ∈ Set.range N.ι ∧
      D = Algebra.adjoin L (Set.range N.ι)}
  have hdir : DirectedOn (· ≤ ·) Dset := by
    rintro _ ⟨N₁, h₁, rfl⟩ _ ⟨N₂, -, rfl⟩
    obtain ⟨N₃, h₁₃, h₂₃⟩ := N₁.exists_range_subset N₂
    exact ⟨_, ⟨N₃, h₁₃ h₁, rfl⟩, Algebra.adjoin_mono h₁₃, Algebra.adjoin_mono h₂₃⟩
  have hcov (r : strictHenselization s) : ∃ D ∈ Dset, r ∈ D := by
    obtain ⟨N, hN⟩ := exists_specPointedEtaleNeighborhood_forall_mem_range 2 ![r, tR]
    exact ⟨_, ⟨N, by simpa using hN 1, rfl⟩, Algebra.subset_adjoin (by simpa using hN 0)⟩
  have hne : Dset.Nonempty := by
    obtain ⟨D, hD, -⟩ := hcov 0
    exact ⟨D, hD⟩
  have : IsFiltered Dset := Subalgebra.isFiltered_of_directedOn hdir hne
  have hdimX := topologicalKrullDim_lt_top_of_finiteType aX
  have hD (D : Subalgebra L (strictHenselization s)) (hD : D ∈ Dset) :
      Algebra.FiniteType L D ∧ ringKrullDim D + 1 ≤ topologicalKrullDim X := by
    obtain ⟨N, ⟨c, hc⟩, rfl⟩ := hD
    let : Algebra K N.R := (Spec.preimage (N.hom ≫ aX)).hom.toAlgebra
    have : Algebra.FiniteType K N.R := N.finiteType_preimage aX
    let ιN : N.R →ₐ[K] strictHenselization s :=
      { N.ι.hom with commutes' k := congr($(N.preimage_comp_ι aX) k) }
    refine ⟨Algebra.finiteType_adjoin_range ιN, ?_⟩
    refine (ringKrullDim_adjoin_range_add_one_le ιN ht (c := c) (hc.trans hψt.symm)).trans ?_
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_le_of_locallyQuasiFinite N.hom
  let c := Scheme.Spec.mapCone (Subalgebra.cocone Dset).op
  refine ⟨L, inferInstance, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom ψ),
    Dsetᵒᵖ, inferInstance, inferInstance, (Subalgebra.diagram Dset).op ⋙ Scheme.Spec, c.π,
    fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap L i.unop.1)),
    ⟨isLimitOfPreserves Scheme.Spec (Subalgebra.isColimitCocone hdir hcov).op⟩, ?_,
    fun i ↦ inferInstanceAs (IsAffine (Spec _)),
    fun i j f ↦ inferInstanceAs (IsAffineHom (Spec.map _)), fun i ↦ ?_, fun i ↦ ?_, fun i j f ↦ ?_,
    fun i ↦ ?_⟩
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : ψ.comp (algebraMap K L) = κR := RingHom.ext hψK
    rw [this, CommRingCat.ofHom_hom, Spec.map_preimage]
  · have := (hD _ i.unop.2).1
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr this)
  · exact (Spec.map_comp (CommRingCat.ofHom (algebraMap L i.unop.1))
      (CommRingCat.ofHom i.unop.1.val.toRingHom)).symm.trans rfl
  · exact (Spec.map_comp (CommRingCat.ofHom (algebraMap L j.unop.1))
      (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f.unop)).toRingHom)).symm.trans rfl
  · have h := (hD _ i.unop.2).2
    have hnt : ringKrullDim i.unop.1 ≠ ⊥ :=
      ne_bot_of_le_ne_bot WithBot.coe_ne_bot ringKrullDim_nonneg_of_nontrivial
    change topologicalKrullDim (PrimeSpectrum i.unop.1) < _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hnt
    rw [← hm] at h ⊢
    induction m using ENat.recTopCoe with
    | top =>
      refine absurd (lt_of_le_of_lt h hdimX) ?_
      rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      exact lt_irrefl _
    | coe n =>
      refine lt_of_lt_of_le ?_ h
      exact_mod_cast Nat.lt_succ_self n

/-- The two descriptions of the `K`-algebra structure of the residue fields of a `K`-scheme
agree: `residueFieldHomOfOver` (through global sections) and `Hom.residueFieldAlgebraMap`
(through the residue field of `Spec K`). -/
lemma residueFieldHomOfOver_eq_residueFieldAlgebraMap {K : Type u} [Field K] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of K)) (x : X) :
    residueFieldHomOfOver aX x = aX.residueFieldAlgebraMap x := by
  have h₁ : X.fromSpecStalk x ≫ aX = Spec.map (X.presheaf.germ ⊤ x trivial) ≫
      Spec.map aX.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of K)).inv := by
    rw [← fromSpecStalk_toSpecΓ, Category.assoc, ← Category.assoc X.toSpecΓ,
      ← Scheme.toSpecΓ_naturality, Category.assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have h₂ : Spec.map (CommRingCat.ofHom (residueFieldHomOfOver aX x)) =
      Spec.map (CommRingCat.ofHom (aX.residueFieldAlgebraMap x)) := by
    rw [aX.specMap_residueFieldAlgebraMap, fromSpecResidueField, Category.assoc, h₁,
      residueFieldHomOfOver, CommRingCat.ofHom_hom, Spec.map_comp, Spec.map_comp, Spec.map_comp]
    simp only [Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h₂)

/-- A point `x` of a scheme locally of finite type over a field `K` with `trdeg_K κ(x) > 0` is
not closed. -/
lemma not_isClosed_singleton_of_residueFieldTrdeg_pos {K : Type u} [Field K] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of K)) [LocallyOfFiniteType aX] {x : X}
    (hx : 0 < residueFieldTrdeg aX x) : ¬ IsClosed {x} := by
  intro hc
  let := (aX.residueFieldAlgebraMap x).toAlgebra
  have : Algebra.IsAlgebraic K (X.residueField x) :=
    (aX.isClosed_singleton_iff_isAlgebraic_residueField x).1 hc
  have h : residueFieldTrdeg aX x = Algebra.trdeg K (X.residueField x) := by
    rw [residueFieldTrdeg, residueFieldHomOfOver_eq_residueFieldAlgebraMap]
  rw [h, trdeg_eq_zero] at hx
  exact lt_irrefl _ hx

/-- Blueprint `corollary-open-direct-image-over-field--2`, in the form of the blueprint: the strict
henselization at a geometric point over a point `x` with `trdeg_K κ(x) > 0` is a limit as in
`exists_isLimit_strictLocalization_of_not_isClosed`. -/
@[stacks 0F0U]
theorem exists_isLimit_strictLocalization_of_residueFieldTrdeg_pos {K Ω : Type u} [Field K]
    [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}} (aX : X ⟶ Spec (.of K)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] (s : Spec (.of Ω) ⟶ X)
    (hs : 0 < residueFieldTrdeg aX (s (IsLocalRing.closedPoint Ω))) :
    ∃ (L : Type u) (_ : Field L) (_ : IsSepClosed L) (_ : Algebra K L)
      (ℓ : strictLocalization s ⟶ Spec (.of L))
      (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u}) (π : (Functor.const I).obj (strictLocalization s) ⟶ D)
      (q : ∀ i, D.obj i ⟶ Spec (.of L)),
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      ℓ ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = strictLocalizationToBase s ≫ aX ∧
      (∀ i, IsAffine (D.obj i)) ∧ (∀ ⦃i j : I⦄ (f : i ⟶ j), IsAffineHom (D.map f)) ∧
      (∀ i, LocallyOfFiniteType (q i)) ∧ (∀ i, π.app i ≫ q i = ℓ) ∧
      (∀ ⦃i j : I⦄ (f : i ⟶ j), D.map f ≫ q j = q i) ∧
      ∀ i, topologicalKrullDim (D.obj i) < topologicalKrullDim X :=
  exists_isLimit_strictLocalization_of_not_isClosed aX s
    (not_isClosed_singleton_of_residueFieldTrdeg_pos aX hs)

end AlgebraicGeometry.Scheme
