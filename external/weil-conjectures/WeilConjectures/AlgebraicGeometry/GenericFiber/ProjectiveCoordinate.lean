/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# A projective coordinate complement is finite

Let `p : Y ⟶ S` be proper over an integral locally noetherian scheme, covered by finitely many
opens `Y_α`, each embedded as a closed subscheme of an affine space `𝔸^{σ_α}_S`. Choose for every
coordinate `t_{α r} : Y_α ⟶ 𝔸¹_S` a nonempty (equivalently, dense) open `V_{α r} ⊆ 𝔸¹_S`. Over a
nonempty open of `S`, the complement `Z` of the union of the `t_{α r}⁻¹ V_{α r}` is finite over
`S`. This is the first step of Deligne's generic constructibility theorem
(`theorem-generic-constructibility-base-change-rj`).

The proof computes the generic fibre: over the residue field `K` of the generic point, the
complement of each `V_{α r}` in `𝔸¹_K` lies in the zero set of a nonzero polynomial `P_{α r}`, so
the generic fibre of the complement is cut out in `Spec K[t]` by the `P_{α r}(t_{α r})` and is
finite. Zariski's main theorem then gives finiteness over a neighbourhood of the generic point,
first for the reduced subscheme on the complement and then, by comparing fibres, for every closed
subscheme supported there.

## Main statements

- `AlgebraicGeometry.exists_isFinite_morphismRestrict_of_range_subset`
  (`lemma-coordinate-projections--2`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Over a field `K`, only finitely many primes of `K[X_r : r ∈ σ]` (`σ` finite) contain
the elements `P_r(X_r)` for given nonzero one-variable polynomials `P_r`. -/
theorem finite_setOf_forall_aeval_X_mem {K : Type u} [Field K] {σ : Type u} [Finite σ]
    (P : σ → Polynomial K) (hP : ∀ r, P r ≠ 0) :
    {q : PrimeSpectrum (MvPolynomial σ K) |
      ∀ r, Polynomial.aeval (MvPolynomial.X r) (P r) ∈ q.asIdeal}.Finite := by
  set J : Ideal (MvPolynomial σ K) :=
    Ideal.span (Set.range fun r ↦ Polynomial.aeval (MvPolynomial.X r) (P r))
  have hX (r : σ) : _root_.IsIntegral K (Ideal.Quotient.mkₐ K J (MvPolynomial.X r)) := by
    refine IsAlgebraic.isIntegral ⟨P r, hP r, ?_⟩
    rw [Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨r, rfl⟩
  have : Algebra.IsIntegral K (MvPolynomial σ K ⧸ J) := by
    refine ⟨fun a ↦ ?_⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K J a
    induction p using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.algHom_C]; exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p r h => rw [map_mul]; exact h.mul (hX r)
  have : Module.Finite K (MvPolynomial σ K ⧸ J) := Algebra.IsIntegral.finite
  have : IsArtinianRing (MvPolynomial σ K ⧸ J) := IsArtinianRing.of_finite K _
  refine (Set.finite_range (PrimeSpectrum.comap (Ideal.Quotient.mk J))).subset fun q hq ↦ ?_
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le]
  rintro _ ⟨r, rfl⟩
  exact hq r

/-- Over an affine base, `AffineSpace.reindex` corresponds to `MvPolynomial.rename`. -/
@[reassoc]
lemma AffineSpace.SpecIso_inv_reindex {n m : Type u} (i : m → n) (R : CommRingCat.{u}) :
    (SpecIso n R).inv ≫ reindex i (Spec R) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename i).toRingHom) ≫ (SpecIso m R).inv := by
  ext1
  · simp only [Category.assoc, reindex_over, SpecIso_inv_over, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext; simp
  · simp only [TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, CommRingCat.comp_apply]
    conv_lhs => enter [2]; tactic => exact reindex_appTop_coord _ _ _
    conv_rhs => enter [2]; tactic => exact SpecIso_inv_appTop_coord _ _
    conv_lhs => tactic => exact SpecIso_inv_appTop_coord _ _
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp

/-- Over a field `K`, given nonempty opens `V_r` of `𝔸¹_K = Spec K[X]`, only finitely many points
of `Spec K[X_r : r ∈ σ]` (`σ` finite) have all their coordinate projections outside `V_r`. -/
theorem finite_setOf_forall_SpecMap_rename_notMem {K : Type u} [Field K] {σ : Type u} [Finite σ]
    (V : σ → (Spec (.of (MvPolynomial PUnit.{u + 1} K))).Opens)
    (hV : ∀ r, (V r : Set (Spec (.of (MvPolynomial PUnit.{u + 1} K)))).Nonempty) :
    {x : Spec (.of (MvPolynomial σ K)) | ∀ r,
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename fun _ : PUnit ↦ r).toRingHom) x ∉
        V r}.Finite := by
  have H (r : σ) : ∃ f : MvPolynomial PUnit.{u + 1} K, f ≠ 0 ∧
      ∀ x : PrimeSpectrum (MvPolynomial PUnit.{u + 1} K), x ∉ V r → f ∈ x.asIdeal := by
    obtain ⟨x, hx⟩ := hV r
    obtain ⟨_, ⟨f, rfl⟩, hxf, hfV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx (V r).2
    refine ⟨f, ?_, fun y hy ↦ ?_⟩
    · rintro rfl
      simp at hxf
    · by_contra h
      exact hy (hfV h)
  choose f hf0 hfV using H
  have key (r : σ) (p : MvPolynomial PUnit.{u + 1} K) :
      Polynomial.aeval (MvPolynomial.X r) (MvPolynomial.uniqueAlgEquiv K PUnit p) =
        MvPolynomial.rename (fun _ : PUnit ↦ r) p := by
    change ((Polynomial.aeval (MvPolynomial.X r)).comp
      (MvPolynomial.uniqueAlgEquiv K PUnit).toAlgHom) p = _
    congr 1
    apply MvPolynomial.algHom_ext
    intro i
    simp
  refine (finite_setOf_forall_aeval_X_mem (fun r ↦ MvPolynomial.uniqueAlgEquiv K PUnit (f r))
    fun r ↦ (map_ne_zero_iff _ (AlgEquiv.injective _)).mpr (hf0 r)).subset fun x hx r ↦ ?_
  rw [key]
  exact hfV r _ (hx r)

/-- Over an irreducible scheme `S` with generic point `η`, given nonempty opens `V_r` of `𝔸¹_S`,
only finitely many points of `𝔸(σ; S)` (`σ` finite) lying over `η` have all their coordinate
projections outside `V_r`. -/
theorem finite_setOf_over_genericPoint {S : Scheme.{u}} [IrreducibleSpace S] {σ : Type u}
    [Finite σ] (V : σ → 𝔸(PUnit; S).Opens)
    (hV : ∀ r, (V r : Set 𝔸(PUnit; S)).Nonempty) :
    {x : 𝔸(σ; S) | (𝔸(σ; S) ↘ S) x = genericPoint S ∧
      ∀ r, AffineSpace.reindex (fun _ : PUnit ↦ r) S x ∉ V r}.Finite := by
  set η := genericPoint S
  set g := S.fromSpecResidueField η
  have hg (z : Spec (S.residueField η)) : g z = η := S.fromSpecResidueField_apply η z
  have hzz (n : Type u) (z : 𝔸(n; Spec (S.residueField η))) :
      (AffineSpace.SpecIso n (S.residueField η)).inv
        ((AffineSpace.SpecIso n (S.residueField η)).hom z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
  set V' : σ → (Spec (.of (MvPolynomial PUnit.{u + 1} (S.residueField η)))).Opens := fun r ↦
    (AffineSpace.SpecIso PUnit (S.residueField η)).inv ⁻¹ᵁ (AffineSpace.map PUnit g ⁻¹ᵁ V r)
  have hV' (r : σ) :
      (V' r : Set (Spec (.of (MvPolynomial PUnit.{u + 1} (S.residueField η))))).Nonempty := by
    obtain ⟨v, hv⟩ := hV r
    have hη : η ∈ (𝔸(PUnit; S) ↘ S) '' (V r : Set 𝔸(PUnit; S)) :=
      (genericPoint_spec S).mem_open_set_iff (AffineSpace.isOpenMap_over _ _ (V r).2) |>.mpr
        ⟨_, trivial, v, hv, rfl⟩
    obtain ⟨v', hv', hv'η⟩ := hη
    obtain ⟨pt⟩ : Nonempty (Spec (S.residueField η)) := inferInstance
    obtain ⟨z, hz, -⟩ :=
      Scheme.exists_preimage_of_isPullback (AffineSpace.isPullback_map (n := PUnit) g)
      v' pt (by rw [hv'η, hg])
    refine ⟨(AffineSpace.SpecIso PUnit (S.residueField η)).hom z, ?_⟩
    change (AffineSpace.map PUnit g) ((AffineSpace.SpecIso PUnit (S.residueField η)).inv
      ((AffineSpace.SpecIso PUnit (S.residueField η)).hom z)) ∈ V r
    rw [hzz, hz]
    exact hv'
  refine (((finite_setOf_forall_SpecMap_rename_notMem V' hV').image
    (AffineSpace.SpecIso σ (S.residueField η)).inv).image (AffineSpace.map σ g)).subset ?_
  rintro x ⟨hx, hxV⟩
  obtain ⟨pt⟩ : Nonempty (Spec (S.residueField η)) := inferInstance
  obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (AffineSpace.isPullback_map (n := σ) g)
    x pt (by rw [hx, hg])
  refine ⟨z, ⟨(AffineSpace.SpecIso σ (S.residueField η)).hom z, fun r hr ↦ hxV r ?_, ?_⟩, rfl⟩
  · change (AffineSpace.map PUnit g) ((AffineSpace.SpecIso PUnit (S.residueField η)).inv
      (Spec.map _ ((AffineSpace.SpecIso σ (S.residueField η)).hom z))) ∈ V r at hr
    rw [← Scheme.Hom.comp_apply (Spec.map _), ← AffineSpace.SpecIso_inv_reindex,
      Scheme.Hom.comp_apply, hzz, ← Scheme.Hom.comp_apply, ← AffineSpace.map_reindex,
      Scheme.Hom.comp_apply] at hr
    exact hr
  · exact hzz σ z

/-- Blueprint `lemma-coordinate-projections--2`: A projective coordinate complement is
finite.

Let `S` be integral and locally noetherian (the blueprint takes `S = Spec A` affine) and let
`p : Y ⟶ S` be proper (the blueprint takes `p` projective). Let `Y = ⋃_α Y_α` be a finite open
cover with closed immersions `e_α : Y_α ⟶ 𝔸^{σ_α}_S` over `S`, and for each coordinate
`t_{α r} : Y_α ⟶ 𝔸¹_S` let `V_{α r} ⊆ 𝔸¹_S` be a nonempty open. Then there is a nonempty open
`W ⊆ S` over which every closed subscheme `Z` of `Y` supported in the complement of
`⋃_{α, r} t_{α r}⁻¹(V_{α r})` (for instance the reduced one) is finite over `W`. -/
theorem exists_isFinite_morphismRestrict_of_range_subset {S Y : Scheme.{u}} [IsIntegral S]
    [IsLocallyNoetherian S] (p : Y ⟶ S) [IsProper p] {ι : Type u} [Finite ι]
    (U : ι → Y.Opens) (hU : ⨆ α, U α = ⊤) (σ : ι → Type u) [∀ α, Finite (σ α)]
    (e : ∀ α, (U α).toScheme ⟶ 𝔸(σ α; S)) [∀ α, IsClosedImmersion (e α)]
    (he : ∀ α, e α ≫ 𝔸(σ α; S) ↘ S = (U α).ι ≫ p)
    (V : ∀ α, σ α → 𝔸(PUnit; S).Opens) (hV : ∀ α r, (V α r : Set 𝔸(PUnit; S)).Nonempty) :
    ∃ W : S.Opens, (W : Set S).Nonempty ∧
      ∀ (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i],
        Set.range i ⊆ (⋃ (α : ι) (r : σ α), (U α).ι ''
          ((e α ≫ AffineSpace.reindex (fun _ : PUnit ↦ r) S) ⁻¹' (V α r : Set 𝔸(PUnit; S))))ᶜ →
        IsFinite ((i ≫ p) ∣_ W) := by
  set C : Set Y := (⋃ (α : ι) (r : σ α), (U α).ι ''
    ((e α ≫ AffineSpace.reindex (fun _ : PUnit ↦ r) S) ⁻¹' (V α r : Set 𝔸(PUnit; S))))ᶜ
  have hC : IsClosed C := by
    refine (isOpen_iUnion fun α ↦ isOpen_iUnion fun r ↦ ?_).isClosed_compl
    exact (U α).ι.isOpenEmbedding.isOpenMap _
      ((V α r).2.preimage (e α ≫ AffineSpace.reindex (fun _ : PUnit ↦ r) S).continuous)
  have hres {X T : Scheme.{u}} (f : X ⟶ T) (W : T.Opens) (x : (f ⁻¹ᵁ W).toScheme) :
      W.ι ((f ∣_ W) x) = f ((f ⁻¹ᵁ W).ι x) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  -- The fibre of `C` over the generic point is finite.
  have hη : (C ∩ p ⁻¹' {genericPoint S}).Finite := by
    refine (Set.finite_iUnion fun α ↦ ((finite_setOf_over_genericPoint (V α) (hV α)).preimage
      (e α).isClosedEmbedding.injective.injOn).image (U α).ι).subset ?_
    rintro y ⟨hyC, hyη⟩
    obtain ⟨α, hα⟩ : ∃ α, y ∈ U α := by
      simpa using (hU.ge (Set.mem_univ y) : y ∈ ⨆ α, U α)
    refine Set.mem_iUnion.mpr ⟨α, ⟨y, hα⟩, ⟨?_, fun r hr ↦ hyC ?_⟩, rfl⟩
    · rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
      exact hyη
    · exact Set.mem_iUnion₂.mpr ⟨α, r, ⟨y, hα⟩, hr, rfl⟩
  -- The reduced closed subscheme supported on `C`.
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨C, hC⟩ : TopologicalSpace.Closeds Y)
  have hrange : Set.range I.subschemeι = C := by
    simp [I, Scheme.IdealSheafData.range_subschemeι]
  obtain ⟨W, hηW, hW⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton
    (I.subschemeι ≫ p) (genericPoint S) <| by
      refine (hη.preimage I.subschemeι.isClosedEmbedding.injective.injOn).subset fun z hz ↦ ?_
      exact ⟨hrange ▸ ⟨z, rfl⟩, hz⟩
  refine ⟨W, ⟨_, hηW⟩, fun Z i _ hiC ↦ ?_⟩
  have hfib (w : W) : (C ∩ p ⁻¹' {w.1}).Finite := by
    refine ((Scheme.Hom.finite_preimage_singleton ((I.subschemeι ≫ p) ∣_ W) w).image
      (((I.subschemeι ≫ p) ⁻¹ᵁ W).ι ≫ I.subschemeι)).subset ?_
    rintro y ⟨hyC, hyw⟩
    obtain ⟨z, rfl⟩ := hrange.ge hyC
    have hzW : z ∈ (I.subschemeι ≫ p) ⁻¹ᵁ W := by
      change p (I.subschemeι z) ∈ W
      rw [hyw]
      exact w.2
    refine ⟨⟨z, hzW⟩, Subtype.ext ?_, rfl⟩
    exact (hres _ W ⟨z, hzW⟩).trans hyw
  have : LocallyQuasiFinite ((i ≫ p) ∣_ W) := by
    refine .of_finite_preimage_singleton _ fun w ↦ ?_
    refine ((hfib w).preimage (f := fun z ↦ i (((i ≫ p) ⁻¹ᵁ W).ι z))
      (i.isClosedEmbedding.injective.comp
        ((i ≫ p) ⁻¹ᵁ W).ι.isOpenEmbedding.injective).injOn).subset
      fun z hz ↦ ⟨hiC ⟨_, rfl⟩, ?_⟩
    change p (i (((i ≫ p) ⁻¹ᵁ W).ι z)) = w.1
    rw [← Scheme.Hom.comp_apply i p, ← hres, hz]
    rfl
  exact IsFinite.of_isProper_of_locallyQuasiFinite _
end AlgebraicGeometry
