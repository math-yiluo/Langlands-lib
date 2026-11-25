import Langlands.GaloisCohomology.Global.EulerCharacteristic.Ratio
import Langlands.Cohomology.Profinite.Mackey.Cohomology

/-!
# The infinite places of a subfield of `K_S` as double cosets

Let `K` be a number field, `Ω` a Galois extension, `S` a set of finite places of `K`, `G_S` the Galois
group of the maximal extension `K_S ⊆ Ω` unramified outside `S`, `ι : PlaceEmbeddings K Ω`, and `L` a
number field with `K → L → Ω` and `L ⊆ K_S`; let `U ⊆ G_S` be the open subgroup fixing `L`. For a
real place `v` of `K` let `G_v = Gal(K̄_v/K_v)` (of order two) with its localization
`φ_v : G_v → G_S`.

To `x ∈ G_S` this file attaches the embedding `ι_v ∘ x⁻¹` of `L` into `K̄_v` (`infiniteEmbedding`), the
complex embedding of `L` obtained from it through `K̄_v ≅ ℂ` (`complexEmbeddingAt`), and the infinite
place of `L` it defines. This depends only on the double coset `U x G_v` (`mackeyInfinitePlace`), and

* the double cosets `U \ G_S / G_v` correspond bijectively to the infinite places of `L` above `v`
  (`mackeyInfinitePlace_injective`, `exists_mackeyInfinitePlace_eq`, `comap_mackeyInfinitePlace`);
* the place attached to `U x G_v` is real exactly when the Mackey subgroup `G_v ∩ x⁻¹ U x` is all of
  `G_v` (`mackeySubgroup_eq_top_iff_isReal`); otherwise it is trivial
  (`mackeySubgroup_eq_bot_of_ne_top`);
* for such a real place `w` and any embeddings `ιL : PlaceEmbeddings L Ω`, the image of complex
  conjugation of `G_v` under `y ↦ x φ_v(y) x⁻¹`, transported to `G_{S_L}(L)`, is conjugate to the image
  of complex conjugation of `L_w` under the localization of `ιL`
  (`exists_conj_realLocalizationHom_closureConj`).

These are the facts about the real places that Shapiro's lemma for the Euler characteristic ratio
needs (`Langlands.GaloisCohomology.Global.EulerCharacteristic.Induced`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  GaloisGroupUnramifiedOutside

universe u

noncomputable section

section Embeddings

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (ι : PlaceEmbeddings K Ω)

/-- The embedding `L → K̄_v` attached to `x ∈ G_S` at an infinite place `v`: `ι_v ∘ x⁻¹` on `L`. -/
def infiniteEmbedding (v : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S) :
    L →ₐ[K] AlgebraicClosure v.Completion :=
  ((ι.infinite v).comp ((maximalUnramifiedOutside K Ω S).val.comp
    (x⁻¹ : GaloisGroupUnramifiedOutside K Ω S).toAlgHom)).comp (embeddingMaximalUnramifiedOutside hL)

theorem infiniteEmbedding_apply (v : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S)
    (l : L) :
    infiniteEmbedding hL ι v x l =
      ι.infinite v ((((x⁻¹ : GaloisGroupUnramifiedOutside K Ω S)
        (embeddingMaximalUnramifiedOutside hL l)) : maximalUnramifiedOutside K Ω S) : Ω) :=
  rfl

theorem mem_mackeySubgroup_infinite_iff (v : InfinitePlace K)
    (x : GaloisGroupUnramifiedOutside K Ω S) (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) :
    σ ∈ mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
        (realLocalizationHom ι S v).toMonoidHom x ↔
      ∀ l : L, σ (infiniteEmbedding hL ι v x l) = infiniteEmbedding hL ι v x l := by
  rw [mem_mackeySubgroup]
  change _ ∈ fixingOpenSubgroup S hL ↔ _
  rw [mem_fixingOpenSubgroup_iff]
  refine forall_congr' fun l => ?_
  have key := realLocalizationHom_apply ι S v σ
    ((x⁻¹ : GaloisGroupUnramifiedOutside K Ω S) (embeddingMaximalUnramifiedOutside hL l))
  rw [infiniteEmbedding_apply, ← key]
  change x (realLocalizationHom ι S v σ (x⁻¹ (embeddingMaximalUnramifiedOutside hL l))) =
    embeddingMaximalUnramifiedOutside hL l ↔ _
  constructor
  · intro h
    have h' := congrArg (⇑(x⁻¹ : GaloisGroupUnramifiedOutside K Ω S)) h
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h'
    rw [h']
  · intro h
    have h' := Subtype.ext ((ι.infinite v).injective h)
    rw [h', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem infiniteEmbedding_mul (v : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S)
    {u : GaloisGroupUnramifiedOutside K Ω S} (hu : u ∈ fixingOpenSubgroup S hL)
    (h : Gal(AlgebraicClosure v.Completion/v.Completion)) (l : L) :
    infiniteEmbedding hL ι v (u * x * realLocalizationHom ι S v h) l =
      h⁻¹ (infiniteEmbedding hL ι v x l) := by
  have hul := (mem_fixingOpenSubgroup_iff S hL u).1 hu l
  have hu' : u⁻¹ (embeddingMaximalUnramifiedOutside hL l) =
      embeddingMaximalUnramifiedOutside hL l := by
    rw [AlgEquiv.aut_inv]
    exact u.symm_apply_eq.2 hul.symm
  rw [infiniteEmbedding_apply, infiniteEmbedding_apply, mul_inv_rev, mul_inv_rev, ← map_inv,
    AlgEquiv.mul_apply, AlgEquiv.mul_apply, hu']
  exact realLocalizationHom_apply ι S v h⁻¹ _

/-- Two elements of `G_S` give the same embedding of `L` exactly when they lie in the same coset
`U x`. -/
theorem mem_fixingOpenSubgroup_of_infiniteEmbedding_eq (v : InfinitePlace K)
    {x y : GaloisGroupUnramifiedOutside K Ω S}
    (h : infiniteEmbedding hL ι v x = infiniteEmbedding hL ι v y) :
    y * x⁻¹ ∈ fixingOpenSubgroup S hL := by
  rw [mem_fixingOpenSubgroup_iff]
  intro l
  have hl : x⁻¹ (embeddingMaximalUnramifiedOutside hL l) =
      y⁻¹ (embeddingMaximalUnramifiedOutside hL l) :=
    Subtype.ext ((ι.infinite v).injective (DFunLike.congr_fun h l))
  rw [AlgEquiv.mul_apply, hl, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem exists_infiniteEmbedding_eq (v : InfinitePlace K)
    (j : L →ₐ[K] AlgebraicClosure v.Completion) :
    ∃ x, infiniteEmbedding hL ι v x = j := by
  let _ : Algebra L (maximalUnramifiedOutside K Ω S) :=
    (embeddingMaximalUnramifiedOutside hL).toRingHom.toAlgebra
  have : IsScalarTower K L (maximalUnramifiedOutside K Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((embeddingMaximalUnramifiedOutside hL).commutes a).symm
  let _ : Algebra L (AlgebraicClosure v.Completion) := j.toRingHom.toAlgebra
  have : IsScalarTower K L (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  have : Algebra.IsAlgebraic L (maximalUnramifiedOutside K Ω S) :=
    Algebra.IsAlgebraic.tower_top (K := K) L
  let j' : maximalUnramifiedOutside K Ω S →ₐ[L] AlgebraicClosure v.Completion :=
    IsAlgClosed.lift
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ((ι.infinite v).comp (maximalUnramifiedOutside K Ω S).val)
    (j'.restrictScalars K)
  refine ⟨g⁻¹, AlgHom.ext fun l => ?_⟩
  have h1 : j l = j' (embeddingMaximalUnramifiedOutside hL l) := (j'.commutes l).symm
  have h2 := DFunLike.congr_fun hg (embeddingMaximalUnramifiedOutside hL l)
  rw [h1, infiniteEmbedding_apply, inv_inv]
  exact h2.symm

/-- The complex embedding of `L` attached to `x ∈ G_S` at an infinite place `v`. -/
def complexEmbeddingAt (v : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S) : L →+* ℂ :=
  (closureToComplex v).comp (infiniteEmbedding hL ι v x).toRingHom

theorem complexEmbeddingAt_apply (v : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S)
    (l : L) : complexEmbeddingAt hL ι v x l = closureToComplex v (infiniteEmbedding hL ι v x l) :=
  rfl

/-- On `K`, the complex embedding attached to `x` at `v` is the embedding of `v`. -/
theorem complexEmbeddingAt_comp_algebraMap (v : InfinitePlace K)
    (x : GaloisGroupUnramifiedOutside K Ω S) :
    (complexEmbeddingAt hL ι v x).comp (algebraMap K L) = v.embedding := by
  ext k
  rw [RingHom.comp_apply, complexEmbeddingAt_apply, AlgHom.commutes,
    closureToComplex_algebraMap_base]

end Embeddings

section RealPlaces

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (ι : PlaceEmbeddings K Ω)

/-- At a real place `v`, the complex embedding attached to `u x φ_v(h)` (`u ∈ U`) is the one attached
to `x` or its conjugate. -/
theorem complexEmbeddingAt_mul (v : InfinitePlace K) (hv : v.IsReal)
    (x : GaloisGroupUnramifiedOutside K Ω S) {u : GaloisGroupUnramifiedOutside K Ω S}
    (hu : u ∈ fixingOpenSubgroup S hL) (h : Gal(AlgebraicClosure v.Completion/v.Completion)) :
    complexEmbeddingAt hL ι v (u * x * realLocalizationHom ι S v h) = complexEmbeddingAt hL ι v x ∨
      complexEmbeddingAt hL ι v (u * x * realLocalizationHom ι S v h) =
        ComplexEmbedding.conjugate (complexEmbeddingAt hL ι v x) := by
  rcases eq_one_or_eq_closureConj v hv h⁻¹ with h1 | hc
  · left
    ext l
    rw [complexEmbeddingAt_apply, complexEmbeddingAt_apply, infiniteEmbedding_mul hL ι v x hu h l,
      h1, AlgEquiv.one_apply]
  · right
    ext l
    rw [complexEmbeddingAt_apply, infiniteEmbedding_mul hL ι v x hu h l, hc,
      closureToComplex_closureConj]
    rfl

variable (S) in
/-- The infinite place of `L` attached to the double coset `U x G_v` at a real place `v` of `K`. -/
def mackeyInfinitePlace (v : {v : InfinitePlace K // v.IsReal})
    (d : MackeyDoubleCoset (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S v.1).toMonoidHom) : InfinitePlace L :=
  InfinitePlace.mk (complexEmbeddingAt hL ι v.1 d.out)

theorem mackeyInfinitePlace_mk (v : {v : InfinitePlace K // v.IsReal})
    (x : GaloisGroupUnramifiedOutside K Ω S) :
    mackeyInfinitePlace S hL ι v (DoubleCoset.mk _ _ x) =
      InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x) := by
  obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mk_out_eq_mul
    (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
    (realLocalizationHom ι S v.1).toMonoidHom.range x
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hb
  rw [mackeyInfinitePlace]
  have e1 : (DoubleCoset.mk _ _ x : MackeyDoubleCoset
      (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S v.1).toMonoidHom).out = a * x * realLocalizationHom ι S v.1 h := hab
  rw [e1]
  rcases complexEmbeddingAt_mul hL ι v.1 v.2 x ha h with e | e
  · rw [e]
  · rw [e, InfinitePlace.mk_conjugate_eq]

/-- The place attached to `U x G_v` lies above `v`. -/
theorem comap_mackeyInfinitePlace (v : {v : InfinitePlace K // v.IsReal})
    (d : MackeyDoubleCoset (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S v.1).toMonoidHom) :
    (mackeyInfinitePlace S hL ι v d).comap (algebraMap K L) = v.1 := by
  rw [mackeyInfinitePlace, InfinitePlace.comap_mk, complexEmbeddingAt_comp_algebraMap,
    InfinitePlace.mk_embedding]

/-- At a real place, the complex embedding of `L` attached to `x` is determined by its place. -/
theorem complexEmbeddingAt_eq_of_mk_eq (v : InfinitePlace K)
    {x y : GaloisGroupUnramifiedOutside K Ω S}
    (h : InfinitePlace.mk (complexEmbeddingAt hL ι v x) =
      InfinitePlace.mk (complexEmbeddingAt hL ι v y)) :
    complexEmbeddingAt hL ι v y = complexEmbeddingAt hL ι v x ∨
      complexEmbeddingAt hL ι v y = ComplexEmbedding.conjugate (complexEmbeddingAt hL ι v x) := by
  rcases InfinitePlace.mk_eq_iff.1 h with e | e
  · exact Or.inl e.symm
  · exact Or.inr e.symm

theorem mackeyInfinitePlace_injective (v : {v : InfinitePlace K // v.IsReal}) :
    Function.Injective (mackeyInfinitePlace S hL ι v) := by
  intro d d' hdd'
  set x := d.out with hx
  set y := d'.out with hy
  have hdd'' : InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x) =
      InfinitePlace.mk (complexEmbeddingAt hL ι v.1 y) := hdd'
  clear_value x y
  -- the two embeddings of `L` into `K̄_v` agree up to complex conjugation
  have key : ∃ h : Gal(AlgebraicClosure v.1.Completion/v.1.Completion),
      infiniteEmbedding hL ι v.1 y = infiniteEmbedding hL ι v.1 (x * realLocalizationHom ι S v.1 h) := by
    rcases complexEmbeddingAt_eq_of_mk_eq hL ι v.1 hdd'' with e | e
    · refine ⟨1, AlgHom.ext fun l => (closureToComplex v.1).injective ?_⟩
      have := congrArg (fun φ : L →+* ℂ => φ l) e
      simp only [complexEmbeddingAt_apply] at this
      rw [this, map_one, mul_one]
    · refine ⟨(closureConj v.1 v.2)⁻¹, AlgHom.ext fun l => (closureToComplex v.1).injective ?_⟩
      have := congrArg (fun φ : L →+* ℂ => φ l) e
      simp only [complexEmbeddingAt_apply] at this
      have e2 := infiniteEmbedding_mul hL ι v.1 x (u := 1) (one_mem _) (closureConj v.1 v.2)⁻¹ l
      rw [one_mul, inv_inv] at e2
      rw [this, e2, closureToComplex_closureConj]
      rfl
  obtain ⟨h, hh⟩ := key
  have hmem := mem_fixingOpenSubgroup_of_infiniteEmbedding_eq hL ι v.1 hh.symm
  rw [← DoubleCoset.out_eq' d, ← DoubleCoset.out_eq' d', ← hx, ← hy, DoubleCoset.eq]
  refine ⟨_, hmem, realLocalizationHom ι S v.1 h, ⟨h, rfl⟩, ?_⟩
  group

/-- Every infinite place of `L` above the real place `v` is attached to a double coset. -/
theorem exists_mackeyInfinitePlace_eq (v : {v : InfinitePlace K // v.IsReal}) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v.1) :
    ∃ d, mackeyInfinitePlace S hL ι v d = w := by
  set ψ := w.embedding
  have hψK : ψ.comp (algebraMap K L) = v.1.embedding := by
    have h1 : InfinitePlace.mk (ψ.comp (algebraMap K L)) = InfinitePlace.mk v.1.embedding := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding, InfinitePlace.mk_embedding, hw]
    have hreal : ComplexEmbedding.IsReal v.1.embedding := InfinitePlace.isReal_iff.1 v.2
    rcases InfinitePlace.mk_eq_iff.1 h1 with e | e
    · exact e
    · calc ψ.comp (algebraMap K L)
          = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (ψ.comp (algebraMap K L))) :=
            (ComplexEmbedding.involutive_conjugate K _).symm
        _ = v.1.embedding := by rw [e]; exact ComplexEmbedding.isReal_iff.1 hreal
  let j : L →ₐ[K] AlgebraicClosure v.1.Completion :=
    { ((closureEquivComplex v.1).symm.toRingHom.comp ψ) with
      commutes' := fun k => by
        change (closureEquivComplex v.1).symm (ψ (algebraMap K L k)) = _
        rw [RingEquiv.symm_apply_eq, closureEquivComplex_apply, closureToComplex_algebraMap_base]
        exact congrArg (fun φ : K →+* ℂ => φ k) hψK }
  obtain ⟨x, hx⟩ := exists_infiniteEmbedding_eq hL ι v.1 j
  refine ⟨DoubleCoset.mk _ _ x, ?_⟩
  rw [mackeyInfinitePlace_mk]
  have : complexEmbeddingAt hL ι v.1 x = ψ := by
    ext l
    rw [complexEmbeddingAt_apply, hx]
    change closureToComplex v.1 ((closureEquivComplex v.1).symm (ψ l)) = ψ l
    rw [← closureEquivComplex_apply, RingEquiv.apply_symm_apply]
  rw [this, InfinitePlace.mk_embedding]

/-- The Mackey subgroup at a real place is everything or trivial. -/
theorem mackeySubgroup_eq_bot_of_ne_top (v : {v : InfinitePlace K // v.IsReal})
    (x : GaloisGroupUnramifiedOutside K Ω S)
    (h : mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S v.1).toMonoidHom x ≠ ⊤) :
    mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S v.1).toMonoidHom x = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  by_contra hne
  apply h
  rw [eq_top_iff]
  intro τ _
  rcases eq_one_or_eq_closureConj v.1 v.2 τ with rfl | rfl
  · exact one_mem _
  · rcases eq_one_or_eq_closureConj v.1 v.2 σ with h1 | h1
    · exact absurd h1 hne
    · exact h1 ▸ hσ

/-- The Mackey subgroup at `x` is everything exactly when the place attached to `x` is real. -/
theorem mackeySubgroup_eq_top_iff_isReal (v : {v : InfinitePlace K // v.IsReal})
    (x : GaloisGroupUnramifiedOutside K Ω S) :
    mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
        (realLocalizationHom ι S v.1).toMonoidHom x = ⊤ ↔
      (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x)).IsReal := by
  rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
  constructor
  · intro h
    have hc : closureConj v.1 v.2 ∈ mackeySubgroup
        (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
        (realLocalizationHom ι S v.1).toMonoidHom x := h ▸ Subgroup.mem_top _
    rw [mem_mackeySubgroup_infinite_iff] at hc
    ext l
    change starRingEnd ℂ (closureToComplex v.1 (infiniteEmbedding hL ι v.1 x l)) =
      closureToComplex v.1 (infiniteEmbedding hL ι v.1 x l)
    rw [← closureToComplex_closureConj v.1 v.2, hc l]
  · intro h
    rw [eq_top_iff]
    intro σ _
    rw [mem_mackeySubgroup_infinite_iff]
    intro l
    rcases eq_one_or_eq_closureConj v.1 v.2 σ with rfl | rfl
    · rfl
    · apply (closureToComplex v.1).injective
      rw [closureToComplex_closureConj]
      exact congrArg (fun φ : L →+* ℂ => φ l) h

end RealPlaces

section Conjugation

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω] [IsGalois L Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (ι : PlaceEmbeddings K Ω)
  (ιL : PlaceEmbeddings L Ω)

omit [NumberField K] [NumberField L] [Algebra K Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  [IsGalois L Ω] in
/-- An automorphism of `K_S` over `L` is determined by what it does after an embedding into `ℂ`. -/
theorem eq_of_comp_eq {τ : maximalUnramifiedOutside L Ω (finitePlacesAbove L S) →+* ℂ}
    {a b : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S)}
    (h : ∀ y, τ (a y) = τ (b y)) : a = b :=
  AlgEquiv.ext fun y => τ.injective (h y)

/-- **Complex conjugations correspond.** Let `v` be a real place of `K` and `x ∈ G_S` such that the
place `w` of `L` attached to `x` is real. Then the image of complex conjugation of `G_v` under
`y ↦ x φ_v(y) x⁻¹`, transported to `G_{S_L}(L)`, is conjugate there to the image of complex
conjugation of `L_w` under the localization of `ιL`. -/
theorem exists_conj_realLocalizationHom_closureConj (v : {v : InfinitePlace K // v.IsReal})
    (x : GaloisGroupUnramifiedOutside K Ω S)
    (hw : (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x)).IsReal)
    (hc : x * realLocalizationHom ι S v.1 (closureConj v.1 v.2) * x⁻¹ ∈ fixingOpenSubgroup S hL) :
    ∃ g : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S),
      realLocalizationHom ιL (finitePlacesAbove L S) (InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x))
          (closureConj _ hw) =
        g⁻¹ * fixingOpenSubgroupEquiv S hL ⟨_, hc⟩ * g := by
  set w := InfinitePlace.mk (complexEmbeddingAt hL ι v.1 x) with hwdef
  set KSL := maximalUnramifiedOutside L Ω (finitePlacesAbove L S)
  have hψ : w.embedding = complexEmbeddingAt hL ι v.1 x :=
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hw)
  -- the two embeddings of `K_S` into `ℂ`
  let τ₁ : KSL →+* ℂ :=
    { toFun := fun y => closureToComplex v.1 (ι.infinite v.1 ((((x⁻¹ : GaloisGroupUnramifiedOutside K Ω S)
        ((maximalUnramifiedOutsideEquiv hL).symm y)) : maximalUnramifiedOutside K Ω S) : Ω))
      map_one' := by simp
      map_mul' := fun a b => by simp
      map_zero' := by simp
      map_add' := fun a b => by simp }
  let τ₂ : KSL →+* ℂ := (closureToComplex w).comp
    ((ιL.infinite w).toRingHom.comp (IntermediateField.val KSL).toRingHom)
  let _ : Algebra L ℂ := w.embedding.toAlgebra
  have h₁ : ∀ l : L, τ₁ (algebraMap L KSL l) = algebraMap L ℂ l := fun l => by
    change closureToComplex v.1 (infiniteEmbedding hL ι v.1 x l) = w.embedding l
    rw [hψ]
    rfl
  have h₂ : ∀ l : L, τ₂ (algebraMap L KSL l) = algebraMap L ℂ l := fun l => by
    change closureToComplex w (ιL.infinite w (algebraMap L Ω l)) = w.embedding l
    rw [AlgHom.commutes, closureToComplex_algebraMap_base]
  let τ₁' : KSL →ₐ[L] ℂ := { τ₁ with commutes' := h₁ }
  let τ₂' : KSL →ₐ[L] ℂ := { τ₂ with commutes' := h₂ }
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal τ₁' τ₂'
  refine ⟨g, eq_of_comp_eq (τ := τ₂) fun y => ?_⟩
  have hg' : ∀ z, τ₂ z = τ₁ (g z) := fun z => DFunLike.congr_fun hg z
  -- complex conjugation through `τ₂`
  have hc₂ : τ₂ (realLocalizationHom ιL (finitePlacesAbove L S) w (closureConj w hw) y) =
      starRingEnd ℂ (τ₂ y) := by
    change closureToComplex w (ιL.infinite w ((realLocalizationHom ιL (finitePlacesAbove L S) w
        (closureConj w hw) y : KSL) : Ω)) = starRingEnd ℂ (closureToComplex w (ιL.infinite w (y : Ω)))
    rw [realLocalizationHom_apply, closureToComplex_closureConj]
  -- complex conjugation through `τ₁`
  have hc₁ : ∀ z, τ₁ (fixingOpenSubgroupEquiv S hL ⟨_, hc⟩ z) = starRingEnd ℂ (τ₁ z) := fun z => by
    have e1 := coe_fixingOpenSubgroupEquiv_apply hL ⟨_, hc⟩ z
    change closureToComplex v.1 (ι.infinite v.1 _) = starRingEnd ℂ (closureToComplex v.1 _)
    have e2 : (((maximalUnramifiedOutsideEquiv hL).symm (fixingOpenSubgroupEquiv S hL ⟨_, hc⟩ z) :
        maximalUnramifiedOutside K Ω S) : Ω) =
        (((x * realLocalizationHom ι S v.1 (closureConj v.1 v.2) * x⁻¹)
          ((maximalUnramifiedOutsideEquiv hL).symm z) : maximalUnramifiedOutside K Ω S) : Ω) := e1
    have e3 : (maximalUnramifiedOutsideEquiv hL).symm (fixingOpenSubgroupEquiv S hL ⟨_, hc⟩ z) =
        (x * realLocalizationHom ι S v.1 (closureConj v.1 v.2) * x⁻¹)
          ((maximalUnramifiedOutsideEquiv hL).symm z) := Subtype.ext e2
    rw [e3, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply x⁻¹ x, inv_mul_cancel,
      AlgEquiv.one_apply, realLocalizationHom_apply, closureToComplex_closureConj]
  rw [hc₂, hg' y, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hg' (g⁻¹ _), ← AlgEquiv.mul_apply g g⁻¹,
    mul_inv_cancel, AlgEquiv.one_apply, hc₁]

end Conjugation

end

end Langlands.GaloisCohomology
