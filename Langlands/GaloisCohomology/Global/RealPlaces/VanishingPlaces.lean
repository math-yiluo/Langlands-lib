import Langlands.GaloisCohomology.Global.RealPlaces.VanishingTwo

/-!
# The real places of a finite extension inside `K_S` and the Mackey double cosets

Let `K` be a number field, `Ω / K` Galois, `S` a set of finite places of `K`, `G_S = Gal(K_S/K)`,
`ι : PlaceEmbeddings K Ω`, `L` a number field with `K → L → Ω` inside `K_S` and `W ⊆ G_S` the open
subgroup fixing `L` (`fixingOpenSubgroup S hL`). For an infinite place `w` of `K` let
`D_w = Gal(K̄_w/K_w)` with its localization `realLocalizationHom ι S w : D_w → G_S`.

**Embeddings and places.** For `x ∈ G_S`, `realLocalEmbedding hL ι w x : L → K̄_w` is `ι_w ∘ x⁻¹` on `L`; its
complex embedding `L → K̄_w → ℂ` (through `closureToComplex`) defines the infinite place
`realPlaceOf hL ι w x` of `L`, which lies over `w` (`comap_realPlaceOf`). The Mackey subgroup
`D_w ∩ x⁻¹ W x` (`mackeySubgroup`) is the subgroup of `D_w` fixing `realLocalEmbedding hL ι w x`
(`mem_mackeySubgroup_real_iff`); at a real place `w` it is all of `D_w` exactly when the place
`realPlaceOf hL ι w x` is real (`isReal_realPlaceOf_iff`).

**The correspondence** (`realMackeyPlaceEquiv`). The pairs of a real place `w` of `K` and a double coset
`W x D_w` whose Mackey subgroup is `D_w` (`RealMackeyTop`) correspond bijectively to the real places of
`L` (`realMackeyPlace`, the place of the representative `x`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open GaloisGroupUnramifiedOutside

universe u

noncomputable section

section Places

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (ι : PlaceEmbeddings K Ω)

/-- The embedding `L → K̄_w` attached to `x ∈ G_S` at an infinite place `w`: `ι_w ∘ x⁻¹` on `L`. -/
def realLocalEmbedding (w : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S) :
    L →ₐ[K] AlgebraicClosure w.Completion :=
  ((ι.infinite w).comp ((maximalUnramifiedOutside K Ω S).val.comp
    (x⁻¹ : GaloisGroupUnramifiedOutside K Ω S).toAlgHom)).comp (embeddingMaximalUnramifiedOutside hL)

theorem realLocalEmbedding_apply (w : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S) (l : L) :
    realLocalEmbedding hL ι w x l =
      ι.infinite w ((((x⁻¹ : GaloisGroupUnramifiedOutside K Ω S)
        (embeddingMaximalUnramifiedOutside hL l)) : maximalUnramifiedOutside K Ω S) : Ω) :=
  rfl

/-- The Mackey subgroup of `D_w` at `x` is the subgroup fixing the embedding of `L` attached to `x`. -/
theorem mem_mackeySubgroup_real_iff (w : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S)
    (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) :
    σ ∈ mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
        (realLocalizationHom ι S w).toMonoidHom x ↔
      ∀ l : L, σ (realLocalEmbedding hL ι w x l) = realLocalEmbedding hL ι w x l := by
  rw [mem_mackeySubgroup]
  change _ ∈ fixingOpenSubgroup S hL ↔ _
  rw [mem_fixingOpenSubgroup_iff]
  refine forall_congr' fun l => ?_
  have key := realLocalizationHom_apply ι S w σ
    ((x⁻¹ : GaloisGroupUnramifiedOutside K Ω S) (embeddingMaximalUnramifiedOutside hL l))
  rw [realLocalEmbedding_apply, ← key]
  change x (realLocalizationHom ι S w σ (x⁻¹ (embeddingMaximalUnramifiedOutside hL l))) =
    embeddingMaximalUnramifiedOutside hL l ↔ _
  constructor
  · intro h
    have h' := congrArg (⇑(x⁻¹ : GaloisGroupUnramifiedOutside K Ω S)) h
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h'
    rw [h']
  · intro h
    have h' := Subtype.ext ((ι.infinite w).injective h)
    rw [h', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem realLocalEmbedding_mul (w : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S)
    {u : GaloisGroupUnramifiedOutside K Ω S} (hu : u ∈ fixingOpenSubgroup S hL)
    (h : Gal(AlgebraicClosure w.Completion/w.Completion)) (l : L) :
    realLocalEmbedding hL ι w (u * x * realLocalizationHom ι S w h) l = h⁻¹ (realLocalEmbedding hL ι w x l) := by
  have hul := (mem_fixingOpenSubgroup_iff S hL u).1 hu l
  have hu' : u⁻¹ (embeddingMaximalUnramifiedOutside hL l) = embeddingMaximalUnramifiedOutside hL l := by
    rw [AlgEquiv.aut_inv]
    exact u.symm_apply_eq.2 hul.symm
  rw [realLocalEmbedding_apply, realLocalEmbedding_apply, mul_inv_rev, mul_inv_rev, ← map_inv,
    AlgEquiv.mul_apply, AlgEquiv.mul_apply, hu']
  exact realLocalizationHom_apply ι S w h⁻¹ _

theorem exists_realLocalEmbedding_eq (w : InfinitePlace K) (j : L →ₐ[K] AlgebraicClosure w.Completion) :
    ∃ x, realLocalEmbedding hL ι w x = j := by
  let _ : Algebra L (maximalUnramifiedOutside K Ω S) :=
    (embeddingMaximalUnramifiedOutside hL).toRingHom.toAlgebra
  have : IsScalarTower K L (maximalUnramifiedOutside K Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((embeddingMaximalUnramifiedOutside hL).commutes a).symm
  let _ : Algebra L (AlgebraicClosure w.Completion) := j.toRingHom.toAlgebra
  have : IsScalarTower K L (AlgebraicClosure w.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  have : Algebra.IsAlgebraic L (maximalUnramifiedOutside K Ω S) :=
    Algebra.IsAlgebraic.tower_top (K := K) L
  let j' : maximalUnramifiedOutside K Ω S →ₐ[L] AlgebraicClosure w.Completion := IsAlgClosed.lift
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ((ι.infinite w).comp (maximalUnramifiedOutside K Ω S).val)
    (j'.restrictScalars K)
  refine ⟨g⁻¹, AlgHom.ext fun l => ?_⟩
  have h1 : j l = j' (embeddingMaximalUnramifiedOutside hL l) := (j'.commutes l).symm
  have h2 := DFunLike.congr_fun hg (embeddingMaximalUnramifiedOutside hL l)
  rw [h1, realLocalEmbedding_apply, inv_inv]
  exact h2.symm

/-- The complex embedding `L → K̄_w → ℂ` attached to `x`. -/
def realComplexEmbeddingOf (w : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S) :
    L →+* ℂ :=
  (closureToComplex w).comp (realLocalEmbedding hL ι w x).toRingHom

theorem realComplexEmbeddingOf_apply (w : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S)
    (l : L) : realComplexEmbeddingOf hL ι w x l = closureToComplex w (realLocalEmbedding hL ι w x l) :=
  rfl

/-- The infinite place of `L` attached to `x` at `w`. -/
def realPlaceOf (w : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S) : InfinitePlace L :=
  InfinitePlace.mk (realComplexEmbeddingOf hL ι w x)

/-- On `K` the complex embedding attached to `x` is the embedding of `w`. -/
theorem realComplexEmbeddingOf_comp_algebraMap (w : InfinitePlace K)
    (x : GaloisGroupUnramifiedOutside K Ω S) :
    (realComplexEmbeddingOf hL ι w x).comp (algebraMap K L) = w.embedding := by
  ext a
  change closureToComplex w (realLocalEmbedding hL ι w x (algebraMap K L a)) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K w.Completion (AlgebraicClosure w.Completion),
    closureToComplex_algebraMap, InfinitePlace.Completion.algebraMap_apply,
    InfinitePlace.Completion.extensionEmbedding_coe]
  rfl

/-- The place attached to `x` lies over `w`. -/
theorem comap_realPlaceOf (w : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S) :
    (realPlaceOf hL ι w x).comap (algebraMap K L) = w := by
  rw [realPlaceOf, InfinitePlace.comap_mk, realComplexEmbeddingOf_comp_algebraMap,
    InfinitePlace.mk_embedding]

/-- At a real place `w`, the place attached to `x` is real if and only if the Mackey subgroup at `x` is
all of `D_w`. -/
theorem isReal_realPlaceOf_iff (w : InfinitePlace K) (hw : w.IsReal)
    (x : GaloisGroupUnramifiedOutside K Ω S) :
    (realPlaceOf hL ι w x).IsReal ↔
      mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
        (realLocalizationHom ι S w).toMonoidHom x = ⊤ := by
  rw [realPlaceOf, InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff, Subgroup.eq_top_iff']
  constructor
  · intro h σ
    rw [mem_mackeySubgroup_real_iff]
    intro l
    rcases eq_one_or_eq_closureConj w hw σ with rfl | rfl
    · rfl
    · apply (closureToComplex w).injective
      rw [closureToComplex_closureConj]
      exact DFunLike.congr_fun h l
  · intro h
    ext l
    have hl := (mem_mackeySubgroup_real_iff hL ι w x (closureConj w hw)).1 (h _) l
    change starRingEnd ℂ (closureToComplex w (realLocalEmbedding hL ι w x l)) =
      closureToComplex w (realLocalEmbedding hL ι w x l)
    rw [← closureToComplex_closureConj w hw, hl]

end Places

section Correspondence

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (ι : PlaceEmbeddings K Ω)

variable (S) in
/-- The pairs of a real place `w` of `K` and a double coset `W x D_w` (`W` the subgroup fixing `L`) whose
Mackey subgroup is all of `D_w`. -/
abbrev RealMackeyTop : Type u :=
  {p : Σ w : {w : InfinitePlace K // w.IsReal}, MackeyDoubleCoset
      (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S w.1).toMonoidHom //
    mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S p.1.1).toMonoidHom p.2.out = ⊤}

/-- The real place of `L` attached to a pair of `RealMackeyTop`: the place of the representative of the
double coset. -/
def realMackeyPlace (p : RealMackeyTop S hL ι) : {w' : InfinitePlace L // w'.IsReal} :=
  ⟨realPlaceOf hL ι p.1.1.1 p.1.2.out, (isReal_realPlaceOf_iff hL ι p.1.1.1 p.1.1.2 _).2 p.2⟩

theorem coe_realMackeyPlace (p : RealMackeyTop S hL ι) :
    ((realMackeyPlace hL ι p : {w' : InfinitePlace L // w'.IsReal}) : InfinitePlace L) =
      realPlaceOf hL ι p.1.1.1 p.1.2.out :=
  rfl

/-- At a top double coset the complex embedding attached to the representative is real. -/
theorem isReal_realComplexEmbeddingOf (p : RealMackeyTop S hL ι) :
    ComplexEmbedding.IsReal (realComplexEmbeddingOf hL ι p.1.1.1 p.1.2.out) :=
  InfinitePlace.isReal_mk_iff.1 (realMackeyPlace hL ι p).2

/-- The complex embedding attached to the representative is the embedding of the attached place. -/
theorem realComplexEmbeddingOf_eq_embedding (p : RealMackeyTop S hL ι) :
    realComplexEmbeddingOf hL ι p.1.1.1 p.1.2.out =
      ((realMackeyPlace hL ι p : {w' : InfinitePlace L // w'.IsReal}) : InfinitePlace L).embedding :=
  (InfinitePlace.embedding_mk_eq_of_isReal (isReal_realComplexEmbeddingOf hL ι p)).symm

theorem realMackeyPlace_injective : Function.Injective (realMackeyPlace hL ι) := by
  rintro ⟨⟨w, d⟩, hd⟩ ⟨⟨w', d'⟩, hd'⟩ h
  have h1 : realPlaceOf hL ι w.1 d.out = realPlaceOf hL ι w'.1 d'.out := congrArg Subtype.val h
  have hw : w = w' := Subtype.ext (by
    rw [← comap_realPlaceOf hL ι w.1 d.out, h1, comap_realPlaceOf])
  subst hw
  have hr : ComplexEmbedding.IsReal (realComplexEmbeddingOf hL ι w.1 d.out) :=
    isReal_realComplexEmbeddingOf hL ι ⟨⟨w, d⟩, hd⟩
  have he : realComplexEmbeddingOf hL ι w.1 d.out = realComplexEmbeddingOf hL ι w.1 d'.out := by
    rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
    · exact h
    · rw [← h, ComplexEmbedding.isReal_iff.1 hr]
  have hmem : d'.out * d.out⁻¹ ∈ fixingOpenSubgroup S hL := by
    rw [mem_fixingOpenSubgroup_iff]
    intro l
    have e := (closureToComplex w.1).injective (DFunLike.congr_fun he l)
    change realLocalEmbedding hL ι w.1 d.out l = realLocalEmbedding hL ι w.1 d'.out l at e
    rw [realLocalEmbedding_apply, realLocalEmbedding_apply] at e
    have hinj : d.out⁻¹ (embeddingMaximalUnramifiedOutside hL l) =
        d'.out⁻¹ (embeddingMaximalUnramifiedOutside hL l) :=
      Subtype.ext ((ι.infinite w.1).injective e)
    rw [AlgEquiv.mul_apply, hinj, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hdd : d = d' := by
    rw [← DoubleCoset.out_eq' d, ← DoubleCoset.out_eq' d', DoubleCoset.eq]
    exact ⟨_, hmem, 1, one_mem _, by group⟩
  subst hdd
  rfl

theorem realMackeyPlace_surjective : Function.Surjective (realMackeyPlace hL ι) := by
  rintro ⟨w', hw'⟩
  let w : {w : InfinitePlace K // w.IsReal} := ⟨w'.comap (algebraMap K L), hw'.comap _⟩
  have hφ : ComplexEmbedding.IsReal w'.embedding := InfinitePlace.isReal_iff.1 hw'
  have hφK : w'.embedding.comp (algebraMap K L) = w.1.embedding :=
    (InfinitePlace.comap_embedding_of_isReal _ w.2).symm
  let j : L →ₐ[K] AlgebraicClosure w.1.Completion :=
    { (closureEquivComplex w.1).symm.toRingHom.comp w'.embedding with
      commutes' := fun a => by
        change (closureEquivComplex w.1).symm (w'.embedding (algebraMap K L a)) = _
        rw [RingEquiv.symm_apply_eq, closureEquivComplex_apply, closureToComplex_algebraMap_base]
        exact DFunLike.congr_fun hφK a }
  obtain ⟨x, hx⟩ := exists_realLocalEmbedding_eq hL ι w.1 j
  let d : MackeyDoubleCoset (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S w.1).toMonoidHom :=
    DoubleCoset.mk _ _ x
  obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mk_out_eq_mul
    (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
    (realLocalizationHom ι S w.1).toMonoidHom.range x
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hb
  have hout : d.out = a * x * realLocalizationHom ι S w.1 h := hab
  have hval : realComplexEmbeddingOf hL ι w.1 d.out = w'.embedding := by
    ext l
    rw [realComplexEmbeddingOf_apply, hout, realLocalEmbedding_mul hL ι w.1 x ha h, hx]
    change closureToComplex w.1 (h⁻¹ ((closureEquivComplex w.1).symm (w'.embedding l))) =
      w'.embedding l
    rcases eq_one_or_eq_closureConj w.1 w.2 h⁻¹ with h1 | h1
    · rw [h1, AlgEquiv.one_apply, ← closureEquivComplex_apply, RingEquiv.apply_symm_apply]
    · rw [h1, closureToComplex_closureConj, ← closureEquivComplex_apply, RingEquiv.apply_symm_apply]
      exact DFunLike.congr_fun (ComplexEmbedding.isReal_iff.1 hφ) l
  have hplace : realPlaceOf hL ι w.1 d.out = w' := by
    rw [realPlaceOf, hval, InfinitePlace.mk_embedding]
  have htop : mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S w.1).toMonoidHom d.out = ⊤ :=
    (isReal_realPlaceOf_iff hL ι w.1 w.2 d.out).1 (hplace ▸ hw')
  exact ⟨⟨⟨w, d⟩, htop⟩, Subtype.ext hplace⟩

/-- **The real places of `L` and the Mackey double cosets.** The top Mackey double cosets at the real
places of `K` correspond to the real places of `L`. -/
def realMackeyPlaceEquiv : RealMackeyTop S hL ι ≃ {w' : InfinitePlace L // w'.IsReal} :=
  Equiv.ofBijective (realMackeyPlace hL ι) ⟨realMackeyPlace_injective hL ι, realMackeyPlace_surjective hL ι⟩

theorem realMackeyPlaceEquiv_apply (p : RealMackeyTop S hL ι) :
    realMackeyPlaceEquiv hL ι p = realMackeyPlace hL ι p :=
  rfl

end Correspondence

section OrderTwo

variable {A B : Type*} [Group A] [Group B]

open Classical in
/-- Two groups of order two, `{1, a}` and `{1, b}`, are isomorphic. -/
def orderTwoMulEquiv (a : A) (b : B) (hA : ∀ x, x = 1 ∨ x = a) (ha : a ≠ 1) (hB : ∀ y, y = 1 ∨ y = b)
    (hb : b ≠ 1) : A ≃* B where
  toFun x := if x = 1 then 1 else b
  invFun y := if y = 1 then 1 else a
  left_inv x := by
    rcases hA x with rfl | rfl
    · simp
    · simp [ha, hb]
  right_inv y := by
    rcases hB y with rfl | rfl
    · simp
    · simp [ha, hb]
  map_mul' x y := by
    have haa : a * a = 1 := (hA (a * a)).resolve_right fun h => ha (by simpa using h)
    have hbb : b * b = 1 := (hB (b * b)).resolve_right fun h => hb (by simpa using h)
    rcases hA x with rfl | rfl <;> rcases hA y with rfl | rfl <;> simp [ha, haa, hbb]

theorem orderTwoMulEquiv_apply_one (a : A) (b : B) (hA : ∀ x, x = 1 ∨ x = a) (ha : a ≠ 1)
    (hB : ∀ y, y = 1 ∨ y = b) (hb : b ≠ 1) : orderTwoMulEquiv a b hA ha hB hb 1 = 1 :=
  map_one _

theorem orderTwoMulEquiv_apply_gen (a : A) (b : B) (hA : ∀ x, x = 1 ∨ x = a) (ha : a ≠ 1)
    (hB : ∀ y, y = 1 ∨ y = b) (hb : b ≠ 1) : orderTwoMulEquiv a b hA ha hB hb a = b := by
  classical
  change (if a = 1 then 1 else b) = b
  simp [ha]

end OrderTwo

/-- The isomorphism of the Galois groups of the closures of two real completions (of possibly different
number fields), sending complex conjugation to complex conjugation. -/
def realClosureGaloisEquiv {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']
    (w : InfinitePlace K) (hw : w.IsReal) (w' : InfinitePlace K') (hw' : w'.IsReal) :
    Gal(AlgebraicClosure w.Completion/w.Completion) ≃*
      Gal(AlgebraicClosure w'.Completion/w'.Completion) :=
  orderTwoMulEquiv (closureConj w hw) (closureConj w' hw') (eq_one_or_eq_closureConj w hw)
    (closureConj_ne_one w hw) (eq_one_or_eq_closureConj w' hw') (closureConj_ne_one w' hw')

section Embeddings

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (ι : PlaceEmbeddings K Ω)

theorem closureToComplex_closureEquivComplex_symm (w' : InfinitePlace L) (z : ℂ) :
    closureToComplex w' ((closureEquivComplex w').symm z) = z := by
  rw [← closureEquivComplex_apply, RingEquiv.apply_symm_apply]

/-- The embedding of `Ω` over `L` into `AlgebraicClosure L_{w'}` at an infinite place `w'` of `L` whose
embedding is the complex embedding attached to `(w, x)`: `ι_w ∘ x⁻¹`, read in `ℂ` through
`K̄_w ≅ ℂ ≅ L̄_{w'}`. -/
def realEmbeddingOverOf (w : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S)
    (w' : InfinitePlace L) (h : realComplexEmbeddingOf hL ι w x = w'.embedding) :
    Ω →ₐ[L] AlgebraicClosure w'.Completion :=
  { ((closureEquivComplex w').symm.toRingHom.comp
      ((closureToComplex w).comp ((ι.infinite w).toRingHom.comp
        ((lift x)⁻¹ : Gal(Ω/K)).toRingEquiv.toRingHom))) with
    commutes' := fun l => by
      have e : (lift x)⁻¹ (algebraMap L Ω l) =
          (((x⁻¹ : GaloisGroupUnramifiedOutside K Ω S) (embeddingMaximalUnramifiedOutside hL l) :
            maximalUnramifiedOutside K Ω S) : Ω) :=
        lift_inv_apply x (embeddingMaximalUnramifiedOutside hL l)
      have e' : closureToComplex w (ι.infinite w ((lift x)⁻¹ (algebraMap L Ω l))) = w'.embedding l := by
        rw [e, ← h]
        rfl
      change (closureEquivComplex w').symm
        (closureToComplex w (ι.infinite w ((lift x)⁻¹ (algebraMap L Ω l)))) = _
      rw [RingEquiv.symm_apply_eq, closureEquivComplex_apply, closureToComplex_algebraMap_base, e'] }

theorem realEmbeddingOverOf_apply (w : InfinitePlace K) (x : GaloisGroupUnramifiedOutside K Ω S)
    (w' : InfinitePlace L) (h : realComplexEmbeddingOf hL ι w x = w'.embedding) (y : Ω) :
    realEmbeddingOverOf hL ι w x w' h y =
      (closureEquivComplex w').symm (closureToComplex w (ι.infinite w ((lift x)⁻¹ y))) :=
  rfl

/-- **Compatibility.** Let `w` be a real place of `K`, `x ∈ G_S` and `w'` a real place of `L` whose
embedding is the complex embedding attached to `(w, x)`. Under `W ≅ G_{S_L}(L)`, conjugation by `x` on the
Mackey subgroup is the decomposition homomorphism of `L_{w'}` for `realEmbeddingOverOf`, the groups
`D_w ≅ D_{w'}` identified by `realClosureGaloisEquiv`. -/
theorem fixingOpenSubgroupEquiv_mackeyConj_real [IsGalois L Ω] (w : InfinitePlace K) (hw : w.IsReal)
    (x : GaloisGroupUnramifiedOutside K Ω S) (w' : InfinitePlace L) (hw' : w'.IsReal)
    (h : realComplexEmbeddingOf hL ι w x = w'.embedding)
    (σ : mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S w).toMonoidHom x) :
    fixingOpenSubgroupEquiv S hL (mackeyConj (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S w).toMonoidHom x σ) =
      decompositionHom w'.Completion
        ((realEmbeddingOverOf hL ι w x w' h).comp
          (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)).val)
        (realClosureGaloisEquiv w hw w' hw' σ.1) := by
  rcases eq_one_or_eq_closureConj w hw σ.1 with h1 | h1
  · have hσ : σ = 1 := Subtype.ext h1
    subst hσ
    simp only [map_one, OneMemClass.coe_one]
  symm
  rw [decompositionHom_eq_iff]
  intro t
  apply (closureEquivComplex w').injective
  have hu := coe_fixingOpenSubgroupEquiv_apply hL (mackeyConj (fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S w).toMonoidHom x σ) t
  have ht : ((t : maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) : Ω) =
      (((maximalUnramifiedOutsideEquiv hL).symm t : maximalUnramifiedOutside K Ω S) : Ω) :=
    (coe_fieldEquivOfRestrictScalarsEq_symm (restrictScalars_maximalUnramifiedOutside S hL) t).symm
  have key : (lift x)⁻¹ ((((x * (realLocalizationHom ι S w).toMonoidHom σ * x⁻¹)
      ((maximalUnramifiedOutsideEquiv hL).symm t) : maximalUnramifiedOutside K Ω S)) : Ω) =
      ((realLocalizationHom ι S w σ ((x⁻¹ : GaloisGroupUnramifiedOutside K Ω S)
        ((maximalUnramifiedOutsideEquiv hL).symm t)) : maximalUnramifiedOutside K Ω S) : Ω) := by
    rw [lift_inv_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply x⁻¹ x,
      inv_mul_cancel, AlgEquiv.one_apply]
    rfl
  have hc : realClosureGaloisEquiv w hw w' hw' σ.1 = closureConj w' hw' := by
    rw [h1]
    exact orderTwoMulEquiv_apply_gen _ _ _ _ _ _
  rw [hc, closureEquivComplex_apply, closureEquivComplex_apply, closureToComplex_closureConj,
    AlgHom.comp_apply, AlgHom.comp_apply, realEmbeddingOverOf_apply, realEmbeddingOverOf_apply, closureToComplex_closureEquivComplex_symm,
    closureToComplex_closureEquivComplex_symm, IntermediateField.coe_val, hu, ht, mackeyConj_apply_coe, key,
    realLocalizationHom_apply, lift_inv_apply, h1, closureToComplex_closureConj]

/-- The embedding of `Ω` at the real place of `L` attached to a pair of `RealMackeyTop`. -/
def realEmbeddingOver (p : RealMackeyTop S hL ι) :
    Ω →ₐ[L] AlgebraicClosure (realMackeyPlace hL ι p).1.Completion :=
  realEmbeddingOverOf hL ι p.1.1.1 p.1.2.out (realMackeyPlace hL ι p).1
    (realComplexEmbeddingOf_eq_embedding hL ι p)

/-- The embeddings of `Ω` at the real places of `L` given by the correspondence `realMackeyPlaceEquiv`. -/
def realMackeyEmbedding : ∀ w' : {w' : InfinitePlace L // w'.IsReal},
    Ω →ₐ[L] AlgebraicClosure w'.1.Completion :=
  Equiv.piCongrLeft (fun w' : {w' : InfinitePlace L // w'.IsReal} =>
      Ω →ₐ[L] AlgebraicClosure w'.1.Completion)
    (realMackeyPlaceEquiv hL ι) fun p => realEmbeddingOver hL ι p

theorem realMackeyEmbedding_realMackeyPlaceEquiv (p : RealMackeyTop S hL ι) :
    realMackeyEmbedding hL ι (realMackeyPlaceEquiv hL ι p) = realEmbeddingOver hL ι p :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

open Classical in
/-- Embeddings of `Ω` at the places of `L`: at the real places those of the correspondence for `ι`
(`realMackeyEmbedding`), elsewhere those of `ι₀`. -/
def realPlaceEmbeddingsOver (ι₀ : PlaceEmbeddings L Ω) : PlaceEmbeddings L Ω where
  finite := ι₀.finite
  infinite w' := if hw' : w'.IsReal then realMackeyEmbedding hL ι ⟨w', hw'⟩ else ι₀.infinite w'

theorem realPlaceEmbeddingsOver_infinite (ι₀ : PlaceEmbeddings L Ω)
    (w' : {w' : InfinitePlace L // w'.IsReal}) :
    (realPlaceEmbeddingsOver hL ι ι₀).infinite w'.1 = realMackeyEmbedding hL ι w' :=
  dite_eq_left_of_eq_true (eq_true w'.2)

/-- Under `W ≅ G_{S_L}(L)`, conjugation by the representative of a top double coset at a real place is
the localization of `G_{S_L}(L)` at the attached real place for `realPlaceEmbeddingsOver hL ι ι₀`. -/
theorem fixingOpenSubgroupEquiv_mackeyConj_eq_realLocalizationHom [IsGalois L Ω]
    (ι₀ : PlaceEmbeddings L Ω) (p : RealMackeyTop S hL ι)
    (σ : mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (realLocalizationHom ι S p.1.1.1).toMonoidHom p.1.2.out) :
    fixingOpenSubgroupEquiv S hL (mackeyConj (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (realLocalizationHom ι S p.1.1.1).toMonoidHom
          p.1.2.out σ) =
      realLocalizationHom (realPlaceEmbeddingsOver hL ι ι₀) (finitePlacesAbove L S)
        (realMackeyPlace hL ι p).1
        (realClosureGaloisEquiv p.1.1.1 p.1.1.2 (realMackeyPlace hL ι p).1
          (realMackeyPlace hL ι p).2 σ.1) := by
  have hE : (realPlaceEmbeddingsOver hL ι ι₀).infinite (realMackeyPlace hL ι p).1 =
      realEmbeddingOver hL ι p :=
    (realPlaceEmbeddingsOver_infinite hL ι ι₀ (realMackeyPlace hL ι p)).trans
      (realMackeyEmbedding_realMackeyPlaceEquiv hL ι p)
  refine (fixingOpenSubgroupEquiv_mackeyConj_real hL ι p.1.1.1 p.1.1.2 p.1.2.out
    (realMackeyPlace hL ι p).1 (realMackeyPlace hL ι p).2
    (realComplexEmbeddingOf_eq_embedding hL ι p) σ).trans ?_
  exact (congrArg (fun j : Ω →ₐ[L] AlgebraicClosure (realMackeyPlace hL ι p).1.Completion =>
    decompositionHom (realMackeyPlace hL ι p).1.Completion
      (j.comp (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)).val)
      (realClosureGaloisEquiv p.1.1.1 p.1.1.2 (realMackeyPlace hL ι p).1
        (realMackeyPlace hL ι p).2 σ.1)) hE).symm

end Embeddings

end

end Langlands.GaloisCohomology
