import Langlands.Galois.RestrictedRamification.OpenSubgroups
import Langlands.Galois.RestrictedRamification.PlaceEmbeddings
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Cohomology.Profinite.Mackey.Decomposition

/-!
# Localization homomorphisms of `G_S`

For a number field `K`, a Galois extension `Ω / K`, a set `S` of finite places of `K` and a choice
`ι : PlaceEmbeddings K Ω` of embeddings of `Ω` into the algebraic closures of the completions, the
decomposition homomorphisms of `ι` composed with restriction to `K_S` are the localization
homomorphisms `G_{K_v} → G_S` at the finite places and `G_{K_w} → G_S` at the infinite places.
For Mathlib's choice of embeddings they are Mathlib's `Field.absoluteGaloisGroup.map` followed by
restriction (`localizationHom_standard`); another choice changes them by conjugation in `G_S`.

The second part describes the localization of an open subgroup `U` of `G_S` fixing a finite
extension `L` of `K` inside `K_S`. An embedding `j : L →ₐ[K] K̄_v` determines a place `w` of `L`
above `v` and an embedding `L_w → K̄_v` extending `j` (through the decomposition
`K_v ⊗_K L ≅ ∏_{w | v} L_w`); the double cosets `U \ G_S / G_{K_v}` for `v ∈ S` correspond to the
places of `L` above `S`, and for each double coset the Mackey subgroup of `G_{K_v}` is the absolute
Galois group of `L_w`, compatibly with the localization of `G_{S_L}(L)` at `w`.
-/

namespace Langlands.Galois

open NumberField IsDedekindDomain

universe u v

noncomputable section

section Localization

variable {K : Type u} [Field K] [NumberField K] {Ω : Type v} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The localization homomorphism `G_{K_v} → G_S` at a finite place `v` for the embeddings `ι`.
Its domain `Gal(AlgebraicClosure K_v / K_v)` is `Field.absoluteGaloisGroup K_v` by definition. -/
def localizationHom (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) :
    Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →ₜ*
      GaloisGroupUnramifiedOutside K Ω S :=
  decompositionHom (v.adicCompletion K) ((ι.finite v).comp (maximalUnramifiedOutside K Ω S).val)

/-- The localization homomorphism `G_{K_w} → G_S` at an infinite place `w` for the embeddings `ι`
(the group is trivial at a complex place). -/
def realLocalizationHom (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))
    (w : InfinitePlace K) :
    Gal(AlgebraicClosure w.Completion/w.Completion) →ₜ* GaloisGroupUnramifiedOutside K Ω S :=
  decompositionHom w.Completion ((ι.infinite w).comp (maximalUnramifiedOutside K Ω S).val)

variable (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))

theorem localizationHom_apply (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K))
    (x : maximalUnramifiedOutside K Ω S) :
    ι.finite v ((localizationHom ι S v σ x : maximalUnramifiedOutside K Ω S) : Ω) =
      σ (ι.finite v x) :=
  decompositionHom_apply ((ι.finite v).comp (maximalUnramifiedOutside K Ω S).val) σ x

theorem realLocalizationHom_apply (w : InfinitePlace K)
    (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) (x : maximalUnramifiedOutside K Ω S) :
    ι.infinite w ((realLocalizationHom ι S w σ x : maximalUnramifiedOutside K Ω S) : Ω) =
      σ (ι.infinite w x) :=
  decompositionHom_apply ((ι.infinite w).comp (maximalUnramifiedOutside K Ω S).val) σ x

/-- The localization homomorphism is the decomposition homomorphism into `Gal(Ω / K)` followed by
restriction to `K_S`. -/
theorem localizationHom_eq_quotientMap (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    localizationHom ι S v σ =
      GaloisGroupUnramifiedOutside.quotientMap K Ω S (decompositionHom _ (ι.finite v) σ) :=
  decompositionHom_comp_val (ι.finite v) (maximalUnramifiedOutside K Ω S) σ

theorem realLocalizationHom_eq_quotientMap (w : InfinitePlace K)
    (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) :
    realLocalizationHom ι S w σ =
      GaloisGroupUnramifiedOutside.quotientMap K Ω S (decompositionHom _ (ι.infinite w) σ) :=
  decompositionHom_comp_val (ι.infinite w) (maximalUnramifiedOutside K Ω S) σ

/-- Localization is compatible with the restriction `G_S → G_T`. -/
theorem restrict_localizationHom {T : Set (HeightOneSpectrum (𝓞 K))} (h : T ⊆ S)
    (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    GaloisGroupUnramifiedOutside.restrict Ω h (localizationHom ι S v σ) = localizationHom ι T v σ := by
  rw [localizationHom_eq_quotientMap, localizationHom_eq_quotientMap,
    GaloisGroupUnramifiedOutside.restrict_quotientMap]

theorem restrict_realLocalizationHom {T : Set (HeightOneSpectrum (𝓞 K))} (h : T ⊆ S)
    (w : InfinitePlace K) (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) :
    GaloisGroupUnramifiedOutside.restrict Ω h (realLocalizationHom ι S w σ) =
      realLocalizationHom ι T w σ := by
  rw [realLocalizationHom_eq_quotientMap, realLocalizationHom_eq_quotientMap,
    GaloisGroupUnramifiedOutside.restrict_quotientMap]

/-- For two choices of embeddings, the localization homomorphisms at a finite place differ by
conjugation by an element of `G_S`. -/
theorem exists_localizationHom_eq_conj (ι ι' : PlaceEmbeddings K Ω) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ g : GaloisGroupUnramifiedOutside K Ω S,
      ∀ σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K),
        localizationHom ι' S v σ = g⁻¹ * localizationHom ι S v σ * g := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ((ι.finite v).comp (maximalUnramifiedOutside K Ω S).val)
    ((ι'.finite v).comp (maximalUnramifiedOutside K Ω S).val)
  refine ⟨g, fun σ => ?_⟩
  change decompositionHom _ ((ι'.finite v).comp (maximalUnramifiedOutside K Ω S).val) σ = _
  rw [hg, decompositionHom_comp]
  rfl

/-- For two choices of embeddings, the localization homomorphisms at an infinite place differ by
conjugation by an element of `G_S`. -/
theorem exists_realLocalizationHom_eq_conj (ι ι' : PlaceEmbeddings K Ω) (w : InfinitePlace K) :
    ∃ g : GaloisGroupUnramifiedOutside K Ω S,
      ∀ σ : Gal(AlgebraicClosure w.Completion/w.Completion),
        realLocalizationHom ι' S w σ = g⁻¹ * realLocalizationHom ι S w σ * g := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ((ι.infinite w).comp (maximalUnramifiedOutside K Ω S).val)
    ((ι'.infinite w).comp (maximalUnramifiedOutside K Ω S).val)
  refine ⟨g, fun σ => ?_⟩
  change decompositionHom _ ((ι'.infinite w).comp (maximalUnramifiedOutside K Ω S).val) σ = _
  rw [hg, decompositionHom_comp]
  rfl

end Localization

section Standard

variable {K : Type u} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- For Mathlib's embeddings, the localization homomorphism at a finite place is Mathlib's
`Field.absoluteGaloisGroup.map (algebraMap K K_v)` followed by restriction to `K_S`. -/
theorem localizationHom_standard (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    localizationHom (PlaceEmbeddings.standard K) S v σ =
      AlgEquiv.restrictNormalHom (maximalUnramifiedOutside K (AlgebraicClosure K) S)
        (Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) σ) := by
  rw [localizationHom_eq_quotientMap, PlaceEmbeddings.decompositionHom_standard_finite]
  rfl

/-- For Mathlib's embeddings, the localization homomorphism at an infinite place is Mathlib's
`Field.absoluteGaloisGroup.map (algebraMap K K_w)` followed by restriction to `K_S`. -/
theorem realLocalizationHom_standard (w : InfinitePlace K)
    (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) :
    realLocalizationHom (PlaceEmbeddings.standard K) S w σ =
      AlgEquiv.restrictNormalHom (maximalUnramifiedOutside K (AlgebraicClosure K) S)
        (Field.absoluteGaloisGroup.map (algebraMap K w.Completion) σ) := by
  rw [realLocalizationHom_eq_quotientMap, PlaceEmbeddings.decompositionHom_standard_infinite]
  rfl

end Standard

section PlaceOfEmbedding

/-! ### The place of `L` determined by an embedding into `K̄_v` -/

open Langlands.Global.AdelicFunctoriality
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

section Idempotents

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Semiring (A i)]
  {R : Type*} [CommRing R] [IsDomain R]

/-- A ring homomorphism from a finite product of rings to a domain sends exactly one of the
idempotents `Pi.single i 1` to `1`. -/
theorem exists_unique_map_single_one_eq_one (φ : (∀ i, A i) →+* R) :
    ∃! i, φ (Pi.single i 1) = 1 := by
  have hidem : ∀ i, φ (Pi.single i 1) = 0 ∨ φ (Pi.single i 1) = 1 := fun i ↦ by
    refine IsIdempotentElem.iff_eq_zero_or_one.1 ?_
    rw [IsIdempotentElem, ← map_mul, ← Pi.single_mul, one_mul]
  have hsum : ∑ i, φ (Pi.single i 1) = 1 := by
    have h1 : ∑ i, Pi.single i (1 : A i) = (1 : ∀ i, A i) := Finset.univ_sum_single 1
    rw [← map_sum, h1, map_one]
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, φ (Pi.single i 1) ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero h] at hsum
    exact zero_ne_one hsum
  refine ⟨i, (hidem i).resolve_left hi, fun j hj ↦ ?_⟩
  by_contra hji
  have h0 : Pi.single j (1 : A j) * Pi.single i 1 = 0 := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [hji]
    · simp [hk]
  have := congrArg φ h0
  rw [map_mul, map_zero, hj, (hidem i).resolve_left hi, one_mul] at this
  exact one_ne_zero this

omit [Fintype ι] [IsDomain R] in
theorem map_eq_map_single_of_map_single_one {φ : (∀ i, A i) →+* R} {i : ι}
    (hi : φ (Pi.single i 1) = 1) (y : ∀ i, A i) : φ y = φ (Pi.single i (y i)) := by
  have h : Pi.single i (1 : A i) * y = Pi.single i (y i) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hk]
  rw [← h, map_mul, hi, one_mul]

end Idempotents

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  {v : HeightOneSpectrum (𝓞 F)}

variable (L v) in
/-- `F_v ⊗_F L ≅ ∏_{w | v} L_w` (the Library's `finiteTensorMap`, bijective by
`completedTensorComparison`). -/
def completionsTensorEquiv :
    v.adicCompletion F ⊗[F] L ≃ₐ[v.adicCompletion F]
      ((w : FinitePlacesAbove L v) → w.1.adicCompletion L) :=
  AlgEquiv.ofBijective (finiteTensorMap v) ((completedTensorComparison F L).1 v)

theorem completionsTensorEquiv_tmul (a : v.adicCompletion F) (x : L) (w : FinitePlacesAbove L v) :
    completionsTensorEquiv L v (a ⊗ₜ x) w =
      algebraMap (v.adicCompletion F) (w.1.adicCompletion L) a * algebraMap L _ x :=
  rfl

theorem completionsTensorEquiv_one_tmul (x : L) :
    completionsTensorEquiv L v (1 ⊗ₜ x) =
      algebraMap L ((w : FinitePlacesAbove L v) → w.1.adicCompletion L) x := by
  funext w
  rw [completionsTensorEquiv_tmul, map_one, one_mul]
  rfl

section General

variable (j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F))

/-- The `F_v`-algebra homomorphism `∏_{w | v} L_w → K̄_v` extending an embedding
`j : L →ₐ[F] K̄_v`. -/
def tensorLiftOfAlgHom :
    ((w : FinitePlacesAbove L v) → w.1.adicCompletion L) →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F) :=
  (Algebra.TensorProduct.lift (Algebra.ofId _ _) j (fun _ _ ↦ Commute.all _ _)).comp
    (completionsTensorEquiv L v).symm.toAlgHom

theorem tensorLiftOfAlgHom_completionsTensorEquiv (t : v.adicCompletion F ⊗[F] L) :
    tensorLiftOfAlgHom j (completionsTensorEquiv L v t) =
      Algebra.TensorProduct.lift (Algebra.ofId _ _) j (fun _ _ ↦ Commute.all _ _) t := by
  simp [tensorLiftOfAlgHom]

theorem tensorLiftOfAlgHom_completionsTensorEquiv_tmul (a : v.adicCompletion F) (x : L) :
    tensorLiftOfAlgHom j (completionsTensorEquiv L v (a ⊗ₜ x)) =
      algebraMap (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) a * j x := by
  rw [tensorLiftOfAlgHom_completionsTensorEquiv, Algebra.TensorProduct.lift_tmul]
  rfl

theorem tensorLiftOfAlgHom_algebraMap (x : L) :
    tensorLiftOfAlgHom j (algebraMap L ((w : FinitePlacesAbove L v) → w.1.adicCompletion L) x) =
      j x := by
  rw [← completionsTensorEquiv_one_tmul, tensorLiftOfAlgHom_completionsTensorEquiv]
  simp

open Classical in
theorem exists_unique_tensorLiftOfAlgHom_single :
    ∃! w : FinitePlacesAbove L v, tensorLiftOfAlgHom j (Pi.single w 1) = 1 :=
  exists_unique_map_single_one_eq_one (tensorLiftOfAlgHom j).toRingHom

/-- The place of `L` above `v` determined by an embedding `j : L →ₐ[F] K̄_v`. -/
def placeOfAlgHom : FinitePlacesAbove L v :=
  (exists_unique_tensorLiftOfAlgHom_single j).exists.choose

open Classical in
theorem tensorLiftOfAlgHom_single_placeOfAlgHom :
    tensorLiftOfAlgHom j (Pi.single (placeOfAlgHom j) 1) = 1 :=
  (exists_unique_tensorLiftOfAlgHom_single j).exists.choose_spec

open Classical in
theorem eq_placeOfAlgHom_of_tensorLiftOfAlgHom {w : FinitePlacesAbove L v}
    (h : tensorLiftOfAlgHom j (Pi.single w 1) = 1) : w = placeOfAlgHom j :=
  (exists_unique_tensorLiftOfAlgHom_single j).unique h (tensorLiftOfAlgHom_single_placeOfAlgHom j)

theorem pi_single_algebraMap {w : FinitePlacesAbove L v} [DecidableEq (FinitePlacesAbove L v)]
    (a : v.adicCompletion F) :
    Pi.single w (algebraMap (v.adicCompletion F) (w.1.adicCompletion L) a) =
      algebraMap (v.adicCompletion F) ((w : FinitePlacesAbove L v) → w.1.adicCompletion L) a *
        Pi.single w 1 := by
  funext u
  by_cases hu : u = w
  · subst hu
    simp
  · simp [hu]

open Classical in
/-- The embedding `L_w → K̄_v` over `F_v` extending `j`, for `w` the place of `j`. -/
def completionEmbeddingOfAlgHom :
    (placeOfAlgHom j).1.adicCompletion L →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F) where
  toFun x := tensorLiftOfAlgHom j (Pi.single (placeOfAlgHom j) x)
  map_one' := tensorLiftOfAlgHom_single_placeOfAlgHom j
  map_mul' x y := by rw [Pi.single_mul, map_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' x y := by rw [Pi.single_add, map_add]
  commutes' a := by
    rw [pi_single_algebraMap, map_mul, AlgHom.commutes,
      tensorLiftOfAlgHom_single_placeOfAlgHom j, mul_one]

theorem tensorLiftOfAlgHom_eq (y : (w : FinitePlacesAbove L v) → w.1.adicCompletion L) :
    tensorLiftOfAlgHom j y = completionEmbeddingOfAlgHom j (y (placeOfAlgHom j)) := by
  classical
  exact map_eq_map_single_of_map_single_one (φ := (tensorLiftOfAlgHom j).toRingHom)
    (tensorLiftOfAlgHom_single_placeOfAlgHom j) y

@[simp]
theorem completionEmbeddingOfAlgHom_algebraMap (x : L) :
    completionEmbeddingOfAlgHom j (algebraMap L ((placeOfAlgHom j).1.adicCompletion L) x) = j x := by
  rw [← tensorLiftOfAlgHom_algebraMap j x, tensorLiftOfAlgHom_eq]
  rfl

end General

/-- Two `F_v`-algebra homomorphisms out of `L_w` that agree on `L` are equal. -/
theorem adicCompletion_algHom_ext {B : Type*} [Semiring B] [Algebra F B]
    [Algebra (v.adicCompletion F) B] [IsScalarTower F (v.adicCompletion F) B]
    {w : FinitePlacesAbove L v} {f g : w.1.adicCompletion L →ₐ[v.adicCompletion F] B}
    (h : ∀ x : L, f (algebraMap L _ x) = g (algebraMap L _ x)) : f = g := by
  have key : (f.comp (Pi.evalAlgHom _ _ w)).comp (completionsTensorEquiv L v).toAlgHom =
      (g.comp (Pi.evalAlgHom _ _ w)).comp (completionsTensorEquiv L v).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro a x
    change f ((completionsTensorEquiv L v (a ⊗ₜ x)) w) = g ((completionsTensorEquiv L v (a ⊗ₜ x)) w)
    rw [completionsTensorEquiv_tmul, map_mul, map_mul]
    congr 1
    · rw [AlgHom.commutes, AlgHom.commutes]
    · exact h x
  ext y
  classical
  obtain ⟨t, ht⟩ := (completionsTensorEquiv L v).surjective (Pi.single w y)
  have := DFunLike.congr_fun key t
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at this
  rw [show (completionsTensorEquiv L v).toAlgHom t = completionsTensorEquiv L v t from rfl, ht,
    Pi.single_eq_same] at this
  exact this

section Place

variable (j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F))

/-- An embedding of some `L_w` over `F_v` extending `j` forces `w` to be the place of `j`. -/
theorem eq_placeOfAlgHom {w : FinitePlacesAbove L v}
    (c : w.1.adicCompletion L →ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F))
    (hc : ∀ x : L, c (algebraMap L _ x) = j x) : w = placeOfAlgHom j := by
  classical
  have key : tensorLiftOfAlgHom j = c.comp (Pi.evalAlgHom _ _ w) := by
    have : (tensorLiftOfAlgHom j).comp (completionsTensorEquiv L v).toAlgHom =
        (c.comp (Pi.evalAlgHom _ _ w)).comp (completionsTensorEquiv L v).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro a x
      change tensorLiftOfAlgHom j (completionsTensorEquiv L v (a ⊗ₜ x)) =
        c ((completionsTensorEquiv L v (a ⊗ₜ x)) w)
      rw [tensorLiftOfAlgHom_completionsTensorEquiv_tmul, completionsTensorEquiv_tmul, map_mul,
        ← hc x]
      congr 1
      exact (c.commutes a).symm
    ext y
    obtain ⟨t, rfl⟩ := (completionsTensorEquiv L v).surjective y
    exact DFunLike.congr_fun this t
  apply eq_placeOfAlgHom_of_tensorLiftOfAlgHom
  refine (DFunLike.congr_fun key _).trans ?_
  rw [AlgHom.comp_apply, Pi.evalAlgHom_apply, Pi.single_eq_same, map_one]

/-- Every place of `L` above `v` is the place of some embedding `L →ₐ[F] K̄_v`. -/
theorem exists_placeOfAlgHom_eq (w : FinitePlacesAbove L v) :
    ∃ j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F), placeOfAlgHom j = w := by
  have := FiniteExtension.local_finite v w.1
  let c : w.1.adicCompletion L →ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F) :=
    IsAlgClosed.lift
  let j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F) :=
    (c.restrictScalars F).comp (IsScalarTower.toAlgHom F L (w.1.adicCompletion L))
  exact ⟨j, (eq_placeOfAlgHom j c fun _ => rfl).symm⟩

/-- Composing an embedding with an element of `Gal(K̄_v / F_v)` does not change its place. -/
theorem placeOfAlgHom_comp (g : Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F)) :
    placeOfAlgHom (((g : AlgebraicClosure (v.adicCompletion F) →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F)).restrictScalars F).comp j) = placeOfAlgHom j :=
  (eq_placeOfAlgHom _ ((g : AlgebraicClosure (v.adicCompletion F) →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F)).comp (completionEmbeddingOfAlgHom j)) fun x => by
    rw [AlgHom.comp_apply, completionEmbeddingOfAlgHom_algebraMap]
    rfl).symm

theorem exists_algEquiv_comp_eq {E : Type*} [Field E] [Algebra (v.adicCompletion F) E]
    (c c' : E →ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F)) :
    ∃ g : Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F), ∀ y, c' y = g (c y) := by
  let χ : c.fieldRange ≃ₐ[v.adicCompletion F] c'.fieldRange :=
    c.equivFieldRange.symm.trans c'.equivFieldRange
  refine ⟨χ.liftNormal (AlgebraicClosure (v.adicCompletion F)), fun y => ?_⟩
  have h := χ.liftNormal_commutes (AlgebraicClosure (v.adicCompletion F)) ⟨c y, y, rfl⟩
  refine Eq.trans ?_ h.symm
  change c' y = ((c'.equivFieldRange (c.equivFieldRange.symm ⟨c y, y, rfl⟩)) : _)
  have : c.equivFieldRange.symm ⟨c y, y, rfl⟩ = y :=
    c.equivFieldRange.symm_apply_eq.2 (Subtype.ext rfl)
  rw [this]
  rfl

/-- Two embeddings with the same place differ by an element of `Gal(K̄_v / F_v)`. -/
theorem exists_algEquiv_of_placeOfAlgHom_eq (j j' : L →ₐ[F] AlgebraicClosure (v.adicCompletion F))
    (h : placeOfAlgHom j = placeOfAlgHom j') :
    ∃ g : Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F), ∀ x, j' x = g (j x) := by
  obtain ⟨c', hc'⟩ : ∃ c' : (placeOfAlgHom j).1.adicCompletion L →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F), ∀ x, c' (algebraMap L _ x) = j' x := by
    rw [h]
    exact ⟨completionEmbeddingOfAlgHom j', completionEmbeddingOfAlgHom_algebraMap j'⟩
  obtain ⟨g, hg⟩ := exists_algEquiv_comp_eq (completionEmbeddingOfAlgHom j) c'
  refine ⟨g, fun x => ?_⟩
  rw [← hc' x, hg, completionEmbeddingOfAlgHom_algebraMap]

theorem apply_completionEmbeddingOfAlgHom_of_forall
    (g : Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F)) (hg : ∀ x, g (j x) = j x)
    (y : (placeOfAlgHom j).1.adicCompletion L) :
    g (completionEmbeddingOfAlgHom j y) = completionEmbeddingOfAlgHom j y := by
  have : ((g : AlgebraicClosure (v.adicCompletion F) →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F)).comp (completionEmbeddingOfAlgHom j)) =
        completionEmbeddingOfAlgHom j :=
    adicCompletion_algHom_ext fun x => by
      rw [AlgHom.comp_apply, completionEmbeddingOfAlgHom_algebraMap]
      exact hg x
  exact DFunLike.congr_fun this y

end Place

end PlaceOfEmbedding


section Fixing

/-! ### The absolute Galois group of `L_w` inside that of `K_v` -/

/-- The completion of a number field at a finite place has characteristic zero. -/
theorem charZero_adicCompletion {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    CharZero (v.adicCompletion F) :=
  charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective

attribute [local instance] charZero_adicCompletion

open Langlands.Global.AdelicFunctoriality
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  {v : HeightOneSpectrum (𝓞 F)} (j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F))

/-- `K̄_v` is an algebraic closure of `L_w` through `completionEmbeddingOfAlgHom j`; the resulting
isomorphism with `AlgebraicClosure L_w`. -/
def closureEquivOfAlgHom : AlgebraicClosure (v.adicCompletion F) ≃+*
    AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) :=
  letI : Algebra ((placeOfAlgHom j).1.adicCompletion L) (AlgebraicClosure (v.adicCompletion F)) :=
    (completionEmbeddingOfAlgHom j).toRingHom.toAlgebra
  haveI : IsScalarTower (v.adicCompletion F) ((placeOfAlgHom j).1.adicCompletion L)
      (AlgebraicClosure (v.adicCompletion F)) :=
    IsScalarTower.of_algebraMap_eq fun a => ((completionEmbeddingOfAlgHom j).commutes a).symm
  haveI : Algebra.IsAlgebraic ((placeOfAlgHom j).1.adicCompletion L)
      (AlgebraicClosure (v.adicCompletion F)) :=
    Algebra.IsAlgebraic.tower_top (K := v.adicCompletion F) ((placeOfAlgHom j).1.adicCompletion L)
  haveI : IsAlgClosure ((placeOfAlgHom j).1.adicCompletion L)
      (AlgebraicClosure (v.adicCompletion F)) :=
    ⟨inferInstance, inferInstance⟩
  (IsAlgClosure.equiv ((placeOfAlgHom j).1.adicCompletion L) (AlgebraicClosure (v.adicCompletion F))
    (AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L))).toRingEquiv

theorem closureEquivOfAlgHom_completionEmbedding (y : (placeOfAlgHom j).1.adicCompletion L) :
    closureEquivOfAlgHom j (completionEmbeddingOfAlgHom j y) =
      algebraMap _ (AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L)) y := by
  let _ : Algebra ((placeOfAlgHom j).1.adicCompletion L) (AlgebraicClosure (v.adicCompletion F)) :=
    (completionEmbeddingOfAlgHom j).toRingHom.toAlgebra
  exact AlgEquiv.commutes _ y

theorem closureEquivOfAlgHom_symm_algebraMap (y : (placeOfAlgHom j).1.adicCompletion L) :
    (closureEquivOfAlgHom j).symm
        (algebraMap _ (AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L)) y) =
      completionEmbeddingOfAlgHom j y :=
  (closureEquivOfAlgHom j).symm_apply_eq.2 (closureEquivOfAlgHom_completionEmbedding j y).symm

/-- The subgroup of `Gal(K̄_v / F_v)` fixing `j(L)`. -/
def fixingOfAlgHom : Subgroup Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F) where
  carrier := {σ | ∀ l, σ (j l) = j l}
  mul_mem' {a b} ha hb l := by
    change a (b (j l)) = j l
    rw [hb l, ha l]
  one_mem' _ := rfl
  inv_mem' {σ} hσ l := by
    rw [AlgEquiv.aut_inv]
    exact σ.symm_apply_eq.2 (hσ l).symm

omit [NumberField L] in
theorem mem_fixingOfAlgHom_iff
    (σ : Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F)) :
    σ ∈ fixingOfAlgHom j ↔ ∀ l, σ (j l) = j l :=
  Iff.rfl

/-- An element of `Gal(K̄_v / F_v)` fixing `j(L)` as an automorphism of `AlgebraicClosure L_w`. -/
def fixingOfAlgHomToAut (σ : fixingOfAlgHom j) :
    Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) /
      (placeOfAlgHom j).1.adicCompletion L) :=
  AlgEquiv.ofRingEquiv (f := ((closureEquivOfAlgHom j).symm.trans σ.1.toRingEquiv).trans
      (closureEquivOfAlgHom j)) fun y => by
    change closureEquivOfAlgHom j (σ.1 ((closureEquivOfAlgHom j).symm (algebraMap _ _ y))) = _
    rw [closureEquivOfAlgHom_symm_algebraMap, apply_completionEmbeddingOfAlgHom_of_forall j σ.1 σ.2,
      closureEquivOfAlgHom_completionEmbedding]

/-- An automorphism of `AlgebraicClosure L_w` as an element of `Gal(K̄_v / F_v)` fixing `j(L)`. -/
def autToFixingOfAlgHom
    (τ : Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) /
      (placeOfAlgHom j).1.adicCompletion L)) : fixingOfAlgHom j :=
  ⟨AlgEquiv.ofRingEquiv (f := ((closureEquivOfAlgHom j).trans τ.toRingEquiv).trans
      (closureEquivOfAlgHom j).symm) fun a => by
    change (closureEquivOfAlgHom j).symm (τ (closureEquivOfAlgHom j (algebraMap _ _ a))) = _
    rw [← (completionEmbeddingOfAlgHom j).commutes a, closureEquivOfAlgHom_completionEmbedding,
      τ.commutes, closureEquivOfAlgHom_symm_algebraMap],
   fun l => by
    change (closureEquivOfAlgHom j).symm (τ (closureEquivOfAlgHom j (j l))) = j l
    rw [← completionEmbeddingOfAlgHom_algebraMap j l, closureEquivOfAlgHom_completionEmbedding,
      τ.commutes, closureEquivOfAlgHom_symm_algebraMap]⟩

/-- The subgroup of `Gal(K̄_v / F_v)` fixing `j(L)` is `Gal(L̄_w / L_w)`. -/
def fixingOfAlgHomMulEquiv : fixingOfAlgHom j ≃*
    Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) /
      (placeOfAlgHom j).1.adicCompletion L) where
  toFun := fixingOfAlgHomToAut j
  invFun := autToFixingOfAlgHom j
  left_inv σ := Subtype.ext (AlgEquiv.ext fun z => by
    change (closureEquivOfAlgHom j).symm (closureEquivOfAlgHom j
      (σ.1 ((closureEquivOfAlgHom j).symm (closureEquivOfAlgHom j z)))) = σ.1 z
    simp)
  right_inv τ := AlgEquiv.ext fun z => by
    change closureEquivOfAlgHom j ((closureEquivOfAlgHom j).symm
      (τ (closureEquivOfAlgHom j ((closureEquivOfAlgHom j).symm z)))) = τ z
    simp
  map_mul' σ τ := AlgEquiv.ext fun z => by
    change closureEquivOfAlgHom j (σ.1 (τ.1 ((closureEquivOfAlgHom j).symm z))) =
      closureEquivOfAlgHom j (σ.1 ((closureEquivOfAlgHom j).symm (closureEquivOfAlgHom j
        (τ.1 ((closureEquivOfAlgHom j).symm z)))))
    simp

theorem fixingOfAlgHomMulEquiv_apply (σ : fixingOfAlgHom j)
    (z : AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L)) :
    fixingOfAlgHomMulEquiv j σ z =
      closureEquivOfAlgHom j (σ.1 ((closureEquivOfAlgHom j).symm z)) :=
  rfl

theorem continuous_coe_fixingOfAlgHomMulEquiv_symm :
    Continuous fun τ : Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) /
        (placeOfAlgHom j).1.adicCompletion L) =>
      (((fixingOfAlgHomMulEquiv j).symm τ : fixingOfAlgHom j) :
        Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F)) := by
  let f : Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) /
      (placeOfAlgHom j).1.adicCompletion L) →*
      Gal(AlgebraicClosure (v.adicCompletion F) / v.adicCompletion F) :=
    (fixingOfAlgHom j).subtype.comp (fixingOfAlgHomMulEquiv j).symm.toMonoidHom
  change Continuous f
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff (v.adicCompletion F)
    (AlgebraicClosure (v.adicCompletion F)) s).1 hs
  classical
  let b := Module.finBasis (v.adicCompletion F) E
  let E' : IntermediateField ((placeOfAlgHom j).1.adicCompletion L)
      (AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L)) :=
    IntermediateField.adjoin _ (Set.range fun i => closureEquivOfAlgHom j (b i : _))
  have hE' : FiniteDimensional ((placeOfAlgHom j).1.adicCompletion L) E' :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((krullTopology_mem_nhds_one_iff _ _ _).2 ⟨E', hE', le_rfl⟩)
    fun τ hτ => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
  have hb : ∀ i, f τ (b i : AlgebraicClosure (v.adicCompletion F)) = b i := fun i => by
    change (closureEquivOfAlgHom j).symm (τ (closureEquivOfAlgHom j (b i : _))) = b i
    rw [hτ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩), RingEquiv.symm_apply_apply]
  intro y hy
  have hlin : ((f τ).toLinearMap ∘ₗ E.val.toLinearMap :
      E →ₗ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F)) = E.val.toLinearMap :=
    b.ext fun i => hb i
  exact LinearMap.congr_fun hlin ⟨y, hy⟩

/-- The subgroup of `Gal(K̄_v / F_v)` fixing `j(L)` is `Gal(L̄_w / L_w)`, as topological groups. -/
def fixingOfAlgHomEquiv : fixingOfAlgHom j ≃ₜ*
    Gal(AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L) /
      (placeOfAlgHom j).1.adicCompletion L) :=
  have hc : Continuous (fixingOfAlgHomMulEquiv j).symm :=
    (continuous_coe_fixingOfAlgHomMulEquiv_symm j).subtype_mk _
  let e := hc.homeoOfEquivCompactToT2 (f := (fixingOfAlgHomMulEquiv j).symm.toEquiv)
  { fixingOfAlgHomMulEquiv j with
    continuous_toFun := e.symm.continuous
    continuous_invFun := hc }

theorem fixingOfAlgHomEquiv_apply (σ : fixingOfAlgHom j)
    (z : AlgebraicClosure ((placeOfAlgHom j).1.adicCompletion L)) :
    fixingOfAlgHomEquiv j σ z = closureEquivOfAlgHom j (σ.1 ((closureEquivOfAlgHom j).symm z)) :=
  rfl

end Fixing

section SubgroupCongr

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- Equal subgroups are isomorphic as topological groups. -/
def continuousMulEquivOfSubgroupEq {A B : Subgroup H} (h : A = B) : A ≃ₜ* B :=
  { MulEquiv.subgroupCongr h with
    continuous_toFun := continuous_subtype_val.subtype_mk _
    continuous_invFun := continuous_subtype_val.subtype_mk _ }

end SubgroupCongr

section Mackey

/-! ### Localization of the open subgroup fixing `L` -/

open Langlands.ProfiniteCohomology GaloisGroupUnramifiedOutside
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (ι : PlaceEmbeddings K Ω)

/-- The embedding `L → K̄_v` attached to an element `x` of `G_S`: `ι_v ∘ x⁻¹` restricted to `L`. -/
def localEmbedding (v : HeightOneSpectrum (𝓞 K)) (x : GaloisGroupUnramifiedOutside K Ω S) :
    L →ₐ[K] AlgebraicClosure (v.adicCompletion K) :=
  ((ι.finite v).comp ((maximalUnramifiedOutside K Ω S).val.comp
    (x⁻¹ : GaloisGroupUnramifiedOutside K Ω S).toAlgHom)).comp (embeddingMaximalUnramifiedOutside hL)

theorem localEmbedding_apply (v : HeightOneSpectrum (𝓞 K)) (x : GaloisGroupUnramifiedOutside K Ω S)
    (l : L) :
    localEmbedding hL ι v x l =
      ι.finite v ((((x⁻¹ : GaloisGroupUnramifiedOutside K Ω S)
        (embeddingMaximalUnramifiedOutside hL l)) : maximalUnramifiedOutside K Ω S) : Ω) :=
  rfl

theorem mem_mackeySubgroup_iff (v : HeightOneSpectrum (𝓞 K)) (x : GaloisGroupUnramifiedOutside K Ω S)
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    σ ∈ mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
        (localizationHom ι S v).toMonoidHom x ↔
      ∀ l : L, σ (localEmbedding hL ι v x l) = localEmbedding hL ι v x l := by
  rw [mem_mackeySubgroup]
  change _ ∈ fixingOpenSubgroup S hL ↔ _
  rw [mem_fixingOpenSubgroup_iff]
  refine forall_congr' fun l => ?_
  have key := localizationHom_apply ι S v σ
    ((x⁻¹ : GaloisGroupUnramifiedOutside K Ω S) (embeddingMaximalUnramifiedOutside hL l))
  rw [localEmbedding_apply, ← key]
  change x (localizationHom ι S v σ (x⁻¹ (embeddingMaximalUnramifiedOutside hL l))) =
    embeddingMaximalUnramifiedOutside hL l ↔ _
  constructor
  · intro h
    have h' := congrArg (⇑(x⁻¹ : GaloisGroupUnramifiedOutside K Ω S)) h
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h'
    rw [h']
  · intro h
    have h' := Subtype.ext ((ι.finite v).injective h)
    rw [h', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

/-- The Mackey subgroup of `G_{K_v}` at `x` is the subgroup fixing the embedding of `L`
attached to `x`. -/
theorem mackeySubgroup_eq (v : HeightOneSpectrum (𝓞 K)) (x : GaloisGroupUnramifiedOutside K Ω S) :
    mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
        (localizationHom ι S v).toMonoidHom x = fixingOfAlgHom (localEmbedding hL ι v x) :=
  Subgroup.ext fun σ => mem_mackeySubgroup_iff hL ι v x σ

theorem localEmbedding_mul (v : HeightOneSpectrum (𝓞 K)) (x : GaloisGroupUnramifiedOutside K Ω S)
    {u : GaloisGroupUnramifiedOutside K Ω S} (hu : u ∈ fixingOpenSubgroup S hL)
    (h : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) (l : L) :
    localEmbedding hL ι v (u * x * localizationHom ι S v h) l =
      h⁻¹ (localEmbedding hL ι v x l) := by
  have hul := (mem_fixingOpenSubgroup_iff S hL u).1 hu l
  have hu' : u⁻¹ (embeddingMaximalUnramifiedOutside hL l) = embeddingMaximalUnramifiedOutside hL l := by
    rw [AlgEquiv.aut_inv]
    exact u.symm_apply_eq.2 hul.symm
  rw [localEmbedding_apply, localEmbedding_apply, mul_inv_rev, mul_inv_rev, ← map_inv,
    AlgEquiv.mul_apply, AlgEquiv.mul_apply, hu']
  exact localizationHom_apply ι S v h⁻¹ _

theorem exists_localEmbedding_eq (v : HeightOneSpectrum (𝓞 K))
    (j : L →ₐ[K] AlgebraicClosure (v.adicCompletion K)) :
    ∃ x, localEmbedding hL ι v x = j := by
  let _ : Algebra L (maximalUnramifiedOutside K Ω S) :=
    (embeddingMaximalUnramifiedOutside hL).toRingHom.toAlgebra
  have : IsScalarTower K L (maximalUnramifiedOutside K Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((embeddingMaximalUnramifiedOutside hL).commutes a).symm
  let _ : Algebra L (AlgebraicClosure (v.adicCompletion K)) := j.toRingHom.toAlgebra
  have : IsScalarTower K L (AlgebraicClosure (v.adicCompletion K)) :=
    IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  have : Algebra.IsAlgebraic L (maximalUnramifiedOutside K Ω S) :=
    Algebra.IsAlgebraic.tower_top (K := K) L
  let j' : maximalUnramifiedOutside K Ω S →ₐ[L] AlgebraicClosure (v.adicCompletion K) :=
    IsAlgClosed.lift
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ((ι.finite v).comp (maximalUnramifiedOutside K Ω S).val)
    (j'.restrictScalars K)
  refine ⟨g⁻¹, AlgHom.ext fun l => ?_⟩
  have h1 : j l = j' (embeddingMaximalUnramifiedOutside hL l) := (j'.commutes l).symm
  have h2 := DFunLike.congr_fun hg (embeddingMaximalUnramifiedOutside hL l)
  rw [h1, localEmbedding_apply, inv_inv]
  exact h2.symm

/-- The place of `L` above `v` attached to `x ∈ G_S`. -/
abbrev localPlace (v : HeightOneSpectrum (𝓞 K)) (x : GaloisGroupUnramifiedOutside K Ω S) :
    Langlands.Global.AdelicFunctoriality.FinitePlacesAbove L v :=
  placeOfAlgHom (localEmbedding hL ι v x)

theorem localPlace_mul (v : HeightOneSpectrum (𝓞 K)) (x : GaloisGroupUnramifiedOutside K Ω S)
    {u : GaloisGroupUnramifiedOutside K Ω S} (hu : u ∈ fixingOpenSubgroup S hL)
    (h : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    localPlace hL ι v (u * x * localizationHom ι S v h) = localPlace hL ι v x := by
  have e : localEmbedding hL ι v (u * x * localizationHom ι S v h) =
      (((h⁻¹ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
        AlgebraicClosure (v.adicCompletion K) →ₐ[v.adicCompletion K]
          AlgebraicClosure (v.adicCompletion K)).restrictScalars K).comp
        (localEmbedding hL ι v x) :=
    AlgHom.ext fun l => localEmbedding_mul hL ι v x hu h l
  rw [localPlace, e, placeOfAlgHom_comp]

variable (S) in
/-- The place of `L` above `S` attached to a double coset `U x G_{K_v}`, `v ∈ S`. -/
def mackeyPlace (p : Σ v : S, MackeyDoubleCoset
      (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (localizationHom ι S v).toMonoidHom) :
    finitePlacesAbove L S :=
  ⟨(localPlace hL ι p.1 p.2.out).1, p.1.1, p.1.2, (localPlace hL ι p.1 p.2.out).2⟩

theorem mackeyPlace_injective : Function.Injective (mackeyPlace S hL ι) := by
  rintro ⟨v, d⟩ ⟨v', d'⟩ h
  have h1 : (localPlace hL ι v d.out).1 = (localPlace hL ι v' d'.out).1 := congrArg Subtype.val h
  have hv : v = v' := by
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    have a := (localPlace hL ι v d.out).2
    have b := (localPlace hL ι v' d'.out).2
    rw [h1] at a
    exact a.over.trans b.over.symm
  subst hv
  have h2 : localPlace hL ι v d.out = localPlace hL ι v d'.out := Subtype.ext h1
  obtain ⟨g, hg⟩ := exists_algEquiv_of_placeOfAlgHom_eq _ _ h2
  have hmem : d'.out * localizationHom ι S v g * d.out⁻¹ ∈ fixingOpenSubgroup S hL := by
    rw [mem_fixingOpenSubgroup_iff]
    intro l
    have hinj : d'.out⁻¹ (embeddingMaximalUnramifiedOutside hL l) =
        localizationHom ι S v g (d.out⁻¹ (embeddingMaximalUnramifiedOutside hL l)) :=
      Subtype.ext ((ι.finite v).injective ((hg l).trans (localizationHom_apply ι S v g _).symm))
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hinj, ← AlgEquiv.mul_apply, mul_inv_cancel,
      AlgEquiv.one_apply]
  have hd : d = d' := by
    rw [← DoubleCoset.out_eq' d, ← DoubleCoset.out_eq' d', DoubleCoset.eq]
    refine ⟨_, hmem, localizationHom ι S v g⁻¹, ⟨g⁻¹, rfl⟩, ?_⟩
    rw [map_inv]
    group
  rw [hd]

theorem mackeyPlace_surjective : Function.Surjective (mackeyPlace S hL ι) := by
  rintro ⟨w, v0, hv0, hw⟩
  let v : S := ⟨v0, hv0⟩
  obtain ⟨j, hj⟩ := exists_placeOfAlgHom_eq
    (⟨w, hw⟩ : Langlands.Global.AdelicFunctoriality.FinitePlacesAbove L v0)
  obtain ⟨x, hx⟩ := exists_localEmbedding_eq hL ι v j
  let d : MackeyDoubleCoset (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (localizationHom ι S v).toMonoidHom :=
    DoubleCoset.mk _ _ x
  refine ⟨⟨v, d⟩, ?_⟩
  obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mk_out_eq_mul
    (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
    (localizationHom ι S v).toMonoidHom.range x
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hb
  apply Subtype.ext
  change (localPlace hL ι v d.out).1 = w
  have e1 : d.out = a * x * localizationHom ι S v h := hab
  rw [e1, localPlace_mul hL ι v x ha h, localPlace, hx, hj]

variable (S) in
/-- The double cosets `U \ G_S / G_{K_v}`, `v ∈ S`, for `U` the subgroup fixing `L`, correspond to
the places of `L` above `S`. -/
def mackeyPlaceEquiv :
    (Σ v : S, MackeyDoubleCoset
      (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (localizationHom ι S v).toMonoidHom) ≃ finitePlacesAbove L S :=
  Equiv.ofBijective (mackeyPlace S hL ι) ⟨mackeyPlace_injective hL ι, mackeyPlace_surjective hL ι⟩

theorem coe_mackeyPlaceEquiv (p : Σ v : S, MackeyDoubleCoset
      (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (localizationHom ι S v).toMonoidHom) :
    (mackeyPlaceEquiv S hL ι p : HeightOneSpectrum (𝓞 L)) = (localPlace hL ι p.1 p.2.out).1 :=
  rfl

/-- The embedding of `Ω` over `L` into `AlgebraicClosure L_w`, `w` the place attached to `x`. -/
def localEmbeddingOver (v : HeightOneSpectrum (𝓞 K)) (x : GaloisGroupUnramifiedOutside K Ω S) :
    Ω →ₐ[L] AlgebraicClosure ((localPlace hL ι v x).1.adicCompletion L) :=
  { ((closureEquivOfAlgHom (localEmbedding hL ι v x)).toRingHom.comp
      ((ι.finite v).toRingHom.comp ((lift x)⁻¹ : Gal(Ω/K)).toRingEquiv.toRingHom)) with
    commutes' := fun l => by
      change closureEquivOfAlgHom (localEmbedding hL ι v x)
        (ι.finite v ((lift x)⁻¹ (((embeddingMaximalUnramifiedOutside hL l :
          maximalUnramifiedOutside K Ω S)) : Ω))) = _
      rw [lift_inv_apply]
      change closureEquivOfAlgHom (localEmbedding hL ι v x) (localEmbedding hL ι v x l) = _
      rw [← completionEmbeddingOfAlgHom_algebraMap, closureEquivOfAlgHom_completionEmbedding]
      exact (IsScalarTower.algebraMap_apply L ((localPlace hL ι v x).1.adicCompletion L) _ l).symm }

theorem localEmbeddingOver_apply (v : HeightOneSpectrum (𝓞 K))
    (x : GaloisGroupUnramifiedOutside K Ω S) (y : Ω) :
    localEmbeddingOver hL ι v x y =
      closureEquivOfAlgHom (localEmbedding hL ι v x) (ι.finite v ((lift x)⁻¹ y)) :=
  rfl

/-- The Mackey subgroup of `G_{K_v}` at `x` is the absolute Galois group of `L_w`, `w` the place
attached to `x`. -/
def mackeyLocalEquiv (v : HeightOneSpectrum (𝓞 K)) (x : GaloisGroupUnramifiedOutside K Ω S) :
    mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
        (localizationHom ι S v).toMonoidHom x ≃ₜ*
      Gal(AlgebraicClosure ((localPlace hL ι v x).1.adicCompletion L) /
        (localPlace hL ι v x).1.adicCompletion L) :=
  (continuousMulEquivOfSubgroupEq (mackeySubgroup_eq hL ι v x)).trans
    (fixingOfAlgHomEquiv (localEmbedding hL ι v x))

theorem mackeyLocalEquiv_apply (v : HeightOneSpectrum (𝓞 K)) (x : GaloisGroupUnramifiedOutside K Ω S)
    (σ : mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (localizationHom ι S v).toMonoidHom x)
    (z : AlgebraicClosure ((localPlace hL ι v x).1.adicCompletion L)) :
    mackeyLocalEquiv hL ι v x σ z = closureEquivOfAlgHom (localEmbedding hL ι v x)
      (σ.1 ((closureEquivOfAlgHom (localEmbedding hL ι v x)).symm z)) :=
  rfl

/-- Under `G_S(K) ⊇ U ≅ G_{S_L}(L)` and the Mackey isomorphism, conjugation by `x` of the Mackey
subgroup is the decomposition homomorphism of `L_w` for the embedding `localEmbeddingOver`. -/
theorem fixingOpenSubgroupEquiv_mackeyConj [IsGalois L Ω] (v : HeightOneSpectrum (𝓞 K))
    (x : GaloisGroupUnramifiedOutside K Ω S)
    (σ : mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      (localizationHom ι S v).toMonoidHom x) :
    fixingOpenSubgroupEquiv S hL (mackeyConj (fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (localizationHom ι S v).toMonoidHom x σ) =
      decompositionHom ((localPlace hL ι v x).1.adicCompletion L)
        ((localEmbeddingOver hL ι v x).comp
          (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)).val)
        (mackeyLocalEquiv hL ι v x σ) := by
  symm
  rw [decompositionHom_eq_iff]
  intro t
  have hu := coe_fixingOpenSubgroupEquiv_apply hL (mackeyConj (fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (localizationHom ι S v).toMonoidHom x σ) t
  have ht : ((t : maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) : Ω) =
      (((maximalUnramifiedOutsideEquiv hL).symm t : maximalUnramifiedOutside K Ω S) : Ω) :=
    (coe_fieldEquivOfRestrictScalarsEq_symm (restrictScalars_maximalUnramifiedOutside S hL) t).symm
  rw [AlgHom.comp_apply, AlgHom.comp_apply, IntermediateField.coe_val, localEmbeddingOver_apply,
    localEmbeddingOver_apply, mackeyLocalEquiv_apply, RingEquiv.symm_apply_apply, hu, ht,
    mackeyConj_apply_coe]
  have key : (lift x)⁻¹ ((((x * (localizationHom ι S v).toMonoidHom σ * x⁻¹)
      ((maximalUnramifiedOutsideEquiv hL).symm t) : maximalUnramifiedOutside K Ω S)) : Ω) =
      ((localizationHom ι S v σ ((x⁻¹ : GaloisGroupUnramifiedOutside K Ω S)
        ((maximalUnramifiedOutsideEquiv hL).symm t)) : maximalUnramifiedOutside K Ω S) : Ω) := by
    rw [lift_inv_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply x⁻¹ x,
      inv_mul_cancel, AlgEquiv.one_apply]
    rfl
  rw [key, localizationHom_apply, lift_inv_apply]

/-- For any embedding `ι'` of `Ω` over `L` into `AlgebraicClosure L_w`, conjugation by `x` of the
Mackey subgroup is, up to conjugation in `G_{S_L}(L)`, the decomposition homomorphism of `ι'`. -/
theorem exists_fixingOpenSubgroupEquiv_mackeyConj_eq [IsGalois L Ω] (v : HeightOneSpectrum (𝓞 K))
    (x : GaloisGroupUnramifiedOutside K Ω S)
    (ι' : Ω →ₐ[L] AlgebraicClosure ((localPlace hL ι v x).1.adicCompletion L)) :
    ∃ g : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S),
      ∀ σ : mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
          (localizationHom ι S v).toMonoidHom x,
        fixingOpenSubgroupEquiv S hL (mackeyConj (fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (localizationHom ι S v).toMonoidHom x σ) =
          g⁻¹ * decompositionHom ((localPlace hL ι v x).1.adicCompletion L)
            (ι'.comp (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)).val)
            (mackeyLocalEquiv hL ι v x σ) * g := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal
    (ι'.comp (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)).val)
    ((localEmbeddingOver hL ι v x).comp (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)).val)
  refine ⟨g, fun σ => ?_⟩
  rw [fixingOpenSubgroupEquiv_mackeyConj, hg, decompositionHom_comp]

/-- The same with the localization homomorphisms of a choice of embeddings `ιL` for `L`. -/
theorem exists_fixingOpenSubgroupEquiv_mackeyConj_eq_localizationHom [IsGalois L Ω]
    (ιL : PlaceEmbeddings L Ω)
    (v : HeightOneSpectrum (𝓞 K)) (x : GaloisGroupUnramifiedOutside K Ω S) :
    ∃ g : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S),
      ∀ σ : mackeySubgroup (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
          (localizationHom ι S v).toMonoidHom x,
        fixingOpenSubgroupEquiv S hL (mackeyConj (fixingOpenSubgroup S hL :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (localizationHom ι S v).toMonoidHom x σ) =
          g⁻¹ * localizationHom ιL (finitePlacesAbove L S) (localPlace hL ι v x).1
            (mackeyLocalEquiv hL ι v x σ) * g := by
  exact exists_fixingOpenSubgroupEquiv_mackeyConj_eq hL ι v x (ιL.finite _)

end Mackey

end

end Langlands.Galois
