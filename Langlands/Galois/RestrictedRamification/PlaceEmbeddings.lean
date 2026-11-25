import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Decomposition homomorphisms and embeddings of closures at the places

An embedding `ι : E →ₐ[K] Ωv` of a normal extension `E / K` into an extension `Ωv` of an extension
`Kv` of `K` gives a continuous homomorphism `Gal(Ωv / Kv) → Gal(E / K)`: an automorphism of `Ωv`
over `Kv` preserves `ι(E)`, and is transported back to `E`. Changing `ι` by an automorphism `g` of
`E` conjugates this homomorphism by `g`.

`PlaceEmbeddings K Ω` bundles, for a number field `K` and a field `Ω` over `K`, one embedding of `Ω`
over `K` into an algebraic closure of each completion of `K`, at the finite and at the infinite
places. When `Ω` is a separable closure of `K` such embeddings exist; for `Ω = AlgebraicClosure K`
the choice made by Mathlib's `Field.absoluteGaloisGroup.map` is `PlaceEmbeddings.standard`, and the
decomposition homomorphisms of `standard` are Mathlib's maps of absolute Galois groups.
-/

namespace Langlands.Galois

open NumberField IsDedekindDomain

section DecompositionHom

variable {K E : Type*} (Kv : Type*) {Ωv : Type*} [Field K] [Field E] [Field Kv] [Field Ωv]
  [Algebra K E] [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv] [IsScalarTower K Kv Ωv]

/-- The homomorphism `Gal(Ωv / Kv) → Gal(E / K)` attached to an embedding `ι : E →ₐ[K] Ωv` of a
normal extension: restriction of scalars to `K`, then restriction to `ι(E)`. -/
noncomputable def decompositionMonoidHom [Normal K E] (ι : E →ₐ[K] Ωv) : Gal(Ωv/Kv) →* Gal(E/K) :=
  letI : Algebra E Ωv := ι.toRingHom.toAlgebra
  haveI : IsScalarTower K E Ωv := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom K)

variable {Kv}

theorem decompositionMonoidHom_apply [Normal K E] (ι : E →ₐ[K] Ωv) (σ : Gal(Ωv/Kv)) (x : E) :
    ι (decompositionMonoidHom Kv ι σ x) = σ (ι x) := by
  let _ : Algebra E Ωv := ι.toRingHom.toAlgebra
  have : IsScalarTower K E Ωv := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) E x

theorem decompositionMonoidHom_eq_iff [Normal K E] (ι : E →ₐ[K] Ωv) (σ : Gal(Ωv/Kv))
    (τ : Gal(E/K)) : decompositionMonoidHom Kv ι σ = τ ↔ ∀ x, ι (τ x) = σ (ι x) := by
  constructor
  · rintro rfl x
    exact decompositionMonoidHom_apply ι σ x
  · intro h
    ext x
    apply ι.injective
    change ι _ = ι _
    rw [decompositionMonoidHom_apply, h]

theorem continuous_decompositionMonoidHom [Normal K E] (ι : E →ₐ[K] Ωv) :
    Continuous (decompositionMonoidHom Kv ι) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨L, hL, hLU⟩ := hU
  let b := Module.finBasis K L
  let T : IntermediateField Kv Ωv := IntermediateField.adjoin Kv (Set.range fun i => ι (b i))
  have hT : FiniteDimensional Kv T := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    exact ((Algebra.IsAlgebraic.isAlgebraic (R := K) ((b i : L) : E)).isIntegral.map ι).tower_top
  apply mem_nhds_iff.mpr
  refine ⟨T.fixingSubgroup, fun σ hσ => hLU ?_, T.fixingSubgroup_isOpen, one_mem _⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, decompositionMonoidHom Kv ι σ (b i : E) = b i := fun i => by
    apply ι.injective
    change ι _ = ι _
    rw [decompositionMonoidHom_apply]
    exact hσ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  intro y hy
  have hy' : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : E) := by
    have := congrArg L.val (b.sum_repr ⟨y, hy⟩)
    rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm
  rw [hy', map_sum]
  simp only [map_smul, hb]

variable (Kv) in
/-- The decomposition homomorphism `Gal(Ωv / Kv) →ₜ* Gal(E / K)` of an embedding
`ι : E →ₐ[K] Ωv` of a normal extension. -/
noncomputable def decompositionHom [Normal K E] (ι : E →ₐ[K] Ωv) : Gal(Ωv/Kv) →ₜ* Gal(E/K) :=
  ⟨decompositionMonoidHom Kv ι, continuous_decompositionMonoidHom ι⟩

@[simp]
theorem decompositionHom_toMonoidHom [Normal K E] (ι : E →ₐ[K] Ωv) :
    (decompositionHom Kv ι).toMonoidHom = decompositionMonoidHom Kv ι :=
  rfl

theorem decompositionHom_apply [Normal K E] (ι : E →ₐ[K] Ωv) (σ : Gal(Ωv/Kv)) (x : E) :
    ι (decompositionHom Kv ι σ x) = σ (ι x) :=
  decompositionMonoidHom_apply ι σ x

theorem decompositionHom_eq_iff [Normal K E] (ι : E →ₐ[K] Ωv) (σ : Gal(Ωv/Kv)) (τ : Gal(E/K)) :
    decompositionHom Kv ι σ = τ ↔ ∀ x, ι (τ x) = σ (ι x) :=
  decompositionMonoidHom_eq_iff ι σ τ

/-- Two embeddings of a normal extension differ by an automorphism. -/
theorem exists_eq_comp_of_normal [Normal K E] (ι ι' : E →ₐ[K] Ωv) :
    ∃ g : Gal(E/K), ι' = ι.comp (g : E →ₐ[K] E) := by
  let _ : Algebra E Ωv := ι.toRingHom.toAlgebra
  have : IsScalarTower K E Ωv := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  refine ⟨ι'.restrictNormal' E, ?_⟩
  ext x
  exact (AlgHom.restrictNormal_commutes ι' E x).symm

/-- Changing the embedding by an automorphism `g` conjugates the decomposition homomorphism. -/
theorem decompositionHom_comp [Normal K E] (ι : E →ₐ[K] Ωv) (g : Gal(E/K)) (σ : Gal(Ωv/Kv)) :
    decompositionHom Kv (ι.comp (g : E →ₐ[K] E)) σ = g⁻¹ * decompositionHom Kv ι σ * g := by
  rw [decompositionHom_eq_iff]
  intro x
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
    AlgEquiv.apply_symm_apply, decompositionHom_apply]

/-- The decomposition homomorphism of a normal subextension `N` of `E` is the restriction to `N`
of the decomposition homomorphism of `E`. -/
theorem decompositionHom_comp_val [Normal K E] (ι : E →ₐ[K] Ωv) (N : IntermediateField K E)
    [Normal K N] (σ : Gal(Ωv/Kv)) :
    decompositionHom Kv (ι.comp N.val) σ = AlgEquiv.restrictNormalHom N (decompositionHom Kv ι σ) := by
  ext x
  apply ι.injective
  change (ι.comp N.val) (decompositionHom Kv (ι.comp N.val) σ x) =
    ι ((AlgEquiv.restrictNormalHom N (decompositionHom Kv ι σ) x : N) : E)
  rw [decompositionHom_apply, AlgEquiv.restrictNormalHom_apply, decompositionHom_apply]
  rfl

/-- Embeddings of a separable extension into a separably closed field exist. -/
theorem nonempty_algHom_of_isSepClosed [Algebra.IsSeparable K E] [IsSepClosed Ωv] :
    Nonempty (E →ₐ[K] Ωv) :=
  ⟨IsSepClosed.lift⟩

end DecompositionHom

section StandardEmbedding

variable {K : Type*} [Field K]

/-- `IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L` for the algebra structure `i`
of `L` over `K`, as a ring homomorphism. -/
noncomputable def standardEmbeddingRingHom (K L : Type*) [Field K] [Field L] (i : Algebra K L) :
    AlgebraicClosure K →+* AlgebraicClosure L :=
  (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toRingHom

theorem standardEmbeddingRingHom_algebraMap (K L : Type*) [Field K] [Field L] (i : Algebra K L)
    (x : K) : standardEmbeddingRingHom K L i (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (algebraMap K L x) := by
  have := (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).commutes x
  rw [IsScalarTower.algebraMap_apply K L (AlgebraicClosure L)] at this
  exact this

/-- The embedding of `AlgebraicClosure K` into the algebraic closure of a field `L` over `K` that
Mathlib's `Field.absoluteGaloisGroup.map (algebraMap K L)` chooses. -/
noncomputable def standardEmbedding {K L : Type*} [Field K] [Field L] [Algebra K L] :
    AlgebraicClosure K →ₐ[K] AlgebraicClosure L where
  toRingHom := standardEmbeddingRingHom K L (algebraMap K L).toAlgebra
  commutes' x := (standardEmbeddingRingHom_algebraMap K L _ x).trans
    (IsScalarTower.algebraMap_apply K L (AlgebraicClosure L) x).symm

private theorem algebraMap_mapOfAlgebra (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
    [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]
    (σ : Gal(AlgebraicClosure L/L)) (x : AlgebraicClosure K) :
    algebraMap (AlgebraicClosure K) (AlgebraicClosure L)
      (DFunLike.coe (F := Gal(AlgebraicClosure K/K)) (Field.absoluteGaloisGroup.mapOfAlgebra K L σ) x) =
      σ (algebraMap _ _ x) :=
  (σ.restrictScalarsHom K).restrictNormal_commutes (AlgebraicClosure K) x

/-- `standardEmbedding` intertwines Mathlib's `Field.absoluteGaloisGroup.map`. -/
theorem standardEmbedding_map {L : Type*} [Field L] [Algebra K L]
    (σ : Gal(AlgebraicClosure L/L)) (x : AlgebraicClosure K) :
    standardEmbedding (DFunLike.coe (F := Gal(AlgebraicClosure K/K))
      (Field.absoluteGaloisGroup.map (algebraMap K L) σ) x) = σ (standardEmbedding x) :=
  @algebraMap_mapOfAlgebra K L _ _ (algebraMap K L).toAlgebra
    (standardEmbeddingRingHom K L (algebraMap K L).toAlgebra).toAlgebra
    (@IsScalarTower.of_algebraMap_eq K (AlgebraicClosure K) (AlgebraicClosure L) _ _ _ _
      (standardEmbeddingRingHom K L (algebraMap K L).toAlgebra).toAlgebra
      (@AlgebraicClosure.instAlgebra L _ K _ (algebraMap K L).toAlgebra)
      (fun x => (standardEmbeddingRingHom_algebraMap K L (algebraMap K L).toAlgebra x).symm)) σ x

/-- For a field `L` over `K`, the decomposition homomorphism of `standardEmbedding` is Mathlib's
`Field.absoluteGaloisGroup.map (algebraMap K L)`. -/
theorem decompositionHom_standardEmbedding {L : Type*} [Field L] [Algebra K L]
    (σ : Gal(AlgebraicClosure L/L)) :
    decompositionHom L (standardEmbedding (K := K) (L := L)) σ =
      Field.absoluteGaloisGroup.map (algebraMap K L) σ :=
  (decompositionHom_eq_iff _ _ _).2 fun x => standardEmbedding_map σ x

end StandardEmbedding

section PlaceEmbeddings

variable (K : Type*) [Field K] [NumberField K] (Ω : Type*) [Field Ω] [Algebra K Ω]

/-- A choice, for every place of `K`, of an embedding of `Ω` over `K` into the algebraic closure of
the completion at that place. -/
structure PlaceEmbeddings where
  /-- The embedding at a finite place. -/
  finite : ∀ v : HeightOneSpectrum (𝓞 K), Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K)
  /-- The embedding at an infinite place. -/
  infinite : ∀ w : InfinitePlace K, Ω →ₐ[K] AlgebraicClosure w.Completion

/-- Embeddings at all places exist when `Ω` is a separable closure of `K`. -/
instance [IsSepClosure K Ω] : Nonempty (PlaceEmbeddings K Ω) :=
  ⟨⟨fun _ => IsSepClosed.lift, fun _ => IsSepClosed.lift⟩⟩

variable {K}

variable (K) in
/-- Mathlib's choice of embeddings of `AlgebraicClosure K` at the places of `K`: the ones that
`Field.absoluteGaloisGroup.map (algebraMap K Kv)` uses. -/
noncomputable def PlaceEmbeddings.standard : PlaceEmbeddings K (AlgebraicClosure K) where
  finite _ := standardEmbedding
  infinite _ := standardEmbedding

theorem PlaceEmbeddings.decompositionHom_standard_finite (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :
    decompositionHom (v.adicCompletion K) ((PlaceEmbeddings.standard K).finite v) σ =
      Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) σ :=
  decompositionHom_standardEmbedding σ

theorem PlaceEmbeddings.decompositionHom_standard_infinite (w : InfinitePlace K)
    (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) :
    decompositionHom w.Completion ((PlaceEmbeddings.standard K).infinite w) σ =
      Field.absoluteGaloisGroup.map (algebraMap K w.Completion) σ :=
  decompositionHom_standardEmbedding σ

end PlaceEmbeddings

end Langlands.Galois
