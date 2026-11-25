# The real places of a finite extension inside `K_S` and the Mackey double cosets

`Langlands/GaloisCohomology/Global/RealPlaces/VanishingPlaces.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω / K` Galois, `S` a set of finite places of `K`, `G_S = Gal(K_S/K)`,
`ι : PlaceEmbeddings K Ω`, `L` a number field with `K → L → Ω` inside `K_S` and `W ⊆ G_S` the open subgroup
fixing it (`fixingOpenSubgroup S hL`). For an infinite place `w` of `K` let `D_w = Gal(K̄_w/K_w)` with its
localization `realLocalizationHom ι S w : D_w → G_S`.

**Embeddings and places.** For `x ∈ G_S`, `realLocalEmbedding hL ι w x : L → K̄_w` is `ι_w ∘ x⁻¹` on `L`;
its complex embedding `realComplexEmbeddingOf` (through `closureToComplex`) defines the infinite place
`realPlaceOf hL ι w x` of `L`, which lies over `w` (`comap_realPlaceOf`). The Mackey subgroup
`D_w ∩ x⁻¹ W x` is the subgroup of `D_w` fixing `realLocalEmbedding hL ι w x`
(`mem_mackeySubgroup_real_iff`); at a real place it is all of `D_w` exactly when the place is real
(`isReal_realPlaceOf_iff`).

**The correspondence** (`realMackeyPlaceEquiv`). The pairs of a real place `w` of `K` and a double coset
`W x D_w` whose Mackey subgroup is `D_w` (`RealMackeyTop`) correspond bijectively to the real places of `L`,
by the place of the representative (`realMackeyPlace`).

**Compatibility.** `orderTwoMulEquiv`: two groups `{1, a}`, `{1, b}` of order two are isomorphic;
`realClosureGaloisEquiv`: `D_w ≅ D_{w'}` for real places of two number fields, conjugation to
conjugation. For a real place `w'` of `L` whose embedding is the complex embedding attached to `(w, x)`,
`realEmbeddingOverOf` is the embedding `Ω → L̄_{w'}` over `L` given by `ι_w ∘ x⁻¹` read through
`K̄_w ≅ ℂ ≅ L̄_{w'}`, and under `W ≅ G_{S_L}(L)` conjugation by `x` on the Mackey subgroup is its
decomposition homomorphism (`fixingOpenSubgroupEquiv_mackeyConj_real`). With the embeddings
`realPlaceEmbeddingsOver hL ι ι₀` of `Ω` at the places of `L` (those of the correspondence at the real
places, those of `ι₀` elsewhere), conjugation by the representative of a top double coset is the
localization of `G_{S_L}(L)` at the attached real place
(`fixingOpenSubgroupEquiv_mackeyConj_eq_realLocalizationHom`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.realLocalEmbedding.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) : L →ₐ[K] AlgebraicClosure w.Completion
Langlands.GaloisCohomology.realLocalEmbedding_apply.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) (l : L) :
  (Langlands.GaloisCohomology.realLocalEmbedding hL ι w x) l =
    (ι.infinite w) ↑(x⁻¹ ((Langlands.Galois.embeddingMaximalUnramifiedOutside hL) l))
Langlands.GaloisCohomology.mem_mackeySubgroup_real_iff.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) :
  σ ∈
      Langlands.ProfiniteCohomology.mackeySubgroup
        (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
        (Langlands.Galois.realLocalizationHom ι S w).toMonoidHom x ↔
    ∀ (l : L),
      σ ((Langlands.GaloisCohomology.realLocalEmbedding hL ι w x) l) =
        (Langlands.GaloisCohomology.realLocalEmbedding hL ι w x) l
Langlands.GaloisCohomology.realLocalEmbedding_mul.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) {u : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S}
  (hu : u ∈ Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
  (h : Gal(AlgebraicClosure w.Completion/w.Completion)) (l : L) :
  (Langlands.GaloisCohomology.realLocalEmbedding hL ι w (u * x * (Langlands.Galois.realLocalizationHom ι S w) h)) l =
    h⁻¹ ((Langlands.GaloisCohomology.realLocalEmbedding hL ι w x) l)
Langlands.GaloisCohomology.exists_realLocalEmbedding_eq.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (j : L →ₐ[K] AlgebraicClosure w.Completion) : ∃ x, Langlands.GaloisCohomology.realLocalEmbedding hL ι w x = j
Langlands.GaloisCohomology.realComplexEmbeddingOf.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) : L →+* ℂ
Langlands.GaloisCohomology.realComplexEmbeddingOf_apply.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) (l : L) :
  (Langlands.GaloisCohomology.realComplexEmbeddingOf hL ι w x) l =
    (Langlands.GaloisCohomology.closureToComplex w) ((Langlands.GaloisCohomology.realLocalEmbedding hL ι w x) l)
Langlands.GaloisCohomology.realPlaceOf.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) : NumberField.InfinitePlace L
Langlands.GaloisCohomology.realComplexEmbeddingOf_comp_algebraMap.{u} {K L Ω : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) :
  (Langlands.GaloisCohomology.realComplexEmbeddingOf hL ι w x).comp (Algebra.algebraMap K L) = w.embedding
Langlands.GaloisCohomology.comap_realPlaceOf.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) :
  (Langlands.GaloisCohomology.realPlaceOf hL ι w x).comap (Algebra.algebraMap K L) = w
Langlands.GaloisCohomology.isReal_realPlaceOf_iff.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K) (hw : w.IsReal)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) :
  (Langlands.GaloisCohomology.realPlaceOf hL ι w x).IsReal ↔
    Langlands.ProfiniteCohomology.mackeySubgroup
        (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
        (Langlands.Galois.realLocalizationHom ι S w).toMonoidHom x =
      ⊤
Langlands.GaloisCohomology.RealMackeyTop.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) : Type u
Langlands.GaloisCohomology.realMackeyPlace.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (p : Langlands.GaloisCohomology.RealMackeyTop S hL ι) : { w' // w'.IsReal }
Langlands.GaloisCohomology.coe_realMackeyPlace.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (p : Langlands.GaloisCohomology.RealMackeyTop S hL ι) :
  ↑(Langlands.GaloisCohomology.realMackeyPlace hL ι p) =
    Langlands.GaloisCohomology.realPlaceOf hL ι (↑(↑p).fst) (Quotient.out (↑p).snd)
Langlands.GaloisCohomology.isReal_realComplexEmbeddingOf.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (p : Langlands.GaloisCohomology.RealMackeyTop S hL ι) :
  NumberField.ComplexEmbedding.IsReal
    (Langlands.GaloisCohomology.realComplexEmbeddingOf hL ι (↑(↑p).fst) (Quotient.out (↑p).snd))
Langlands.GaloisCohomology.realComplexEmbeddingOf_eq_embedding.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (p : Langlands.GaloisCohomology.RealMackeyTop S hL ι) :
  Langlands.GaloisCohomology.realComplexEmbeddingOf hL ι (↑(↑p).fst) (Quotient.out (↑p).snd) =
    (↑(Langlands.GaloisCohomology.realMackeyPlace hL ι p)).embedding
Langlands.GaloisCohomology.realMackeyPlace_injective.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) : Function.Injective (Langlands.GaloisCohomology.realMackeyPlace hL ι)
Langlands.GaloisCohomology.realMackeyPlace_surjective.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) : Function.Surjective (Langlands.GaloisCohomology.realMackeyPlace hL ι)
Langlands.GaloisCohomology.realMackeyPlaceEquiv.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) : Langlands.GaloisCohomology.RealMackeyTop S hL ι ≃ { w' // w'.IsReal }
Langlands.GaloisCohomology.realMackeyPlaceEquiv_apply.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (p : Langlands.GaloisCohomology.RealMackeyTop S hL ι) :
  (Langlands.GaloisCohomology.realMackeyPlaceEquiv hL ι) p = Langlands.GaloisCohomology.realMackeyPlace hL ι p
Langlands.GaloisCohomology.orderTwoMulEquiv.{u_1, u_2} {A : Type u_1} {B : Type u_2} [Group A] [Group B] (a : A) (b : B)
  (hA : ∀ (x : A), x = 1 ∨ x = a) (ha : a ≠ 1) (hB : ∀ (y : B), y = 1 ∨ y = b) (hb : b ≠ 1) : A ≃* B
Langlands.GaloisCohomology.orderTwoMulEquiv_apply_one.{u_1, u_2} {A : Type u_1} {B : Type u_2} [Group A] [Group B]
  (a : A) (b : B) (hA : ∀ (x : A), x = 1 ∨ x = a) (ha : a ≠ 1) (hB : ∀ (y : B), y = 1 ∨ y = b) (hb : b ≠ 1) :
  (Langlands.GaloisCohomology.orderTwoMulEquiv a b hA ha hB hb) 1 = 1
Langlands.GaloisCohomology.orderTwoMulEquiv_apply_gen.{u_1, u_2} {A : Type u_1} {B : Type u_2} [Group A] [Group B]
  (a : A) (b : B) (hA : ∀ (x : A), x = 1 ∨ x = a) (ha : a ≠ 1) (hB : ∀ (y : B), y = 1 ∨ y = b) (hb : b ≠ 1) :
  (Langlands.GaloisCohomology.orderTwoMulEquiv a b hA ha hB hb) a = b
Langlands.GaloisCohomology.realClosureGaloisEquiv.{u_1, u_2} {K : Type u_1} {K' : Type u_2} [Field K] [NumberField K]
  [Field K'] [NumberField K'] (w : NumberField.InfinitePlace K) (hw : w.IsReal) (w' : NumberField.InfinitePlace K')
  (hw' : w'.IsReal) :
  Gal(AlgebraicClosure w.Completion/w.Completion) ≃* Gal(AlgebraicClosure w'.Completion/w'.Completion)
Langlands.GaloisCohomology.closureToComplex_closureEquivComplex_symm.{u} {L : Type u} [Field L] [NumberField L]
  (w' : NumberField.InfinitePlace L) (z : ℂ) :
  (Langlands.GaloisCohomology.closureToComplex w') ((Langlands.GaloisCohomology.closureEquivComplex w').symm z) = z
Langlands.GaloisCohomology.realEmbeddingOverOf.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) (w' : NumberField.InfinitePlace L)
  (h : Langlands.GaloisCohomology.realComplexEmbeddingOf hL ι w x = w'.embedding) :
  Ω →ₐ[L] AlgebraicClosure w'.Completion
Langlands.GaloisCohomology.realEmbeddingOverOf_apply.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w : NumberField.InfinitePlace K)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) (w' : NumberField.InfinitePlace L)
  (h : Langlands.GaloisCohomology.realComplexEmbeddingOf hL ι w x = w'.embedding) (y : Ω) :
  (Langlands.GaloisCohomology.realEmbeddingOverOf hL ι w x w' h) y =
    (Langlands.GaloisCohomology.closureEquivComplex w').symm
      ((Langlands.GaloisCohomology.closureToComplex w) ((ι.infinite w) (x.lift⁻¹ y)))
Langlands.GaloisCohomology.fixingOpenSubgroupEquiv_mackeyConj_real.{u} {K L Ω : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) [IsGalois L Ω] (w : NumberField.InfinitePlace K) (hw : w.IsReal)
  (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) (w' : NumberField.InfinitePlace L) (hw' : w'.IsReal)
  (h : Langlands.GaloisCohomology.realComplexEmbeddingOf hL ι w x = w'.embedding)
  (σ :
    ↥(Langlands.ProfiniteCohomology.mackeySubgroup
        (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
        (Langlands.Galois.realLocalizationHom ι S w).toMonoidHom x)) :
  (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL)
      ((Langlands.ProfiniteCohomology.mackeyConj
          (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
          (Langlands.Galois.realLocalizationHom ι S w).toMonoidHom x)
        σ) =
    (Langlands.Galois.decompositionHom w'.Completion
        ((Langlands.GaloisCohomology.realEmbeddingOverOf hL ι w x w' h).comp
          (Langlands.Galois.maximalUnramifiedOutside L Ω (Langlands.Galois.finitePlacesAbove L S)).val))
      ((Langlands.GaloisCohomology.realClosureGaloisEquiv w hw w' hw') ↑σ)
Langlands.GaloisCohomology.realEmbeddingOver.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (p : Langlands.GaloisCohomology.RealMackeyTop S hL ι) :
  Ω →ₐ[L] AlgebraicClosure (↑(Langlands.GaloisCohomology.realMackeyPlace hL ι p)).Completion
Langlands.GaloisCohomology.realMackeyEmbedding.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (w' : { w' // w'.IsReal }) : Ω →ₐ[L] AlgebraicClosure (↑w').Completion
Langlands.GaloisCohomology.realMackeyEmbedding_realMackeyPlaceEquiv.{u} {K L Ω : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (p : Langlands.GaloisCohomology.RealMackeyTop S hL ι) :
  Langlands.GaloisCohomology.realMackeyEmbedding hL ι ((Langlands.GaloisCohomology.realMackeyPlaceEquiv hL ι) p) =
    Langlands.GaloisCohomology.realEmbeddingOver hL ι p
Langlands.GaloisCohomology.realPlaceEmbeddingsOver.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ι₀ : Langlands.Galois.PlaceEmbeddings L Ω) :
  Langlands.Galois.PlaceEmbeddings L Ω
Langlands.GaloisCohomology.realPlaceEmbeddingsOver_infinite.{u} {K L Ω : Type u} [Field K] [NumberField K] [Field L]
  [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (ι₀ : Langlands.Galois.PlaceEmbeddings L Ω) (w' : { w' // w'.IsReal }) :
  (Langlands.GaloisCohomology.realPlaceEmbeddingsOver hL ι ι₀).infinite ↑w' =
    Langlands.GaloisCohomology.realMackeyEmbedding hL ι w'
Langlands.GaloisCohomology.fixingOpenSubgroupEquiv_mackeyConj_eq_realLocalizationHom.{u} {K L Ω : Type u} [Field K]
  [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsGalois K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hL : ∀ (x : L), (Algebra.algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) [IsGalois L Ω] (ι₀ : Langlands.Galois.PlaceEmbeddings L Ω)
  (p : Langlands.GaloisCohomology.RealMackeyTop S hL ι)
  (σ :
    ↥(Langlands.ProfiniteCohomology.mackeySubgroup
        (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
        (Langlands.Galois.realLocalizationHom ι S ↑(↑p).fst).toMonoidHom (Quotient.out (↑p).snd))) :
  (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL)
      ((Langlands.ProfiniteCohomology.mackeyConj
          (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
          (Langlands.Galois.realLocalizationHom ι S ↑(↑p).fst).toMonoidHom (Quotient.out (↑p).snd))
        σ) =
    (Langlands.Galois.realLocalizationHom (Langlands.GaloisCohomology.realPlaceEmbeddingsOver hL ι ι₀)
        (Langlands.Galois.finitePlacesAbove L S) ↑(Langlands.GaloisCohomology.realMackeyPlace hL ι p))
      ((Langlands.GaloisCohomology.realClosureGaloisEquiv ↑(↑p).fst ⋯
          ↑(Langlands.GaloisCohomology.realMackeyPlace hL ι p) ⋯)
        ↑σ)
```

## Outline of the proofs

As for the finite places in `Langlands.Galois.RestrictedRamification.Localization` (`localEmbedding`,
`mackeyPlaceEquiv`), with infinite places described by complex embeddings: a place `mk φ` is real exactly
when `φ` is fixed by complex conjugation (`InfinitePlace.isReal_mk_iff`), and `closureConj` becomes
complex conjugation in `ℂ` (`closureToComplex_closureConj`). Injectivity: equal real places give equal
real embeddings (`InfinitePlace.mk_eq_iff`), hence `x' x⁻¹ ∈ W`. Surjectivity: the embedding of a real
place `w'` of `L`, read in `K̄_w` for `w` below it, is `realLocalEmbedding x` for some `x`
(`exists_realLocalEmbedding_eq`, through `exists_eq_comp_of_normal`); the representative of the double
coset changes it by an element of `D_w`, which fixes it. Compatibility: checked on the conjugation with
`decompositionHom_eq_iff`, both sides read in `ℂ`.

## Declarations

`realLocalEmbedding`, `realLocalEmbedding_apply`, `mem_mackeySubgroup_real_iff`, `realLocalEmbedding_mul`, `exists_realLocalEmbedding_eq`, `realComplexEmbeddingOf`, `realComplexEmbeddingOf_apply`, `realPlaceOf`, `realComplexEmbeddingOf_comp_algebraMap`, `comap_realPlaceOf`, `isReal_realPlaceOf_iff`, `RealMackeyTop`, `realMackeyPlace`, `coe_realMackeyPlace`, `isReal_realComplexEmbeddingOf`, `realComplexEmbeddingOf_eq_embedding`, `realMackeyPlace_injective`, `realMackeyPlace_surjective`, `realMackeyPlaceEquiv`, `realMackeyPlaceEquiv_apply`, `orderTwoMulEquiv`, `orderTwoMulEquiv_apply_one`, `orderTwoMulEquiv_apply_gen`, `realClosureGaloisEquiv`, `closureToComplex_closureEquivComplex_symm`, `realEmbeddingOverOf`, `realEmbeddingOverOf_apply`, `fixingOpenSubgroupEquiv_mackeyConj_real`, `realEmbeddingOver`, `realMackeyEmbedding`, `realMackeyEmbedding_realMackeyPlaceEquiv`, `realPlaceEmbeddingsOver`, `realPlaceEmbeddingsOver_infinite`, `fixingOpenSubgroupEquiv_mackeyConj_eq_realLocalizationHom`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingMackeyPlaces.lean` (lines 105–260: `gsRealEmbedding`, `mem_mackeySubgroup_real_iff`, `gsRealEmbedding_mul`, `realMemberPlace`, `realMemberPlace_injective`, `realMemberPlace_surjective`) and `src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingMackeyTransfer.lean` (lines 51–147: `exists_real_data`). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The places of `L` are the Mathlib infinite places of complex embeddings through `closureToComplex` instead of the source's `infPlaceOfEmbedding` and completions over `v.Completion`; the isomorphism `D_w ≅ D_{w'}` is the one of groups of order two (`orderTwoMulEquiv`) instead of the source's conjugation by an isomorphism of algebraic closures (`galConjEquiv`); the embeddings of `L` are collected in `realPlaceEmbeddingsOver`, as `placeEmbeddingsOver` does for the finite places.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §1, p. 427 (decomposition groups and the embeddings `i_𝔭`).
- J. Neukirch, *Algebraic Number Theory* (Springer 1999), chapter II, §8, Extension Theorem (8.1), pp. 161–162 (places of `L` above a place of `K` and embeddings up to conjugation).
