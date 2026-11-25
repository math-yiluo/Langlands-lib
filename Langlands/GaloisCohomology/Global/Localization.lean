import Langlands.Galois.RestrictedRamification.Localization
import Langlands.Cohomology.Profinite.InnerConjugation
import Langlands.Cohomology.Profinite.Comparison.Continuous
import Langlands.GaloisCohomology.CompactSupport.NineTerm
import Mathlib.RepresentationTheory.Homological.ContCohomology.Sha

/-!
# Localization maps in Galois cohomology and the groups `Шⁿ_S`

For a homomorphism `φ : H →ₜ* G` of topological groups and a smooth `G`-module `A`, restriction
along `φ` is `map φ (𝟙 _) n : Hⁿ(G, A) → Hⁿ(H, A)`. If `φ` is replaced by its conjugate by an
element `g ∈ G`, the restriction changes by the isomorphism `a ↦ g⁻¹ • a` of the restricted modules
(`map_conj`); in particular the kernel does not change.

For a number field `K`, a Galois extension `Ω / K` and embeddings `ι : PlaceEmbeddings K Ω`, the
localization at a finite place `v` (resp. an infinite place `w`) of a smooth module of a Galois
group `Gal(E / K)`, `E ⊆ Ω` normal over `K`, is restriction along the decomposition homomorphism
`Gal(K̄_v / K_v) → Gal(E / K)` of `ι` (`localCohomologyMap`). For `E = K_S` this is restriction
along `localizationHom ι S v` (`localization`, `realLocalization`), and `Шⁿ_S(M)` is the group of
classes that vanish at every place of `S` and at every real place (`sha`). It does not depend on
the embeddings (`sha_eq`). For `E = Ω = AlgebraicClosure K` and Mathlib's embeddings, the classes
vanishing at all finite and all real places correspond, under the comparison of the foundations
with Mathlib's continuous cohomology, to Mathlib's `ContinuousCohomology.tateShafarevich`
(`absoluteSha_standard_eq_tateShafarevich`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Conjugation

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- For homomorphisms `φ' = g⁻¹ φ g`, the isomorphism `a ↦ g⁻¹ • a` from `A` restricted along `φ`
to `A` restricted along `φ'`. -/
def conjResHom (A : Rep.{u} k G) {φ φ' : H →* G} (g : G) (h : ∀ x, φ' x = g⁻¹ * φ x * g) :
    Rep.res φ A ⟶ Rep.res φ' A :=
  Rep.ofHom ⟨A.ρ g⁻¹, fun x => by
    ext a
    change A.ρ g⁻¹ (A.ρ (φ x) a) = A.ρ (φ' x) (A.ρ g⁻¹ a)
    rw [h, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩

/-- `conjResHom` is `a ↦ g⁻¹ • a`. -/
theorem conjResHom_hom_apply (A : Rep.{u} k G) {φ φ' : H →* G} (g : G)
    (h : ∀ x, φ' x = g⁻¹ * φ x * g) (a : A) : (conjResHom A g h).hom a = A.ρ g⁻¹ a :=
  rfl

/-- `conjResHom` for `g` followed by `conjResHom` for `g⁻¹` is the identity. -/
theorem conjResHom_comp_conjResHom (A : Rep.{u} k G) {φ φ' : H →* G} (g : G)
    (h : ∀ x, φ' x = g⁻¹ * φ x * g) (h' : ∀ x, φ x = g⁻¹⁻¹ * φ' x * g⁻¹) :
    conjResHom A g h ≫ conjResHom A g⁻¹ h' = 𝟙 _ := by
  ext a
  change A.ρ g⁻¹⁻¹ (A.ρ g⁻¹ a) = a
  rw [← Module.End.mul_apply, ← map_mul, inv_inv, mul_inv_cancel, map_one, Module.End.one_apply]

variable [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G]

omit [CompactSpace G] in
/-- A map along `φ` followed by a map of coefficients is the map along `φ` of the composite. -/
theorem map_comp_coeffMap (A : Rep.{u} k G) [IsSmoothRep A] {B C : Rep.{u} k H} [IsSmoothRep B]
    [IsSmoothRep C] (φ : H →ₜ* G) (f : Rep.res (φ : H →* G) A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    map φ f n ≫ coeffMap g n = map φ (f ≫ g) n := by
  rw [coeffMap_eq]
  unfold map
  exact (HomologicalComplex.homologyMap_comp (cochainsMap φ f) (cochainsMap (.id H) g) n).symm

/-- Restriction along a conjugate homomorphism: `res_{g⁻¹ φ g} = (a ↦ g⁻¹ • a)_* ∘ res_φ`. -/
theorem map_conj (A : Rep.{u} k G) [IsSmoothRep A] (φ φ' : H →ₜ* G) (g : G)
    (h : ∀ x, φ' x = g⁻¹ * φ x * g) (n : ℕ) :
    map φ' (𝟙 (Rep.res (φ' : H →* G) A)) n =
      map φ (𝟙 (Rep.res (φ : H →* G) A)) n ≫
        coeffMap (conjResHom (φ := (φ : H →* G)) (φ' := (φ' : H →* G)) A g h) n := by
  have hφ'c : φ' = (⟨innerConjHom g, continuous_innerConjHom g⟩ : G →ₜ* G).comp φ :=
    ContinuousMonoidHom.ext fun x => h x
  subst hφ'c
  have e1 : (𝟙 (Rep.res (((⟨innerConjHom g, continuous_innerConjHom g⟩ : G →ₜ* G).comp φ :
      H →ₜ* G) : H →* G) A)) =
      (Rep.resFunctor (φ : H →* G)).map (innerConjMor A g) ≫
        conjResHom (φ := (φ : H →* G))
          (φ' := (((⟨innerConjHom g, continuous_innerConjHom g⟩ : G →ₜ* G).comp φ : H →ₜ* G) :
            H →* G)) A g h := by
    ext a
    change a = A.ρ g⁻¹ (A.ρ g a)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [e1]
  refine (map_comp (⟨innerConjHom g, continuous_innerConjHom g⟩ : G →ₜ* G) (innerConjMor A g) φ
    _ n).trans ?_
  rw [show map ⟨innerConjHom g, continuous_innerConjHom g⟩ (innerConjMor A g) n = 𝟙 _ from
    cohomologyInnerConj_eq_id n A g, Category.id_comp, map_comp_coeffMap, Category.id_comp]

/-- Restriction along a conjugate homomorphism has the same kernel. -/
theorem map_conj_apply_eq_zero_iff (A : Rep.{u} k G) [IsSmoothRep A] (φ φ' : H →ₜ* G) (g : G)
    (h : ∀ x, φ' x = g⁻¹ * φ x * g) (n : ℕ) (x : cohomology A n) :
    (map φ' (𝟙 (Rep.res (φ' : H →* G) A)) n).hom x = 0 ↔
      (map φ (𝟙 (Rep.res (φ : H →* G) A)) n).hom x = 0 := by
  have h' : ∀ x, φ x = g⁻¹⁻¹ * φ' x * g⁻¹ := fun x => by rw [h x]; group
  rw [map_conj A φ φ' g h n, ModuleCat.comp_apply]
  constructor
  · intro hx
    have := congrArg
      (coeffMap (conjResHom (φ := (φ' : H →* G)) (φ' := (φ : H →* G)) A g⁻¹ h') n).hom hx
    rwa [map_zero, ← ModuleCat.comp_apply, ← coeffMap_comp, conjResHom_comp_conjResHom,
      coeffMap_id] at this
  · intro hx
    rw [hx, map_zero]

end Conjugation

section Decomposition

variable {k K E Kv Ωv : Type u} [CommRing k] [Field K] [Field E] [Field Kv] [Field Ωv]
  [Algebra K E] [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv] [IsScalarTower K Kv Ωv]
  [IsGalois K E]

variable (Kv) in
/-- Restriction of the cohomology of a smooth `Gal(E / K)`-module to `Gal(Ωv / Kv)` along the
decomposition homomorphism of an embedding `ι : E →ₐ[K] Ωv`. -/
def localCohomologyMap (ι : E →ₐ[K] Ωv) (A : Rep.{u} k Gal(E/K)) [IsSmoothRep A] (n : ℕ) :
    cohomology A n ⟶ cohomology (Rep.res (decompositionHom Kv ι : Gal(Ωv/Kv) →* Gal(E/K)) A) n :=
  map (decompositionHom Kv ι) (𝟙 (Rep.res (decompositionHom Kv ι : Gal(Ωv/Kv) →* Gal(E/K)) A)) n

/-- Changing the embedding by an automorphism `g` of `E` changes the local map by the
isomorphism `a ↦ g⁻¹ • a`. -/
theorem localCohomologyMap_comp (ι : E →ₐ[K] Ωv) (g : Gal(E/K)) (A : Rep.{u} k Gal(E/K))
    [IsSmoothRep A] (n : ℕ) :
    localCohomologyMap Kv (ι.comp (g : E →ₐ[K] E)) A n =
      localCohomologyMap Kv ι A n ≫ coeffMap (conjResHom (φ := (decompositionHom Kv ι : Gal(Ωv/Kv) →* Gal(E/K)))
        (φ' := (decompositionHom Kv (ι.comp (g : E →ₐ[K] E)) : Gal(Ωv/Kv) →* Gal(E/K))) A g
        (decompositionHom_comp ι g)) n :=
  map_conj A _ _ g (decompositionHom_comp ι g) n

/-- The kernel of the local map does not depend on the embedding. -/
theorem localCohomologyMap_apply_eq_zero_iff (ι ι' : E →ₐ[K] Ωv) (A : Rep.{u} k Gal(E/K))
    [IsSmoothRep A] (n : ℕ) (x : cohomology A n) :
    (localCohomologyMap Kv ι' A n).hom x = 0 ↔ (localCohomologyMap Kv ι A n).hom x = 0 := by
  obtain ⟨g, rfl⟩ := exists_eq_comp_of_normal ι ι'
  exact map_conj_apply_eq_zero_iff A _ _ g (decompositionHom_comp ι g) n x

end Decomposition

section Localization

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (ι : PlaceEmbeddings K Ω) {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type u} [CommRing k]
  (M : Rep.{u} k (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]

/-- `M` as a module of the local Galois group at a finite place `v`. -/
abbrev localModule (v : HeightOneSpectrum (𝓞 K)) :
    Rep.{u} k Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) :=
  Rep.res (localizationHom ι S v : _ →* GaloisGroupUnramifiedOutside K Ω S) M

/-- `M` as a module of the local Galois group at an infinite place `w`. -/
abbrev realLocalModule (w : InfinitePlace K) :
    Rep.{u} k Gal(AlgebraicClosure w.Completion/w.Completion) :=
  Rep.res (realLocalizationHom ι S w : _ →* GaloisGroupUnramifiedOutside K Ω S) M

/-- Localization `Hⁿ(G_S, M) → Hⁿ(K_v, M)` at a finite place `v`. -/
def localization (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    cohomology M n →+ cohomology (localModule ι M v) n :=
  (map (localizationHom ι S v) (𝟙 (localModule ι M v)) n).hom.toAddMonoidHom

/-- Localization `Hⁿ(G_S, M) → Hⁿ(K_w, M)` at an infinite place `w`. -/
def realLocalization (w : InfinitePlace K) (n : ℕ) :
    cohomology M n →+ cohomology (realLocalModule ι M w) n :=
  (map (realLocalizationHom ι S w) (𝟙 (realLocalModule ι M w)) n).hom.toAddMonoidHom

/-- `localization` is the map along `localizationHom`. -/
theorem localization_apply (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (x : cohomology M n) :
    localization ι M v n x = (map (localizationHom ι S v) (𝟙 (localModule ι M v)) n).hom x :=
  rfl

/-- `realLocalization` is the map along `realLocalizationHom`. -/
theorem realLocalization_apply (w : InfinitePlace K) (n : ℕ) (x : cohomology M n) :
    realLocalization ι M w n x = (map (realLocalizationHom ι S w) (𝟙 (realLocalModule ι M w)) n).hom x :=
  rfl

/-- The kernel of the localization at a finite place does not depend on the embeddings. -/
theorem localization_eq_zero_iff (ι' : PlaceEmbeddings K Ω) (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (x : cohomology M n) :
    localization ι' M v n x = 0 ↔ localization ι M v n x = 0 := by
  obtain ⟨g, hg⟩ := exists_localizationHom_eq_conj S ι ι' v
  exact map_conj_apply_eq_zero_iff M _ _ g hg n x

/-- The kernel of the localization at an infinite place does not depend on the embeddings. -/
theorem realLocalization_eq_zero_iff (ι' : PlaceEmbeddings K Ω) (w : InfinitePlace K)
    {n : ℕ} (x : cohomology M n) :
    realLocalization ι' M w n x = 0 ↔ realLocalization ι M w n x = 0 := by
  obtain ⟨g, hg⟩ := exists_realLocalizationHom_eq_conj S ι ι' w
  exact map_conj_apply_eq_zero_iff M _ _ g hg n x

/-- `Шⁿ_S(M)`: the classes of `Hⁿ(G_S, M)` that vanish at every place of `S` and at every real
place. -/
def sha (n : ℕ) : AddSubgroup (cohomology M n) :=
  (⨅ v : S, (localization ι M v n).ker) ⊓
    ⨅ w : {w : InfinitePlace K // w.IsReal}, (realLocalization ι M w n).ker

/-- A class lies in `Шⁿ_S(M)` exactly when it vanishes at the places of `S` and at the real places. -/
theorem mem_sha {n : ℕ} {x : cohomology M n} :
    x ∈ sha ι M n ↔ (∀ v ∈ S, localization ι M v n x = 0) ∧
      ∀ w : InfinitePlace K, w.IsReal → realLocalization ι M w n x = 0 := by
  rw [sha, AddSubgroup.mem_inf, AddSubgroup.mem_iInf, AddSubgroup.mem_iInf]
  exact ⟨fun h => ⟨fun v hv => h.1 ⟨v, hv⟩, fun w hw => h.2 ⟨w, hw⟩⟩,
    fun h => ⟨fun v => h.1 v.1 v.2, fun w => h.2 w.1 w.2⟩⟩

/-- `Шⁿ_S(M)` does not depend on the choice of embeddings. -/
theorem sha_eq (ι' : PlaceEmbeddings K Ω) (n : ℕ) : sha ι M n = sha ι' M n := by
  ext x
  simp only [mem_sha, localization_eq_zero_iff ι M ι', realLocalization_eq_zero_iff ι M ι']

end Localization

section Abstract

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (ι : PlaceEmbeddings K Ω) {S : Set (HeightOneSpectrum (𝓞 K))}
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]

/-- On the places of `S`, localization is the abstract restriction `ptRes` of the family
`(localizationHom ι S v)_{v ∈ S}`. -/
theorem localization_eq_ptRes (v : S) (n : ℕ) :
    localization ι M v n = ptRes (fun v : S => localizationHom ι S v) M v n :=
  rfl

/-- `Шⁿ_S(M)` lies in the kernel `ptSha` of the abstract localization to the places of `S`. -/
theorem sha_le_ptSha (n : ℕ) : sha ι M n ≤ ptSha (fun v : S => localizationHom ι S v) M n := by
  intro x hx
  rw [mem_ptSha]
  funext v
  exact ((mem_sha ι M).1 hx).1 v.1 v.2

end Abstract

section Absolute

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (ι : PlaceEmbeddings K Ω) {k : Type u} [CommRing k] (A : Rep.{u} k Gal(Ω/K)) [IsSmoothRep A]

/-- The classes of `Hⁿ(Gal(Ω / K), A)` that vanish at every finite place and every real place
(`Шⁿ` of the absolute Galois group when `Ω` is a separable closure). -/
def absoluteSha (n : ℕ) : AddSubgroup (cohomology A n) :=
  (⨅ v : HeightOneSpectrum (𝓞 K),
      (localCohomologyMap (v.adicCompletion K) (ι.finite v) A n).hom.toAddMonoidHom.ker) ⊓
    ⨅ w : {w : InfinitePlace K // w.IsReal},
      (localCohomologyMap w.1.Completion (ι.infinite w.1) A n).hom.toAddMonoidHom.ker

/-- Membership in `absoluteSha`. -/
theorem mem_absoluteSha {n : ℕ} {x : cohomology A n} :
    x ∈ absoluteSha ι A n ↔
      (∀ v, (localCohomologyMap (v.adicCompletion K) (ι.finite v) A n).hom x = 0) ∧
        ∀ w : InfinitePlace K, w.IsReal →
          (localCohomologyMap w.Completion (ι.infinite w) A n).hom x = 0 := by
  rw [absoluteSha, AddSubgroup.mem_inf, AddSubgroup.mem_iInf, AddSubgroup.mem_iInf]
  exact ⟨fun h => ⟨fun v => h.1 v, fun w hw => h.2 ⟨w, hw⟩⟩,
    fun h => ⟨fun v => h.1 v, fun w => h.2 w.1 w.2⟩⟩

/-- It does not depend on the choice of embeddings. -/
theorem absoluteSha_eq (ι' : PlaceEmbeddings K Ω) (n : ℕ) : absoluteSha ι A n = absoluteSha ι' A n := by
  ext x
  simp only [mem_absoluteSha, localCohomologyMap_apply_eq_zero_iff (ι.finite _) (ι'.finite _),
    localCohomologyMap_apply_eq_zero_iff (ι.infinite _) (ι'.infinite _)]

end Absolute

section Mathlib

/-! ### Comparison with Mathlib's `ContinuousCohomology.tateShafarevich` -/

/-- The absolute Galois group of a field of characteristic zero is compact. -/
instance compactSpace_absoluteGaloisGroup (L : Type) [Field L] [CharZero L] :
    CompactSpace (Field.absoluteGaloisGroup L) :=
  inferInstanceAs (CompactSpace (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L))

section General

variable {K : Type} [Field K] [CharZero K] {V : Type} (f : V → Type) [∀ v, Field (f v)]
  [∀ v, Algebra K (f v)] [∀ v, CharZero (f v)]
  (X : TopRep.{0} ℤ (Field.absoluteGaloisGroup K)) [hd : DiscreteTopology X]
  [hs : IsSmoothRep (underlyingRep X)]

/-- Restriction along Mathlib's map of absolute Galois groups preserves smoothness. -/
instance isSmoothRep_res_absoluteGaloisGroupMap (v : V) :
    IsSmoothRep (Rep.res (Field.absoluteGaloisGroup.map (algebraMap K (f v)) :
      Field.absoluteGaloisGroup (f v) →* Field.absoluteGaloisGroup K) (underlyingRep X)) :=
  IsSmoothRep.res (Field.absoluteGaloisGroup.map (algebraMap K (f v))).continuous _

/-- The same for the underlying representation of a restricted topological representation. -/
instance isSmoothRep_underlyingRep_res_absoluteGaloisGroupMap (v : V) :
    IsSmoothRep (underlyingRep (TopRep.res (Field.absoluteGaloisGroup.map (algebraMap K (f v)) :
      Field.absoluteGaloisGroup (f v) →* Field.absoluteGaloisGroup K) X)) :=
  IsSmoothRep.res (Field.absoluteGaloisGroup.map (algebraMap K (f v))).continuous (underlyingRep X)

/-- Under the comparison `linearEquivContinuousCohomology` of the foundations with Mathlib's
continuous cohomology, Mathlib's Tate–Shafarevich group of a discrete module consists of the
classes killed by the restrictions along Mathlib's maps of absolute Galois groups. -/
theorem linearEquivContinuousCohomology_mem_tateShafarevich_iff (n : ℕ)
    (x : cohomology (underlyingRep X) n) :
    linearEquivContinuousCohomology X n x ∈ ContinuousCohomology.tateShafarevich f X n ↔
      ∀ v, (map (Field.absoluteGaloisGroup.map (algebraMap K (f v)))
        (𝟙 (Rep.res (Field.absoluteGaloisGroup.map (algebraMap K (f v)) :
          Field.absoluteGaloisGroup (f v) →* Field.absoluteGaloisGroup K) (underlyingRep X))) n).hom
            x = 0 := by
  rw [ContinuousCohomology.mem_tateShafarevich]
  refine forall_congr' fun v => ?_
  have := isoContinuousCohomology_naturality (X := X)
    (Y := TopRep.res (Field.absoluteGaloisGroup.map (algebraMap K (f v)) :
      Field.absoluteGaloisGroup (f v) →* Field.absoluteGaloisGroup K) X)
    (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n
  have h2 := congrArg (fun φ => φ.hom x) this
  simp only [ModuleCat.comp_apply] at h2
  have key : (ContinuousCohomology.map (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom
      (linearEquivContinuousCohomology X n x) =
      (isoContinuousCohomology _ n).hom ((map (Field.absoluteGaloisGroup.map (algebraMap K (f v)))
        (𝟙 (Rep.res (Field.absoluteGaloisGroup.map (algebraMap K (f v)) :
          Field.absoluteGaloisGroup (f v) →* Field.absoluteGaloisGroup K) (underlyingRep X))) n).hom x) :=
    h2.symm
  rw [key]
  constructor
  · intro h
    have h3 := congrArg (isoContinuousCohomology _ n).inv.hom h
    rwa [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply, map_zero] at h3
  · intro h
    rw [h, map_zero]

end General

section NumberField

variable {K : Type} [Field K] [NumberField K]

/-- The places used for the comparison with Mathlib: the finite places and the real places. -/
abbrev ShaPlace (K : Type) [Field K] [NumberField K] : Type :=
  HeightOneSpectrum (𝓞 K) ⊕ {w : InfinitePlace K // w.IsReal}

/-- The completion of `K` at a place of `ShaPlace K`. -/
abbrev shaCompletion : ShaPlace K → Type
  | .inl v => v.adicCompletion K
  | .inr w => w.1.Completion

/-- The completions are fields. -/
instance (p : ShaPlace K) : Field (shaCompletion p) := by
  rcases p with v | w <;> exact inferInstanceAs (Field _)

/-- The completions are `K`-algebras. -/
instance (p : ShaPlace K) : Algebra K (shaCompletion p) := by
  rcases p with v | w <;> exact inferInstanceAs (Algebra K _)

/-- The completions have characteristic zero. -/
instance (p : ShaPlace K) : CharZero (shaCompletion p) := by
  rcases p with v | w
  · exact charZero_adicCompletion v
  · exact charZero_of_injective_algebraMap (algebraMap K w.1.Completion).injective

/-- Restrictions along equal homomorphisms have the same kernel. -/
theorem map_apply_eq_zero_iff_of_eq {k G H : Type} [CommRing k] [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (A : Rep.{0} k G) [IsSmoothRep A] {φ ψ : H →ₜ* G} (h : φ = ψ) (n : ℕ) (x : cohomology A n) :
    (map φ (𝟙 (Rep.res (φ : H →* G) A)) n).hom x = 0 ↔
      (map ψ (𝟙 (Rep.res (ψ : H →* G) A)) n).hom x = 0 := by
  subst h; rfl

/-- For `Ω = AlgebraicClosure K` and Mathlib's embeddings, the classes of `Hⁿ(G_K, A)` vanishing
at all finite and all real places are, under the comparison of the foundations with Mathlib's
continuous cohomology (`A` with the discrete topology), Mathlib's Tate–Shafarevich group for the
completions at those places. -/
theorem mem_absoluteSha_standard_iff (A : Rep.{0} ℤ Gal(AlgebraicClosure K/K)) [IsSmoothRep A]
    (n : ℕ) (x : cohomology A n) :
    x ∈ absoluteSha (PlaceEmbeddings.standard K) A n ↔
      linearEquivContinuousCohomologyDiscrete A n x ∈
        ContinuousCohomology.tateShafarevich (shaCompletion (K := K)) (discreteTopRep A) n := by
  rw [mem_absoluteSha]
  refine Iff.trans ?_ (linearEquivContinuousCohomology_mem_tateShafarevich_iff (shaCompletion (K := K)) (discreteTopRep A)
    (hd := ⟨rfl⟩) (hs := ‹IsSmoothRep A›) n x).symm
  have hf : ∀ v : HeightOneSpectrum (𝓞 K),
      decompositionHom (v.adicCompletion K) ((PlaceEmbeddings.standard K).finite v) =
        Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) := fun v =>
    ContinuousMonoidHom.ext (PlaceEmbeddings.decompositionHom_standard_finite v)
  have hi : ∀ w : InfinitePlace K,
      decompositionHom w.Completion ((PlaceEmbeddings.standard K).infinite w) =
        Field.absoluteGaloisGroup.map (algebraMap K w.Completion) := fun w =>
    ContinuousMonoidHom.ext (PlaceEmbeddings.decompositionHom_standard_infinite w)
  constructor
  · rintro ⟨h1, h2⟩ (v | w)
    · exact (map_apply_eq_zero_iff_of_eq A (hf v) n x).1 (h1 v)
    · exact (map_apply_eq_zero_iff_of_eq A (hi w.1) n x).1 (h2 w.1 w.2)
  · intro h
    exact ⟨fun v => (map_apply_eq_zero_iff_of_eq A (hf v) n x).2 (h (.inl v)),
      fun w hw => (map_apply_eq_zero_iff_of_eq A (hi w) n x).2 (h (.inr ⟨w, hw⟩))⟩

end NumberField

end Mathlib


end

end Langlands.GaloisCohomology

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Sha

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

/-- The classes of `Hⁿ(G, A)` whose restrictions to every `H_v` vanish. -/
def shaSubmodule (A : Rep.{u} k G) [IsSmoothRep A] (n : ℕ) : Submodule k (cohomology A n) where
  carrier := {x | ∀ v, (map (φ v) (𝟙 (Rep.res (φ v : Hv v →* G) A)) n).hom x = 0}
  add_mem' {x y} hx hy v := by
    change (map (φ v) (𝟙 (Rep.res (φ v : Hv v →* G) A)) n).hom (x + y) = 0
    rw [map_add, hx v, hy v, add_zero]
  zero_mem' v := map_zero _
  smul_mem' c x hx v := by
    change (map (φ v) (𝟙 (Rep.res (φ v : Hv v →* G) A)) n).hom (c • x) = 0
    rw [map_smul, hx v, smul_zero]

theorem mem_shaSubmodule_iff (A : Rep.{u} k G) [IsSmoothRep A] {n : ℕ} (x : cohomology A n) :
    x ∈ shaSubmodule φ A n ↔ ∀ v, (map (φ v) (𝟙 (Rep.res (φ v : Hv v →* G) A)) n).hom x = 0 :=
  Iff.rfl

end Sha

end

end Langlands.GaloisCohomology
