import Langlands.Cohomology.DivisibleSystem.AdjunctionHomSystem
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite direct sums of Hom complexes and of Hom-complex systems

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, p.311: the complexes used for the spectral sequences (4.9) have terms
`⊕_{i+j=k} Hom_{𝒪/ℓ^m𝒪[GJ]}(⊕_{(e,δ) ∈ O_{-i}} c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ),
Hom(𝒪_m[K_p/H_p]^M, 𝓛_m))`, "which can be rewritten" as (4.10.2)
`⊕_{i+j=k} ⊕_{(e,δ) ∈ O_{-i}} Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ), Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`.
The first argument is the direct sum (4.4.4) (p.310) of compactly induced modules. The
published module `AdjunctionHomSystem` treats the Frobenius reciprocity step of this
rewriting for a single compact induction; this module treats the splitting of Hom out of a
finite direct sum, for Hom complexes and for the inverse systems over `m` of Hom complexes
of `ℓ`-divisible systems.

* `LinearHomComplex.sourceBiproductIso`: for a finite family of cochain complexes `Kᵢ` with a
  biproduct, the isomorphism of Hom complexes `Hom^•(⨁ᵢ Kᵢ, L) ≅ ⨁ᵢ Hom^•(Kᵢ, L)`;
* `exact_biproductShortComplex`, `shortExact_biproductShortComplex`: finite biproducts of
  (short) exact short complexes in an abelian category are (short) exact;
* `biproductSystem`, `limitBiproductSystemIso`: the levelwise biproduct of a finite family of
  functors, and the isomorphism `lim_j ⨁ᵢ Fᵢ j ≅ ⨁ᵢ lim_j Fᵢ j`;
* `DivisibleSystem.biproduct`: the direct sum of a finite family of `ℓ`-divisible systems,
  with its inclusions and projections;
* `DivisibleSystem.homComplexSystemBiproductIso` and
  `DivisibleSystem.homComplexLimitBiproductIso`: the inverse system of Hom complexes out of a
  finite direct sum of `ℓ`-divisible systems of cochain complexes is the levelwise biproduct
  of the inverse systems of Hom complexes, and similarly for the inverse limits;
* `smoothHomComplexSystemBiproductReciprocityIso` and
  `smoothHomComplexLimitBiproductReciprocityIso`: combined with the published
  `smoothHomComplexSystemReciprocityIso`, for open subgroups `Hᵢ` of `G`,
  `Hom^•_G(⨁ᵢ c-Ind_{Hᵢ}^G Tᵢ m, W m) ≅ ⨁ᵢ Hom^•_{Hᵢ}(Tᵢ m, W m|_{Hᵢ})` as inverse systems
  over `m`, and on the inverse limits.

This is the shape of Harris's rewriting for a single degree `-i`, with the index set
`O_{-i}` and `Hᵢ = S(ẽ)`. The index type is assumed finite, which Harris's text does not state
on these pages; the identification of Harris's complexes with Hom complexes of this kind is
not formalized here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

universe w v u u'

attribute [local instance] Abelian.hasFiniteBiproducts

namespace LinearHomComplex

section Additive

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {P P' Q Q' : CochainComplex C ℤ}

/-- The chain map `map R f g` is additive in the chain map `f` of first complexes. -/
lemma map_add_left (f₁ f₂ : P' ⟶ P) (g : Q ⟶ Q') :
    map R (f₁ + f₂) g = map R f₁ g + map R f₂ g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  change ((map R (f₁ + f₂) g).f n z).v p q hpq =
    ((map R f₁ g).f n z : Cochain P' Q' n).v p q hpq +
      ((map R f₂ g).f n z : Cochain P' Q' n).v p q hpq
  rw [map_f_apply, map_f_apply, map_f_apply, HomologicalComplex.add_f_apply,
    Preadditive.add_comp]

/-- The chain map `map R 0 g` is zero. -/
lemma map_zero_left (g : Q ⟶ Q') : map R (0 : P' ⟶ P) g = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  change ((map R (0 : P' ⟶ P) g).f n z).v p q hpq = 0
  rw [map_f_apply, HomologicalComplex.zero_f_apply, zero_comp]

/-- The chain map `map R f g` commutes with finite sums in `f`. -/
lemma map_sum_left {ι : Type*} (s : Finset ι) (f : ι → (P' ⟶ P)) (g : Q ⟶ Q') :
    map R (∑ i ∈ s, f i) g = ∑ i ∈ s, map R (f i) g :=
  map_sum (AddMonoidHom.mk' (fun f : P' ⟶ P => map R f g) fun f₁ f₂ => map_add_left R f₁ f₂ g)
    f s

end Additive

section Biproduct

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {ι : Type} [Finite ι] (K : ι → CochainComplex C ℤ) [HasBiproduct K] (L : CochainComplex C ℤ)

/-- The Hom complex out of a finite biproduct of cochain complexes is the biproduct of the
Hom complexes: `Hom^•(⨁ᵢ Kᵢ, L) ≅ ⨁ᵢ Hom^•(Kᵢ, L)`. The `i`-th component of the map is
precomposition with the inclusion `Kᵢ ⟶ ⨁ᵢ Kᵢ`, and the `i`-th component of the inverse is
precomposition with the projection `⨁ᵢ Kᵢ ⟶ Kᵢ`. -/
def sourceBiproductIso : complex R (⨁ K) L ≅ ⨁ fun i => complex R (K i) L where
  hom := biproduct.lift fun i => map R (biproduct.ι K i) (𝟙 L)
  inv := biproduct.desc fun i => map R (biproduct.π K i) (𝟙 L)
  hom_inv_id := by
    have := Fintype.ofFinite ι
    rw [biproduct.lift_desc]
    calc ∑ i, map R (biproduct.ι K i) (𝟙 L) ≫ map R (biproduct.π K i) (𝟙 L)
        = ∑ i, map R (biproduct.π K i ≫ biproduct.ι K i) (𝟙 L) :=
          Finset.sum_congr rfl fun i _ => by rw [map_comp, Category.comp_id]
      _ = map R (∑ i, biproduct.π K i ≫ biproduct.ι K i) (𝟙 L) := (map_sum_left R _ _ _).symm
      _ = 𝟙 _ := by rw [biproduct.total, map_id]
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
    rw [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, map_comp]
    simp only [Category.comp_id]
    by_cases h : i = j
    · subst h
      rw [biproduct.ι_π_self, biproduct.ι_π_self, map_id]
    · rw [biproduct.ι_π_ne _ (Ne.symm h), biproduct.ι_π_ne _ h, map_zero_left]

/-- The `i`-th component of `sourceBiproductIso` is precomposition with the inclusion of
`Kᵢ`. -/
@[reassoc (attr := simp)]
lemma sourceBiproductIso_hom_π (i : ι) :
    (sourceBiproductIso R K L).hom ≫ biproduct.π _ i = map R (biproduct.ι K i) (𝟙 L) :=
  biproduct.lift_π _ _

/-- The restriction of the inverse of `sourceBiproductIso` to the `i`-th summand is
precomposition with the projection onto `Kᵢ`. -/
@[reassoc (attr := simp)]
lemma ι_sourceBiproductIso_inv (i : ι) :
    biproduct.ι _ i ≫ (sourceBiproductIso R K L).inv = map R (biproduct.π K i) (𝟙 L) :=
  biproduct.ι_desc _ _

end Biproduct

end LinearHomComplex

section ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type} [Finite ι]

/-- The short complex `⨁ᵢ Sᵢ.X₁ ⟶ ⨁ᵢ Sᵢ.X₂ ⟶ ⨁ᵢ Sᵢ.X₃` of a finite family of short
complexes `Sᵢ`, with the biproducts of the maps. -/
@[simps]
def biproductShortComplex (S : ι → ShortComplex C) : ShortComplex C where
  X₁ := ⨁ fun i => (S i).X₁
  X₂ := ⨁ fun i => (S i).X₂
  X₃ := ⨁ fun i => (S i).X₃
  f := biproduct.map fun i => (S i).f
  g := biproduct.map fun i => (S i).g
  zero := biproduct.hom_ext _ _ fun i => by
    rw [Category.assoc, biproduct.map_π, biproduct.map_π_assoc, (S i).zero, comp_zero, zero_comp]

/-- The projection of `biproductShortComplex S` onto `S i`. -/
def biproductShortComplexπ (S : ι → ShortComplex C) (i : ι) : biproductShortComplex S ⟶ S i where
  τ₁ := biproduct.π (fun i => (S i).X₁) i
  τ₂ := biproduct.π (fun i => (S i).X₂) i
  τ₃ := biproduct.π (fun i => (S i).X₃) i
  comm₁₂ := (biproduct.map_π (fun i => (S i).f) i).symm
  comm₂₃ := (biproduct.map_π (fun i => (S i).g) i).symm

/-- The inclusion of `S i` into `biproductShortComplex S`. -/
def biproductShortComplexι (S : ι → ShortComplex C) (i : ι) : S i ⟶ biproductShortComplex S where
  τ₁ := biproduct.ι (fun i => (S i).X₁) i
  τ₂ := biproduct.ι (fun i => (S i).X₂) i
  τ₃ := biproduct.ι (fun i => (S i).X₃) i
  comm₁₂ := biproduct.ι_map (fun i => (S i).f) i
  comm₂₃ := biproduct.ι_map (fun i => (S i).g) i

/-- A finite biproduct of exact short complexes is exact: the identity of
`biproductShortComplex S` is the sum of the composites of the projections onto the `Sᵢ` and
the inclusions, so the identity of its homology factors through the homologies of the `Sᵢ`,
which are zero. -/
lemma exact_biproductShortComplex (S : ι → ShortComplex C) (h : ∀ i, (S i).Exact) :
    (biproductShortComplex S).Exact := by
  have := Fintype.ofFinite ι
  have hsum : ∀ (S₁ S₂ : ShortComplex C) (φ : ι → (S₁ ⟶ S₂)),
      (∑ i, φ i).τ₁ = ∑ i, (φ i).τ₁ ∧ (∑ i, φ i).τ₂ = ∑ i, (φ i).τ₂ ∧
        (∑ i, φ i).τ₃ = ∑ i, (φ i).τ₃ := fun S₁ S₂ φ =>
    ⟨map_sum (AddMonoidHom.mk' (fun φ : S₁ ⟶ S₂ => φ.τ₁) fun _ _ => rfl) φ Finset.univ,
      map_sum (AddMonoidHom.mk' (fun φ : S₁ ⟶ S₂ => φ.τ₂) fun _ _ => rfl) φ Finset.univ,
      map_sum (AddMonoidHom.mk' (fun φ : S₁ ⟶ S₂ => φ.τ₃) fun _ _ => rfl) φ Finset.univ⟩
  have htot : ∑ i, biproductShortComplexπ S i ≫ biproductShortComplexι S i =
      𝟙 (biproductShortComplex S) := by
    obtain ⟨h₁, h₂, h₃⟩ := hsum _ _ fun i => biproductShortComplexπ S i ≫ biproductShortComplexι S i
    ext
    · rw [h₁]
      exact biproduct.total (f := fun i => (S i).X₁)
    · rw [h₂]
      exact biproduct.total (f := fun i => (S i).X₂)
    · rw [h₃]
      exact biproduct.total (f := fun i => (S i).X₃)
  have key : (ShortComplex.homologyFunctor C).map (𝟙 (biproductShortComplex S)) = 0 := by
    rw [← htot, Functor.map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : (ShortComplex.homologyFunctor C).map (biproductShortComplexπ S i) = 0 :=
      (((S i).exact_iff_isZero_homology).1 (h i)).eq_of_tgt _ _
    rw [Functor.map_comp, h0, zero_comp]
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  exact ((ShortComplex.homologyFunctor C).map_id _).symm.trans key

/-- A finite biproduct of short exact short complexes is short exact. -/
lemma shortExact_biproductShortComplex (S : ι → ShortComplex C) (h : ∀ i, (S i).ShortExact) :
    (biproductShortComplex S).ShortExact :=
  have : ∀ i, Mono (S i).f := fun i => (h i).mono_f
  have : ∀ i, Epi (S i).g := fun i => (h i).epi_g
  { exact := exact_biproductShortComplex S fun i => (h i).exact
    mono_f := (inferInstance : Mono (biproduct.map fun i => (S i).f))
    epi_g := (inferInstance : Epi (biproduct.map fun i => (S i).g)) }

end ShortComplex

section BiproductSystem

variable {J : Type*} [Category J] {D : Type u'} [Category.{v} D] [HasZeroMorphisms D]
  {ι : Type*} [HasBiproductsOfShape ι D]

/-- The levelwise biproduct `j ↦ ⨁ᵢ Fᵢ j` of a family of functors `Fᵢ : J ⥤ D`. -/
abbrev biproductSystem (F : ι → J ⥤ D) : J ⥤ D where
  obj j := ⨁ fun i => (F i).obj j
  map φ := biproduct.map fun i => (F i).map φ
  map_id j := biproduct.hom_ext _ _ fun i => by
    rw [biproduct.map_π, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  map_comp φ ψ := biproduct.hom_ext _ _ fun i => by
    rw [biproduct.map_π, Functor.map_comp, Category.assoc, biproduct.map_π,
      biproduct.map_π_assoc]

lemma biproductSystem_obj (F : ι → J ⥤ D) (j : J) :
    (biproductSystem F).obj j = ⨁ fun i => (F i).obj j :=
  rfl

lemma biproductSystem_map (F : ι → J ⥤ D) {j j' : J} (φ : j ⟶ j') :
    (biproductSystem F).map φ = biproduct.map fun i => (F i).map φ :=
  rfl

/-- A family of natural transformations `Fᵢ ⟶ F'ᵢ` induces a natural transformation of the
levelwise biproducts. -/
def biproductSystemMap {F F' : ι → J ⥤ D} (α : ∀ i, F i ⟶ F' i) :
    biproductSystem F ⟶ biproductSystem F' where
  app j := biproduct.map fun i => (α i).app j
  naturality j j' φ := by
    change (biproduct.map fun i => (F i).map φ) ≫ (biproduct.map fun i => (α i).app j') =
      (biproduct.map fun i => (α i).app j) ≫ (biproduct.map fun i => (F' i).map φ)
    refine biproduct.hom_ext _ _ fun i => ?_
    rw [Category.assoc, Category.assoc, biproduct.map_π, biproduct.map_π, biproduct.map_π_assoc,
      biproduct.map_π_assoc, (α i).naturality]

lemma biproductSystemMap_app {F F' : ι → J ⥤ D} (α : ∀ i, F i ⟶ F' i) (j : J) :
    (biproductSystemMap α).app j = biproduct.map fun i => (α i).app j :=
  rfl

/-- A family of natural isomorphisms `Fᵢ ≅ F'ᵢ` induces a natural isomorphism of the
levelwise biproducts. -/
def biproductSystemMapIso {F F' : ι → J ⥤ D} (e : ∀ i, F i ≅ F' i) :
    biproductSystem F ≅ biproductSystem F' :=
  NatIso.ofComponents (fun j => biproduct.mapIso fun i => (e i).app j)
    fun φ => (biproductSystemMap fun i => (e i).hom).naturality φ

lemma biproductSystemMapIso_hom {F F' : ι → J ⥤ D} (e : ∀ i, F i ≅ F' i) :
    (biproductSystemMapIso e).hom = biproductSystemMap fun i => (e i).hom :=
  rfl

/-- The levelwise projection `⨁ᵢ Fᵢ ⟶ Fᵢ`. -/
def biproductSystemπ (F : ι → J ⥤ D) (i : ι) : biproductSystem F ⟶ F i where
  app j := biproduct.π (fun i => (F i).obj j) i
  naturality _ _ φ := biproduct.map_π (fun i => (F i).map φ) i

/-- The levelwise inclusion `Fᵢ ⟶ ⨁ᵢ Fᵢ`. -/
def biproductSystemι (F : ι → J ⥤ D) (i : ι) : F i ⟶ biproductSystem F where
  app j := biproduct.ι (fun i => (F i).obj j) i
  naturality _ _ φ := (biproduct.ι_map (fun i => (F i).map φ) i).symm

lemma biproductSystemπ_app (F : ι → J ⥤ D) (i : ι) (j : J) :
    (biproductSystemπ F i).app j = biproduct.π (fun i => (F i).obj j) i :=
  rfl

lemma biproductSystemι_app (F : ι → J ⥤ D) (i : ι) (j : J) :
    (biproductSystemι F i).app j = biproduct.ι (fun i => (F i).obj j) i :=
  rfl

end BiproductSystem

section LimitBiproductSystem

variable {J : Type*} [Category J] {D : Type u'} [Category.{v} D] [Preadditive D]
  {ι : Type} [Finite ι] [HasBiproductsOfShape ι D] [HasLimitsOfShape J D]

/-- Limits commute with finite biproducts: `lim_j ⨁ᵢ Fᵢ j ≅ ⨁ᵢ lim_j Fᵢ j`. The `i`-th
component of the map is the limit of the projections `⨁ᵢ Fᵢ ⟶ Fᵢ`, and the `i`-th component
of the inverse is the limit of the inclusions `Fᵢ ⟶ ⨁ᵢ Fᵢ`. -/
def limitBiproductSystemIso (F : ι → J ⥤ D) :
    limit (biproductSystem F) ≅ ⨁ fun i => limit (F i) where
  hom := biproduct.lift fun i => limMap (biproductSystemπ F i)
  inv := biproduct.desc fun i => limMap (biproductSystemι F i)
  hom_inv_id := by
    have := Fintype.ofFinite ι
    refine limit.hom_ext fun j => ?_
    rw [biproduct.lift_desc, Category.id_comp, Preadditive.sum_comp]
    calc ∑ i, (limMap (biproductSystemπ F i) ≫ limMap (biproductSystemι F i)) ≫
          limit.π (biproductSystem F) j
        = ∑ i, limit.π (biproductSystem F) j ≫
            ((biproductSystemπ F i).app j ≫ (biproductSystemι F i).app j) :=
          Finset.sum_congr rfl fun i _ => by rw [Category.assoc, limMap_π, limMap_π_assoc]
      _ = limit.π (biproductSystem F) j ≫
            ∑ i, (biproductSystemπ F i).app j ≫ (biproductSystemι F i).app j :=
          (Preadditive.comp_sum _ _ _).symm
      _ = limit.π (biproductSystem F) j :=
          (congrArg (limit.π (biproductSystem F) j ≫ ·)
            (biproduct.total (f := fun i => (F i).obj j))).trans (Category.comp_id _)
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun k => ?_
    rw [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π]
    simp only [Category.comp_id]
    by_cases h : i = k
    · subst h
      rw [biproduct.ι_π_self]
      refine limit.hom_ext fun j => ?_
      rw [Category.assoc, limMap_π, limMap_π_assoc, Category.id_comp]
      exact (congrArg (limit.π (F i) j ≫ ·)
        (biproduct.ι_π_self (fun i => (F i).obj j) i)).trans (Category.comp_id _)
    · rw [biproduct.ι_π_ne _ h]
      refine limit.hom_ext fun j => ?_
      rw [Category.assoc, limMap_π, limMap_π_assoc, zero_comp]
      exact (congrArg (limit.π (F i) j ≫ ·)
        (biproduct.ι_π_ne (fun i => (F i).obj j) h)).trans comp_zero

/-- The `i`-th component of `limitBiproductSystemIso F` is the limit of the projections. -/
@[reassoc (attr := simp)]
lemma limitBiproductSystemIso_hom_π (F : ι → J ⥤ D) (i : ι) :
    (limitBiproductSystemIso F).hom ≫ biproduct.π (fun i => limit (F i)) i =
      limMap (biproductSystemπ F i) :=
  biproduct.lift_π _ _

/-- The restriction of the inverse of `limitBiproductSystemIso F` to the `i`-th summand is the
limit of the inclusions. -/
@[reassoc (attr := simp)]
lemma ι_limitBiproductSystemIso_inv (F : ι → J ⥤ D) (i : ι) :
    biproduct.ι (fun i => limit (F i)) i ≫ (limitBiproductSystemIso F).inv =
      limMap (biproductSystemι F i) :=
  biproduct.ι_desc _ _

end LimitBiproductSystem

namespace DivisibleSystem

section Biproduct

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ} {ι : Type} [Finite ι]

/-- Multiplication by `ℓ ^ m` on a finite biproduct is the biproduct of the
multiplications. -/
lemma powSMul_biproduct (X : ι → C) (m : ℕ) :
    powSMul ℓ m (⨁ X) = biproduct.map fun i => powSMul ℓ m (X i) :=
  biproduct.hom_ext _ _ fun i => by
    rw [biproduct.map_π]
    exact (comp_powSMul ℓ m (biproduct.π X i)).symm

/-- The direct sum `m ↦ ⨁ᵢ Tᵢ m` of a finite family of `ℓ`-divisible systems, with the
biproducts of the maps `i` and `j`. -/
abbrev biproduct (T : ι → DivisibleSystem C ℓ) : DivisibleSystem C ℓ where
  tower := biproductSystem fun i => (T i).tower
  inclusion h := biproduct.map fun i => (T i).inclusion h
  powSMul_eq_zero m := by
    change powSMul ℓ m (⨁ fun i => (T i).obj m) = 0
    rw [powSMul_biproduct]
    refine biproduct.hom_ext _ _ fun i => ?_
    rw [biproduct.map_π, (T i).powSMul_eq_zero, comp_zero, zero_comp]
  inclusion_comp {m' m} h := by
    change (biproduct.map fun i => (T i).inclusion h) ≫
      (biproduct.map fun i => (T i).tower.map (homOfLE (Nat.sub_le m m')).op) = 0
    refine biproduct.hom_ext _ _ fun i => ?_
    rw [Category.assoc, biproduct.map_π, biproduct.map_π_assoc, (T i).inclusion_comp, comp_zero,
      zero_comp]
  shortExact h := shortExact_biproductShortComplex
    (fun i => ShortComplex.mk _ _ ((T i).inclusion_comp h)) fun i => (T i).shortExact h
  torsion_exact {m' m} h := shortComplex_exact_congr rfl
    (powSMul_biproduct (fun i => (T i).obj m) m').symm
    (exact_biproductShortComplex (fun i => ShortComplex.mk ((T i).inclusion h)
      (powSMul ℓ m' ((T i).obj m)) (by rw [comp_powSMul, (T i).powSMul_eq_zero, zero_comp]))
      fun i => (T i).torsion_exact h)
  flat a b := shortComplex_exact_congr
    (powSMul_biproduct (fun i => (T i).obj (a + b)) a).symm
    (powSMul_biproduct (fun i => (T i).obj (a + b)) b).symm
    (exact_biproductShortComplex (fun i => ShortComplex.mk (powSMul ℓ a ((T i).obj (a + b)))
      (powSMul ℓ b ((T i).obj (a + b)))
      (by rw [powSMul_comp_powSMul, (T i).powSMul_eq_zero])) fun i => (T i).flat a b)

variable (T : ι → DivisibleSystem C ℓ)

lemma biproduct_tower : (biproduct T).tower = biproductSystem fun i => (T i).tower :=
  rfl

lemma biproduct_inclusion {m' m : ℕ} (h : m' < m) :
    (biproduct T).inclusion h = biproduct.map fun i => (T i).inclusion h :=
  rfl

/-- The inclusion `Tᵢ ⟶ ⨁ᵢ Tᵢ` of `ℓ`-divisible systems. -/
def biproductι (i : ι) : T i ⟶ biproduct T :=
  ⟨{ app m := biproduct.ι (fun i => (T i).tower.obj m) i
     naturality _ _ φ := (biproduct.ι_map (fun i => (T i).tower.map φ) i).symm },
    fun h => (biproduct.ι_map (fun i => (T i).inclusion h) i).symm⟩

/-- The projection `⨁ᵢ Tᵢ ⟶ Tᵢ` of `ℓ`-divisible systems. -/
def biproductπ (i : ι) : biproduct T ⟶ T i :=
  ⟨{ app m := biproduct.π (fun i => (T i).tower.obj m) i
     naturality _ _ φ := biproduct.map_π (fun i => (T i).tower.map φ) i },
    fun h => biproduct.map_π (fun i => (T i).inclusion h) i⟩

@[simp]
lemma biproductι_tower_app (i : ι) (m : ℕᵒᵖ) :
    (biproductι T i).tower.app m = biproduct.ι (fun i => (T i).tower.obj m) i :=
  rfl

@[simp]
lemma biproductπ_tower_app (i : ι) (m : ℕᵒᵖ) :
    (biproductπ T i).tower.app m = biproduct.π (fun i => (T i).tower.obj m) i :=
  rfl

end Biproduct

section Precomp

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} {T T' : DivisibleSystem (CochainComplex C ℤ) ℓ}
  (W : DivisibleSystem (CochainComplex C ℤ) ℓ)

/-- The transitions of graded morphisms commute with precomposition by a morphism of the
inverse systems `T'.tower ⟶ T.tower`. -/
lemma cochainTransition_ofHom_comp (α : T'.tower ⟶ T.tower) {m' m : ℕ} (h : m' ≤ m) {n : ℤ}
    (z : Cochain (T.obj m) (W.obj m) n) :
    cochainTransition T' W h ((Cochain.ofHom (α.app (op m))).comp z (zero_add n)) =
      (Cochain.ofHom (α.app (op m'))).comp (cochainTransition T W h z) (zero_add n) := by
  rw [cochainTransition_eq_iff]
  ext p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v, Cochain.ofHom_v,
    Cochain.ofHom_v, cochainTransition_v]
  have hα : (T'.projection h).f p ≫ (α.app (op m')).f p =
      (α.app (op m)).f p ≫ (T.projection h).f p := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    exact congrArg (fun φ => HomologicalComplex.Hom.f φ p) (α.naturality (homOfLE h).op)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hα).trans
    ((Category.assoc _ _ _).trans ((congrArg ((α.app (op m)).f p ≫ ·)
      (projection_comp_homTransition (T.degree p) (W.degree q) h (z.v p q hpq))).trans
        (Category.assoc _ _ _).symm)))

/-- Precomposition by a morphism of inverse systems commutes with the transition chain
maps of the Hom complexes. -/
lemma map_comp_homComplexTransition (α : T'.tower ⟶ T.tower) {m' m : ℕ} (h : m' ≤ m) :
    LinearHomComplex.map R (α.app (op m)) (𝟙 (W.obj m)) ≫ homComplexTransition R T' W h =
      homComplexTransition R T W h ≫ LinearHomComplex.map R (α.app (op m')) (𝟙 (W.obj m')) := by
  ext n z
  change cochainTransition T' W h
      (((Cochain.ofHom (α.app (op m))).comp z (zero_add n)).comp
        (Cochain.ofHom (𝟙 (W.obj m))) (add_zero n)) =
    ((Cochain.ofHom (α.app (op m'))).comp (cochainTransition T W h z) (zero_add n)).comp
      (Cochain.ofHom (𝟙 (W.obj m'))) (add_zero n)
  rw [Cochain.comp_id, Cochain.comp_id]
  exact cochainTransition_ofHom_comp W α h z

/-- A morphism of inverse systems `T'.tower ⟶ T.tower` induces, by precomposition, a
morphism of the inverse systems of Hom complexes `homComplexSystem R T W ⟶
homComplexSystem R T' W`. -/
@[simps]
def homComplexSystemPrecomp (α : T'.tower ⟶ T.tower) :
    homComplexSystem R T W ⟶ homComplexSystem R T' W where
  app m := LinearHomComplex.map R (α.app m) (𝟙 (W.obj m.unop))
  naturality _ _ φ := (map_comp_homComplexTransition R W α (leOfHom φ.unop)).symm

end Precomp

section BiproductHom

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} {ι : Type} [Finite ι] (T : ι → DivisibleSystem (CochainComplex C ℤ) ℓ)
  (W : DivisibleSystem (CochainComplex C ℤ) ℓ)

/-- The inverse system of Hom complexes out of a finite direct sum of `ℓ`-divisible systems
of cochain complexes is the levelwise biproduct of the inverse systems of Hom complexes:
`(m ↦ Hom^•(⨁ᵢ Tᵢ m, W m)) ≅ (m ↦ ⨁ᵢ Hom^•(Tᵢ m, W m))`, levelwise by
`LinearHomComplex.sourceBiproductIso`. -/
def homComplexSystemBiproductIso :
    homComplexSystem R (biproduct T) W ≅ biproductSystem fun i => homComplexSystem R (T i) W :=
  NatIso.ofComponents
    (fun m => LinearHomComplex.sourceBiproductIso R (fun i => (T i).obj m.unop) (W.obj m.unop))
    (fun {m m'} φ => by
      change homComplexTransition R (biproduct T) W (leOfHom φ.unop) ≫
          (LinearHomComplex.sourceBiproductIso R (fun i => (T i).obj m'.unop)
            (W.obj m'.unop)).hom =
        (LinearHomComplex.sourceBiproductIso R (fun i => (T i).obj m.unop) (W.obj m.unop)).hom ≫
          biproduct.map fun i => homComplexTransition R (T i) W (leOfHom φ.unop)
      refine biproduct.hom_ext _ _ fun i => ?_
      rw [Category.assoc, Category.assoc, LinearHomComplex.sourceBiproductIso_hom_π,
        biproduct.map_π, LinearHomComplex.sourceBiproductIso_hom_π_assoc]
      exact (map_comp_homComplexTransition R W (biproductι T i).tower
        (leOfHom φ.unop)).symm)

/-- The `i`-th component of `homComplexSystemBiproductIso` at level `m` is precomposition with
the inclusion `Tᵢ m ⟶ ⨁ᵢ Tᵢ m`. -/
@[reassoc (attr := simp)]
lemma homComplexSystemBiproductIso_hom_app_π (m : ℕᵒᵖ) (i : ι) :
    (homComplexSystemBiproductIso R T W).hom.app m ≫
        biproduct.π (fun i => LinearHomComplex.complex R ((T i).obj m.unop) (W.obj m.unop)) i =
      (homComplexSystemPrecomp R W (biproductι T i).tower).app m :=
  LinearHomComplex.sourceBiproductIso_hom_π R (fun i => (T i).obj m.unop) (W.obj m.unop) i

/-- The inverse limit of the Hom complexes out of a finite direct sum of `ℓ`-divisible
systems of cochain complexes is the biproduct of the inverse limits:
`lim_m Hom^•(⨁ᵢ Tᵢ m, W m) ≅ ⨁ᵢ lim_m Hom^•(Tᵢ m, W m)`. -/
def homComplexLimitBiproductIso :
    homComplexLimit R (biproduct T) W ≅ ⨁ fun i => homComplexLimit R (T i) W :=
  HasLimit.isoOfNatIso (homComplexSystemBiproductIso R T W) ≪≫
    limitBiproductSystemIso fun i => homComplexSystem R (T i) W

/-- The `i`-th component of `homComplexLimitBiproductIso` is the limit of the precompositions
with the inclusions `Tᵢ m ⟶ ⨁ᵢ Tᵢ m`. -/
lemma homComplexLimitBiproductIso_hom_π (i : ι) :
    (homComplexLimitBiproductIso R T W).hom ≫
        biproduct.π (fun i => homComplexLimit R (T i) W) i =
      limMap (homComplexSystemPrecomp R W (biproductι T i).tower) := by
  rw [homComplexLimitBiproductIso, Iso.trans_hom, Category.assoc, limitBiproductSystemIso_hom_π]
  refine limit.hom_ext fun m => ?_
  rw [Category.assoc, limMap_π, HasLimit.isoOfNatIso_hom_π_assoc, limMap_π]
  exact congrArg (limit.π (homComplexSystem R (biproduct T) W) m ≫ ·)
    (homComplexSystemBiproductIso_hom_app_π R T W m i)

end BiproductHom

end DivisibleSystem

section Smooth

open SupercuspidalExt

variable (R : Type u) [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ℓ : ℕ} {ι : Type} [Finite ι] {H : ι → Subgroup G}
  (hH : ∀ i, IsOpen (H i : Set G))

/-- Harris 1999, p.311, the rewriting to (4.10.2) for a single degree `-i`: for a finite
family of open subgroups `Hᵢ` of `G` and `ℓ`-divisible systems `Tᵢ` of cochain complexes of
smooth representations of `Hᵢ`, the inverse system of Hom complexes
`m ↦ Hom^•_G(⨁ᵢ c-Ind_{Hᵢ}^G Tᵢ m, W m)` is isomorphic to the levelwise biproduct of the
inverse systems `m ↦ Hom^•_{Hᵢ}(Tᵢ m, W m|_{Hᵢ})`. -/
def smoothHomComplexSystemBiproductReciprocityIso
    (T : (i : ι) → SmoothRepComplexDivisibleSystem.{u, u, u} R (H i) ℓ)
    (W : SmoothRepComplexDivisibleSystem.{u, u, u} R G ℓ) :
    smoothHomComplexSystem R G
        (DivisibleSystem.biproduct fun i => compactInductionSystem R (hH i) (T i)) W ≅
      biproductSystem fun i => smoothHomComplexSystem R (H i) (T i) (restrictionSystem R (hH i) W) :=
  DivisibleSystem.homComplexSystemBiproductIso R _ W ≪≫
    biproductSystemMapIso fun i => smoothHomComplexSystemReciprocityIso R (hH i) (T i) W

/-- The isomorphism of inverse limits induced by
`smoothHomComplexSystemBiproductReciprocityIso`:
`lim_m Hom^•_G(⨁ᵢ c-Ind_{Hᵢ}^G Tᵢ m, W m) ≅ ⨁ᵢ lim_m Hom^•_{Hᵢ}(Tᵢ m, W m|_{Hᵢ})`. -/
def smoothHomComplexLimitBiproductReciprocityIso
    (T : (i : ι) → SmoothRepComplexDivisibleSystem.{u, u, u} R (H i) ℓ)
    (W : SmoothRepComplexDivisibleSystem.{u, u, u} R G ℓ) :
    DivisibleSystem.homComplexLimit R
        (DivisibleSystem.biproduct fun i => compactInductionSystem R (hH i) (T i)) W ≅
      ⨁ fun i => DivisibleSystem.homComplexLimit R (T i) (restrictionSystem R (hH i) W) :=
  HasLimit.isoOfNatIso (smoothHomComplexSystemBiproductReciprocityIso R hH T W) ≪≫
    limitBiproductSystemIso fun i =>
      smoothHomComplexSystem R (H i) (T i) (restrictionSystem R (hH i) W)

end Smooth

end Langlands.Cohomology
