import Langlands.ClassField.Global.InvariantLocalFromTotalStatement
import Langlands.ClassField.Global.IdeleTotalSection
import Langlands.ClassField.Global.DecompositionField

/-! # Local compatibility of global invariants from the total idele invariant

The Shapiro corestriction `Hⁿ(H, Res_φ B) ⟶ Hⁿ(G, B)` along an injective `φ : H →* G` of
finite index, its composite with restriction (multiplication by the index), and its
naturality; the corestriction of the local image of a local class is the idele-class image of
the finite local section, so its global invariant is the local invariant; the corestriction is
injective on `H²(Gal(E_w/F_v), C_E)` once restriction to `Gal(E_w/F_v)` factors through a
field `F'` of degree `[Gal(E/F) : Gal(E_w/F_v)]`; and the resulting local compatibility.
-/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Shapiro

set_option backward.isDefEq.respectTransparency false

section Additive

variable (k G : Type u) [CommRing k] [Group G]

/-- Group cohomology is additive in the coefficients. -/
instance groupCohomology_functor_additive (n : ℕ) :
    (groupCohomology.functor k G n).Additive where
  map_add {_ _ f g} := by
    simp only [groupCohomology.functor_map, groupCohomology.map]
    rw [← HomologicalComplex.homologyMap_add]
    congr 1

variable {k G}

/-- The map induced on cohomology by `m • f` is `m •` the map induced by `f`. -/
theorem map_id_nsmul {A B : Rep.{u} k G} (f : A ⟶ B) (m n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (m • f) n =
      m • groupCohomology.map (MonoidHom.id G) f n :=
  (groupCohomology.functor k G n).map_nsmul

end Additive

section Corestriction

variable {k G H : Type u} [CommRing k] [Group G] [Group H] {φ : H →* G}
  [Fintype (G ⧸ φ.range)]

variable (φ) in
/-- The coset sum of the identity after the adjoint of the identity is multiplication by the
index: `∑_{x φ(H)} x • (x⁻¹ • b) = [G : φ(H)] • b`. -/
theorem resCoindToHom_comp_coindSum_id (B : Rep.{u} k G) :
    Rep.resCoindToHom φ B (Rep.res φ B) (𝟙 _) ≫ coindSum φ (𝟙 (Rep.res φ B)) =
      Fintype.card (G ⧸ φ.range) • 𝟙 B := by
  ext b
  change (coindSum φ (𝟙 (Rep.res φ B))).hom
      ((Rep.resCoindToHom φ B (Rep.res φ B) (𝟙 _)).hom b) = Fintype.card (G ⧸ φ.range) • b
  rw [coindSum_hom_apply, ← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun c _ => ?_
  induction c using QuotientGroup.induction_on with | H x => ?_
  change B.ρ x (B.ρ x⁻¹ b) = b
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

variable (φ) in
/-- The coset sum of `ι` is the coinduced map of `ι` followed by the coset sum of the
identity. -/
theorem coindSum_eq_coindMap_comp {A : Rep.{u} k H} {B : Rep.{u} k G}
    (ι : A ⟶ Rep.res φ B) :
    coindSum φ ι = Rep.coindMap φ ι ≫ coindSum φ (𝟙 (Rep.res φ B)) := by
  ext f
  change (coindSum φ ι).hom f = (coindSum φ (𝟙 (Rep.res φ B))).hom ((Rep.coindMap φ ι).hom f)
  rw [coindSum_hom_apply, coindSum_hom_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  induction c using QuotientGroup.induction_on with | H x => rfl

variable (φ) in
/-- Composing a coset sum with a morphism of `G`-representations. -/
theorem coindSum_comp {A : Rep.{u} k H} {B B' : Rep.{u} k G} (ι : A ⟶ Rep.res φ B)
    (π : B ⟶ B') :
    coindSum φ ι ≫ π = coindSum φ (ι ≫ (Rep.resFunctor φ).map π) := by
  ext f
  change π.hom ((coindSum φ ι).hom f) = (coindSum φ (ι ≫ (Rep.resFunctor φ).map π)).hom f
  rw [coindSum_hom_apply, coindSum_hom_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  induction c using QuotientGroup.induction_on with | H x => ?_
  exact Rep.hom_comm_apply π x _

omit [Fintype (G ⧸ φ.range)] in
variable (φ) in
/-- The Shapiro map is natural in the coefficients. -/
theorem map_coindMap_comp_shapiroMapOf {A : Rep.{u} k H} {B : Rep.{u} k G}
    (ι : A ⟶ Rep.res φ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (Rep.coindMap φ ι) n ≫
        shapiroMapOf φ (Rep.res φ B) n =
      shapiroMapOf φ A n ≫ groupCohomology.map (MonoidHom.id H) ι n := by
  rw [shapiroMapOf, shapiroMapOf, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  exact groupCohomology.map_congr (MonoidHom.ext fun _ => rfl) (by ext; rfl) n

variable (hφ : Function.Injective φ)

/-- The Shapiro corestriction `Hⁿ(H, Res_φ B) ⟶ Hⁿ(G, B)`: the inverse Shapiro isomorphism
followed by the map induced by the coset sum of the identity. -/
def shapiroCor (B : Rep.{u} k G) (n : ℕ) :
    groupCohomology (Rep.res φ B) n ⟶ groupCohomology B n :=
  (shapiroIsoOf hφ (Rep.res φ B) n).inv ≫
    groupCohomology.map (MonoidHom.id G) (coindSum φ (𝟙 (Rep.res φ B))) n

/-- Restriction followed by corestriction is multiplication by the index. -/
theorem map_comp_shapiroCor (B : Rep.{u} k G) (n : ℕ) :
    groupCohomology.map φ (𝟙 (Rep.res φ B)) n ≫ shapiroCor hφ B n =
      Fintype.card (G ⧸ φ.range) • 𝟙 _ := by
  rw [← map_resCoindToHom_comp_shapiroMapOf, shapiroCor, Category.assoc,
    ← shapiroIsoOf_hom hφ, Iso.hom_inv_id_assoc, ← groupCohomology.map_id_comp]
  exact (congrArg (fun f => groupCohomology.map (MonoidHom.id G) f n)
    (resCoindToHom_comp_coindSum_id φ B)).trans (by rw [map_id_nsmul, groupCohomology.map_id])

/-- Restriction followed by corestriction, on classes. -/
theorem shapiroCor_map (B : Rep.{u} k G) (n : ℕ) (x : groupCohomology B n) :
    shapiroCor hφ B n (groupCohomology.map φ (𝟙 (Rep.res φ B)) n x) =
      Fintype.card (G ⧸ φ.range) • x := by
  have h := ConcreteCategory.congr_hom (map_comp_shapiroCor hφ B n) x
  exact h

/-- The inverse Shapiro isomorphism followed by the coset sum of `ι` is the map induced by
`ι` followed by the corestriction. -/
theorem shapiroIsoOf_inv_map_coindSum {A : Rep.{u} k H} {B : Rep.{u} k G}
    (ι : A ⟶ Rep.res φ B) (n : ℕ) :
    (shapiroIsoOf hφ A n).inv ≫ groupCohomology.map (MonoidHom.id G) (coindSum φ ι) n =
      groupCohomology.map (MonoidHom.id H) ι n ≫ shapiroCor hφ B n := by
  rw [coindSum_eq_coindMap_comp, groupCohomology.map_id_comp, shapiroCor, ← Category.assoc,
    ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact map_coindMap_comp_shapiroMapOf φ ι n

end Corestriction

end Langlands.Shapiro

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open FundamentalClass

section LocalSection

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Normal F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The single-coordinate embedding into `J_E`, followed by the quotient to `C_E`, is the
single-coordinate embedding into `C_E`. -/
theorem ideleLocalEmbedding_comp_ideleQuotientCoefficients :
    ideleLocalEmbedding v w ≫
        (Rep.resFunctor (decompositionHom v w)).map (ideleQuotientCoefficients F E) =
      localIdeleClassCoefficients v w := by
  ext x
  rfl

variable [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]

/-- The corestriction from `Gal(E_w/F_v)` to `Gal(E/F)` with coefficients `C_E`. -/
abbrev decompositionCorestriction (n : ℕ) :
    groupCohomology (Rep.res (decompositionHom v w) (relativeIdeleClassRepresentation F E)) n ⟶
      relativeIdeleClassCohomology F E n :=
  Shapiro.shapiroCor (decompositionHom_injective v w) (relativeIdeleClassRepresentation F E) n

/-- The idele-class image of the finite local section is the corestriction of the local
image in `Hⁿ(Gal(E_w/F_v), C_E)`. -/
theorem ideleLocalSection_comp_ideleQuotientCohomologyMap (n : ℕ) :
    ideleLocalSection v w n ≫ ideleQuotientCohomologyMap F E n =
      localIdeleClassMap v w n ≫ decompositionCorestriction v w n := by
  rw [ideleLocalSection, Category.assoc, ← groupCohomology.map_id_comp, ideleSemilocalSection,
    Shapiro.coindSum_comp, ideleLocalEmbedding_comp_ideleQuotientCoefficients,
    Shapiro.shapiroIsoOf_inv_map_coindSum]

/-- Restriction to `Gal(E_w/F_v)` followed by corestriction is multiplication by the index. -/
theorem decompositionCorestriction_decompositionRestriction (n : ℕ)
    (b : relativeIdeleClassCohomology F E n) :
    decompositionCorestriction v w n (decompositionRestriction v w n b) =
      Fintype.card ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range) • b :=
  Shapiro.shapiroCor_map _ _ n b

end LocalSection

/-- In `ℚ/ℤ`, every class killed by `m` is `k` times a class killed by `k * m`. -/
theorem exists_nsmul_eq_of_nsmul_eq_zero {k m : ℕ} (hk : k ≠ 0) {z : RationalModIntegers}
    (hz : m • z = 0) : ∃ x : RationalModIntegers, (k * m) • x = 0 ∧ k • x = z := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hkx : k • (QuotientAddGroup.mk (q / k) : RationalModIntegers) = QuotientAddGroup.mk q := by
    rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hk)]
  exact ⟨_, by rw [mul_comm, mul_smul, hkx, hz], hkx⟩

section Invariant

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] (inv : GlobalInvariantMaps.{u})

/-- Under the image and restriction laws, restriction `H²(Gal(E/F), C_E) → H²(Gal(E/F'), C_E)`
is surjective: invariants of `E/F'` lie in `(1/[E:F'])ℤ/ℤ`, which is `[F':F]` times
`(1/[E:F])ℤ/ℤ`. -/
theorem relativeIdeleClassRestriction_surjective (hi : InvariantImages inv)
    (hr : InvariantRestrictionOnClasses inv) (F' : Type u) [Field F'] [NumberField F']
    [Algebra F F'] [Algebra F' E] [IsScalarTower F F' E] :
    Function.Surjective (relativeIdeleClassRestriction F F' E 2) := by
  have : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
  have : FiniteDimensional F F' := FiniteDimensional.left F F' E
  intro y
  have hy : inv F' E y ∈ denominatorSubgroup (Module.finrank F' E) := by
    rw [← (hi F' E).2]
    exact ⟨y, rfl⟩
  obtain ⟨x, hx, hxy⟩ := exists_nsmul_eq_of_nsmul_eq_zero
    (k := Module.finrank F F') Module.finrank_pos.ne' hy
  rw [Module.finrank_mul_finrank] at hx
  have hx' : x ∈ (inv F E).range := by
    rw [(hi F E).2]
    exact hx
  obtain ⟨a, ha⟩ := hx'
  refine ⟨a, (hi F' E).1 ?_⟩
  rw [hr F F' E a, ha, hxy]

attribute [local instance] isGalois_adicCompletion FiniteExtension.local_finite

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
  [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]

/-- If `inv` agrees with every total idele invariant, the global invariant of the corestricted
local image of a local class is its local invariant. -/
theorem inv_decompositionCorestriction_localIdeleClassMap
    (hagree : InvariantTotalAgreement I hI inv)
    (a : relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) :
    inv F E (decompositionCorestriction v w 2 (localIdeleClassMap v w 2 a)) =
      (I (residuePrime v)).relative (padicField v) (w.adicCompletion E) a := by
  classical
  obtain ⟨wf, hw⟩ : ∃ wf : ∀ v' : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v',
      (wf v).1 = w :=
    ⟨Function.update (fun _ => Classical.arbitrary _) v ⟨w, ‹_›⟩, by
      rw [Function.update_self]⟩
  subst hw
  let wi : ∀ v' : InfinitePlace F, InfinitePlacesAbove E v' := fun v' =>
    ⟨(InfinitePlace.comap_surjective (k := F) (K := E) v').choose, by
      have h := (InfinitePlace.comap_surjective (k := F) (K := E) v').choose_spec
      revert h
      generalize (InfinitePlace.comap_surjective (k := F) (K := E) v').choose = z
      rintro rfl
      exact ⟨rfl⟩⟩
  have h := ConcreteCategory.congr_hom
    (ideleLocalSection_comp_ideleQuotientCohomologyMap v (wf v).1 2) a
  calc inv F E (decompositionCorestriction v (wf v).1 2 (localIdeleClassMap v (wf v).1 2 a))
      = inv F E (ideleQuotientCohomologyMap F E 2 (ideleLocalSection v (wf v).1 2 a)) :=
        congrArg (inv F E) h.symm
    _ = totalIdeleInvariant I hI wf wi (ideleLocalSection v (wf v).1 2 a) := hagree F E wf wi _
    _ = _ := totalIdeleInvariant_ideleLocalSection I hI wf wi v a

variable (F' : Type u) [Field F'] [NumberField F'] [Algebra F F'] [Algebra F' E]
  [IsScalarTower F F' E]
  (Θ : relativeIdeleClassCohomology F' E 2 ⟶
    groupCohomology (Rep.res (decompositionHom v w) (relativeIdeleClassRepresentation F E)) 2)

omit [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)] in
/-- If restriction to `Gal(E_w/F_v)` factors through `H²(Gal(E/F'), C_E)` by a surjection,
it is surjective. -/
theorem decompositionRestriction_surjective (hi : InvariantImages inv)
    (hr : InvariantRestrictionOnClasses inv) (hΘ : Function.Surjective Θ)
    (hcomp : relativeIdeleClassRestriction F F' E 2 ≫ Θ = decompositionRestriction v w 2) :
    Function.Surjective (decompositionRestriction v w 2) := by
  rw [← hcomp]
  exact hΘ.comp (relativeIdeleClassRestriction_surjective inv hi hr F')

/-- If restriction to `Gal(E_w/F_v)` factors through `H²(Gal(E/F'), C_E)` by a surjection and
`[F' : F]` is the index of `Gal(E_w/F_v)`, then the corestriction is injective on `H²`. -/
theorem decompositionCorestriction_injective (hi : InvariantImages inv)
    (hr : InvariantRestrictionOnClasses inv) (hΘ : Function.Surjective Θ)
    (hcomp : relativeIdeleClassRestriction F F' E 2 ≫ Θ = decompositionRestriction v w 2)
    (hdeg : Module.finrank F F' = Fintype.card ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)) :
    Function.Injective (decompositionCorestriction v w 2) := by
  have : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
  intro y₁ y₂ hy
  obtain ⟨b, hb⟩ := decompositionRestriction_surjective inv v w F' Θ hi hr hΘ hcomp (y₁ - y₂)
  have hkb : Fintype.card ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range) • b = 0 := by
    rw [← decompositionCorestriction_decompositionRestriction, hb, map_sub, hy, sub_self]
  have hres : relativeIdeleClassRestriction F F' E 2 b = 0 := by
    apply (hi F' E).1
    rw [hr F F' E b, map_zero, hdeg, ← map_nsmul, hkb, map_zero]
  rw [← sub_eq_zero, ← hb, ← hcomp, ConcreteCategory.comp_apply, hres, map_zero]

/-- Local compatibility at `w ∣ v`, given a field `F'` through which restriction to
`Gal(E_w/F_v)` factors surjectively and whose degree over `F` is the index of
`Gal(E_w/F_v)`. -/
theorem localIdeleClassMap_eq_decompositionRestriction_iff_of_field
    (hi : InvariantImages inv) (hr : InvariantRestrictionOnClasses inv)
    (hagree : InvariantTotalAgreement I hI inv) (hΘ : Function.Surjective Θ)
    (hcomp : relativeIdeleClassRestriction F F' E 2 ≫ Θ = decompositionRestriction v w 2)
    (hdeg : Module.finrank F F' = Fintype.card ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range))
    (a : relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2)
    (b : relativeIdeleClassCohomology F E 2) :
    localIdeleClassMap v w 2 a = decompositionRestriction v w 2 b ↔
      Module.finrank F F' • inv F E b =
        (I (residuePrime v)).relative (padicField v) (w.adicCompletion E) a := by
  have h3 := inv_decompositionCorestriction_localIdeleClassMap inv I hI v w hagree a
  rw [hdeg]
  constructor
  · intro h
    rw [← h3, h, decompositionCorestriction_decompositionRestriction, map_nsmul]
  · intro h
    apply decompositionCorestriction_injective inv v w F' Θ hi hr hΘ hcomp hdeg
    apply (hi F E).1
    rw [h3, decompositionCorestriction_decompositionRestriction, map_nsmul, h]

end Invariant

open FundamentalClass in
/-- Global invariants satisfying the image and restriction laws and agreeing with every total
idele invariant are locally compatible: take `F'` to be the decomposition field of `w ∣ v`. -/
theorem globalInvariantLocalFromTotalStatement : GlobalInvariantLocalFromTotalStatement.{u} := by
  intro I hI inv hi hr hagree F _ _ E _ _ _ _ v w _ _ a b
  let := Fintype.ofFinite ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)
  rw [finrank_div_finrank_local]
  exact localIdeleClassMap_eq_decompositionRestriction_iff_of_field inv I hI v w
    (decompositionField v w) (decompositionCohomologyIso v w 2).hom hi hr hagree
    (fun y => ⟨(decompositionCohomologyIso v w 2).inv y, by simp⟩)
    (relativeIdeleClassRestriction_comp_decompositionCohomologyIso v w 2)
    (by rw [finrank_decompositionField, Subgroup.index_eq_card, Nat.card_eq_fintype_card]) a b

end Langlands.ClassField.Global
