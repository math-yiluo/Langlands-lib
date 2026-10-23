import Langlands.ClassField.Global.ReciprocityStatement
import Langlands.ClassField.Global.CompletionTower
import Langlands.ClassField.Global.IdeleArchimedean
import Langlands.ClassField.Global.IdeleLocalInjectivity
import Langlands.ClassField.Global.IdeleFiniteInvariant
import Langlands.ClassField.Global.IdeleCohomologyExactnessProof
import Langlands.ClassField.Global.FundamentalClassStatement

/-! # Local invariants in towers of number fields and the Hasse principle for `H²(Eˣ)`

For a tower `F ⊆ E ⊆ L` of number fields with `E / F` and `L / F` Galois, the local components
of global classes in `H²(Gal(E/F), Eˣ)` commute with inflation to `L` and with restriction to
intermediate fields; consequently the finite and archimedean local invariants, and the
reciprocity law `SumOfInvariantsVanishes`, are unchanged by inflation. Assuming
`H¹(Gal(E/F), C_E) = 0`, a class of `H²(Gal(E/F), Eˣ)` all of whose local components vanish is
zero.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory FundamentalClass

universe u

namespace Reciprocity

section MapCongr

variable {k G H : Type u} [CommRing k] [Group G] [Group H] {A : Rep.{u} k H} {B : Rep.{u} k G}

/-- Cohomology maps along equal group homomorphisms with equal underlying coefficient maps are
equal. -/
theorem groupCohomology_map_congr {f f' : G →* H} (h : f = f')
    {φ : Rep.res f A ⟶ B} {φ' : Rep.res f' A ⟶ B} (hφ : ∀ x, φ.hom x = φ'.hom x) (n : ℕ) :
    groupCohomology.map f φ n = groupCohomology.map f' φ' n := by
  subst h
  congr
  ext x
  exact hφ x

end MapCongr

section Inflation

variable {F E L : Type u} [Field F] [Field E] [Field L] [NumberField F] [NumberField E]
  [NumberField L] [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal] [u.asIdeal.LiesOver v.asIdeal]

/-- Morphism form of `unitsLocalMap_relativeInflation`. -/
theorem relativeInflation_comp_unitsLocalMap :
    relativeInflation F E L 2 ≫ unitsLocalMap v u 2 =
      unitsLocalMap v w 2 ≫
        relativeInflation (padicField v).Carrier (w.adicCompletion E) (u.adicCompletion L) 2 := by
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  refine groupCohomology_map_congr ?_ ?_ 2
  · ext σ : 1
    exact CompletionTower.decompositionHom_restrictNormal v w u σ
  · intro y
    apply (@Additive.toMul (u.adicCompletion L)ˣ).injective
    apply Units.ext
    change algebraMap L (u.adicCompletion L) (algebraMap E L ((Additive.toMul y : Eˣ) : E)) =
      algebraMap (w.adicCompletion E) (u.adicCompletion L)
        (algebraMap E (w.adicCompletion E) ((Additive.toMul y : Eˣ) : E))
    rw [← IsScalarTower.algebraMap_apply E L (u.adicCompletion L),
      ← IsScalarTower.algebraMap_apply E (w.adicCompletion E) (u.adicCompletion L)]

/-- **Local components commute with inflation.** For `F ⊆ E ⊆ L` and finite places
`u | w | v`, the local component at `u` of the inflation of `x ∈ H²(Gal(E/F), Eˣ)` is the local
inflation from `E_w / F_v` to `L_u / F_v` of the local component of `x` at `w`. -/
theorem unitsLocalMap_relativeInflation (x : relativeCohomology F E 2) :
    (unitsLocalMap v u 2).hom ((relativeInflation F E L 2).hom x) =
      (relativeInflation (padicField v).Carrier (w.adicCompletion E) (u.adicCompletion L)
        2).hom ((unitsLocalMap v w 2).hom x) :=
  congrArg (fun φ => φ.hom x) (relativeInflation_comp_unitsLocalMap v w u)

/-- **Finite local invariants are unchanged by inflation.** If the local invariant maps are
compatible with inflation, the finite local invariant at `u | w | v` of the inflation of
`x ∈ H²(Gal(E/F), Eˣ)` equals the finite local invariant of `x` at `w`. -/
theorem finiteLocalInvariant_relativeInflation
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)
    (x : relativeCohomology F E 2) :
    finiteLocalInvariant v u I ((relativeInflation F E L 2).hom x) =
      finiteLocalInvariant v w I x := by
  have := isGalois_adicCompletion v w
  have := isGalois_adicCompletion v u
  have := FiniteExtension.local_finite v w
  have := FiniteExtension.local_finite v u
  have := FiniteExtension.local_finite w u
  change (I (residuePrime v)).relative (padicField v) (u.adicCompletion L)
      ((unitsLocalMap v u 2).hom ((relativeInflation F E L 2).hom x)) =
    (I (residuePrime v)).relative (padicField v) (w.adicCompletion E)
      ((unitsLocalMap v w 2).hom x)
  rw [unitsLocalMap_relativeInflation v w u]
  exact hI (residuePrime v) (padicField v) (w.adicCompletion E) (u.adicCompletion L) _

end Inflation

section Restriction

variable {F K L : Type u} [Field F] [Field K] [Field L] [NumberField F] [NumberField K]
  [NumberField L] [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  [IsGalois F L]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal] [u.asIdeal.LiesOver v.asIdeal]

/-- Morphism form of `unitsLocalMap_relativeRestriction`. -/
theorem relativeRestriction_comp_unitsLocalMap :
    haveI := IsGalois.tower_top_of_isGalois F K L
    relativeRestriction F K L 2 ≫ unitsLocalMap w u 2 =
      unitsLocalMap v u 2 ≫
        relativeRestriction (padicField v).Carrier (w.adicCompletion K) (u.adicCompletion L) 2 := by
  have := IsGalois.tower_top_of_isGalois F K L
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  refine groupCohomology_map_congr ?_ ?_ 2
  · ext σ x : 2
    apply (algebraMap L (u.adicCompletion L)).injective
    change algebraMap L (u.adicCompletion L) (decompositionHom w u σ x) =
      algebraMap L (u.adicCompletion L) (decompositionHom v u
        (σ.restrictScalars (v.adicCompletion F)) x)
    rw [algebraMap_decompositionHom, algebraMap_decompositionHom]
    rfl
  · intro y
    rfl

/-- **Local components commute with restriction.** For `F ⊆ K ⊆ L` with `L / F` Galois and
finite places `u | w | v`, the local component at `u` of the restriction to `Gal(L/K)` of
`y ∈ H²(Gal(L/F), Lˣ)` is the local restriction from `Gal(L_u/F_v)` to `Gal(L_u/K_w)` of the
local component of `y` at `u`. -/
theorem unitsLocalMap_relativeRestriction (y : relativeCohomology F L 2) :
    haveI := IsGalois.tower_top_of_isGalois F K L
    (unitsLocalMap w u 2).hom ((relativeRestriction F K L 2).hom y) =
      (relativeRestriction (padicField v).Carrier (w.adicCompletion K) (u.adicCompletion L)
        2).hom ((unitsLocalMap v u 2).hom y) :=
  congrArg (fun φ => φ.hom y) (relativeRestriction_comp_unitsLocalMap v w u)

end Restriction

section ArchimedeanValue

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

open Classical in
/-- The `archimedeanCocycleHom` value when a nontrivial element of `Gal(E/F)` fixes `w`, with the
element chosen in its definition. -/
theorem archimedeanCocycleHom_apply_of_exists (w : InfinitePlace E)
    (h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1)
    (f : groupCohomology.cocycles₂ (unitsRepresentation F E)) :
    archimedeanCocycleHom w f = signClass (w.embedding (conjugationValue h.choose f : E)) := by
  change dite _ _ _ = _
  split_ifs
  rfl

open Classical in
/-- The `archimedeanCocycleHom` value when no nontrivial element of `Gal(E/F)` fixes `w`. -/
theorem archimedeanCocycleHom_apply_of_not_exists (w : InfinitePlace E)
    (h : ¬∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1)
    (f : groupCohomology.cocycles₂ (unitsRepresentation F E)) :
    archimedeanCocycleHom w f = 0 := by
  change dite _ _ _ = _
  split_ifs
  rfl

/-- At an infinite place `w` fixed by a nontrivial `c ∈ Gal(E/F)`, the archimedean cocycle
value is the sign class of `w(f(c,c) · f(1,1))`, for this `c`. -/
theorem archimedeanCocycleHom_apply_of_mem {w : InfinitePlace E} {c : E ≃ₐ[F] E}
    (hc : c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w) (hc1 : c ≠ 1)
    (f : groupCohomology.cocycles₂ (unitsRepresentation F E)) :
    archimedeanCocycleHom w f = signClass (w.embedding (conjugationValue c f : E)) := by
  have h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1 := ⟨c, hc, hc1⟩
  rw [archimedeanCocycleHom_apply_of_exists w h,
    (isConj_of_mem_stabilizer w h.choose_spec.1 h.choose_spec.2).ext
      (isConj_of_mem_stabilizer w hc hc1)]

/-- At an infinite place with trivial stabilizer the archimedean cocycle value is zero. -/
theorem archimedeanCocycleHom_apply_of_stabilizer_eq_bot {w : InfinitePlace E}
    (hw : MulAction.stabilizer (E ≃ₐ[F] E) w = ⊥)
    (f : groupCohomology.cocycles₂ (unitsRepresentation F E)) :
    archimedeanCocycleHom w f = 0 := by
  refine archimedeanCocycleHom_apply_of_not_exists w ?_ f
  rintro ⟨c, hc, hc1⟩
  rw [hw] at hc
  exact hc1 (Subgroup.mem_bot.1 hc)

/-- The sign class of a complex number is unchanged by complex conjugation. -/
theorem signClass_conjugate (φ : E →+* ℂ) (z : E) :
    signClass (ComplexEmbedding.conjugate φ z) = signClass (φ z) := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  unfold signClass
  rw [Complex.conj_re]

end ArchimedeanValue

section ArchimedeanInflation

variable {F E L : Type u} [Field F] [Field E] [Field L] [Algebra F E] [Algebra E L]
  [Algebra F L] [IsScalarTower F E L] [Normal F E]

/-- If `c'` is the complex conjugation of `φ : L →+* ℂ`, its restriction to `E` is the complex
conjugation of the restriction of `φ` to `E`. -/
theorem isConj_comp_restrictNormal {φ : L →+* ℂ} {c' : L ≃ₐ[F] L}
    (h : ComplexEmbedding.IsConj φ c') :
    ComplexEmbedding.IsConj (φ.comp (algebraMap E L)) (AlgEquiv.restrictNormalHom E c') := by
  refine RingHom.ext fun x => ?_
  change ComplexEmbedding.conjugate (φ.comp (algebraMap E L)) x =
    φ (algebraMap E L (c'.restrictNormal E x))
  rw [AlgEquiv.restrictNormal_commutes, h.eq,
    ComplexEmbedding.conjugate_coe_eq]
  rfl

/-- The value `f(c,c) · f(1,1)` of the inflation of a 2-cocycle `f` of `Eˣ` at `c ∈ Gal(L/F)` is
the image in `L` of the value of `f` at the restriction of `c` to `E`. -/
theorem conjugationValue_inflation (c' : L ≃ₐ[F] L)
    (f : groupCohomology.cocycles₂ (unitsRepresentation F E)) :
    (conjugationValue c' (groupCohomology.mapCocycles₂ (AlgEquiv.restrictNormalHom E)
        (inflationCoefficients F E L) f) : L) =
      algebraMap E L (conjugationValue (AlgEquiv.restrictNormalHom E c') f : E) := by
  have h1 : AlgEquiv.restrictNormalHom (F := F) (K₁ := L) E 1 = 1 := map_one _
  unfold conjugationValue
  rw [groupCohomology.coe_mapCocycles₂]
  change algebraMap E L ((@Additive.toMul Eˣ (f (AlgEquiv.restrictNormalHom E c',
      AlgEquiv.restrictNormalHom E c')) : E)) *
    algebraMap E L ((@Additive.toMul Eˣ (f (AlgEquiv.restrictNormalHom E 1,
      AlgEquiv.restrictNormalHom E 1)) : E)) = _
  rw [h1, ← map_mul]
  rfl

end ArchimedeanInflation

section PlaceChoices

variable {F E L : Type u} [Field F] [Field E] [Field L] [Algebra F E] [Algebra E L]
  [Algebra F L] [IsScalarTower F E L]

/-- An infinite place of `L` whose restriction to `E` lies above `v` lies above `v`. -/
theorem liesOver_of_comap_eq {u : InfinitePlace L} {w : InfinitePlace E}
    (h : u.comap (algebraMap E L) = w) (v : InfinitePlace F) [w.LiesOver v] : u.LiesOver v := by
  have h' : u.comap (algebraMap F L) = v := by
    rw [IsScalarTower.algebraMap_eq F E L, InfinitePlace.comap_comp, h]
    exact InfinitePlace.LiesOver.comap_eq w v
  constructor
  rw [← h']
  ext x
  rfl

/-- The restriction to `E` of an infinite place of `L` above `v` lies above `v`. -/
theorem liesOver_comap (u : InfinitePlace L) (v : InfinitePlace F) [u.LiesOver v] :
    (u.comap (algebraMap E L)).LiesOver v := by
  have h : (u.comap (algebraMap E L)).comap (algebraMap F E) = v := by
    rw [← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq]
    exact InfinitePlace.LiesOver.comap_eq u v
  exact ⟨by rw [← h]; rfl⟩

variable [NumberField F] [NumberField E] [NumberField L]

variable (L) in
/-- Lift a choice of finite places of `E` above the finite places of `F` to `L`: above `v` take
the place `placeAbove L (wf v)` of `L` above the chosen place `wf v` of `E`. -/
def liftFinitePlaces (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v) :
    ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove L v := fun v =>
  haveI := (wf v).2
  haveI := (placeAbove L (wf v).1).2
  ⟨(placeAbove L (wf v).1).1, Ideal.LiesOver.trans _ (wf v).1.asIdeal _⟩

variable (E) in
/-- Restrict a choice of finite places of `L` above the finite places of `F` to `E`: above `v`
take the place `placeBelow E (wf' v)` of `E` below the chosen place `wf' v` of `L`. -/
def restrictFinitePlaces (wf' : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove L v) :
    ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v := fun v =>
  haveI := (wf' v).2
  ⟨placeBelow E (wf' v).1, Ideal.LiesOver.tower_bot (wf' v).1.asIdeal _ v.asIdeal⟩

variable (L) in
/-- Lift a choice of infinite places of `E` above the infinite places of `F` to `L`: above `v`
take some infinite place of `L` whose restriction to `E` is the chosen place `wi v`. -/
def liftInfinitePlaces (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v) :
    ∀ v : InfinitePlace F, InfinitePlacesAbove L v := fun v =>
  haveI := Algebra.IsAlgebraic.tower_top (K := F) E (A := L)
  ⟨(InfinitePlace.comap_surjective (K := L) (wi v).1).choose,
    liesOver_of_comap_eq (InfinitePlace.comap_surjective (K := L) (wi v).1).choose_spec v⟩

/-- The lifted infinite places restrict to the chosen ones. -/
theorem comap_liftInfinitePlaces (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (v : InfinitePlace F) :
    (liftInfinitePlaces L wi v).1.comap (algebraMap E L) = (wi v).1 :=
  haveI := Algebra.IsAlgebraic.tower_top (K := F) E (A := L)
  (InfinitePlace.comap_surjective (K := L) (wi v).1).choose_spec

variable (E) in
/-- Restrict a choice of infinite places of `L` above the infinite places of `F` to `E`. -/
def restrictInfinitePlaces (wi' : ∀ v : InfinitePlace F, InfinitePlacesAbove L v) :
    ∀ v : InfinitePlace F, InfinitePlacesAbove E v := fun v =>
  ⟨(wi' v).1.comap (algebraMap E L), liesOver_comap (wi' v).1 v⟩

end PlaceChoices

section ArchimedeanTower

variable {F E L : Type u} [Field F] [Field E] [Field L] [NumberField F] [NumberField E]
  [NumberField L] [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]

omit [NumberField E] in
/-- **Archimedean invariants are unchanged by inflation.** For an infinite place `u` of `L`, the
archimedean invariant at `u` of the inflation of `x ∈ H²(Gal(E/F), Eˣ)` equals the archimedean
invariant of `x` at the restriction of `u` to `E`. -/
theorem archimedeanInvariant_relativeInflation (u : InfinitePlace L)
    (x : relativeCohomology F E 2) :
    archimedeanInvariant u ((relativeInflation F E L 2).hom x) =
      archimedeanInvariant (u.comap (algebraMap E L)) x := by
  obtain ⟨f, rfl⟩ := H2π_surjective x
  rw [groupCohomology.H2π_comp_map_apply]
  unfold archimedeanInvariant
  rw [H2Lift_H2π, H2Lift_H2π]
  set ψ := u.embedding.comp (algebraMap E L) with hψ
  have hw : u.comap (algebraMap E L) = InfinitePlace.mk ψ := by
    rw [hψ, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  rw [hw]
  by_cases h : ∃ c' : L ≃ₐ[F] L, c' ∈ MulAction.stabilizer (L ≃ₐ[F] L) u ∧ c' ≠ 1
  · obtain ⟨c', hc'S, hc'1⟩ := h
    rw [archimedeanCocycleHom_apply_of_mem hc'S hc'1, conjugationValue_inflation]
    have hc := isConj_comp_restrictNormal (E := E) (isConj_of_mem_stabilizer u hc'S hc'1)
    change signClass (ψ (conjugationValue (AlgEquiv.restrictNormalHom E c') f : E)) = _
    by_cases hc1 : AlgEquiv.restrictNormalHom E c' = 1
    · rw [hc1] at hc ⊢
      have hψr : ComplexEmbedding.IsReal ψ := ComplexEmbedding.isConj_one_iff.1 hc
      rw [archimedeanCocycleHom_apply_of_stabilizer_eq_bot
        (InfinitePlace.IsUnramified.stabilizer_eq_bot
          (InfinitePlace.IsReal.isUnramified F (InfinitePlace.isReal_iff.2
            (by rwa [InfinitePlace.embedding_mk_eq_of_isReal hψr]))))]
      set a : E := ((@Additive.toMul Eˣ (f (1, 1)) : Eˣ) : E)
      have hval : (conjugationValue 1 f : E) = a * a := rfl
      have hstar : star (ψ a) = ψ a := by
        have := RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hψr) a
        rwa [ComplexEmbedding.conjugate_coe_eq] at this
      have key := signClass_star_mul_self (ψ a)
      rw [hstar] at key
      rw [hval, map_mul]
      exact key
    · have hcS : AlgEquiv.restrictNormalHom E c' ∈
          MulAction.stabilizer (E ≃ₐ[F] E) (InfinitePlace.mk ψ) :=
        (InfinitePlace.mem_stabilizer_mk_iff ψ _).2 (Or.inr hc)
      rw [archimedeanCocycleHom_apply_of_mem hcS hc1]
      rcases InfinitePlace.embedding_mk_eq ψ with he | he
      · rw [he]
      · rw [he, signClass_conjugate]
  · rw [archimedeanCocycleHom_apply_of_not_exists u h]
    have hu : InfinitePlace.IsUnramified F u := by
      rw [InfinitePlace.isUnramified_iff_stabilizer_eq_bot]
      refine (Subgroup.eq_bot_iff_forall _).2 fun c' hc' => ?_
      by_contra hc'1
      exact h ⟨c', hc', hc'1⟩
    have hw' := InfinitePlace.IsUnramified.comap E hu
    rw [hw] at hw'
    rw [archimedeanCocycleHom_apply_of_stabilizer_eq_bot hw'.stabilizer_eq_bot]

/-- **The reciprocity law is unchanged by inflation.** If the local invariant maps are compatible
with inflation, a class `x ∈ H²(Gal(E/F), Eˣ)` satisfies `SumOfInvariantsVanishes` iff its
inflation to `H²(Gal(L/F), Lˣ)` does: for chosen places of `L` (resp. of `E`) the places of `E`
below them (resp. chosen places of `L` above them) have the same local invariants. -/
theorem sumOfInvariantsVanishes_relativeInflation_iff
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)
    (x : relativeCohomology F E 2) :
    SumOfInvariantsVanishes I ((relativeInflation F E L 2).hom x) ↔
      SumOfInvariantsVanishes I x := by
  constructor
  · intro h wf wi
    let wf' := liftFinitePlaces L wf
    let wi' := liftInfinitePlaces L wi
    have hf : (fun v => haveI := (wf' v).2;
        finiteLocalInvariant v (wf' v).1 I ((relativeInflation F E L 2).hom x)) =
        fun v => haveI := (wf v).2; finiteLocalInvariant v (wf v).1 I x := by
      funext v
      have := (wf v).2
      have := (placeAbove L (wf v).1).2
      have : (placeAbove L (wf v).1).1.asIdeal.LiesOver v.asIdeal := (wf' v).2
      exact finiteLocalInvariant_relativeInflation v (wf v).1 (placeAbove L (wf v).1).1 I hI x
    have hi : ∀ v, archimedeanInvariant (wi' v).1 ((relativeInflation F E L 2).hom x) =
        archimedeanInvariant (wi v).1 x := by
      intro v
      rw [archimedeanInvariant_relativeInflation]
      exact congrArg (fun w => archimedeanInvariant w x) (comap_liftInfinitePlaces wi v)
    obtain ⟨h1, h2⟩ := h wf' wi'
    simp only [hi] at h2
    rw [hf] at h1 h2
    exact ⟨h1, h2⟩
  · intro h wf' wi'
    let wf := restrictFinitePlaces E wf'
    let wi := restrictInfinitePlaces E wi'
    have hf : (fun v => haveI := (wf' v).2;
        finiteLocalInvariant v (wf' v).1 I ((relativeInflation F E L 2).hom x)) =
        fun v => haveI := (wf v).2; finiteLocalInvariant v (wf v).1 I x := by
      funext v
      have := (wf' v).2
      have : (placeBelow E (wf' v).1).asIdeal.LiesOver v.asIdeal := (wf v).2
      exact finiteLocalInvariant_relativeInflation v (placeBelow E (wf' v).1) (wf' v).1 I hI x
    have hi : ∀ v, archimedeanInvariant (wi' v).1 ((relativeInflation F E L 2).hom x) =
        archimedeanInvariant (wi v).1 x :=
      fun v => archimedeanInvariant_relativeInflation (wi' v).1 x
    obtain ⟨h1, h2⟩ := h wf wi
    simp only [← hi] at h2
    rw [← hf] at h1 h2
    exact ⟨h1, h2⟩

end ArchimedeanTower

section Hasse

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

omit [NumberField F] [IsGalois F E] in
/-- If `H¹(Gal(E/F), C_E) = 0`, the map `H²(Gal(E/F), Eˣ) → H²(Gal(E/F), J_E)` induced by the
principal embedding is injective (long exact cohomology sequence of `Eˣ → J_E → C_E`). -/
theorem principalIdeleCohomologyMap_two_injective
    (hH1 : Subsingleton (relativeIdeleClassCohomology F E 1 : Type u)) :
    Function.Injective (principalIdeleCohomologyMap F E 2).hom := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hex := (groupCohomology.mapShortComplex₁_exact
    (ideleCoefficientSequence_shortExact F E) (i := 1) rfl).moduleCat_range_eq_ker
  have hk : y ∈ LinearMap.ker (groupCohomology.mapShortComplex₁
      (ideleCoefficientSequence_shortExact F E) (i := 1) rfl).g.hom := hy
  rw [← hex] at hk
  obtain ⟨z, rfl⟩ := hk
  have hz : z = 0 := @Subsingleton.elim (relativeIdeleClassCohomology F E 1 : Type u) hH1 z 0
  rw [hz]
  exact map_zero _

end Hasse

/-- **Hasse principle for `H²(Eˣ)`.** Assume `H¹(Gal(E/F), C_E) = 0` for all finite Galois
extensions of number fields, and that the local invariant maps have the local image laws. A
class `x ∈ H²(Gal(E/F), Eˣ)` whose local components at all finite places vanish and whose
archimedean invariants all vanish is zero. -/
theorem eq_zero_of_local_eq_zero (hH1 : IdeleClassH1Vanishing.{u})
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
    {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] (x : relativeCohomology F E 2)
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
      [w.asIdeal.LiesOver v.asIdeal], (unitsLocalMap v w 2).hom x = 0)
    (hinf : ∀ w : InfinitePlace E, archimedeanInvariant w x = 0) :
    x = 0 := by
  apply principalIdeleCohomologyMap_two_injective (hH1 F E)
  rw [map_zero]
  obtain ⟨f, hf, hf1⟩ := (archimedeanIdeleInvariant_eq_zero_iff
    ((principalIdeleCohomologyMap F E 2).hom x)).1 fun w => by
      exact (archimedeanIdeleInvariant_principalIdeleCohomologyMap w x).trans (hinf w)
  rw [← hf]
  refine H2π_eq_zero_of_ideleLocalMap_eq_zero ?_ ?_ (fun v => (placeAbove E v).1)
    (hwf := fun v => (placeAbove E v).2) f hf1 ?_
  · intro v w hw
    have := isGalois_adicCompletion v w
    have := FiniteExtension.local_finite v w
    exact (I (residuePrime v)).relativeH2_finite (hI _) (padicField v) _
  · intro v w hw
    have := isGalois_adicCompletion v w
    have := FiniteExtension.local_finite v w
    exact le_of_eq ((I (residuePrime v)).relativeH2_card (hI _) (padicField v) _)
  · intro v
    have := (placeAbove E v).2
    rw [hf]
    exact (congrArg (fun φ => φ.hom x)
      (principalIdeleCohomologyMap_comp_ideleLocalMap v (placeAbove E v).1 2)).trans
      (hfin v _)

end Reciprocity

end Langlands.ClassField.Global
