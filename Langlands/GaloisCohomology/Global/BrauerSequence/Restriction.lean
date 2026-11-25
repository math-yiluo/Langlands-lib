import Langlands.GaloisCohomology.Global.BrauerSequence.Existence
import Langlands.Global.CompletionPadicTower
import Mathlib.FieldTheory.Normal.Closure

/-!
# Restriction of global Brauer classes to finite extensions

A global Brauer class `x` killed by `m` dies in every finite extension `E ⊆ Ω` of `K` whose local
degrees above the finite places where `x` is nonzero are multiples of `m`, provided the real
localizations of `x` vanish at the real places of `K` below a real place of `E`
(`brauerRestriction_eq_zero'`). With all real localizations zero this is the field
`brauerRestriction_eq_zero` of `BrauerSequenceData`; for `E` without real places the condition is
empty.

The proof is at a finite level. The class is inflated from `H²(Gal(L/K), Lˣ)` for a finite Galois
`L ⊇ E`; restriction to `Gal(Ω/E)` of an inflated class is the inflation of the Library's
restriction `relativeRestriction K E L 2` (`unitsRestriction_unitsTowerMap`,
`unitsRestriction_isoGroupCohomology_inv`). The restricted class is zero by the Library's Hasse
principle for `L / E` (`Reciprocity.eq_zero_of_local_eq_zero`): its finite local invariants are
`[E_u : K_v]` times those of the class (`finiteLocalInvariant_relativeRestriction`, from the local
restriction law of the Library's local invariant family, as in the Library's
`finiteIdeleInvariantRestriction_of_relativeRestriction`); its archimedean invariant at an infinite
place of `L` above a real place of `E` vanishes with that of the class
(`archimedeanInvariant_relativeRestriction_eq_zero`), and at the other infinite places, unramified
over `E`, because their decomposition group in `Gal(L/E)` is trivial.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open Langlands.ClassFieldTheory.Local Langlands.ClassFieldTheory.Global
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

noncomputable section

section FiniteLevel

variable {F K L : Type u} [Field F] [Field K] [Field L] [NumberField F] [NumberField K]
  [NumberField L] [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L] [IsGalois F L]

/-- **Local invariants of a restricted class.** For `F ⊆ K ⊆ L` with `L / F` Galois and finite
places `q | w | v`, the local invariant at `q` over `K` of the restriction of `c` is `[K_w : F_v]`
times its local invariant at `q` over `F` (the units version of the Library's
`finiteIdeleInvariantRestriction_of_relativeRestriction`). -/
theorem finiteLocalInvariant_relativeRestriction
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hRes : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeRestriction)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [q.asIdeal.LiesOver w.asIdeal] [q.asIdeal.LiesOver v.asIdeal]
    (c : relativeCohomology F L 2) :
    haveI := IsGalois.tower_top_of_isGalois F K L
    Reciprocity.finiteLocalInvariant w q I ((relativeRestriction F K L 2).hom c) =
      Module.finrank (v.adicCompletion F) (w.adicCompletion K) •
        Reciprocity.finiteLocalInvariant v q I c := by
  have := IsGalois.tower_top_of_isGalois F K L
  have := isGalois_adicCompletion v q
  have := isGalois_adicCompletion w q
  have := FiniteExtension.local_finite v w
  have := FiniteExtension.local_finite v q
  have := FiniteExtension.local_finite w q
  let := (padicField v).algebra
  let := (towerPadicField v w).algebra
  have := towerPadicField_isScalarTower v w
  have h := hRes (residuePrime v) (padicField v) (towerPadicField v w)
    (q.adicCompletion L) ((unitsLocalMap v q 2).hom c)
  rw [relative_towerPadicField v w I] at h
  change (I (residuePrime w)).relative (padicField w) (q.adicCompletion L)
      ((unitsLocalMap w q 2).hom ((relativeRestriction F K L 2).hom c)) =
    Module.finrank (v.adicCompletion F) (w.adicCompletion K) •
      (I (residuePrime v)).relative (padicField v) (q.adicCompletion L)
        ((unitsLocalMap v q 2).hom c)
  rw [Reciprocity.unitsLocalMap_relativeRestriction v w q]
  exact h

omit [NumberField F] [NumberField K] [NumberField L] in
/-- **Archimedean invariants of a restricted class.** If the archimedean invariant over `F` of `c`
at an infinite place `q` of `L` vanishes, so does the archimedean invariant over `K` of its
restriction. -/
theorem archimedeanInvariant_relativeRestriction_eq_zero (q : InfinitePlace L)
    (c : relativeCohomology F L 2) (hc : Reciprocity.archimedeanInvariant q c = 0) :
    haveI := IsGalois.tower_top_of_isGalois F K L
    Reciprocity.archimedeanInvariant q ((relativeRestriction F K L 2).hom c) = 0 := by
  classical
  have := IsGalois.tower_top_of_isGalois F K L
  obtain ⟨f, rfl⟩ := Reciprocity.H2π_surjective c
  rw [groupCohomology.H2π_comp_map_apply]
  unfold Reciprocity.archimedeanInvariant at hc ⊢
  rw [Reciprocity.H2Lift_H2π] at hc ⊢
  by_cases h : ∃ d : L ≃ₐ[K] L, d ∈ MulAction.stabilizer (L ≃ₐ[K] L) q ∧ d ≠ 1
  · obtain ⟨d, hd, hd1⟩ := h
    have hsmul : (d.restrictScalars F) • q = d • q := rfl
    have hd' : d.restrictScalars F ∈ MulAction.stabilizer (L ≃ₐ[F] L) q := by
      rw [MulAction.mem_stabilizer_iff] at hd ⊢
      rw [hsmul, hd]
    have hd1' : d.restrictScalars F ≠ 1 := fun h1 =>
      hd1 (AlgEquiv.ext fun x => by
        have := congrArg (fun σ : L ≃ₐ[F] L => σ x) h1
        exact this)
    rw [Reciprocity.archimedeanCocycleHom_apply_of_mem hd hd1]
    rw [Reciprocity.archimedeanCocycleHom_apply_of_mem hd' hd1'] at hc
    exact hc
  · exact Reciprocity.archimedeanCocycleHom_apply_of_not_exists q h _

end FiniteLevel

section Compatibility

variable (K E L Ω : Type u) [Field K] [Field E] [Field L] [Field Ω] [Algebra K E] [Algebra K L]
  [Algebra K Ω] [Algebra E L] [Algebra E Ω] [Algebra L Ω] [IsScalarTower K E L]
  [IsScalarTower K E Ω] [IsScalarTower K L Ω] [IsScalarTower E L Ω] [IsGalois K Ω] [IsGalois E Ω]
  [IsGalois K L] [IsGalois E L] [FiniteDimensional K L] [FiniteDimensional E L]

omit [FiniteDimensional K L] [FiniteDimensional E L] in
/-- Restriction to `Gal(Ω/E)` of a class inflated from `Gal(L/K)` is the inflation from `Gal(L/E)`
of its restriction. -/
theorem unitsRestriction_unitsTowerMap (y : cohomology (unitsModule K L) 2) :
    (unitsRestriction K E Ω 2).hom ((unitsTowerMap K L Ω 2).hom y) =
      (unitsTowerMap E L Ω 2).hom ((unitsRestriction K E L 2).hom y) := by
  have hgrp : (BrauerComparison.normalKrullRestriction K L Ω).comp
      (BrauerComparison.krullRestriction K E Ω Ω) =
      (BrauerComparison.krullRestriction K E L L).comp
        (BrauerComparison.normalKrullRestriction E L Ω) := by
    refine ContinuousMonoidHom.ext fun σ => AlgEquiv.ext fun x => ?_
    apply (algebraMap L Ω).injective
    change algebraMap L Ω ((AlgEquiv.restrictNormalHom L)
        (BrauerComparison.krullRestriction K E Ω Ω σ) x) =
      algebraMap L Ω (BrauerComparison.krullRestriction K E L L
        ((AlgEquiv.restrictNormalHom L) σ) x)
    rw [krullRestriction_self_apply K E L]
    change algebraMap L Ω (((BrauerComparison.krullRestriction K E Ω Ω σ).restrictNormal L) x) =
      algebraMap L Ω ((σ.restrictNormal L) x)
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormal_commutes,
      krullRestriction_self_apply K E Ω]
  have e1 := congrArg (fun F => F.hom y) (map_comp (A := unitsModule K L) (B := unitsModule K Ω)
    (C := unitsModule E Ω) (BrauerComparison.normalKrullRestriction K L Ω)
    (underlyingHom _ (BrauerComparison.continuousUnitInflationCoefficients K L Ω))
    (BrauerComparison.krullRestriction K E Ω Ω)
    (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients K E Ω Ω)) 2)
  have e2 := congrArg (fun F => F.hom y) (map_comp (A := unitsModule K L) (B := unitsModule E L)
    (C := unitsModule E Ω) (BrauerComparison.krullRestriction K E L L)
    (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients K E L L))
    (BrauerComparison.normalKrullRestriction E L Ω)
    (underlyingHom _ (BrauerComparison.continuousUnitInflationCoefficients E L Ω)) 2)
  refine e1.symm.trans (Eq.trans ?_ e2)
  refine congrArg (fun F => F.hom y) (map_congr (A := unitsModule K L) (B := unitsModule E Ω) _ _
    hgrp ?_ 2)
  intro b
  exact Additive.toMul.injective (Units.ext rfl)

/-- On a finite level, the restriction of the cochain model is the Library's
`relativeRestriction`. -/
theorem unitsRestriction_isoGroupCohomology_inv (a : relativeCohomology K L 2) :
    (unitsRestriction K E L 2).hom ((isoGroupCohomology (unitsModule K L) 2).inv.hom a) =
      (isoGroupCohomology (unitsModule E L) 2).inv.hom ((relativeRestriction K E L 2).hom a) := by
  set y := (isoGroupCohomology (unitsModule K L) 2).inv.hom a with hy
  have h1 := congrArg (fun f => f.hom y)
    (map_comp_toGroupCohomology (A := unitsModule K L) (B := unitsModule E L)
      (BrauerComparison.krullRestriction K E L L)
      (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients K E L L)) 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [← isoGroupCohomology_hom, ← isoGroupCohomology_hom, hy, Iso.inv_hom_id_apply] at h1
  have h3 : (isoGroupCohomology (unitsModule E L) 2).hom.hom ((unitsRestriction K E L 2).hom y) =
      (relativeRestriction K E L 2).hom a :=
    h1.trans (congrArg (fun F => F.hom a) (Reciprocity.groupCohomology_map_congr
      (MonoidHom.ext fun σ => AlgEquiv.ext fun x => krullRestriction_self_apply K E L σ x)
      (φ' := restrictionCoefficients K E L)
      (fun b => by exact Additive.toMul.injective (Units.ext rfl)) 2))
  rw [← h3, Iso.hom_inv_id_apply]

end Compatibility

section BrauerRestriction

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω)

/-- **Restriction to extensions with large local degrees.** A global Brauer class `x` killed by `m`
dies in every finite extension `E ⊆ Ω` of `K` whose local degrees above the finite places where `x`
is nonzero are multiples of `m`, provided the real localizations of `x` vanish at the real places of
`K` below a real place of `E`. This holds when all real localizations of `x` vanish (the field
`brauerRestriction_eq_zero` of `BrauerSequenceData`) and when `E` has no real place. -/
theorem brauerRestriction_eq_zero' (E : IntermediateField K Ω) [FiniteDimensional K E]
    (x : cohomology (unitsModule K Ω) 2) (m : ℕ) (hm : m • x = 0)
    (hreal : ∀ u : InfinitePlace E, u.IsReal →
      realBrauerLocalization ι (u.comap (algebraMap K E)) 2 x = 0)
    (hloc : ∀ v, brauerLocalization ι v 2 x ≠ 0 → ∀ (w : HeightOneSpectrum (𝓞 E))
      [w.asIdeal.LiesOver v.asIdeal], m ∣ localDegree E v w) :
    brauerRestriction E x = 0 := by
  classical
  obtain ⟨E₀, a₀, rfl⟩ := exists_unitsInflation_eq 2 x
  -- a finite Galois level `L` containing `E` and `E₀`
  let L : IntermediateField K Ω := E₀.toIntermediateField ⊔ IntermediateField.normalClosure K E Ω
  have hE : E ≤ L := (IntermediateField.le_normalClosure E).trans le_sup_right
  have : FiniteDimensional K L := inferInstance
  have : IsGalois K L := inferInstance
  have : NumberField L := NumberField.of_module_finite K L
  have : NumberField E := NumberField.of_module_finite K E
  set a : relativeCohomology K L 2 :=
    (unitsInflationOfLE (le_sup_left : E₀.toIntermediateField ≤ L) 2).hom a₀ with ha
  have hx : (unitsInflation E₀.toIntermediateField 2).hom a₀ = (unitsInflation L 2).hom a := by
    rw [ha, ← unitsInflationOfLE_comp_unitsInflation (le_sup_left : E₀.toIntermediateField ≤ L) 2]
    rfl
  rw [hx] at hm hreal hloc ⊢
  set x := (unitsInflation L 2).hom a with hxdef
  -- the tower `K ⊆ E ⊆ L ⊆ Ω`
  let _ : Algebra E L := (IntermediateField.inclusion hE).toRingHom.toAlgebra
  have : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower E L Ω := IsScalarTower.of_algebraMap_eq' rfl
  have : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  have : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  have : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite K E L
  -- restriction of an inflated class
  have hres : brauerRestriction E x = (unitsTowerMap E L Ω 2).hom
      ((isoGroupCohomology (unitsModule E L) 2).inv.hom ((relativeRestriction K E L 2).hom a)) := by
    rw [← unitsRestriction_isoGroupCohomology_inv, ← unitsRestriction_unitsTowerMap, hxdef,
      unitsInflation_apply_eq]
    rfl
  rw [hres]
  suffices hb : (relativeRestriction K E L 2).hom a = 0 by rw [hb, map_zero, map_zero]
  have hI := brauerInvariantFamily_spec.{u}
  have hImages : ∀ (p : ℕ) [Fact p.Prime], (brauerInvariantFamily.{u} p).RelativeImages :=
    fun p _ => (hI p).1.2.1
  have hcongr : ∀ (v : HeightOneSpectrum (𝓞 K)) (w₁ w₂ : HeightOneSpectrum (𝓞 L))
      [w₁.asIdeal.LiesOver v.asIdeal] [w₂.asIdeal.LiesOver v.asIdeal], w₁ = w₂ →
      Reciprocity.finiteLocalInvariant v w₁ brauerInvariantFamily.{u} a =
        Reciprocity.finiteLocalInvariant v w₂ brauerInvariantFamily.{u} a := by
    intro v w₁ w₂ _ _ h
    subst h
    rfl
  refine Reciprocity.eq_zero_of_local_eq_zero ideleClassH1Vanishing brauerInvariantFamily.{u}
    hImages _ (fun u q _ => ?_) (fun q => ?_)
  · -- finite places: the local invariant is `[E_u : K_v]` times that of `x`
    let v : HeightOneSpectrum (𝓞 K) := u.under (𝓞 K)
    have : u.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
    have : q.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans q.asIdeal u.asIdeal v.asIdeal
    have h0 : Reciprocity.finiteLocalInvariant u q brauerInvariantFamily.{u}
        ((relativeRestriction K E L 2).hom a) = 0 := by
      rw [finiteLocalInvariant_relativeRestriction brauerInvariantFamily.{u}
        (fun p _ => (hI p).1.2.2.2) v u q a]
      have hinv : Reciprocity.finiteLocalInvariant v q brauerInvariantFamily.{u} a =
          localInvariant ι v x := by
        obtain ⟨ι', hι'⟩ := exists_localPlace_eq L v ⟨q, inferInstance⟩
        rw [← localInvariant_eq ι ι' v, hxdef, localInvariant_unitsInflation ι' L v
          brauerInvariantFamily.{u} (fun p _ => (hI p).2) (fun p _ => (hI p).1.2.2.1),
          hcongr v _ _ hι']
      rw [hinv]
      by_cases hv : brauerLocalization ι v 2 x = 0
      · rw [localInvariant_apply, hv, map_zero, smul_zero]
      · obtain ⟨k, hk⟩ := hloc v hv u
        have hmx : m • localInvariant ι v x = 0 := by rw [← map_nsmul, hm, map_zero]
        change Module.finrank (v.adicCompletion K) (u.adicCompletion E) = m * k at hk
        rw [hk, mul_nsmul, hmx, smul_zero]
    have := isGalois_adicCompletion u q
    have := FiniteExtension.local_finite u q
    exact (injective_iff_map_eq_zero _).1 ((hImages (residuePrime u)) (padicField u) _).1 _ h0
  · -- infinite places
    by_cases hq : (q.comap (algebraMap E L)).IsReal
    · -- below a real place of `E`: the archimedean invariant of `x` vanishes
      apply archimedeanInvariant_relativeRestriction_eq_zero
      let w : InfinitePlace K := q.comap (algebraMap K L)
      have : q.LiesOver w := ⟨rfl⟩
      obtain ⟨ι', hι'⟩ := exists_realPlace_eq L w q
      have h0 := realLocalInvariant_unitsInflation ι' L w a
      rw [hι'] at h0
      have hw : realBrauerLocalization ι w 2 x = 0 := by
        have hcomp : (q.comap (algebraMap E L)).comap (algebraMap K E) = w := by
          rw [← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq K E L]
        rw [← hcomp]
        exact hreal (q.comap (algebraMap E L)) hq
      rw [← h0, realLocalInvariant_eq ι ι', realLocalInvariant, ← hxdef, hw, realInvariant_zero]
    · -- otherwise `q` is unramified over `E`: its decomposition group in `Gal(L/E)` is trivial
      obtain ⟨f, hf⟩ := Reciprocity.H2π_surjective ((relativeRestriction K E L 2).hom a)
      rw [← hf]
      unfold Reciprocity.archimedeanInvariant
      rw [Reciprocity.H2Lift_H2π]
      refine Reciprocity.archimedeanCocycleHom_apply_of_not_exists q ?_ _
      rintro ⟨d, hd, hd1⟩
      have hram : ¬ q.IsUnramified E := by
        rw [InfinitePlace.isUnramified_iff_stabilizer_eq_bot]
        intro h
        apply hd1
        have hd' : d ∈ (⊥ : Subgroup (L ≃ₐ[E] L)) := h ▸ hd
        exact Subgroup.mem_bot.1 hd'
      rw [InfinitePlace.not_isUnramified_iff] at hram
      exact hq hram.2

end BrauerRestriction

end

end Langlands.GaloisCohomology
