import Langlands.ClassField.Global.LocalUnitVanishing
import Mathlib.RingTheory.DedekindDomain.Different

/-! # Finite support of the local components of idele cohomology in degree two -/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory Limits FundamentalClass

section Units

variable {E : Type u} [Field E] [NumberField E]

/-- An idele has a valuation-unit coordinate at all but finitely many finite places. -/
theorem finite_setOf_ideleCoordinate_not_mem_localUnits (x : IdeleGroup (𝓞 E) E) :
    {w : HeightOneSpectrum (𝓞 E) | ideleCoordinate w x ∉ localUnits w}.Finite := by
  have e1 : ∀ᶠ w in Filter.cofinite,
      (x : AdeleRing (𝓞 E) E).2 w ∈ adicCompletionIntegers E w :=
    ((x : AdeleRing (𝓞 E) E).2).2
  have e2 : ∀ᶠ w in Filter.cofinite,
      ((x⁻¹ : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).2 w ∈ adicCompletionIntegers E w :=
    (((x⁻¹ : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).2).2
  have h1 := Filter.eventually_cofinite.1 e1
  have h2 := Filter.eventually_cofinite.1 e2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hmem
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hmem
  apply hw
  rw [mem_localUnits_iff, ideleCoordinate_val]
  have ha : Valued.v ((x : AdeleRing (𝓞 E) E).2 w) ≤ 1 := hmem.1
  have hb : Valued.v (((x⁻¹ : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).2 w) ≤ 1 := hmem.2
  have hprod : (x : AdeleRing (𝓞 E) E).2 w *
      (((x⁻¹ : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).2 w) = 1 :=
    congrArg (fun y : AdeleRing (𝓞 E) E => y.2 w) (Units.mul_inv x)
  have hv := congrArg Valued.v hprod
  rw [map_mul, map_one] at hv
  apply le_antisymm ha
  by_contra hlt
  push Not at hlt
  have : Valued.v ((x : AdeleRing (𝓞 E) E).2 w) *
      Valued.v (((x⁻¹ : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).2 w) < 1 :=
    mul_lt_one_of_lt_of_le hlt hb
  rw [hv] at this
  exact lt_irrefl _ this

end Units

section Ramification

variable (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- Only finitely many finite places of `E` are ramified over `F`: a ramified place divides the
different ideal of `𝓞 E` over `𝓞 F`, which is nonzero. -/
theorem finite_setOf_ramificationIdx_ne_one :
    {w : HeightOneSpectrum (𝓞 E) | w.asIdeal.ramificationIdx (𝓞 F) ≠ 1}.Finite := by
  have hne : differentIdeal (𝓞 F) (𝓞 E) ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact differentIdeal_ne_bot
  refine (Ideal.finite_factors hne).subset fun w hw => ?_
  by_contra hdvd
  have := (not_dvd_differentIdeal_iff (A := 𝓞 F) (P := w.asIdeal)).1 hdvd
  exact hw (Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F))

omit [NumberField F] [NumberField E] in
variable {F E} in
/-- A finite place of `E` lies over at most one finite place of `F`. -/
theorem subsingleton_setOf_liesOver (w : HeightOneSpectrum (𝓞 E)) :
    {v : HeightOneSpectrum (𝓞 F) | w.asIdeal.LiesOver v.asIdeal}.Subsingleton :=
  fun _ h₁ _ h₂ => HeightOneSpectrum.ext
    ((h₁ : w.asIdeal.LiesOver _).over.trans (h₂ : w.asIdeal.LiesOver _).over.symm)

end Ramification

section Cocycles

/-- A function into `A` whose composite with an injective morphism `ι : A ⟶ B` is a 2-cocycle
is itself a 2-cocycle. -/
theorem mem_cocycles₂_of_injective {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G}
    (ι : A ⟶ B) (hι : Function.Injective ι.hom) (f : G × G → A)
    (hf : (fun x => ι.hom (f x)) ∈ groupCohomology.cocycles₂ B) :
    f ∈ groupCohomology.cocycles₂ A := by
  rw [groupCohomology.mem_cocycles₂_def] at hf ⊢
  intro g h j
  apply hι
  simpa only [map_sub, map_add, map_zero, Rep.hom_comm_apply] using hf g h j

end Cocycles

section LocalVanishing

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- If `w` is unramified over `v`, `H²(Gal(E_w/F_v), E_wˣ)` has at most `[E_w : F_v]` elements,
and every value of a 2-cocycle `f` of `J_E` has a valuation-unit `w`-coordinate, then the local
map at `w` kills the class of `f`. -/
theorem ideleLocalMap_H2π_eq_zero [IsGalois F E] (he : w.asIdeal.ramificationIdx (𝓞 F) = 1)
    [Finite (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2)]
    (hcard : Nat.card (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) ≤
      Module.finrank (v.adicCompletion F) (w.adicCompletion E))
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E))
    (hf : ∀ g h : E ≃ₐ[F] E,
      ideleCoordinate w (@Additive.toMul (IdeleGroup (𝓞 E) E) (f (g, h))) ∈ localUnits w) :
    ideleLocalMap v w 2 (groupCohomology.H2π _ f) = 0 := by
  let f' : (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) ×
      (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) →
      (localUnitsRepresentation v w).V := fun x =>
    Additive.ofMul (⟨ideleCoordinate w (@Additive.toMul (IdeleGroup (𝓞 E) E)
      (f (decompositionHom v w x.1, decompositionHom v w x.2))), hf _ _⟩ : localUnits w)
  have hinj : Function.Injective (localUnitsInclusion v w).hom := fun a b hab =>
    Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective hab))
  have hf' : f' ∈ groupCohomology.cocycles₂ (localUnitsRepresentation v w) := by
    apply mem_cocycles₂_of_injective (localUnitsInclusion v w) hinj
    exact (groupCohomology.mapCocycles₂ (decompositionHom v w) (ideleLocalProjection v w) f).2
  have key : groupCohomology.mapCocycles₂ (decompositionHom v w) (ideleLocalProjection v w) f =
      groupCohomology.mapCocycles₂ (MonoidHom.id _) (localUnitsInclusion v w) ⟨f', hf'⟩ := by
    ext g h
    rfl
  have hz : groupCohomology.H2π (localUnitsRepresentation v w) ⟨f', hf'⟩ = 0 :=
    @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.1
      (isZero_H2_localUnits v w he hcard)) _ _
  rw [groupCohomology.H2π_comp_map_apply, key, ← groupCohomology.H2π_comp_map_apply, hz,
    map_zero]

end LocalVanishing

section Support

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- The finite places `v` of `F` at which a class `c ∈ Hⁿ(Gal(E/F), J_E)` has a nonzero local
component `ideleLocalMap v w n c` for some finite place `w` of `E` over `v`. -/
def ideleLocalSupport [Normal F E] {n : ℕ} (c : relativeIdeleCohomology F E n) :
    Set (HeightOneSpectrum (𝓞 F)) :=
  {v | ∃ (w : HeightOneSpectrum (𝓞 E)) (_ : w.asIdeal.LiesOver v.asIdeal),
    ideleLocalMap v w n c ≠ 0}

/-- **Finite support.** Assume that at every finite place `w | v` the group
`H²(Gal(E_w/F_v), E_wˣ)` is finite with at most `[E_w : F_v]` elements. Then for every class
`c ∈ H²(Gal(E/F), J_E)`, only finitely many finite places `v` of `F` have a place `w | v` with
nonzero local component of `c` at `w`: `ideleLocalSupport c` is finite. -/
theorem finite_setOf_ideleLocalMap_ne_zero [IsGalois F E]
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
      [w.asIdeal.LiesOver v.asIdeal],
      Finite (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2))
    (hcard : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
      [w.asIdeal.LiesOver v.asIdeal],
      Nat.card (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) ≤
        Module.finrank (v.adicCompletion F) (w.adicCompletion E))
    (c : relativeIdeleCohomology F E 2) :
    (ideleLocalSupport c).Finite := by
  induction c using groupCohomology.H2_induction_on with
  | h f =>
  let T : Set (HeightOneSpectrum (𝓞 E)) :=
    (⋃ x : (E ≃ₐ[F] E) × (E ≃ₐ[F] E),
      {w | ideleCoordinate w (@Additive.toMul (IdeleGroup (𝓞 E) E) (f x)) ∉ localUnits w}) ∪
    {w | w.asIdeal.ramificationIdx (𝓞 F) ≠ 1}
  have hT : T.Finite :=
    (Set.finite_iUnion fun x => finite_setOf_ideleCoordinate_not_mem_localUnits _).union
      (finite_setOf_ramificationIdx_ne_one F E)
  refine (hT.biUnion fun w _ => (subsingleton_setOf_liesOver (F := F) w).finite).subset ?_
  rintro v ⟨w, hw, hne⟩
  refine Set.mem_biUnion (x := w) ?_ hw
  by_contra hwT
  apply hne
  simp only [T, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
    not_not] at hwT
  have := hfin v w
  exact ideleLocalMap_H2π_eq_zero v w hwT.2 (hcard v w) f (fun g h => hwT.1 (g, h))

/-- **Finite support** for a choice `wf v` of a place over each finite place `v` of `F`. -/
theorem finite_setOf_ideleLocalMap_choice_ne_zero [IsGalois F E]
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
      [w.asIdeal.LiesOver v.asIdeal],
      Finite (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2))
    (hcard : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
      [w.asIdeal.LiesOver v.asIdeal],
      Nat.card (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) ≤
        Module.finrank (v.adicCompletion F) (w.adicCompletion E))
    (wf : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
    [hwf : ∀ v, (wf v).asIdeal.LiesOver v.asIdeal] (c : relativeIdeleCohomology F E 2) :
    {v : HeightOneSpectrum (𝓞 F) | ideleLocalMap v (wf v) 2 c ≠ 0}.Finite :=
  (finite_setOf_ideleLocalMap_ne_zero hfin hcard c).subset fun v hv => ⟨wf v, hwf v, hv⟩

end Support

end Langlands.ClassField.Global
