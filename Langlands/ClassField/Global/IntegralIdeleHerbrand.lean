import Langlands.ClassField.Global.IntegralIdeleCoefficients
import Langlands.ClassField.Global.IdeleLocalInjectivity
import Langlands.ClassField.Global.IdeleArchimedean
import Langlands.ClassField.Global.LocalUnitHerbrandProof
import Langlands.ClassField.Global.ArchimedeanHerbrandFactor
import Langlands.Cohomology.ProductDecomposition
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.ClassField.Global.IntegralIdeleHerbrandStatement
import Langlands.ClassField.Global.IdeleClassBaseImage

/-! # The Herbrand quotient of the integral ideles

The integral ideles `J∞` decompose, as a representation of `G = Gal(E/F)`, into the semilocal
unit modules over the finite places `v` of `F`, each coinduced from `U_w` along
`decompositionHom v w`, and the semilocal modules over the orbits of infinite places, each
coinduced from `E_wˣ` along the stabilizer of `w`. Hence `H¹` and `H²` of `J∞` are the
products of the local cohomology groups.
-/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory groupCohomology FundamentalClass
open Langlands.Cohomology.ProductDecomposition Langlands.Cohomology.Herbrand

namespace IntegralIdeleHerbrand

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] localUnitsAction integralIdeleAction

section Finite

variable (w : HeightOneSpectrum (𝓞 E))

/-- The finite coordinate at `w` of an integral idele, as a valuation unit. -/
def unitCoordinate : integralIdeles E →* localUnits w where
  toFun x := ⟨ideleCoordinate w (x : IdeleGroup (𝓞 E) E),
    (mem_integralIdeles_iff_localUnits _).1 x.2 w⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp] theorem coe_unitCoordinate (x : integralIdeles E) :
    ((unitCoordinate w x : localUnits w) : (w.adicCompletion E)ˣ) =
      ideleCoordinate w (x : IdeleGroup (𝓞 E) E) := rfl

variable [Normal F E] (v : HeightOneSpectrum (𝓞 F)) [w.asIdeal.LiesOver v.asIdeal]

/-- The local projection `J∞ → U_w`, a morphism of representations of `Gal(E_w/F_v)`. -/
def integralLocalProjection :
    Rep.res (decompositionHom v w) (integralIdeleRepresentation F E) ⟶
      localUnitsRepresentation v w :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul (unitCoordinate w (@Additive.toMul (integralIdeles E) x))
          map_add' := fun x y => congrArg Additive.ofMul (map_mul (unitCoordinate w)
            (@Additive.toMul (integralIdeles E) x) (@Additive.toMul (integralIdeles E) y))
          map_smul' := fun r x => congrArg Additive.ofMul (map_zpow (unitCoordinate w)
            (@Additive.toMul (integralIdeles E) x) r.down) }
      isIntertwining' := fun σ => by
        ext x
        exact congrArg Additive.ofMul (Subtype.ext
          (ideleCoordinate_relativeIdeleAut_decompositionHom v w σ
            ((@Additive.toMul (integralIdeles E) x : integralIdeles E) : IdeleGroup (𝓞 E) E))) }

/-- The semilocal projection `J∞ ⟶ Coind(U_w)`, `x ↦ (g ↦ (g • x)_w)`. -/
def integralSemilocalProjection :
    integralIdeleRepresentation F E ⟶
      Rep.coind (decompositionHom v w) (localUnitsRepresentation v w) :=
  Rep.resCoindToHom _ _ _ (integralLocalProjection w v)

theorem coindLocalUnitsInclusion_integralSemilocalProjection
    (x : integralIdeleRepresentation F E) :
    (coindLocalUnitsInclusion v w).hom ((integralSemilocalProjection w v).hom x) =
      (ideleSemilocalProjection v w).hom ((integralIdeleInclusion F E).hom x) := by
  apply Subtype.ext
  funext g
  rfl

end Finite

section Places

variable (F E) in
/-- The index set: finite places of `F` and orbits of infinite places of `E`. -/
abbrev PlaceIndex := HeightOneSpectrum (𝓞 F) ⊕ infinitePlaceOrbits F E

/-- The chosen place of `E` above a finite place `v` of `F`. -/
abbrev finitePlace (v : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 E) :=
  (placeAbove E v).1

instance liesOver_finitePlace (v : HeightOneSpectrum (𝓞 F)) :
    (finitePlace (E := E) v).asIdeal.LiesOver v.asIdeal :=
  (placeAbove E v).2

/-- The chosen representative of an orbit of infinite places. -/
abbrev infinitePlace (O : infinitePlaceOrbits F E) : InfinitePlace E := O.out

variable [Normal F E]

/-- The local factor of `J∞` at an index. -/
def factor : PlaceIndex F E →
    Rep.{u} NormalizedTwoCocycle.CoefficientScalars.{u} (E ≃ₐ[F] E)
  | .inl v => Rep.coind (decompositionHom v (finitePlace v))
      (localUnitsRepresentation v (finitePlace v))
  | .inr O => Rep.coind (MulAction.stabilizer (E ≃ₐ[F] E) (infinitePlace O)).subtype
      (infiniteLocalRepresentation F (infinitePlace O))

/-- The projection of `J∞` to its local factor at an index. -/
def projection : ∀ i : PlaceIndex F E, integralIdeleRepresentation F E ⟶ factor i
  | .inl v => integralSemilocalProjection (finitePlace v) v
  | .inr O => integralIdeleInclusion F E ≫ infiniteSemilocalProjection F (infinitePlace O)

omit [NumberField F] [NumberField E] [Normal F E] in
theorem infinitePlace_mem_orbit (w : InfinitePlace E) :
    ∃ g : E ≃ₐ[F] E, infinitePlaceEquiv g.toRingEquiv
      (infinitePlace (F := F) (Quotient.mk'' w : infinitePlaceOrbits F E)) = w := by
  have h : (infinitePlace (F := F) (Quotient.mk'' w : infinitePlaceOrbits F E)) ∈
      MulAction.orbit (E ≃ₐ[F] E) w :=
    Quotient.exact (Quotient.out_eq (Quotient.mk'' w : infinitePlaceOrbits F E))
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ?_⟩
  rw [infinitePlaceEquiv_eq_inv_smul, ← hg, inv_smul_smul]

variable [IsGalois F E]

/-- An integral idele whose local projections all vanish is trivial. -/
theorem eq_zero_of_projection_eq_zero (x : integralIdeleRepresentation F E)
    (hx : ∀ i, (projection i).hom x = 0) : x = 0 := by
  set y : IdeleGroup (𝓞 E) E :=
    ((@Additive.toMul (integralIdeles E) x : integralIdeles E) : IdeleGroup (𝓞 E) E) with hy
  suffices h : y = 1 by
    apply Additive.toMul.injective
    exact Subtype.ext h
  have hinf : (y : AdeleRing (𝓞 E) E).1 = 1 := by
    rw [ideleInfinite_eq_one_iff]
    intro w
    obtain ⟨g, hg⟩ := infinitePlace_mem_orbit (F := F) w
    have h0 := hx (.inr (Quotient.mk'' w))
    have h1 : (infiniteSemilocalProjection F (infinitePlace (F := F)
        (Quotient.mk'' w : infinitePlaceOrbits F E))).hom ((integralIdeleInclusion F E).hom x) =
        (infiniteSemilocalProjection F (infinitePlace (F := F)
          (Quotient.mk'' w : infinitePlaceOrbits F E))).hom
          ((integralIdeleInclusion F E).hom 0) := by
      rw [map_zero, map_zero]
      exact h0
    have h2 := ideleInfiniteCoordinate_eq_of_infiniteSemilocalProjection_eq _ h1 g
    rw [hg] at h2
    exact h2.trans (map_one _)
  refine idele_ext (hinf.trans rfl) fun w => ?_
  have h0 : (integralSemilocalProjection (finitePlace (placeBelow F w)) (placeBelow F w)).hom x =
      0 := hx (.inl (placeBelow F w))
  have h1 : (ideleSemilocalProjection (placeBelow F w) (finitePlace (placeBelow F w))).hom
      ((integralIdeleInclusion F E).hom x) =
      (ideleSemilocalProjection (placeBelow F w) (finitePlace (placeBelow F w))).hom
        ((integralIdeleInclusion F E).hom 0) := by
    rw [map_zero, map_zero, ← coindLocalUnitsInclusion_integralSemilocalProjection, h0, map_zero]
  exact (ideleCoordinate_eq_of_ideleSemilocalProjection_eq _ _ h1 w).trans (map_one _)


/-- The finite coordinate of the idele with infinite coordinates `a` is `1`. -/
theorem ideleCoordinate_ideleOfInfiniteCoordinates (a : ∀ w : InfinitePlace E, (w.Completion)ˣ)
    (w : HeightOneSpectrum (𝓞 E)) : ideleCoordinate w (ideleOfInfiniteCoordinates a) = 1 :=
  Units.ext rfl

/-- The infinite coordinate of an idele with infinite part `1` is `1`. -/
theorem ideleInfiniteCoordinate_ideleOfCoordinates
    (a : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (ha : {w | a w ∉ localUnits w}.Finite) (w : InfinitePlace E) :
    ideleInfiniteCoordinate w (ideleOfCoordinates a ha) = 1 :=
  Units.ext rfl

omit [NumberField F] [NumberField E] [Normal F E] [IsGalois F E] in
theorem quotient_mk_infinitePlaceEquiv (g : E ≃ₐ[F] E) (O : infinitePlaceOrbits F E) :
    (Quotient.mk'' (infinitePlaceEquiv g.toRingEquiv (infinitePlace O)) :
      infinitePlaceOrbits F E) = O := by
  rw [infinitePlaceEquiv_eq_inv_smul]
  conv_rhs => rw [← Quotient.out_eq O]
  exact Quotient.sound ⟨g⁻¹, rfl⟩

/-- Integral ideles with prescribed local components exist. -/
theorem exists_projection_eq (b : ∀ i : PlaceIndex F E, factor i) :
    ∃ x : integralIdeleRepresentation F E, ∀ i, (projection i).hom x = b i := by
  classical
  let sfin : HeightOneSpectrum (𝓞 F) → IdeleGroup (𝓞 E) E := fun v =>
    letI : Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (finitePlace (E := E) v)).range) :=
      Fintype.ofFinite _
    @Additive.toMul (IdeleGroup (𝓞 E) E) ((ideleSemilocalSection v (finitePlace v)).hom
      ((coindLocalUnitsInclusion v (finitePlace v)).hom (b (.inl v))))
  let sinf : infinitePlaceOrbits F E → IdeleGroup (𝓞 E) E := fun O =>
    letI : Fintype ((E ≃ₐ[F] E) ⧸
        (MulAction.stabilizer (E ≃ₐ[F] E) (infinitePlace O)).subtype.range) :=
      Fintype.ofFinite _
    @Additive.toMul (IdeleGroup (𝓞 E) E)
      ((infiniteSemilocalSection F (infinitePlace O)).hom (b (.inr O)))
  -- the projection of a section is the given element
  have hsfin : ∀ v : HeightOneSpectrum (𝓞 F),
      (ideleSemilocalProjection v (finitePlace v)).hom (Additive.ofMul (sfin v)) =
        (coindLocalUnitsInclusion v (finitePlace v)).hom (b (.inl v)) := fun v => by
    let : Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (finitePlace (E := E) v)).range) :=
      Fintype.ofFinite _
    exact ideleSemilocalProjection_ideleSemilocalSection v (finitePlace v) _
  have hsinf : ∀ O : infinitePlaceOrbits F E,
      (infiniteSemilocalProjection F (infinitePlace O)).hom (Additive.ofMul (sinf O)) =
        b (.inr O) := fun O => by
    let : Fintype ((E ≃ₐ[F] E) ⧸
        (MulAction.stabilizer (E ≃ₐ[F] E) (infinitePlace O)).subtype.range) :=
      Fintype.ofFinite _
    exact infiniteSemilocalProjection_infiniteSemilocalSection (infinitePlace O) _
  let afin : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ := fun w =>
    ideleCoordinate w (sfin (placeBelow F w))
  let ainf : ∀ w : InfinitePlace E, (w.Completion)ˣ := fun w =>
    ideleInfiniteCoordinate w (sinf (Quotient.mk'' w))
  have hafin : ∀ w, afin w ∈ localUnits w := fun w => by
    have hx : ∀ g, Additive.toMul (((ideleSemilocalProjection (placeBelow F w)
        (finitePlace (placeBelow F w))).hom (Additive.ofMul (sfin (placeBelow F w)))).1 g) ∈
        localUnits (finitePlace (placeBelow F w)) := fun g => by
      rw [hsfin]
      exact ((b (.inl (placeBelow F w)) :
        Rep.coind (decompositionHom (placeBelow F w) (finitePlace (placeBelow F w)))
          (localUnitsRepresentation (placeBelow F w) (finitePlace (placeBelow F w)))).1 g).toMul.2
    exact ideleCoordinate_mem_localUnits_of_ideleSemilocalProjection _ _ _ hx w
  have hfin : {w | afin w ∉ localUnits w}.Finite := by
    simp [hafin]
  let z : IdeleGroup (𝓞 E) E := ideleOfCoordinates afin hfin * ideleOfInfiniteCoordinates ainf
  have hzfin : ∀ w, ideleCoordinate w z = afin w := fun w => by
    simp [z, ideleCoordinate_ideleOfInfiniteCoordinates]
  have hzinf : ∀ w, ideleInfiniteCoordinate w z = ainf w := fun w => by
    simp [z, ideleInfiniteCoordinate_ideleOfCoordinates]
  have hz : z ∈ integralIdeles E := by
    rw [mem_integralIdeles_iff_localUnits]
    intro w
    rw [hzfin]
    exact hafin w
  let x : integralIdeleRepresentation F E := Additive.ofMul (⟨z, hz⟩ : integralIdeles E)
  refine ⟨x, ?_⟩
  rintro (v | O)
  · apply coindLocalUnitsInclusion_injective v (finitePlace v)
    change (coindLocalUnitsInclusion v (finitePlace v)).hom
        ((integralSemilocalProjection (finitePlace v) v).hom x) = _
    rw [coindLocalUnitsInclusion_integralSemilocalProjection (finitePlace v) v x, ← hsfin]
    apply Subtype.ext
    funext g
    change Additive.ofMul (ideleCoordinate (finitePlace v) (relativeIdeleAut F E g z)) =
      Additive.ofMul (ideleCoordinate (finitePlace v) (relativeIdeleAut F E g (sfin v)))
    congr 1
    refine ideleCoordinate_relativeIdeleAut_eq v g (fun u _ => ?_) (finitePlace v)
    rw [hzfin]
    change ideleCoordinate u (sfin (placeBelow F u)) = _
    rw [placeBelow_eq v u]
  · change (infiniteSemilocalProjection F (infinitePlace O)).hom
        ((integralIdeleInclusion F E).hom x) = _
    rw [← hsinf]
    apply Subtype.ext
    funext g
    change Additive.ofMul (ideleInfiniteCoordinate (infinitePlace O) (relativeIdeleAut F E g z)) =
      Additive.ofMul (ideleInfiniteCoordinate (infinitePlace O)
        (relativeIdeleAut F E g (sinf O)))
    congr 1
    rw [ideleInfiniteCoordinate_relativeIdeleAut_eq_iff, hzinf]
    change ideleInfiniteCoordinate _ (sinf (Quotient.mk'' _)) = _
    rw [quotient_mk_infinitePlaceEquiv]

end Places


section Counting

/-- A Herbrand quotient transported along equivalences of cohomology groups, possibly for
different groups. -/
theorem hasHerbrandQuotient_of_equiv {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep.{u} k G} {B : Rep.{u} k H} (e₁ : groupCohomology A 1 ≃ groupCohomology B 1)
    (e₂ : groupCohomology A 2 ≃ groupCohomology B 2) {q : ℚ} (h : HasHerbrandQuotient A q) :
    HasHerbrandQuotient B q := by
  obtain ⟨h₁, h₂, h⟩ := h
  refine ⟨e₁.finite_iff.1 h₁, e₂.finite_iff.1 h₂, ?_⟩
  rw [← Nat.card_congr e₁, ← Nat.card_congr e₂, h]

theorem subsingleton_of_equiv {X Y : Type*} (e : X ≃ Y) [Subsingleton X] : Subsingleton Y :=
  e.symm.subsingleton

variable [Normal F E]

/-- Shapiro's lemma for the finite factors. -/
def factorEquivFinite (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    groupCohomology (factor (F := F) (E := E) (.inl v)) n ≃
      groupCohomology (localUnitsRepresentation v (finitePlace (E := E) v)) n :=
  (Shapiro.shapiroIsoOf (decompositionHom_injective v (finitePlace v)) _ n).toLinearEquiv.toEquiv

/-- Shapiro's lemma for the infinite factors. -/
def factorEquivInfinite (O : infinitePlaceOrbits F E) (n : ℕ) :
    groupCohomology (factor (F := F) (E := E) (.inr O)) n ≃
      groupCohomology (infiniteLocalRepresentation F (infinitePlace O)) n :=
  (Shapiro.shapiroIsoOf Subtype.val_injective _ n).toLinearEquiv.toEquiv

variable [IsGalois F E]

theorem hasHerbrandQuotient_factor_inl [IsCyclic (E ≃ₐ[F] E)] (v : HeightOneSpectrum (𝓞 F)) :
    HasHerbrandQuotient (factor (F := F) (E := E) (.inl v)) 1 := by
  have : IsCyclic (finitePlace (E := E) v |>.adicCompletion E ≃ₐ[v.adicCompletion F]
      (finitePlace (E := E) v).adicCompletion E) :=
    isCyclic_of_injective _ (decompositionHom_injective v (finitePlace v))
  exact hasHerbrandQuotient_of_equiv (factorEquivFinite v 1).symm (factorEquivFinite v 2).symm
    (LocalUnitHerbrand.hasHerbrandQuotient_localUnits v (finitePlace v))

theorem subsingleton_factor_inl (v : HeightOneSpectrum (𝓞 F))
    (he : (finitePlace (E := E) v).asIdeal.ramificationIdx (𝓞 F) = 1) :
    Subsingleton (groupCohomology (factor (F := F) (E := E) (.inl v)) 1) ∧
      Subsingleton (groupCohomology (factor (F := F) (E := E) (.inl v)) 2) := by
  obtain ⟨h₁, h₂⟩ := unramifiedCompletionUnitVanishing F E v (finitePlace v) he
  exact ⟨subsingleton_of_equiv (factorEquivFinite v 1).symm,
    subsingleton_of_equiv (factorEquivFinite v 2).symm⟩

omit [Normal F E] [IsGalois F E] in
/-- The finite places of `F` whose chosen place above is ramified. -/
theorem finite_ramifiedPlaces :
    {v : HeightOneSpectrum (𝓞 F) |
      (finitePlace (E := E) v).asIdeal.ramificationIdx (𝓞 F) ≠ 1}.Finite := by
  refine ((finite_setOf_ramificationIdx_ne_one F E).image (placeBelow F)).subset ?_
  intro v hv
  exact ⟨finitePlace v, hv, placeBelow_eq v (finitePlace v)⟩

/-- The decomposition of the cohomology of `J∞` in degrees one and two. -/
noncomputable def cohomologyEquiv (n : ℕ) (hn : n = 1 ∨ n = 2) :
    integralIdeleCohomology F E n ≃ ∀ i : PlaceIndex F E, groupCohomology (factor i) n :=
  productEquiv eq_zero_of_projection_eq_zero exists_projection_eq n hn

/-- The cohomology groups of `J∞` are finite and their orders are the products of the local
orders over the finitely many ramified finite places and all infinite orbits. -/
theorem integralIdeleHerbrand [IsCyclic (E ≃ₐ[F] E)]
    (harch : ∀ w : InfinitePlace E, HasHerbrandQuotient (infiniteLocalRepresentation F w)
      (Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w))) :
    Finite (integralIdeleCohomology F E 1) ∧ Finite (integralIdeleCohomology F E 2) ∧
      Nat.card (integralIdeleCohomology F E 2) =
        archimedeanHerbrandFactor F E * Nat.card (integralIdeleCohomology F E 1) := by
  classical
  let := Fintype.ofFinite (infinitePlaceOrbits F E)
  set T := (finite_ramifiedPlaces (F := F) (E := E)).toFinset
  set S : Finset (PlaceIndex F E) := T.image Sum.inl ∪ Finset.univ.image Sum.inr
  have hS : ∀ n, n = 1 ∨ n = 2 → ∀ i ∉ S, Subsingleton (groupCohomology (factor i) n) := by
    rintro n hn (v | O) hi
    · have hv : v ∉ T := fun hv => hi (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv))
      have he : (finitePlace (E := E) v).asIdeal.ramificationIdx (𝓞 F) = 1 := by
        by_contra h
        exact hv ((Set.Finite.mem_toFinset _).2 h)
      rcases hn with rfl | rfl
      · exact (subsingleton_factor_inl v he).1
      · exact (subsingleton_factor_inl v he).2
    · exact absurd (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ O))) hi
  let q : PlaceIndex F E → ℕ := Sum.elim (fun _ => 1)
    (fun O => Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) (infinitePlace O)))
  have hloc : ∀ i : PlaceIndex F E, Finite (groupCohomology (factor i) 1) ∧
      Finite (groupCohomology (factor i) 2) ∧
      Nat.card (groupCohomology (factor i) 2) = q i * Nat.card (groupCohomology (factor i) 1) := by
    rintro (v | O)
    · obtain ⟨h₁, h₂, h₃⟩ := hasHerbrandQuotient_factor_inl (F := F) (E := E) v
      refine ⟨h₁, h₂, ?_⟩
      simp only [q, Sum.elim_inl, one_mul]
      exact_mod_cast h₃.trans (one_mul _)
    · obtain ⟨h₁, h₂, h₃⟩ := hasHerbrandQuotient_of_equiv (factorEquivInfinite O 1).symm
        (factorEquivInfinite O 2).symm (harch (infinitePlace O))
      exact ⟨h₁, h₂, by simp only [q, Sum.elim_inr]; exact_mod_cast h₃⟩
  have e₁ := cohomologyEquiv (F := F) (E := E) 1 (Or.inl rfl)
  have e₂ := cohomologyEquiv (F := F) (E := E) 2 (Or.inr rfl)
  have hS₁ := hS 1 (Or.inl rfl)
  have hS₂ := hS 2 (Or.inr rfl)
  have hfin₁ : Finite (∀ i : PlaceIndex F E, groupCohomology (factor i) 1) :=
    finite_pi S hS₁ fun i _ => (hloc i).1
  have hfin₂ : Finite (∀ i : PlaceIndex F E, groupCohomology (factor i) 2) :=
    finite_pi S hS₂ fun i _ => (hloc i).2.1
  refine ⟨Finite.of_equiv _ e₁.symm, Finite.of_equiv _ e₂.symm, ?_⟩
  rw [Nat.card_congr e₁, Nat.card_congr e₂, natCard_pi_eq_prod S hS₁, natCard_pi_eq_prod S hS₂,
    Finset.prod_congr rfl (fun i _ => (hloc i).2.2), Finset.prod_mul_distrib]
  congr 1
  have hdisj : Disjoint (T.image (Sum.inl : _ → PlaceIndex F E))
      (Finset.univ.image (Sum.inr : _ → PlaceIndex F E)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨O, -, h⟩ := Finset.mem_image.1 hb
    exact Sum.inr_ne_inl h
  rw [Finset.prod_union hdisj, Finset.prod_image (fun _ _ _ _ h => Sum.inl_injective h),
    Finset.prod_image (fun _ _ _ _ h => Sum.inr_injective h)]
  simp only [q, Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, one_mul]
  rw [archimedeanHerbrandFactor_eq_prod F E infinitePlace (fun O => Quotient.out_eq' O)]

end Counting


section BaseImage

universe v

variable (F : Type u) (E : Type v) [Field F] [Field E] [NumberField E] [Algebra F E]

/-- The cohomology of the integral ideles is unchanged on replacing the base field by its
image in `E`. -/
def integralIdeleCohomologyBaseImageIso (n : ℕ) :
    integralIdeleCohomology F E n ≅ integralIdeleCohomology (⊥ : IntermediateField F E) E n :=
  groupCohomology.mapIso (baseImageAutEquiv F E) (LinearEquiv.refl _ _) (fun _ => rfl) n

omit [NumberField E] in
theorem baseImageAutEquiv_smul_infinitePlace (σ : E ≃ₐ[F] E) (w : InfinitePlace E) :
    baseImageAutEquiv F E σ • w = σ • w := rfl

omit [NumberField E] in
theorem natCard_stabilizer_baseImage (w : InfinitePlace E) :
    Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w) =
      Nat.card (MulAction.stabilizer (E ≃ₐ[(⊥ : IntermediateField F E)] E) w) :=
  Nat.card_congr
    { toFun := fun σ => ⟨baseImageAutEquiv F E σ, by
        rw [MulAction.mem_stabilizer_iff, baseImageAutEquiv_smul_infinitePlace]
        exact σ.2⟩
      invFun := fun σ => ⟨(baseImageAutEquiv F E).symm σ, by
        rw [MulAction.mem_stabilizer_iff, ← baseImageAutEquiv_smul_infinitePlace,
          MulEquiv.apply_symm_apply]
        exact σ.2⟩
      left_inv := fun σ => Subtype.ext ((baseImageAutEquiv F E).symm_apply_apply σ)
      right_inv := fun σ => Subtype.ext ((baseImageAutEquiv F E).apply_symm_apply σ) }

theorem archimedeanHerbrandFactor_baseImage :
    archimedeanHerbrandFactor F E = archimedeanHerbrandFactor (⊥ : IntermediateField F E) E := by
  classical
  have hrel : ∀ w w' : InfinitePlace E,
      (MulAction.orbitRel (E ≃ₐ[F] E) (InfinitePlace E)) w w' ↔
        (MulAction.orbitRel (E ≃ₐ[(⊥ : IntermediateField F E)] E) (InfinitePlace E)) w w' := by
    intro w w'
    constructor
    · rintro ⟨σ, hσ⟩
      exact ⟨baseImageAutEquiv F E σ, hσ⟩
    · rintro ⟨σ, hσ⟩
      refine ⟨(baseImageAutEquiv F E).symm σ, ?_⟩
      change (baseImageAutEquiv F E).symm σ • w' = w
      rw [← hσ]
      change baseImageAutEquiv F E ((baseImageAutEquiv F E).symm σ) • w' = σ • w'
      rw [MulEquiv.apply_symm_apply]
  let φ : infinitePlaceOrbits F E ≃ infinitePlaceOrbits (⊥ : IntermediateField F E) E :=
    Quotient.congr (Equiv.refl _) hrel
  let := Fintype.ofFinite (infinitePlaceOrbits F E)
  let := Fintype.ofFinite (infinitePlaceOrbits (⊥ : IntermediateField F E) E)
  unfold archimedeanHerbrandFactor
  refine Fintype.prod_equiv φ _ _ fun q => ?_
  induction q using Quotient.inductionOn with
  | h w => exact natCard_stabilizer_baseImage F E w

end BaseImage

/-- `h(J∞) = D∞` in independent universes, given the archimedean local input. -/
theorem cyclicIntegralIdeleHerbrand_of.{v}
    (harch : ArchimedeanCompletionHerbrand.{v}) : CyclicIntegralIdeleHerbrand.{u, v} := by
  intro F _ _ E _ _ _ _ _
  let F₀ := (⊥ : IntermediateField F E)
  have : IsCyclic (E ≃ₐ[F₀] E) := (baseImageAutEquiv F E).isCyclic.mp inferInstance
  obtain ⟨h₁, h₂, h₃⟩ := integralIdeleHerbrand (F := F₀) (E := E) (fun w => harch F₀ E w)
  let e₁ := (integralIdeleCohomologyBaseImageIso F E 1).toLinearEquiv.toEquiv
  let e₂ := (integralIdeleCohomologyBaseImageIso F E 2).toLinearEquiv.toEquiv
  refine ⟨Finite.of_equiv _ e₁.symm, Finite.of_equiv _ e₂.symm, ?_⟩
  rw [Nat.card_congr e₁, Nat.card_congr e₂, h₃, archimedeanHerbrandFactor_baseImage F E]

end IntegralIdeleHerbrand

end Langlands.ClassField.Global
