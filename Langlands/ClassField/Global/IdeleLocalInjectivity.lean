import Langlands.ClassField.Global.IdeleLocalSupport

/-! # Injectivity of the finite local components of idele cohomology in degree two -/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension Pointwise
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory Limits FundamentalClass

section Places

variable (F : Type u) {E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

/-- The finite place of `F` below a finite place `w` of `E`, with prime ideal `w ∩ 𝓞 F`. -/
def placeBelow (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := w.asIdeal.under (𝓞 F)
  isPrime := inferInstance
  ne_bot := Ideal.under_ne_bot (𝓞 F) w.ne_bot

instance liesOver_placeBelow (w : HeightOneSpectrum (𝓞 E)) :
    w.asIdeal.LiesOver (placeBelow F w).asIdeal :=
  ⟨rfl⟩

variable {F}

omit [NumberField F] [NumberField E] in
/-- The place below `w` is the place `v` that `w` lies over. -/
theorem placeBelow_eq (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] : placeBelow F w = v :=
  HeightOneSpectrum.ext (Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal)).symm

omit [NumberField F] [NumberField E] in
/-- The Galois action on finite places of `E` preserves the place below. -/
theorem liesOver_finitePlaceEquiv (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] (g : E ≃ₐ[F] E) :
    (finitePlaceEquiv g.toRingEquiv w).asIdeal.LiesOver v.asIdeal := by
  constructor
  rw [Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal)]
  ext x
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, finitePlaceEquiv_mem]
  have hx : RingOfIntegers.mapRingEquiv g.toRingEquiv (algebraMap (𝓞 F) (𝓞 E) x) =
      algebraMap (𝓞 F) (𝓞 E) x :=
    RingOfIntegers.ext (g.commutes (x : F))
  rw [hx]

/-- `Gal(E/F)` acts transitively on the finite places of `E` over a finite place of `F`. -/
theorem exists_finitePlaceEquiv_eq [IsGalois F E] (v : HeightOneSpectrum (𝓞 F))
    (w w' : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] :
    ∃ g : E ≃ₐ[F] E, finitePlaceEquiv g.toRingEquiv w = w' := by
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 F) (𝓞 E) (E ≃ₐ[F] E)
    w'.asIdeal w.asIdeal
    ((Ideal.LiesOver.over (P := w'.asIdeal) (p := v.asIdeal)).symm.trans
      (Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal)))
  refine ⟨g, HeightOneSpectrum.ext ?_⟩
  rw [finitePlaceEquiv_asIdeal, hg]
  ext x
  rw [Ideal.mem_comap]
  exact Ideal.smul_mem_pointwise_smul_iff

end Places

section Ideles

variable {E : Type u} [Field E] [NumberField E]

/-- Two ideles are equal if their infinite adele parts and all finite coordinates agree. -/
theorem idele_ext {x y : IdeleGroup (𝓞 E) E}
    (h₁ : (x : AdeleRing (𝓞 E) E).1 = (y : AdeleRing (𝓞 E) E).1)
    (h₂ : ∀ w, ideleCoordinate w x = ideleCoordinate w y) : x = y :=
  Units.ext (Prod.ext h₁ (FiniteAdeleRing.ext E fun w => congrArg Units.val (h₂ w)))

/-- A family of units which are valuation units at all but finitely many places is integral at
all but finitely many places. -/
theorem eventually_mem_adicCompletionIntegers
    (a : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (ha : {w | a w ∉ localUnits w}.Finite) :
    ∀ᶠ w in Filter.cofinite, (a w : w.adicCompletion E) ∈ adicCompletionIntegers E w := by
  refine Filter.eventually_cofinite.2 (ha.subset fun w hw hmem => hw ?_)
  rw [mem_localUnits_iff] at hmem
  rw [mem_adicCompletionIntegers]
  exact hmem.le

/-- The idele with infinite part `1` and finite coordinates `a w`, for a family `a` of units
which are valuation units at all but finitely many places. -/
def ideleOfCoordinates (a : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (ha : {w | a w ∉ localUnits w}.Finite) : IdeleGroup (𝓞 E) E where
  val := ((1 : InfiniteAdeleRing E),
    (RestrictedProduct.mk (fun w => (a w : w.adicCompletion E))
      (eventually_mem_adicCompletionIntegers a ha) : FiniteAdeleRing (𝓞 E) E))
  inv := ((1 : InfiniteAdeleRing E),
    (RestrictedProduct.mk (fun w => (((a w)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E))
      (eventually_mem_adicCompletionIntegers (fun w => (a w)⁻¹)
        (ha.subset fun _ hw h => hw (inv_mem h))) : FiniteAdeleRing (𝓞 E) E))
  val_inv := Prod.ext (mul_one _) (FiniteAdeleRing.ext E fun w => Units.mul_inv (a w))
  inv_val := Prod.ext (mul_one _) (FiniteAdeleRing.ext E fun w => Units.inv_mul (a w))

@[simp]
theorem ideleCoordinate_ideleOfCoordinates
    (a : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (ha : {w | a w ∉ localUnits w}.Finite) (w : HeightOneSpectrum (𝓞 E)) :
    ideleCoordinate w (ideleOfCoordinates a ha) = a w :=
  Units.ext rfl

theorem ideleOfCoordinates_infinite
    (a : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (ha : {w | a w ∉ localUnits w}.Finite) :
    ((ideleOfCoordinates a ha : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).1 = 1 :=
  rfl

/-- The ideles with infinite adele part `1`. -/
def ideleInfiniteTrivial : Subgroup (IdeleGroup (𝓞 E) E) where
  carrier := {x | (x : AdeleRing (𝓞 E) E).1 = 1}
  mul_mem' {x y} hx hy := by
    have h : ((x * y : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).1 =
        (x : AdeleRing (𝓞 E) E).1 * (y : AdeleRing (𝓞 E) E).1 := rfl
    change ((x * y : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).1 = 1
    rw [h, hx, hy, one_mul]
  one_mem' := rfl
  inv_mem' {x} hx := by
    have h : ((x⁻¹ : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).1 *
        (x : AdeleRing (𝓞 E) E).1 = 1 :=
      congrArg Prod.fst (Units.inv_mul x)
    change ((x⁻¹ : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).1 = 1
    change (x : AdeleRing (𝓞 E) E).1 = 1 at hx
    rw [hx, mul_one] at h
    exact h

theorem mem_ideleInfiniteTrivial_iff (x : IdeleGroup (𝓞 E) E) :
    x ∈ ideleInfiniteTrivial ↔ (x : AdeleRing (𝓞 E) E).1 = 1 :=
  Iff.rfl

variable {F : Type u} [Field F] [Algebra F E]

/-- The Galois action preserves the ideles with infinite part `1`. -/
theorem relativeIdeleAut_mem_ideleInfiniteTrivial (g : E ≃ₐ[F] E) {x : IdeleGroup (𝓞 E) E}
    (hx : x ∈ ideleInfiniteTrivial) : relativeIdeleAut F E g x ∈ ideleInfiniteTrivial := by
  change infiniteAdeleEquiv g.toRingEquiv (x : AdeleRing (𝓞 E) E).1 = 1
  change (x : AdeleRing (𝓞 E) E).1 = 1 at hx
  rw [hx, map_one]

/-- The coordinate of `g • x` at `w` is the transport of the coordinate of `x` at
`finitePlaceEquiv g w`. -/
theorem ideleCoordinate_relativeIdeleAut (g : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E))
    (x : IdeleGroup (𝓞 E) E) :
    (ideleCoordinate w (relativeIdeleAut F E g x) : w.adicCompletion E) =
      finiteCompletionEquiv g.toRingEquiv w
        (ideleCoordinate (finitePlaceEquiv g.toRingEquiv w) x) :=
  rfl

end Ideles

section Blocks

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] in
/-- If two ideles have the same coordinates at all places over `v`, so do their translates by
any `g ∈ Gal(E/F)`. -/
theorem ideleCoordinate_relativeIdeleAut_eq (v : HeightOneSpectrum (𝓞 F)) (g : E ≃ₐ[F] E)
    {x y : IdeleGroup (𝓞 E) E}
    (h : ∀ (u : HeightOneSpectrum (𝓞 E)) [u.asIdeal.LiesOver v.asIdeal],
      ideleCoordinate u x = ideleCoordinate u y)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    ideleCoordinate w (relativeIdeleAut F E g x) =
      ideleCoordinate w (relativeIdeleAut F E g y) := by
  have := liesOver_finitePlaceEquiv v w g
  apply Units.ext
  rw [ideleCoordinate_relativeIdeleAut, ideleCoordinate_relativeIdeleAut,
    h (finitePlaceEquiv g.toRingEquiv w)]

variable [IsGalois F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The value of the semilocal projection at `g` is the `w`-coordinate of `g • x`. -/
theorem ideleSemilocalProjection_apply (x : (relativeIdeleRepresentation F E).V)
    (g : E ≃ₐ[F] E) :
    ((ideleSemilocalProjection v w).hom x).1 g =
      Additive.ofMul (ideleCoordinate w
        (relativeIdeleAut F E g (@Additive.toMul (IdeleGroup (𝓞 E) E) x))) :=
  rfl

/-- The semilocal projection at `w` determines the coordinates at all places over `v`. -/
theorem ideleCoordinate_eq_of_ideleSemilocalProjection_eq
    {x y : (relativeIdeleRepresentation F E).V}
    (h : (ideleSemilocalProjection v w).hom x = (ideleSemilocalProjection v w).hom y)
    (w' : HeightOneSpectrum (𝓞 E)) [w'.asIdeal.LiesOver v.asIdeal] :
    ideleCoordinate w' (@Additive.toMul (IdeleGroup (𝓞 E) E) x) =
      ideleCoordinate w' (@Additive.toMul (IdeleGroup (𝓞 E) E) y) := by
  obtain ⟨g, rfl⟩ := exists_finitePlaceEquiv_eq v w w'
  have hg : ideleCoordinate w (relativeIdeleAut F E g (@Additive.toMul (IdeleGroup (𝓞 E) E) x)) =
      ideleCoordinate w (relativeIdeleAut F E g (@Additive.toMul (IdeleGroup (𝓞 E) E) y)) :=
    congrArg (fun f => Additive.toMul (f.1 g)) h
  apply Units.ext
  apply (finiteCompletionEquiv g.toRingEquiv w).injective
  exact congrArg Units.val hg

/-- If every value of the semilocal projection of `x` at `w` is a valuation unit, then `x` has
valuation-unit coordinates at all places over `v`. -/
theorem ideleCoordinate_mem_localUnits_of_ideleSemilocalProjection
    (x : (relativeIdeleRepresentation F E).V)
    (hx : ∀ g, Additive.toMul (((ideleSemilocalProjection v w).hom x).1 g) ∈ localUnits w)
    (w' : HeightOneSpectrum (𝓞 E)) [w'.asIdeal.LiesOver v.asIdeal] :
    ideleCoordinate w' (@Additive.toMul (IdeleGroup (𝓞 E) E) x) ∈ localUnits w' := by
  obtain ⟨g, rfl⟩ := exists_finitePlaceEquiv_eq v w w'
  have hg : ideleCoordinate w
      (relativeIdeleAut F E g (@Additive.toMul (IdeleGroup (𝓞 E) E) x)) ∈ localUnits w := hx g
  rw [mem_localUnits_iff, ideleCoordinate_relativeIdeleAut, finiteCompletionEquiv_valuation]
    at hg
  rw [mem_localUnits_iff]
  exact hg

variable [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]

/-- The semilocal projection of the semilocal section of `β` is `β`. -/
theorem ideleSemilocalProjection_ideleSemilocalSection
    (β : Rep.coind (decompositionHom v w)
      (unitsRepresentation (padicField v).Carrier (w.adicCompletion E))) :
    (ideleSemilocalProjection v w).hom ((ideleSemilocalSection v w).hom β) = β :=
  congrArg (fun φ => φ.hom β) (ideleSemilocalSection_comp_ideleSemilocalProjection v w)

/-- Section after projection does not change the coordinates at the places over `v`. -/
theorem ideleCoordinate_ideleSemilocalSection_ideleSemilocalProjection
    (x : (relativeIdeleRepresentation F E).V)
    (w' : HeightOneSpectrum (𝓞 E)) [w'.asIdeal.LiesOver v.asIdeal] :
    ideleCoordinate w' (@Additive.toMul (IdeleGroup (𝓞 E) E)
        ((ideleSemilocalSection v w).hom ((ideleSemilocalProjection v w).hom x))) =
      ideleCoordinate w' (@Additive.toMul (IdeleGroup (𝓞 E) E) x) :=
  ideleCoordinate_eq_of_ideleSemilocalProjection_eq v w
    (ideleSemilocalProjection_ideleSemilocalSection v w _) w'

end Blocks

section CoindUnits

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Normal F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The coinduced inclusion `Coind(U_w) ⟶ Coind(E_wˣ)` along `decompositionHom v w`. -/
abbrev coindLocalUnitsInclusion :
    Rep.coind (decompositionHom v w) (localUnitsRepresentation v w) ⟶
      Rep.coind (decompositionHom v w)
        (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)) :=
  Rep.coindMap (decompositionHom v w) (localUnitsInclusion v w)

theorem coindLocalUnitsInclusion_injective :
    Function.Injective (coindLocalUnitsInclusion v w).hom := by
  intro a b hab
  apply Subtype.ext
  funext g
  have h := congrArg (fun f => f.1 g) hab
  exact Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))

/-- An element of `Coind(E_wˣ)` with valuation-unit values comes from `Coind(U_w)`. -/
theorem exists_coindLocalUnitsInclusion_eq
    (y : Rep.coind (decompositionHom v w)
      (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)))
    (hy : ∀ g, Additive.toMul (y.1 g) ∈ localUnits w) :
    ∃ a, (coindLocalUnitsInclusion v w).hom a = y := by
  refine ⟨⟨fun g => Additive.ofMul (⟨Additive.toMul (y.1 g), hy g⟩ : localUnits w),
    fun s g => ?_⟩, rfl⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg Additive.toMul (y.2 s g)

/-- `H²(Gal(E/F), Coind(U_w)) = 0` under the hypotheses of `isZero_H2_localUnits`. -/
theorem isZero_H2_coindLocalUnits [IsGalois F E] (he : w.asIdeal.ramificationIdx (𝓞 F) = 1)
    [Finite (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2)]
    (hcard : Nat.card (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) ≤
      Module.finrank (v.adicCompletion F) (w.adicCompletion E)) :
    IsZero (groupCohomology (Rep.coind (decompositionHom v w) (localUnitsRepresentation v w)) 2) :=
  (isZero_H2_localUnits v w he hcard).of_iso
    (Shapiro.shapiroIsoOf (decompositionHom_injective v w) _ 2)

end CoindUnits

section Primitives

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- If the local map at `w` kills the class of a 2-cocycle `f` of `J_E`, then the semilocal
projection of `f` is the coboundary of a cochain with values in `Coind(E_wˣ)`. -/
theorem exists_d₁₂_eq_ideleSemilocalProjection
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E))
    (hf : ideleLocalMap v w 2 (groupCohomology.H2π _ f) = 0) :
    ∃ β : (E ≃ₐ[F] E) → Rep.coind (decompositionHom v w)
        (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)),
      ∀ g h, (groupCohomology.d₁₂ _).hom β (g, h) =
        (ideleSemilocalProjection v w).hom (f (g, h)) := by
  have hinj : Function.Injective (Shapiro.shapiroMapOf (decompositionHom v w)
      (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)) 2) := by
    have := Shapiro.isIso_shapiroMapOf (decompositionHom_injective v w)
      (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)) 2
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  have h1 : groupCohomology.map (MonoidHom.id _) (ideleSemilocalProjection v w) 2
      (groupCohomology.H2π _ f) = 0 := by
    apply hinj
    rw [map_zero, ← ConcreteCategory.comp_apply, ← ideleLocalMap_eq]
    exact hf
  rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_eq_zero_iff] at h1
  obtain ⟨β, hβ⟩ := h1
  exact ⟨β, fun g h => congrFun hβ (g, h)⟩

/-- At a place `w` with ramification index `1` where every value of `f` has valuation-unit
coordinates at all places over `v`, the semilocal projection of `f` is the coboundary of a
cochain with values in `Coind(E_wˣ)` whose values are valuation units. -/
theorem exists_d₁₂_eq_ideleSemilocalProjection_units
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1)
    [Finite (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2)]
    (hcard : Nat.card (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) ≤
      Module.finrank (v.adicCompletion F) (w.adicCompletion E))
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E))
    (hf : ∀ (x : (E ≃ₐ[F] E) × (E ≃ₐ[F] E)) (u : HeightOneSpectrum (𝓞 E))
      [u.asIdeal.LiesOver v.asIdeal],
      ideleCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E) (f x)) ∈ localUnits u) :
    ∃ β : (E ≃ₐ[F] E) → Rep.coind (decompositionHom v w)
        (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)),
      (∀ g h, (groupCohomology.d₁₂ _).hom β (g, h) =
        (ideleSemilocalProjection v w).hom (f (g, h))) ∧
      ∀ g k, Additive.toMul ((β g).1 k) ∈ localUnits w := by
  have hu : ∀ x k, Additive.toMul (((ideleSemilocalProjection v w).hom (f x)).1 k) ∈
      localUnits w := by
    intro x k
    have := liesOver_finitePlaceEquiv v w k
    have hk := hf x (finitePlaceEquiv k.toRingEquiv w)
    change ideleCoordinate w (relativeIdeleAut F E k
      (@Additive.toMul (IdeleGroup (𝓞 E) E) (f x))) ∈ localUnits w
    rw [mem_localUnits_iff] at hk ⊢
    rw [ideleCoordinate_relativeIdeleAut, finiteCompletionEquiv_valuation]
    exact hk
  choose fU hfU using fun x => exists_coindLocalUnitsInclusion_eq v w _ (hu x)
  have hfU' : fU ∈ groupCohomology.cocycles₂
      (Rep.coind (decompositionHom v w) (localUnitsRepresentation v w)) := by
    apply mem_cocycles₂_of_injective _ (coindLocalUnitsInclusion_injective v w)
    rw [groupCohomology.mem_cocycles₂_def]
    intro g h j
    have hc := congrArg (ideleSemilocalProjection v w).hom
      ((groupCohomology.mem_cocycles₂_def f).1 f.2 g h j)
    rw [map_zero, map_sub, map_add, map_sub, Rep.hom_comm_apply] at hc
    simp only [hfU]
    exact hc
  have hz : groupCohomology.H2π _ ⟨fU, hfU'⟩ = 0 :=
    @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.1
      (isZero_H2_coindLocalUnits v w he hcard)) _ _
  rw [groupCohomology.H2π_eq_zero_iff] at hz
  obtain ⟨γ, hγ⟩ := hz
  refine ⟨fun g => (coindLocalUnitsInclusion v w).hom (γ g), fun g₁ g₂ => ?_,
    fun g k => (Additive.toMul ((γ g).1 k)).2⟩
  have hgh : (groupCohomology.d₁₂ _).hom γ (g₁, g₂) = fU (g₁, g₂) := congrFun hγ (g₁, g₂)
  rw [groupCohomology.d₁₂_hom_apply] at hgh
  rw [groupCohomology.d₁₂_hom_apply, ← hfU (g₁, g₂), ← hgh, map_add, map_sub,
    Rep.hom_comm_apply]

end Primitives

section Injectivity

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- Let `β` be a primitive of the semilocal projection at `w | v` of a 2-cocycle `f`, and let
`b` be a cochain of `J_E` whose coordinates at the places over `v` are those of the semilocal
sections of `β`. Then the coboundary of `b` and `f` have the same coordinates at the places
over `v`. -/
theorem ideleCoordinate_d₁₂_eq [IsGalois F E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E))
    (β : (E ≃ₐ[F] E) → Rep.coind (decompositionHom v w)
        (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)))
    (hβ : ∀ g h, (groupCohomology.d₁₂ _).hom β (g, h) =
        (ideleSemilocalProjection v w).hom (f (g, h)))
    (b : (E ≃ₐ[F] E) → (relativeIdeleRepresentation F E).V)
    (hb : ∀ (k : E ≃ₐ[F] E) (u : HeightOneSpectrum (𝓞 E)) [u.asIdeal.LiesOver v.asIdeal],
      ideleCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E) (b k)) =
        ideleCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E)
          ((ideleSemilocalSection v w).hom (β k))))
    (g h : E ≃ₐ[F] E) (u : HeightOneSpectrum (𝓞 E)) [u.asIdeal.LiesOver v.asIdeal] :
    ideleCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E)
        ((groupCohomology.d₁₂ _).hom b (g, h))) =
      ideleCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E) (f (g, h))) := by
  have hβ' := hβ g h
  rw [groupCohomology.d₁₂_hom_apply] at hβ'
  have hρ : ideleCoordinateLinear v u ((relativeIdeleRepresentation F E).ρ g (b h)) =
      ideleCoordinateLinear v u ((relativeIdeleRepresentation F E).ρ g
        ((ideleSemilocalSection v w).hom (β h))) :=
    congrArg Additive.ofMul (ideleCoordinate_relativeIdeleAut_eq v g (hb h) u)
  have hb' : ∀ k, ideleCoordinateLinear v u (b k) =
      ideleCoordinateLinear v u ((ideleSemilocalSection v w).hom (β k)) :=
    fun k => congrArg Additive.ofMul (hb k u)
  have key : (ideleSemilocalSection v w).hom
      ((Rep.coind (decompositionHom v w)
        (unitsRepresentation (padicField v).Carrier (w.adicCompletion E))).ρ g (β h) -
          β (g * h) + β g) =
      (relativeIdeleRepresentation F E).ρ g ((ideleSemilocalSection v w).hom (β h)) -
        (ideleSemilocalSection v w).hom (β (g * h)) + (ideleSemilocalSection v w).hom (β g) := by
    rw [map_add, map_sub, Rep.hom_comm_apply]
  apply Additive.ofMul.injective
  change ideleCoordinateLinear v u ((groupCohomology.d₁₂ _).hom b (g, h)) =
    ideleCoordinateLinear v u (f (g, h))
  rw [groupCohomology.d₁₂_hom_apply, map_add, map_sub, hρ, hb', hb', ← map_sub, ← map_add,
    ← key, hβ']
  exact congrArg Additive.ofMul
    (ideleCoordinate_ideleSemilocalSection_ideleSemilocalProjection v w (f (g, h)) u)

/-- **Injectivity of the finite local components in degree two.** Assume that at every finite
place `w | v` the group `H²(Gal(E_w/F_v), E_wˣ)` is finite with at most `[E_w : F_v]` elements,
and choose a place `wf v` over each finite place `v` of `F`. Let `f` be a 2-cocycle of `J_E`
whose values all have infinite adele part `1`. If the local map at `wf v` kills the class of `f`
for every finite place `v`, then the class of `f` in `H²(Gal(E/F), J_E)` is zero. -/
theorem H2π_eq_zero_of_ideleLocalMap_eq_zero [IsGalois F E]
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
      [w.asIdeal.LiesOver v.asIdeal],
      Finite (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2))
    (hcard : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
      [w.asIdeal.LiesOver v.asIdeal],
      Nat.card (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) ≤
        Module.finrank (v.adicCompletion F) (w.adicCompletion E))
    (wf : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
    [hwf : ∀ v, (wf v).asIdeal.LiesOver v.asIdeal]
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E))
    (hinf : ∀ x, ((@Additive.toMul (IdeleGroup (𝓞 E) E) (f x) : IdeleGroup (𝓞 E) E) :
      AdeleRing (𝓞 E) E).1 = 1)
    (hloc : ∀ v, ideleLocalMap v (wf v) 2 (groupCohomology.H2π _ f) = 0) :
    groupCohomology.H2π _ f = 0 := by
  classical
  have hfint : ∀ v, Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (wf v)).range) :=
    fun v => Fintype.ofFinite _
  let T : Set (HeightOneSpectrum (𝓞 E)) :=
    (⋃ x : (E ≃ₐ[F] E) × (E ≃ₐ[F] E),
      {w | ideleCoordinate w (@Additive.toMul (IdeleGroup (𝓞 E) E) (f x)) ∉ localUnits w}) ∪
    {w | w.asIdeal.ramificationIdx (𝓞 F) ≠ 1}
  have hT : T.Finite :=
    (Set.finite_iUnion fun x => finite_setOf_ideleCoordinate_not_mem_localUnits _).union
      (finite_setOf_ramificationIdx_ne_one F E)
  have hβ : ∀ v, ∃ β : (E ≃ₐ[F] E) → Rep.coind (decompositionHom v (wf v))
        (unitsRepresentation (padicField v).Carrier ((wf v).adicCompletion E)),
      (∀ g h, (groupCohomology.d₁₂ _).hom β (g, h) =
        (ideleSemilocalProjection v (wf v)).hom (f (g, h))) ∧
      ((∀ u : HeightOneSpectrum (𝓞 E), u.asIdeal.LiesOver v.asIdeal → u ∉ T) →
        ∀ g k, Additive.toMul ((β g).1 k) ∈ localUnits (wf v)) := by
    intro v
    by_cases hv : ∀ u : HeightOneSpectrum (𝓞 E), u.asIdeal.LiesOver v.asIdeal → u ∉ T
    · have hwT := hv (wf v) inferInstance
      simp only [T, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
        not_not] at hwT
      have hfu : ∀ (x : (E ≃ₐ[F] E) × (E ≃ₐ[F] E)) (u : HeightOneSpectrum (𝓞 E))
          [u.asIdeal.LiesOver v.asIdeal],
          ideleCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E) (f x)) ∈ localUnits u := by
        intro x u hu
        have huT := hv u hu
        simp only [T, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
          not_not] at huT
        exact huT.1 x
      have := hfin v (wf v)
      obtain ⟨β, hβd, hβu⟩ :=
        exists_d₁₂_eq_ideleSemilocalProjection_units v (wf v) hwT.2 (hcard v (wf v)) f hfu
      exact ⟨β, hβd, fun _ => hβu⟩
    · obtain ⟨β, hβd⟩ := exists_d₁₂_eq_ideleSemilocalProjection v (wf v) f (hloc v)
      exact ⟨β, hβd, fun h => absurd h hv⟩
  choose β hβd hβu using hβ
  let s : HeightOneSpectrum (𝓞 F) → (E ≃ₐ[F] E) → (relativeIdeleRepresentation F E).V :=
    fun v g => (ideleSemilocalSection v (wf v)).hom (β v g)
  let a : (E ≃ₐ[F] E) → ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ :=
    fun g w => ideleCoordinate w (@Additive.toMul (IdeleGroup (𝓞 E) E) (s (placeBelow F w) g))
  have ha : ∀ g, {w | a g w ∉ localUnits w}.Finite := by
    intro g
    refine (hT.biUnion fun u _ =>
      Set.finite_range fun k : E ≃ₐ[F] E => finitePlaceEquiv k.toRingEquiv u).subset ?_
    intro w hw
    by_contra hwT
    apply hw
    have hgood : ∀ u : HeightOneSpectrum (𝓞 E),
        u.asIdeal.LiesOver (placeBelow F w).asIdeal → u ∉ T := by
      intro u hu huT
      apply hwT
      obtain ⟨k, hk⟩ := exists_finitePlaceEquiv_eq (placeBelow F w) u w
      exact Set.mem_biUnion huT ⟨k, hk⟩
    exact ideleCoordinate_mem_localUnits_of_ideleSemilocalProjection (placeBelow F w)
      (wf (placeBelow F w)) ((ideleSemilocalSection _ _).hom (β (placeBelow F w) g))
      (fun k => by
        rw [ideleSemilocalProjection_ideleSemilocalSection]
        exact hβu _ hgood g k) w
  let b : (E ≃ₐ[F] E) → (relativeIdeleRepresentation F E).V :=
    fun g => Additive.ofMul (ideleOfCoordinates (a g) (ha g))
  have hb : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : E ≃ₐ[F] E) (u : HeightOneSpectrum (𝓞 E))
      [u.asIdeal.LiesOver v.asIdeal],
      ideleCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E) (b k)) =
        ideleCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E) (s v k)) := by
    intro v k u _
    change ideleCoordinate u (ideleOfCoordinates (a k) (ha k)) = _
    rw [ideleCoordinate_ideleOfCoordinates]
    change ideleCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E) (s (placeBelow F u) k)) = _
    rw [placeBelow_eq v u]
  rw [groupCohomology.H2π_eq_zero_iff]
  refine ⟨b, funext fun x => ?_⟩
  obtain ⟨g, h⟩ := x
  apply (@Additive.toMul (IdeleGroup (𝓞 E) E)).injective
  apply idele_ext
  · rw [hinf (g, h)]
    have hmem : ∀ k, @Additive.toMul (IdeleGroup (𝓞 E) E) (b k) ∈ ideleInfiniteTrivial :=
      fun k => ideleOfCoordinates_infinite (a k) (ha k)
    have hX : @Additive.toMul (IdeleGroup (𝓞 E) E) ((groupCohomology.d₁₂ _).hom b (g, h)) ∈
        ideleInfiniteTrivial := by
      rw [groupCohomology.d₁₂_hom_apply]
      change relativeIdeleAut F E g (@Additive.toMul (IdeleGroup (𝓞 E) E) (b h)) /
          @Additive.toMul (IdeleGroup (𝓞 E) E) (b (g * h)) *
          @Additive.toMul (IdeleGroup (𝓞 E) E) (b g) ∈ ideleInfiniteTrivial
      exact mul_mem (div_mem (relativeIdeleAut_mem_ideleInfiniteTrivial g (hmem h)) (hmem _))
        (hmem g)
    exact hX
  · intro w
    exact ideleCoordinate_d₁₂_eq (placeBelow F w) (wf (placeBelow F w)) f (β _) (hβd _) b
      (hb _) g h w

end Injectivity

end Langlands.ClassField.Global
