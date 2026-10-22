import Langlands.ClassField.Global.FundamentalClassStatement

/-! # Restriction, inflation and local maps of relative idele-class cohomology

The arithmetic equivariance of the `w`-coordinate embedding `E_wˣ → C_E` along
`decompositionHom v w : Gal(E_w/F_v) → Gal(E/F)` and of the idele-class inclusion
`C_E → C_L` along `Gal(L/F) → Gal(E/F)`; the resulting coefficient morphisms of
representations and the maps they induce on Mathlib's group cohomology; and the
translation of the explicit cochain relations used in
`FundamentalClass.Restriction`, `FundamentalClass.Inflation` and
`FundamentalClass.LocalCompatibility` into equations between cohomology classes, for
individual cocycles and for whole class families.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Filter
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory FundamentalClass

universe u

section Transport

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]

/-- The isomorphism induced on idele classes by `e` sends the image of a local unit at
`q = finitePlaceEquiv e p` to the image at `p` of its transport along any continuous ring
homomorphism which extends `e` on the dense image of `K`. -/
theorem ideleClassEquiv_ofAdicCompletion_of_eq (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L))
    (q : HeightOneSpectrum (𝓞 K)) (h : finitePlaceEquiv e p = q)
    (φ : q.adicCompletion K →+* p.adicCompletion L) (hφ : Continuous φ)
    (hφe : ∀ a : K, φ (algebraMap K (q.adicCompletion K) a) =
      algebraMap L (p.adicCompletion L) (e a))
    (x : (q.adicCompletion K)ˣ) :
    ideleClassEquiv e (IdeleClassGroup.ofAdicCompletion (𝓞 K) K q x) =
      IdeleClassGroup.ofAdicCompletion (𝓞 L) L p (Units.map φ.toMonoidHom x) := by
  subst h
  have hφ' : ∀ y, φ y = finiteCompletionEquiv e p y := by
    intro y
    have h := (denseRange_algebraMap K (finitePlaceEquiv e p)).equalizer hφ
      (continuous_finiteCompletionEquiv e p) (by
        funext a
        exact (hφe a).trans (finiteCompletionEquiv_coe e p a).symm)
    exact congrFun h y
  rw [ideleClassEquiv_ofAdicCompletion]
  congr 1
  exact Units.ext (hφ' _).symm

/-- Two continuous maps out of the completions at two equal finite places, which agree on
the image of the number field, agree on the two coordinates of any family. -/
theorem adicCompletion_coordinate_eq {B : Type*} [TopologicalSpace B] [T2Space B]
    {P P' : HeightOneSpectrum (𝓞 K)} (h : P = P')
    (Φ : P.adicCompletion K → B) (Ψ : P'.adicCompletion K → B)
    (hΦ : Continuous Φ) (hΨ : Continuous Ψ)
    (hΦΨ : ∀ a : K, Φ (algebraMap K _ a) = Ψ (algebraMap K _ a))
    (x : ∀ Q : HeightOneSpectrum (𝓞 K), Q.adicCompletion K) :
    Φ (x P) = Ψ (x P') := by
  subst h
  exact congrFun ((denseRange_algebraMap K P).equalizer hΦ hΨ (funext hΦΨ)) (x P)

end Transport

section Decomposition

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- Every `F_v`-automorphism of `E_w` is continuous. -/
theorem continuous_localAut
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) : Continuous σ := by
  let _ : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  have := FiniteExtension.local_finite v w
  exact σ.toLinearMap.continuous_of_finiteDimensional

/-- An element of `E_w` lies in the open unit ball exactly when its powers tend to zero. -/
theorem valued_lt_one_iff_tendsto (x : w.adicCompletion E) :
    Valued.v x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) :=
  Valued.toNormedField.norm_lt_one_iff.symm.trans
    tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.symm

/-- Local automorphisms preserve the open unit ball. -/
theorem valued_localAut_lt_one_iff
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    (x : w.adicCompletion E) : Valued.v (σ x) < 1 ↔ Valued.v x < 1 := by
  have key : ∀ (τ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
      (y : w.adicCompletion E), Valued.v y < 1 → Valued.v (τ y) < 1 := by
    intro τ y hy
    rw [valued_lt_one_iff_tendsto] at hy ⊢
    have h := ((continuous_localAut v w τ).tendsto 0).comp hy
    rw [map_zero] at h
    refine h.congr fun n => ?_
    simp
  refine ⟨fun hx => ?_, key σ x⟩
  simpa using key σ.symm (σ x) hx

/-- `decompositionHom v w σ` is the restriction of `σ` to `E`. -/
theorem algebraMap_decompositionHom [Normal F E]
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) (x : E) :
    algebraMap E (w.adicCompletion E) (decompositionHom v w σ x) =
      σ (algebraMap E (w.adicCompletion E) x) := by
  simp only [decompositionHom, MonoidHom.comp_apply, AlgEquiv.restrictNormalHom,
    MonoidHom.mk'_apply, AlgEquiv.restrictNormal_commutes]
  rfl

/-- The automorphism `decompositionHom v w σ` of `E` fixes the place `w`. -/
theorem finitePlaceEquiv_decompositionHom [Normal F E]
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) :
    finitePlaceEquiv (decompositionHom v w σ).toRingEquiv w = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [finitePlaceEquiv_mem, ← valuation_lt_one_iff_mem (K := E),
    ← valuation_lt_one_iff_mem (K := E), ← valuedAdicCompletion_eq_valuation',
    ← valuedAdicCompletion_eq_valuation']
  change Valued.v (algebraMap E (w.adicCompletion E)
      (decompositionHom v w σ (algebraMap (𝓞 E) E x))) < 1 ↔ _
  rw [algebraMap_decompositionHom]
  exact valued_localAut_lt_one_iff v w σ _

/-- The `w`-coordinate embedding `E_wˣ → C_E` is equivariant along
`decompositionHom v w : Gal(E_w/F_v) → Gal(E/F)`. -/
theorem relativeIdeleClassAut_decompositionHom_ofAdicCompletion [Normal F E]
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    (x : (w.adicCompletion E)ˣ) :
    relativeIdeleClassAut F E (decompositionHom v w σ)
        (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w x) =
      IdeleClassGroup.ofAdicCompletion (𝓞 E) E w (Units.map σ.toRingEquiv.toMonoidHom x) := by
  change ideleClassEquiv (decompositionHom v w σ).toRingEquiv
      (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w x) = _
  exact ideleClassEquiv_ofAdicCompletion_of_eq _ w w (finitePlaceEquiv_decompositionHom v w σ)
    (σ : w.adicCompletion E →+* w.adicCompletion E) (continuous_localAut v w σ)
    (fun a => (algebraMap_decompositionHom v w σ a).symm) x

end Decomposition

section Inclusion

variable {E L : Type u} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]

omit [NumberField E] [NumberField L] in
/-- Compatible isomorphisms of `E` and `L` correspond on the places below. -/
theorem finitePlaceEquiv_under (e : E ≃+* E) (f : L ≃+* L)
    (h : ∀ a : E, f (algebraMap E L a) = algebraMap E L (e a)) (q : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv e (q.under (𝓞 E)) = (finitePlaceEquiv f q).under (𝓞 E) := by
  have key : ∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) (RingOfIntegers.mapRingEquiv e x) =
      RingOfIntegers.mapRingEquiv f (algebraMap (𝓞 E) (𝓞 L) x) := fun x =>
    RingOfIntegers.ext (h x).symm
  apply HeightOneSpectrum.ext
  ext x
  change algebraMap (𝓞 E) (𝓞 L) (RingOfIntegers.mapRingEquiv e x) ∈ q.asIdeal ↔
    RingOfIntegers.mapRingEquiv f (algebraMap (𝓞 E) (𝓞 L) x) ∈ q.asIdeal
  rw [key]

/-- The finite-adele inclusion intertwines transports along compatible isomorphisms of `E`
and `L`. -/
theorem finiteAdeleInclusion_finiteAdeleEquiv (e : E ≃+* E) (f : L ≃+* L)
    (h : ∀ a : E, f (algebraMap E L a) = algebraMap E L (e a))
    (x : FiniteAdeleRing (𝓞 E) E) :
    finiteAdeleInclusion (finiteAdeleEquiv e x) = finiteAdeleEquiv f (finiteAdeleInclusion x) := by
  apply FiniteAdeleRing.ext
  intro q
  change FiniteExtension.completionMap (q.under (𝓞 E)) q
      (finiteCompletionEquiv e (q.under (𝓞 E)) (x (finitePlaceEquiv e (q.under (𝓞 E))))) =
    finiteCompletionEquiv f q (FiniteExtension.completionMap
      ((finitePlaceEquiv f q).under (𝓞 E)) (finitePlaceEquiv f q)
      (x ((finitePlaceEquiv f q).under (𝓞 E))))
  exact adicCompletion_coordinate_eq (finitePlaceEquiv_under e f h q)
    (fun y => FiniteExtension.completionMap (q.under (𝓞 E)) q
      (finiteCompletionEquiv e (q.under (𝓞 E)) y))
    (fun y => finiteCompletionEquiv f q (FiniteExtension.completionMap
      ((finitePlaceEquiv f q).under (𝓞 E)) (finitePlaceEquiv f q) y))
    ((FiniteExtension.continuous_completionMap (q.under (𝓞 E)) q).comp
      (continuous_finiteCompletionEquiv e (q.under (𝓞 E))))
    ((continuous_finiteCompletionEquiv f q).comp
      (FiniteExtension.continuous_completionMap ((finitePlaceEquiv f q).under (𝓞 E))
        (finitePlaceEquiv f q)))
    (fun a => by simp only [finiteCompletionEquiv_coe, FiniteExtension.completionMap_coe, h])
    (fun Q => x Q)

/-- The infinite-adele map intertwines transports along compatible isomorphisms of `E` and
`L`. -/
theorem infiniteAdeleMap_infiniteAdeleEquiv (e : E ≃+* E) (f : L ≃+* L)
    (h : ∀ a : E, f (algebraMap E L a) = algebraMap E L (e a)) (x : InfiniteAdeleRing E) :
    infiniteAdeleMap (algebraMap E L) (infiniteAdeleEquiv e x) =
      infiniteAdeleEquiv f (infiniteAdeleMap (algebraMap E L) x) := by
  have hc : (algebraMap E L).comp e.toRingHom = f.toRingHom.comp (algebraMap E L) := by
    ext a
    exact (h a).symm
  change infiniteAdeleMap (algebraMap E L) (infiniteAdeleMap e.toRingHom x) =
    infiniteAdeleMap f.toRingHom (infiniteAdeleMap (algebraMap E L) x)
  rw [← RingHom.comp_apply, ← infiniteAdeleMap_comp, hc, infiniteAdeleMap_comp,
    RingHom.comp_apply]

/-- The adele inclusion intertwines transports along compatible isomorphisms of `E` and
`L`. -/
theorem adeleInclusion_adeleEquiv (e : E ≃+* E) (f : L ≃+* L)
    (h : ∀ a : E, f (algebraMap E L a) = algebraMap E L (e a)) (x : AdeleRing (𝓞 E) E) :
    adeleInclusion (adeleEquiv e x) = adeleEquiv f (adeleInclusion x) :=
  Prod.ext (infiniteAdeleMap_infiniteAdeleEquiv e f h x.1)
    (finiteAdeleInclusion_finiteAdeleEquiv e f h x.2)

/-- The idele-class inclusion intertwines transports along compatible isomorphisms of `E`
and `L`. -/
theorem ideleClassInclusion_ideleClassEquiv (e : E ≃+* E) (f : L ≃+* L)
    (h : ∀ a : E, f (algebraMap E L a) = algebraMap E L (e a))
    (x : IdeleClassGroup (𝓞 E) E) :
    ideleClassInclusion (ideleClassEquiv e x) = ideleClassEquiv f (ideleClassInclusion x) := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    change (QuotientGroup.mk (ideleInclusion (ideleEquiv e a)) : IdeleClassGroup (𝓞 L) L) =
      QuotientGroup.mk (ideleEquiv f (ideleInclusion a))
    exact congrArg QuotientGroup.mk (Units.ext (adeleInclusion_adeleEquiv e f h a))

/-- The idele-class inclusion `C_E → C_L` is equivariant along the restriction
`Gal(L/F) → Gal(E/F)`. -/
theorem ideleClassInclusion_relativeIdeleClassAut {F : Type u} [Field F] [Algebra F E]
    [Algebra F L] [IsScalarTower F E L] [Normal F E] (σ : L ≃ₐ[F] L)
    (a : IdeleClassGroup (𝓞 E) E) :
    ideleClassInclusion (relativeIdeleClassAut F E (AlgEquiv.restrictNormalHom E σ) a) =
      relativeIdeleClassAut F L σ (ideleClassInclusion a) :=
  ideleClassInclusion_ideleClassEquiv _ _
    (fun x => (AlgEquiv.restrictNormal_commutes σ E x).symm) a

end Inclusion

section Cochains

/-! ### Explicit cochains and maps on second cohomology -/

/-- Two degree-two cocycles have the same class exactly when they are related by an explicit
one-cochain `b`, in the convention `x(g, h) + b(gh) = b(g) + g • b(h) + y(g, h)`. -/
theorem H2π_eq_H2π_iff {k G : Type u} [CommRing k] [Group G] {A : Rep.{u} k G}
    (x y : groupCohomology.cocycles₂ A) :
    groupCohomology.H2π A x = groupCohomology.H2π A y ↔
      ∃ b : G → A, ∀ g h : G, x (g, h) + b (g * h) = b g + A.ρ g (b h) + y (g, h) := by
  rw [groupCohomology.H2π_eq_iff, groupCohomology.coboundaries₂, LinearMap.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, fun g h => ?_⟩
    have h1 := congrFun hb (g, h)
    simp only [groupCohomology.d₁₂_hom_apply, Pi.sub_apply] at h1
    rw [eq_sub_iff_add_eq] at h1
    rw [← h1]
    abel
  · rintro ⟨b, hb⟩
    refine ⟨b, funext fun gh => ?_⟩
    obtain ⟨g, h⟩ := gh
    simp only [groupCohomology.d₁₂_hom_apply, Pi.sub_apply]
    rw [eq_sub_iff_add_eq, eq_sub_of_add_eq (hb g h)]
    abel

/-- The class equation `map f φ [x] = [y]` for the map induced on second cohomology by
`f : G →* H` and `φ : res f A ⟶ B`, as an explicit cochain relation. -/
theorem map_H2π_eq_H2π_iff {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep.{u} k H} {B : Rep.{u} k G} (f : G →* H) (φ : Rep.res f A ⟶ B)
    (x : groupCohomology.cocycles₂ A) (y : groupCohomology.cocycles₂ B) :
    groupCohomology.map f φ 2 (groupCohomology.H2π A x) = groupCohomology.H2π B y ↔
      ∃ b : G → B, ∀ g h : G,
        φ.hom (x (f g, f h)) + b (g * h) = b g + B.ρ g (b h) + y (g, h) := by
  rw [groupCohomology.H2π_comp_map_apply, H2π_eq_H2π_iff]
  rfl

end Cochains

section RestrictionMap

variable (F F' E : Type u) [Field F] [Field F'] [Field E] [NumberField E]
  [Algebra F F'] [Algebra F E] [Algebra F' E] [IsScalarTower F F' E]

/-- The coefficient morphism of restriction to `Gal(E/F')`: the identity of `C_E`. -/
def ideleClassRestrictionCoefficients :
    Rep.res (AlgEquiv.restrictScalarsHom F : (E ≃ₐ[F'] E) →* (E ≃ₐ[F] E))
      (relativeIdeleClassRepresentation F E) ⟶ relativeIdeleClassRepresentation F' E :=
  Rep.ofHom
    { toLinearMap := LinearMap.id
      isIntertwining' _ := rfl }

/-- Restriction `Hⁿ(Gal(E/F), C_E) → Hⁿ(Gal(E/F'), C_E)`. -/
abbrev relativeIdeleClassRestriction (n : ℕ) :
    relativeIdeleClassCohomology F E n ⟶ relativeIdeleClassCohomology F' E n :=
  groupCohomology.map (AlgEquiv.restrictScalarsHom F)
    (ideleClassRestrictionCoefficients F F' E) n

variable {F F' E}

/-- The cochain relation of `FundamentalClass.Restriction` says exactly that the restriction
of `[x]` is `[y]`. -/
theorem relativeIdeleClassRestriction_cohomologyClass_eq_iff (x : RelativeIdeleCocycle F E)
    (y : RelativeIdeleCocycle F' E) :
    relativeIdeleClassRestriction F F' E 2 x.cohomologyClass = y.cohomologyClass ↔
      ∃ b : (E ≃ₐ[F'] E) → IdeleClassGroup (𝓞 E) E, ∀ σ τ : E ≃ₐ[F'] E,
        x (σ.restrictScalars F, τ.restrictScalars F) * b (σ * τ) =
          b σ * relativeIdeleClassAut F' E σ (b τ) * y (σ, τ) := by
  refine (map_H2π_eq_H2π_iff _ _ x.toCocycle₂ y.toCocycle₂).trans ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    exact ⟨fun σ => (b σ).toMul, fun σ τ => congrArg Additive.toMul (hb σ τ)⟩
  · rintro ⟨b, hb⟩
    exact ⟨fun σ => Additive.ofMul (b σ), fun σ τ => congrArg Additive.ofMul (hb σ τ)⟩

end RestrictionMap

section InflationMap

variable (F E L : Type u) [Field F] [Field E] [Field L] [NumberField E] [NumberField L]
  [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L] [Normal F E]

/-- The idele-class inclusion `C_E → C_L` on the additive coefficient modules, linear over the
lifted integers. -/
def ideleClassInclusionLinear :
    (relativeIdeleClassRepresentation F E).V →ₗ[ULift.{u} ℤ]
      (relativeIdeleClassRepresentation F L).V where
  toFun a := Additive.ofMul
    (ideleClassInclusion (K := E) (L := L) (@Additive.toMul (IdeleClassGroup (𝓞 E) E) a))
  map_add' a b := congrArg Additive.ofMul (map_mul (ideleClassInclusion (K := E) (L := L))
    (@Additive.toMul (IdeleClassGroup (𝓞 E) E) a) (@Additive.toMul (IdeleClassGroup (𝓞 E) E) b))
  map_smul' r a := congrArg Additive.ofMul (map_zpow (ideleClassInclusion (K := E) (L := L))
    (@Additive.toMul (IdeleClassGroup (𝓞 E) E) a) r.down)

omit [IsScalarTower F E L] [Normal F E] in
/-- The value of `ideleClassInclusionLinear`. -/
theorem ideleClassInclusionLinear_apply (a : (relativeIdeleClassRepresentation F E).V) :
    ideleClassInclusionLinear F E L a = Additive.ofMul
      (ideleClassInclusion (K := E) (L := L) (@Additive.toMul (IdeleClassGroup (𝓞 E) E) a)) :=
  rfl

/-- The coefficient morphism of inflation from `Gal(E/F)` to `Gal(L/F)`: the idele-class
inclusion, equivariant by `ideleClassInclusion_relativeIdeleClassAut`. -/
def ideleClassInflationCoefficients :
    Rep.res (AlgEquiv.restrictNormalHom E : (L ≃ₐ[F] L) →* (E ≃ₐ[F] E))
      (relativeIdeleClassRepresentation F E) ⟶ relativeIdeleClassRepresentation F L :=
  Rep.ofHom
    { toLinearMap := ideleClassInclusionLinear F E L
      isIntertwining' σ := by
        ext a
        exact congrArg Additive.ofMul
          (ideleClassInclusion_relativeIdeleClassAut σ
            (@Additive.toMul (IdeleClassGroup (𝓞 E) E) a)) }

/-- Inflation `Hⁿ(Gal(E/F), C_E) → Hⁿ(Gal(L/F), C_L)`, through the idele-class inclusion. -/
abbrev relativeIdeleClassInflation (n : ℕ) :
    relativeIdeleClassCohomology F E n ⟶ relativeIdeleClassCohomology F L n :=
  groupCohomology.map (AlgEquiv.restrictNormalHom E)
    (ideleClassInflationCoefficients F E L) n

variable {F E L}

/-- The cochain relation of `FundamentalClass.Inflation`, with exponent `m`, says exactly that
the inflation of `[x]` is `m • [y]`. -/
theorem relativeIdeleClassInflation_cohomologyClass_eq_iff (x : RelativeIdeleCocycle F E)
    (y : RelativeIdeleCocycle F L) (m : ℕ) :
    relativeIdeleClassInflation F E L 2 x.cohomologyClass = m • y.cohomologyClass ↔
      ∃ b : (L ≃ₐ[F] L) → IdeleClassGroup (𝓞 L) L, ∀ σ τ : L ≃ₐ[F] L,
        ideleClassInclusion
            (x (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ)) *
            b (σ * τ) =
          b σ * relativeIdeleClassAut F L σ (b τ) * y (σ, τ) ^ m := by
  have hm : m • y.cohomologyClass =
      groupCohomology.H2π (relativeIdeleClassRepresentation F L) (m • y.toCocycle₂) :=
    (map_nsmul _ m _).symm
  rw [hm]
  refine (map_H2π_eq_H2π_iff _ _ x.toCocycle₂ (m • y.toCocycle₂)).trans ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    refine ⟨fun σ => @Additive.toMul (IdeleClassGroup (𝓞 L) L) (b σ), fun σ τ => ?_⟩
    exact congrArg (@Additive.toMul (IdeleClassGroup (𝓞 L) L)) (hb σ τ)
  · rintro ⟨b, hb⟩
    refine ⟨fun σ => Additive.ofMul (b σ), fun σ τ => ?_⟩
    exact congrArg Additive.ofMul (hb σ τ)

end InflationMap

section LocalMap

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Normal F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The `w`-coordinate embedding `E_wˣ → C_E` on the additive coefficient modules, linear over
the lifted integers. -/
def localIdeleClassLinear :
    (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)).V →ₗ[ULift.{u} ℤ]
      (relativeIdeleClassRepresentation F E).V where
  toFun x := Additive.ofMul (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w
    (@Additive.toMul (w.adicCompletion E)ˣ x))
  map_add' x y := congrArg Additive.ofMul (map_mul (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w)
    (@Additive.toMul (w.adicCompletion E)ˣ x) (@Additive.toMul (w.adicCompletion E)ˣ y))
  map_smul' r x := congrArg Additive.ofMul (map_zpow (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w)
    (@Additive.toMul (w.adicCompletion E)ˣ x) r.down)

omit [Normal F E] in
/-- The value of `localIdeleClassLinear`. -/
theorem localIdeleClassLinear_apply
    (x : (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)).V) :
    localIdeleClassLinear v w x = Additive.ofMul (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w
      (@Additive.toMul (w.adicCompletion E)ˣ x)) :=
  rfl

/-- The coefficient morphism `E_wˣ → C_E` of representations of `Gal(E_w/F_v)`, where `C_E`
is restricted along `decompositionHom v w`. -/
def localIdeleClassCoefficients :
    unitsRepresentation (padicField v).Carrier (w.adicCompletion E) ⟶
      Rep.res (decompositionHom v w) (relativeIdeleClassRepresentation F E) :=
  Rep.ofHom
    { toLinearMap := localIdeleClassLinear v w
      isIntertwining' σ := by
        ext x
        exact congrArg Additive.ofMul
          (relativeIdeleClassAut_decompositionHom_ofAdicCompletion v w σ
            (@Additive.toMul (w.adicCompletion E)ˣ x)).symm }

/-- The map `Hⁿ(Gal(E_w/F_v), E_wˣ) → Hⁿ(Gal(E_w/F_v), C_E)` induced by the `w`-coordinate. -/
abbrev localIdeleClassMap (n : ℕ) :
    relativeCohomology (padicField v).Carrier (w.adicCompletion E) n ⟶
      groupCohomology (Rep.res (decompositionHom v w) (relativeIdeleClassRepresentation F E)) n :=
  groupCohomology.map (MonoidHom.id _) (localIdeleClassCoefficients v w) n

/-- Restriction `Hⁿ(Gal(E/F), C_E) → Hⁿ(Gal(E_w/F_v), C_E)` along `decompositionHom v w`. -/
abbrev decompositionRestriction (n : ℕ) :
    relativeIdeleClassCohomology F E n ⟶
      groupCohomology (Rep.res (decompositionHom v w) (relativeIdeleClassRepresentation F E)) n :=
  groupCohomology.map (decompositionHom v w) (𝟙 _) n

/-- The cochain relation of `FundamentalClass.LocalCompatibility` says exactly that the image
of `[z]` in `H²(Gal(E_w/F_v), C_E)` is the restriction of `[y]`. -/
theorem localIdeleClassMap_eq_decompositionRestriction_iff
    (z : groupCohomology.cocycles₂
      (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)))
    (y : RelativeIdeleCocycle F E) :
    localIdeleClassMap v w 2 (groupCohomology.H2π _ z) =
        decompositionRestriction v w 2 y.cohomologyClass ↔
      ∃ b : (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) →
          IdeleClassGroup (𝓞 E) E,
        ∀ σ τ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E,
          IdeleClassGroup.ofAdicCompletion (𝓞 E) E w
              (@Additive.toMul (w.adicCompletion E)ˣ (z (σ, τ))) * b (σ * τ) =
            b σ * relativeIdeleClassAut F E (decompositionHom v w σ) (b τ) *
              y (decompositionHom v w σ, decompositionHom v w τ) := by
  have hy : decompositionRestriction v w 2 y.cohomologyClass =
      groupCohomology.H2π _ (groupCohomology.mapCocycles₂ (decompositionHom v w) (𝟙 _)
        y.toCocycle₂) :=
    groupCohomology.H2π_comp_map_apply _ _ _
  rw [hy]
  refine (map_H2π_eq_H2π_iff _ _ z _).trans ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    refine ⟨fun σ => @Additive.toMul (IdeleClassGroup (𝓞 E) E) (b σ), fun σ τ => ?_⟩
    exact congrArg (@Additive.toMul (IdeleClassGroup (𝓞 E) E)) (hb σ τ)
  · rintro ⟨b, hb⟩
    refine ⟨fun σ => Additive.ofMul (b σ), fun σ τ => ?_⟩
    exact congrArg Additive.ofMul (hb σ τ)

end LocalMap

namespace FundamentalClass

/-! ### The compatibility conditions as equations of classes -/

/-- `FundamentalClass.Restriction` says exactly that restriction to `Gal(E/F')` sends the class
`c F E` to `c F' E`. -/
theorem restriction_iff_classes (c : ClassFamily.{u}) :
    Restriction c ↔
      ∀ (F F' E : Type u) [Field F] [Field F'] [Field E]
        [NumberField F] [NumberField F'] [NumberField E]
        [Algebra F F'] [Algebra F E] [Algebra F' E] [IsScalarTower F F' E] [IsGalois F E],
        haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
        relativeIdeleClassRestriction F F' E 2 (c F E) = c F' E := by
  constructor
  · intro h F F' E _ _ _ _ _ _ _ _ _ _ _
    obtain ⟨x, hx⟩ := RelativeIdeleCocycle.cohomologyClass_surjective (c F E)
    have : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    obtain ⟨y, hy⟩ := RelativeIdeleCocycle.cohomologyClass_surjective (c F' E)
    rw [← hx, ← hy]
    exact (relativeIdeleClassRestriction_cohomologyClass_eq_iff x y).2 (h F F' E x y hx hy)
  · intro h F F' E _ _ _ _ _ _ _ _ _ _ _ x y hx hy
    refine (relativeIdeleClassRestriction_cohomologyClass_eq_iff x y).1 ?_
    rw [hx, hy]
    exact h F F' E

/-- `FundamentalClass.Inflation` says exactly that inflation along `Gal(L/F) → Gal(E/F)` with
coefficients pushed forward to `C_L` sends `c F E` to `[L : E] • c F L`. -/
theorem inflation_iff_classes (c : ClassFamily.{u}) :
    Inflation c ↔
      ∀ (F E L : Type u) [Field F] [Field E] [Field L]
        [NumberField F] [NumberField E] [NumberField L]
        [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
        [IsGalois F E] [IsGalois F L],
        relativeIdeleClassInflation F E L 2 (c F E) = Module.finrank E L • c F L := by
  constructor
  · intro h F E L _ _ _ _ _ _ _ _ _ _ _ _
    obtain ⟨x, hx⟩ := RelativeIdeleCocycle.cohomologyClass_surjective (c F E)
    obtain ⟨y, hy⟩ := RelativeIdeleCocycle.cohomologyClass_surjective (c F L)
    rw [← hx, ← hy]
    exact (relativeIdeleClassInflation_cohomologyClass_eq_iff x y _).2 (h F E L x y hx hy)
  · intro h F E L _ _ _ _ _ _ _ _ _ _ _ _ x y hx hy
    refine (relativeIdeleClassInflation_cohomologyClass_eq_iff x y _).1 ?_
    rw [hx, hy]
    exact h F E L

/-- `FundamentalClass.LocalCompatibility` says exactly that at every finite place `w | v` the
`w`-coordinate image of every local fundamental class of `E_w / F_v` equals the restriction of
`c F E` along `decompositionHom v w`. -/
theorem localCompatibility_iff_classes (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (c : ClassFamily.{u}) :
    LocalCompatibility I c ↔
      ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
        [Algebra F E] [IsGalois F E]
        (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
        [w.asIdeal.LiesOver v.asIdeal]
        [IsGalois (padicField v).Carrier (w.adicCompletion E)],
        haveI : FiniteDimensional (padicField v).Carrier (w.adicCompletion E) :=
          FiniteExtension.local_finite v w
        ∀ a : relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2,
          IsFundamentalClass (padicField v).Carrier (w.adicCompletion E)
              ((I (residuePrime v)).relative (padicField v) (w.adicCompletion E)) a →
            localIdeleClassMap v w 2 a = decompositionRestriction v w 2 (c F E) := by
  constructor
  · intro h F _ _ E _ _ _ _ v w _ _ a ha
    induction a using groupCohomology.H2_induction_on with
    | h z =>
      obtain ⟨y, hy⟩ := RelativeIdeleCocycle.cohomologyClass_surjective (c F E)
      rw [← hy]
      exact (localIdeleClassMap_eq_decompositionRestriction_iff v w z y).2
        (h F E v w z y ha hy)
  · intro h F _ _ E _ _ _ _ v w _ _ z y hz hy
    refine (localIdeleClassMap_eq_decompositionRestriction_iff v w z y).1 ?_
    rw [hy]
    exact h F E v w _ hz

end FundamentalClass

end Langlands.ClassField.Global
