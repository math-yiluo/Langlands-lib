import Langlands.Cohomology.HyperextIsotypicDegenerationBaseChange
import Langlands.Representation.Smooth.Definitions
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Invariants of hyperext groups and localization

Let `S` be a localization of a commutative ring `R` at a submonoid `M` (for example
`R = 𝒪`, the ring of integers of a finite extension of `ℚ_ℓ`, and `S` its fraction field). For a
representation `ρ` of a group `Γ` over `R` in which every orbit is finite, the map
`invariantsBaseChangeMap S ρ : S ⊗[R] ρ^Γ → (S ⊗[R] ρ)^Γ` of `HyperextIsotypicBaseChange` is
bijective. Combined with `HyperextIsotypicDegenerationBaseChange`, this gives sufficient
conditions for the base-change maps on `Γ`-invariants of hyperext groups to be bijective.

* `HasFiniteOrbits`: every orbit of a representation is finite. `hasFiniteOrbits_of_finite`
  (finite groups) and `hasFiniteOrbits_comp_subtype_of_isSmooth` (a smooth representation
  restricted to a compact subgroup) give examples.
* `invariantsLinearMap_bijective`: the restriction to invariants of a bijective intertwining map is
  bijective.
* `invariantsBaseChangeMap_surjective_of_isLocalization`,
  `invariantsBaseChangeMap_bijective_of_isLocalization` and the linear equivalence
  `invariantsBaseChangeEquivOfIsLocalization`: invariants commute with localization for
  representations with finite orbits.
* `abutmentInvariantsBaseChangeMap_bijective_of_isLocalization` and
  `cohomologyHomInvariantsBaseChangeMap_bijective_of_isLocalization`: for an exact semilinear
  functor along a localization, the base-change map on `Γ`-invariants of `Hom(K, W₀⟦n⟧)` (resp.
  `Hom(H^{-n} K, W)`) is bijective if the action of `Γ` has finite orbits and the base-change map
  before taking invariants is bijective.
* `abutmentInvariantsBaseChangeMap_bijective_of_isLocalization_of_cohomologyHom` and the linear
  equivalence `abutmentInvariantsLocalizationEquiv`: under the degeneration hypotheses, the same
  conclusion for `Hom(K, W₀⟦n⟧)` with both hypotheses stated for `Hom(H^{-n} K, W)`.
* `smoothCohomologyHomInvariantsBaseChangeMap_bijective_of_isLocalization`,
  `smoothAbutmentInvariantsBaseChangeMap_bijective_of_isLocalization` and
  `smoothAbutmentInvariantsLocalizationEquiv`: the versions for extension of scalars of smooth
  representations.

The finite-orbit hypotheses and the bijectivity of the base-change maps before taking invariants
remain hypotheses; this module does not verify them for any particular complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

namespace HyperextScalarExtension

open HyperextAbutment

universe w uR uS uG uC vC uD vD s s' t t' uΓ

section Algebra

variable {R : Type uR} [CommRing R] {Γ : Type uΓ} [Group Γ] {V W : Type*} [AddCommGroup V]
  [Module R V] [AddCommGroup W] [Module R W]

/-- A representation `ρ` of `Γ` has finite orbits if the orbit `{ρ γ v | γ ∈ Γ}` of every vector
`v` is finite. -/
def HasFiniteOrbits (ρ : Representation R Γ V) : Prop :=
  ∀ v : V, (Set.range fun γ : Γ => ρ γ v).Finite

/-- Every representation of a finite group has finite orbits. -/
lemma hasFiniteOrbits_of_finite [Finite Γ] (ρ : Representation R Γ V) : HasFiniteOrbits ρ :=
  fun _ => Set.finite_range _

/-- The restriction of a smooth representation of a topological group `G` to a compact subgroup
`K` has finite orbits. -/
lemma hasFiniteOrbits_comp_subtype_of_isSmooth {G : Type uG} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {ρ : Representation R G V} (hρ : IsSmooth ρ) (K : Subgroup G)
    [CompactSpace K] : HasFiniteOrbits (ρ.comp K.subtype) := by
  intro v
  obtain ⟨U, hU⟩ := hρ v
  let H : Subgroup K := U.toSubgroup.subgroupOf K
  have hH : IsOpen (H : Set K) := U.isOpen.preimage continuous_subtype_val
  have : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  refine (Set.finite_range fun q : K ⧸ H => ρ (q.out : K) v).subset ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H k
  refine ⟨(k : K ⧸ H), ?_⟩
  have hfix : ρ ((h : K) : G) v = v :=
    (Representation.mem_invariants _ v).1 hU ⟨((h : K) : G), Subgroup.mem_subgroupOf.1 h.2⟩
  change ρ ((((k : K ⧸ H).out : K)) : G) v = ρ (k : G) v
  rw [hh, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hfix]

/-- The restriction to invariants of a bijective intertwining map is bijective. -/
lemma invariantsLinearMap_bijective {ρ : Representation R Γ V} {σ : Representation R Γ W}
    (φ : ρ.IntertwiningMap σ) (hφ : Function.Bijective φ) :
    Function.Bijective (invariantsLinearMap φ) := by
  refine ⟨fun x y h => Subtype.ext (hφ.1 (congrArg Subtype.val h)), fun y => ?_⟩
  obtain ⟨v, hv⟩ := hφ.2 y
  refine ⟨⟨v, (Representation.mem_invariants ρ v).2 fun γ => hφ.1 ?_⟩, Subtype.ext hv⟩
  rw [Representation.IntertwiningMap.isIntertwining _ _ φ γ v, hv]
  exact (Representation.mem_invariants σ _).1 y.2 γ

variable (S : Type uS) [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]

include M

/-- **Invariants commute with localization for representations with finite orbits.** If `S` is
a localization of `R` at a submonoid `M` and every orbit of `ρ` is finite, then
`invariantsBaseChangeMap S ρ : S ⊗[R] ρ^Γ → (S ⊗[R] ρ)^Γ` is surjective. -/
theorem invariantsBaseChangeMap_surjective_of_isLocalization {ρ : Representation R Γ V}
    (hρ : HasFiniteOrbits ρ) : Function.Surjective (invariantsBaseChangeMap S ρ) := by
  have hloc : IsLocalizedModule M (TensorProduct.mk R S V 1) :=
    (isLocalizedModule_iff_isBaseChange M S _).2 (TensorProduct.isBaseChange R V S)
  rintro ⟨x, hx⟩
  obtain ⟨⟨v, m⟩, hm⟩ := IsLocalizedModule.surj M (TensorProduct.mk R S V 1) x
  replace hm : (m : R) • x = (1 : S) ⊗ₜ[R] v := by
    rw [← Submonoid.smul_def]; exact hm
  have h1 : ∀ γ : Γ, ∃ c : M, c • (ρ γ v - v) = 0 := fun γ => by
    refine (IsLocalizedModule.eq_zero_iff M (TensorProduct.mk R S V 1)).1 ?_
    have hγ : (1 : S) ⊗ₜ[R] ρ γ v = (1 : S) ⊗ₜ[R] v := by
      rw [← baseChangeRepresentation_apply_tmul, ← hm, LinearMap.map_smul_of_tower,
        (Representation.mem_invariants _ x).1 hx γ]
    rw [map_sub, TensorProduct.mk_apply, TensorProduct.mk_apply, hγ, sub_self]
  have h2 : ∀ w ∈ Set.range fun γ : Γ => ρ γ v, ∃ c : R, c ∈ M ∧ c • (w - v) = 0 := by
    rintro _ ⟨γ, rfl⟩
    obtain ⟨c, hc⟩ := h1 γ
    exact ⟨c, c.2, hc⟩
  choose! c hcM hc using h2
  let P : R := ∏ w ∈ (hρ v).toFinset, c w
  have hPM : P ∈ M := Submonoid.prod_mem _ fun w hw => hcM w ((hρ v).mem_toFinset.1 hw)
  have hP : ∀ γ : Γ, P • ρ γ v = P • v := fun γ => by
    have hw : ρ γ v ∈ (hρ v).toFinset := (hρ v).mem_toFinset.2 ⟨γ, rfl⟩
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem c hw
    rw [← sub_eq_zero, ← smul_sub]
    change (∏ w ∈ (hρ v).toFinset, c w) • (ρ γ v - v) = 0
    rw [hd, mul_comm, mul_smul, hc _ ⟨γ, rfl⟩, smul_zero]
  have hPv : P • v ∈ ρ.invariants := (Representation.mem_invariants ρ _).2 fun γ => by
    rw [map_smul, hP γ]
  let u : S := IsLocalization.mk' S (1 : R) (⟨(m : R) * P, M.mul_mem m.2 hPM⟩ : M)
  have hu : u * algebraMap R S ((m : R) * P) = 1 := by
    rw [IsLocalization.mk'_spec, map_one]
  refine ⟨u ⊗ₜ[R] ⟨P • v, hPv⟩, Subtype.ext ?_⟩
  change u ⊗ₜ[R] (P • v) = x
  calc u ⊗ₜ[R] (P • v) = u • (P • ((1 : S) ⊗ₜ[R] v)) := by
        rw [← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = u • (P • ((m : R) • x)) := by rw [hm]
    _ = (u * algebraMap R S ((m : R) * P)) • x := by
        rw [mul_smul, algebraMap_smul, mul_comm, mul_smul]
    _ = x := by rw [hu, one_smul]

/-- If `S` is a localization of `R` and every orbit of `ρ` is finite, then
`invariantsBaseChangeMap S ρ` is bijective. -/
theorem invariantsBaseChangeMap_bijective_of_isLocalization {ρ : Representation R Γ V}
    (hρ : HasFiniteOrbits ρ) : Function.Bijective (invariantsBaseChangeMap S ρ) :=
  have : Module.Flat R S := IsLocalization.flat S M
  ⟨invariantsBaseChangeMap_injective S ρ,
    invariantsBaseChangeMap_surjective_of_isLocalization S M hρ⟩

/-- For a localization `S` of `R` and a representation `ρ` with finite orbits, the `S`-linear
equivalence `S ⊗[R] ρ^Γ ≃ (S ⊗[R] ρ)^Γ` given by `invariantsBaseChangeMap`. -/
def invariantsBaseChangeEquivOfIsLocalization {ρ : Representation R Γ V}
    (hρ : HasFiniteOrbits ρ) :
    S ⊗[R] ρ.invariants ≃ₗ[S] (baseChangeRepresentation S ρ).invariants :=
  LinearEquiv.ofBijective (invariantsBaseChangeMap S ρ)
    (invariantsBaseChangeMap_bijective_of_isLocalization S M hρ)

/-- The underlying map of `invariantsBaseChangeEquivOfIsLocalization` is
`invariantsBaseChangeMap`. -/
@[simp]
lemma invariantsBaseChangeEquivOfIsLocalization_apply {ρ : Representation R Γ V}
    (hρ : HasFiniteOrbits ρ) (x : S ⊗[R] ρ.invariants) :
    invariantsBaseChangeEquivOfIsLocalization S M hρ x = invariantsBaseChangeMap S ρ x :=
  rfl

end Algebra

section Derived

variable {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear R C] [HasDerivedCategory.{s} C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [Linear S D] [HasDerivedCategory.{s'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable (hF : IsSemilinear R S F)
variable {Γ : Type uΓ} [Group Γ]

include M

open DerivedCategory

/-- If `S` is a localization of `R`, the action of `Γ` on `Hom(K, W₀⟦n⟧)` has finite orbits and
`abutmentBaseChangeMap` is bijective (the hypothesis `h`), then
`abutmentInvariantsBaseChangeMap` is bijective. -/
theorem abutmentInvariantsBaseChangeMap_bijective_of_isLocalization {K : DerivedCategory C}
    {W : C} (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ)
    (hfin : HasFiniteOrbits (abutmentRepresentation R ρ σ n))
    (h : Function.Bijective (abutmentBaseChangeMap F hF K W n)) :
    Function.Bijective (abutmentInvariantsBaseChangeMap F hF ρ σ n) :=
  (invariantsLinearMap_bijective (abutmentBaseChangeIntertwiningMap F hF ρ σ n) h).comp
    (invariantsBaseChangeMap_bijective_of_isLocalization S M hfin)

/-- If `S` is a localization of `R`, the action of `Γ` on `Hom(H^{-n} K, W)` has finite orbits
and `cohomologyHomBaseChangeMap` is bijective (the hypothesis `h`), then
`cohomologyHomInvariantsBaseChangeMap` is bijective. -/
theorem cohomologyHomInvariantsBaseChangeMap_bijective_of_isLocalization {K : DerivedCategory C}
    {W : C} (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ)
    (hfin : HasFiniteOrbits (cohomologyHomRepresentation R ρ σ n))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    Function.Bijective (cohomologyHomInvariantsBaseChangeMap F hF ρ σ n) :=
  (invariantsLinearMap_bijective (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n) h).comp
    (invariantsBaseChangeMap_bijective_of_isLocalization S M hfin)

variable [HasExt.{t} C] [HasExt.{t'} D]

/-- **Invariants of abutments and localization.** Under the degeneration hypotheses, if `S` is a
localization of `R`, the action of `Γ` on `Hom(H^{-n} K, W)` has finite orbits and
`cohomologyHomBaseChangeMap` is bijective (the hypothesis `h`), then
`abutmentInvariantsBaseChangeMap` is bijective. -/
theorem abutmentInvariantsBaseChangeMap_bijective_of_isLocalization_of_cohomologyHom
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (hfin : HasFiniteOrbits (cohomologyHomRepresentation R ρ σ n))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    Function.Bijective (abutmentInvariantsBaseChangeMap F hF ρ σ n) :=
  (abutmentInvariantsBaseChangeMap_bijective_iff F hF b hK hW hW' n ρ σ).2
    (cohomologyHomInvariantsBaseChangeMap_bijective_of_isLocalization M F hF ρ σ n hfin h)

/-- Under the hypotheses of
`abutmentInvariantsBaseChangeMap_bijective_of_isLocalization_of_cohomologyHom`, the `S`-linear
equivalence `S ⊗[R] Hom(K, W₀⟦n⟧)^Γ ≃ Hom(F K, (F W)₀⟦n⟧)^Γ` given by
`abutmentInvariantsBaseChangeMap`. -/
def abutmentInvariantsLocalizationEquiv
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (hfin : HasFiniteOrbits (cohomologyHomRepresentation R ρ σ n))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    S ⊗[R] (abutmentRepresentation R ρ σ n).invariants ≃ₗ[S]
      (abutmentRepresentation S ((F.mapDerivedCategory.mapAut K).comp ρ)
        ((F.mapAut W).comp σ) n).invariants :=
  LinearEquiv.ofBijective (abutmentInvariantsBaseChangeMap F hF ρ σ n)
    (abutmentInvariantsBaseChangeMap_bijective_of_isLocalization_of_cohomologyHom M F hF b hK hW
      hW' n ρ σ hfin h)

/-- The underlying map of `abutmentInvariantsLocalizationEquiv` is
`abutmentInvariantsBaseChangeMap`. -/
@[simp]
lemma abutmentInvariantsLocalizationEquiv_apply
    {K : DerivedCategory C} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) {W : C}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (hfin : HasFiniteOrbits (cohomologyHomRepresentation R ρ σ n))
    (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n)))
    (x : S ⊗[R] (abutmentRepresentation R ρ σ n).invariants) :
    abutmentInvariantsLocalizationEquiv M F hF b hK hW hW' n ρ σ hfin h x =
      abutmentInvariantsBaseChangeMap F hF ρ σ n x :=
  rfl

end Derived

section Smooth

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S] [Module.Flat R S]
  (M : Submonoid R) [IsLocalization M S]
  (G : Type uG) [Group G] [TopologicalSpace G]
  [HasDerivedCategory.{s} (SmoothRep.{uR, uG, w} R G)]
  [HasDerivedCategory.{s'} (SmoothRep.{uS, uG, max uS w} S G)]
  {Γ : Type uΓ} [Group Γ]

include M

open DerivedCategory

/-- `cohomologyHomInvariantsBaseChangeMap_bijective_of_isLocalization` for extension of scalars of
smooth representations along a localization `R → S`. -/
theorem smoothCohomologyHomInvariantsBaseChangeMap_bijective_of_isLocalization
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} {W : SmoothRep.{uR, uG, w} R G}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ)
    (hfin : HasFiniteOrbits (cohomologyHomRepresentation R ρ σ n))
    (h : Function.Bijective
      (smoothCohomologyHomBaseChangeMap.{w, uR, uS, uG, s, s'} R S G K W (-n))) :
    Function.Bijective
      (smoothCohomologyHomInvariantsBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n) :=
  cohomologyHomInvariantsBaseChangeMap_bijective_of_isLocalization M
    (smoothRepExtendScalars.{w} R S G) (smoothRepExtendScalars_isSemilinear.{w} R S G) ρ σ n
    hfin h

variable [HasExt.{t} (SmoothRep.{uR, uG, w} R G)] [HasExt.{t'} (SmoothRep.{uS, uG, max uS w} S G)]

/-- `abutmentInvariantsBaseChangeMap_bijective_of_isLocalization_of_cohomologyHom` for extension
of scalars of smooth representations along a localization `R → S`. -/
theorem smoothAbutmentInvariantsBaseChangeMap_bijective_of_isLocalization
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K))
    {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (hfin : HasFiniteOrbits (cohomologyHomRepresentation R ρ σ n))
    (h : Function.Bijective
      (smoothCohomologyHomBaseChangeMap.{w, uR, uS, uG, s, s'} R S G K W (-n))) :
    Function.Bijective
      (smoothAbutmentInvariantsBaseChangeMap.{w, uR, uS, uG, s, s'} R S G ρ σ n) :=
  abutmentInvariantsBaseChangeMap_bijective_of_isLocalization_of_cohomologyHom M
    (smoothRepExtendScalars.{w} R S G) (smoothRepExtendScalars_isSemilinear.{w} R S G) b hK hW
    hW' n ρ σ hfin h

/-- `abutmentInvariantsLocalizationEquiv` for extension of scalars of smooth representations along
a localization `R → S`: under the hypotheses of
`smoothAbutmentInvariantsBaseChangeMap_bijective_of_isLocalization`,
`smoothAbutmentInvariantsBaseChangeMap` as an `S`-linear equivalence. -/
def smoothAbutmentInvariantsLocalizationEquiv
    {K : DerivedCategory (SmoothRep.{uR, uG, w} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K))
    {W : SmoothRep.{uR, uG, w} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w} R S G).obj W) i))
    (n : ℤ) (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (hfin : HasFiniteOrbits (cohomologyHomRepresentation R ρ σ n))
    (h : Function.Bijective
      (smoothCohomologyHomBaseChangeMap.{w, uR, uS, uG, s, s'} R S G K W (-n))) :
    S ⊗[R] (abutmentRepresentation R ρ σ n).invariants ≃ₗ[S]
      (abutmentRepresentation S
        (((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.mapAut K).comp ρ)
        (((smoothRepExtendScalars.{w} R S G).mapAut W).comp σ) n).invariants :=
  abutmentInvariantsLocalizationEquiv M (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) b hK hW hW' n ρ σ hfin h

end Smooth

end HyperextScalarExtension

end Langlands.Cohomology
