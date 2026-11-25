/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing
public import WeilConjectures.Mathlib.RingTheory.Etale.Weakly

/-!
# Étale cohomology of a strictly henselian local scheme

Let `R` be a strictly henselian local ring and `X = Spec R`. Every étale morphism `U ⟶ X`
whose image contains the closed point has a section: if `Spec B ⊆ U` is an affine open
containing a point `y` over the closed point and `n ⊆ B` the corresponding prime, then
`R ⟶ B_n` is a local weakly étale homomorphism of local rings, hence bijective since `R` is
strictly henselian (`Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing`), and
`B ⟶ B_n ≅ R` defines the section.

Consequently every covering sieve of the terminal object of the small étale site of `X`
contains the identity. So the global sections functor is exact, the constant sheaf `ℤ` which
corepresents it is projective, and `Hⁿ(X_ét, F) = 0` for every abelian sheaf `F` and `n > 0`;
moreover the global sections of the constant sheaf with value `A` are `A`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_section_of_etale_of_isStrictlyHenselianLocalRing`: étale
  neighbourhoods of the closed point have sections.
- `AlgebraicGeometry.Scheme.subsingleton_H_of_isStrictlyHenselianLocalRing`:
  `Hⁿ(Spec R_ét, F) = 0` for `n > 0`.
- `AlgebraicGeometry.Scheme.hZeroConstantSheafAddEquiv`:
  `H⁰(Spec R_ét, A) ≅ A` for the constant sheaf with value `A`.

## References

- Stacks Project, Lemma 59.55.1, <https://stacks.math.columbia.edu/tag/03QO>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]

/-- The terminal object `𝟙 : Spec R ⟶ Spec R` of the small étale site of `Spec R`. -/
noncomputable def etaleTerminal : (Spec (.of R)).Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of R)))
    (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of R)))

/-- `𝟙 : Spec R ⟶ Spec R` is the terminal object of the small étale site of `Spec R`. -/
noncomputable def isTerminalEtaleTerminal : IsTerminal (etaleTerminal R) :=
  MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of R))

variable {R}

/-- Over a strictly henselian local ring `R`, an étale morphism `f : U ⟶ Spec R` whose image
contains the closed point has a section. -/
theorem exists_section_of_etale_of_isStrictlyHenselianLocalRing {U : Scheme.{u}}
    (f : U ⟶ Spec (.of R)) [AlgebraicGeometry.Etale f] (y : U)
    (hy : f y = IsLocalRing.closedPoint R) :
    ∃ σ : Spec (.of R) ⟶ U, σ ≫ f = 𝟙 _ := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hV : IsAffineOpen V := hV
  let B := Γ(U, V)
  let φ : CommRingCat.of R ⟶ B := Spec.preimage (hV.fromSpec ≫ f)
  have hφ : Spec.map φ = hV.fromSpec ≫ f := Spec.map_preimage _
  have hφe : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale), hφ]
    infer_instance
  algebraize [φ.hom]
  let n := hV.primeIdealOf ⟨y, hyV⟩
  have hn : n.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal R := by
    have h : (Spec.map φ) n = IsLocalRing.closedPoint R := by
      change (Spec.map φ) (hV.primeIdealOf ⟨y, hyV⟩) = _
      rw [hφ, Scheme.Hom.comp_apply, hV.fromSpec_primeIdealOf, hy]
    exact congrArg PrimeSpectrum.asIdeal h
  let Bn := Localization.AtPrime n.asIdeal
  have : Algebra.WeaklyEtale R B := inferInstance
  have : Algebra.WeaklyEtale R Bn := Algebra.WeaklyEtale.trans R B Bn
  have : IsLocalHom (algebraMap R Bn) := by
    refine ⟨fun x hx ↦ ?_⟩
    rw [IsScalarTower.algebraMap_apply R B Bn,
      IsLocalization.AtPrime.isUnit_to_map_iff Bn n.asIdeal] at hx
    by_contra hx'
    exact hx (by
      have : x ∈ IsLocalRing.maximalIdeal R := hx'
      rw [← hn] at this
      exact this)
  have hbij := Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing (R := R) (S := Bn)
  let e : R ≃+* Bn := RingEquiv.ofBijective (algebraMap R Bn) hbij
  let ψ : B ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (e.symm.toRingHom.comp (algebraMap B Bn))
  have hψ : φ ≫ ψ = 𝟙 _ := by
    ext x
    change e.symm (algebraMap B Bn (algebraMap R B x)) = x
    rw [← IsScalarTower.algebraMap_apply R B Bn]
    exact e.symm_apply_apply x
  refine ⟨Spec.map ψ ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, hψ, Spec.map_id]

variable (R)

/-- Over a strictly henselian local ring `R`, every covering sieve of `Spec R` in the small étale
site contains the identity. -/
lemma id_mem_of_mem_smallEtaleTopology_of_isStrictlyHenselianLocalRing
    (S : Sieve (etaleTerminal R))
    (hS : S ∈ (Spec (.of R)).smallEtaleTopology (etaleTerminal R)) : S.arrows (𝟙 _) := by
  obtain ⟨𝒰, h𝒰, p, hle⟩ := (mem_smallGrothendieckTopology _ _).1 hS
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq (IsLocalRing.closedPoint R)
  have : AlgebraicGeometry.Etale (𝒰.f j) := 𝒰.map_prop j
  obtain ⟨σ, hσ⟩ := exists_section_of_etale_of_isStrictlyHenselianLocalRing (𝒰.f j) y hy
  have hmem : S.arrows ((𝒰.f j).asOverProp _) := hle _ _ (Presieve.ofArrows.mk j)
  convert S.downward_closed hmem (MorphismProperty.Over.homMk (A := (etaleTerminal R))
    (B := (𝒰.X j).asOverProp _ (p j)) σ (by
      change σ ≫ (𝒰.X j ↘ _) = 𝟙 _
      rw [← comp_over (𝒰.f j), ← Category.assoc, hσ, Category.id_comp]
      rfl))
  exact MorphismProperty.Over.Hom.ext hσ.symm

/-- Over a strictly henselian local ring `R`, an epimorphism of étale sheaves on `Spec R` with
values in a concrete category is surjective on global sections. -/
lemma surjective_app_of_epi_of_isStrictlyHenselianLocalRing {A : Type*} [Category A]
    {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]
    [(Spec (.of R)).smallEtaleTopology.WEqualsLocallyBijective A]
    [HasSheafify (Spec (.of R)).smallEtaleTopology A]
    [(Spec (.of R)).smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    [Balanced (Sheaf (Spec (.of R)).smallEtaleTopology A)]
    {F G : Sheaf (Spec (.of R)).smallEtaleTopology A} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (etaleTerminal R))) := by
  have := (Sheaf.isLocallySurjective_iff_epi' A φ).2 inferInstance
  intro s
  obtain ⟨t, ht⟩ := id_mem_of_mem_smallEtaleTopology_of_isStrictlyHenselianLocalRing R _
    (Presheaf.imageSieve_mem (Spec (.of R)).smallEtaleTopology φ.hom
      (U := op (etaleTerminal R)) s)
  exact ⟨t, ht.trans (by simp)⟩

instance preservesEpimorphisms_sheafSections_of_isStrictlyHenselianLocalRing :
    ((sheafSections (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (etaleTerminal R))).PreservesEpimorphisms where
  preserves φ _ := (AddCommGrpCat.epi_iff_surjective _).2
    (surjective_app_of_epi_of_isStrictlyHenselianLocalRing R φ)

/-- Over a strictly henselian local ring `R`, the constant sheaf `ℤ` on the small étale site of
`Spec R` is projective: it corepresents the global sections functor, which is exact. -/
instance projective_constantSheaf_of_isStrictlyHenselianLocalRing :
    Projective ((constantSheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))) :=
  @Adjunction.map_projective _ _ _ _ _ _
    (constantSheafAdj _ _ (isTerminalEtaleTerminal R))
    (preservesEpimorphisms_sheafSections_of_isStrictlyHenselianLocalRing R) _
    AddCommGrpCat.projective_of_uliftInt

/-- Over a strictly henselian local ring `R`, every abelian étale sheaf on `Spec R` has no
cohomology in positive degrees. -/
theorem subsingleton_H_of_isStrictlyHenselianLocalRing
    (F : Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) :=
  Abelian.Ext.subsingleton_of_projective _ _ _

/-- Over a strictly henselian local ring `R`, the sections over `Spec R` of an étale presheaf of
abelian groups and of its sheafification agree. -/
lemma bijective_toSheafify_app_of_isStrictlyHenselianLocalRing
    (P : (Spec (.of R)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Function.Bijective
      ((toSheafify (Spec (.of R)).smallEtaleTopology P).app (op (etaleTerminal R))) := by
  refine ⟨fun a b hab ↦ ?_, fun s ↦ ?_⟩
  · have hmem := Presheaf.equalizerSieve_mem (Spec (.of R)).smallEtaleTopology
      (toSheafify (Spec (.of R)).smallEtaleTopology P) a b hab
    simpa using id_mem_of_mem_smallEtaleTopology_of_isStrictlyHenselianLocalRing R _ hmem
  · obtain ⟨t, ht⟩ := id_mem_of_mem_smallEtaleTopology_of_isStrictlyHenselianLocalRing R _
      (Presheaf.imageSieve_mem (Spec (.of R)).smallEtaleTopology
        (toSheafify (Spec (.of R)).smallEtaleTopology P) s)
    exact ⟨t, ht.trans (by simp)⟩

/-- Over a strictly henselian local ring `R`, the cohomology in degree `0` of the constant
étale sheaf on `Spec R` with value `A` is `A`. -/
noncomputable def hZeroConstantSheafAddEquiv
    (A : AddCommGrpCat.{u + 1}) :
    Sheaf.H ((constantSheaf (Spec (.of R)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj A) 0 ≃+ A :=
  (Sheaf.H.equiv₀ _ (isTerminalEtaleTerminal R)).trans
    (AddEquiv.ofBijective _
      (bijective_toSheafify_app_of_isStrictlyHenselianLocalRing R
        ((Functor.const _).obj A))).symm

end AlgebraicGeometry.Scheme
