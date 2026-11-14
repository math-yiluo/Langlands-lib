import Langlands.Global.AdelicGaloisTwistTorus
import Langlands.Global.AdelicGaloisRootAction
import Langlands.Global.AdelicGaloisTwistSubgroup
import Langlands.Global.AdelicNormalizerConjugation
import Langlands.Global.AdelicGaloisRootActionProof
import Langlands.GroupScheme.Torus.ConnectedReductive

/-! # Galois twisting of a split Borel pair from a Galois root action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Torus

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] [FiniteDimensional F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffine T₀.toGrp.X.left] [LocallyOfFiniteType T₀.toGrp.X.hom]
  (i₀ : T₀.toGrp ⟶ G)

/-- The base change `i₀_L : T₀_L → G_L` of a homomorphism `i₀ : T₀ → G`. -/
abbrev torusInclusion :
    ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp ⟶
      AffineWeil.unitBaseChange F L G :=
  (GroupScheme.baseChange (algebraBaseMap F L)).map i₀

/-- The twist of `G_L` on the image of an adelic torus point is the image of the twisted
torus point. -/
theorem galoisTwist_map_torusInclusion (σ : L ≃ₐ[F] L)
    (t : AdelicGroupPoints L ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp) :
    galoisTwist F L G σ (map L _ (AffineWeil.unitBaseChange F L G)
        (torusInclusion F L G T₀ i₀) t) =
      map L _ (AffineWeil.unitBaseChange F L G) (torusInclusion F L G T₀ i₀)
        (galoisTwistLie F L T₀ σ t) :=
  galoisTwist_comp_baseChange F L G T₀.toGrp σ i₀ t

end Torus

section Conjugation

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] [FiniteDimensional F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

omit [NumberField F] [NumberField L] [FiniteDimensional F L] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
/-- The rational coefficient point of a section over the base is its base point. -/
theorem rationalCoeffEquiv_eq_basePointEquiv
    (m : rationalPoints (AffineWeil.unitBaseChange F L G)) :
    rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G) m = basePointEquiv m := by
  apply Over.OverMorphism.ext
  rw [rationalCoeffEquiv_left, basePointEquiv_apply, Over.comp_left]
  exact (Category.id_comp _).symm

omit [NumberField F] [FiniteDimensional F L] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
/-- The rational section of a rational point is the principal adelic point of its base
point. -/
theorem rationalSection_eq_rational_basePointEquiv
    (m : rationalPoints (AffineWeil.unitBaseChange F L G)) :
    rationalSection F L G m = rational L (AffineWeil.unitBaseChange F L G) (basePointEquiv m) :=
  congrArg (rational L (AffineWeil.unitBaseChange F L G))
    (rationalCoeffEquiv_eq_basePointEquiv F L G m)

variable {F L G} {T : CommGroupScheme (Spec (CommRingCat.of L))}

omit [NumberField F] [FiniteDimensional F L] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
/-- If `m⁻¹` normalizes `i` through `τ`, then `i(s)` is the `m`-conjugate of
`i(τ s)`. -/
theorem map_eq_rationalSection_conj (i : T.toGrp ⟶ AffineWeil.unitBaseChange F L G)
    {m : rationalPoints (AffineWeil.unitBaseChange F L G)} {τ : T ≅ T}
    (h : IsNormalizingPoint i m⁻¹ τ) (s : AdelicGroupPoints L T.toGrp) :
    map L T.toGrp _ i s =
      rationalSection F L G m *
        map L T.toGrp _ i (map L T.toGrp T.toGrp (CommGroupScheme.groupHom τ.symm.inv) s) *
          (rationalSection F L G m)⁻¹ := by
  have h' : IsNormalizingPoint i m τ.symm := by
    have := h.inv
    rwa [inv_inv] at this
  rw [rationalSection_eq_rational_basePointEquiv, eq_mul_inv_iff_mul_eq]
  exact map_mul_rational_basePointEquiv h' s

local instance : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom :=
  isAffineHom_of_isAffine _

/-- Clause 3 of a Galois Borel twist for one adelic torus point `t`, from a twisted point
`t₁` with `φ(i t) = i t₁`, a normalizing point `m⁻¹` with automorphism `τ`, preservation of
the norm-one subgroup, and the simple-root norm comparison for `τ s` against `t`. -/
theorem exists_galoisTwist_torus_conj (σ : L ≃ₐ[F] L)
    (i : T.toGrp ⟶ AffineWeil.unitBaseChange F L G) (ν : cocharacterLattice T)
    {m : rationalPoints (AffineWeil.unitBaseChange F L G)} {τ : T ≅ T}
    (h : IsNormalizingPoint i m⁻¹ τ)
    (hN : ∀ x, x ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G) →
      galoisTwist F L G σ x ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G))
    (t t₁ : AdelicGroupPoints L T.toGrp)
    (hφ : galoisTwist F L G σ (map L T.toGrp _ i t) = map L T.toGrp _ i t₁)
    (hβ : ∀ β ∈ simpleRelativeRoots i ν, ∃ β' ∈ simpleRelativeRoots i ν,
      PositiveRealTorus.normCharacter L T (τ.symm.inv ≫ β) t₁ =
        PositiveRealTorus.normCharacter L T β' t) :
    ∃ t' : AdelicGroupPoints L T.toGrp,
      galoisTwist F L G σ (map L T.toGrp _ i t) =
          rationalSection F L G m * map L T.toGrp _ i t' * (rationalSection F L G m)⁻¹ ∧
        (map L T.toGrp _ i t ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G) →
          map L T.toGrp _ i t' ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G)) ∧
        ∀ β ∈ simpleRelativeRoots i ν, ∃ β' ∈ simpleRelativeRoots i ν,
          PositiveRealTorus.normCharacter L T β t' = PositiveRealTorus.normCharacter L T β' t := by
  refine ⟨map L T.toGrp T.toGrp (CommGroupScheme.groupHom τ.symm.inv) t₁, ?_, ?_, ?_⟩
  · rw [hφ]
    exact map_eq_rationalSection_conj i h t₁
  · intro ht
    have h1 := hN _ ht
    rw [hφ, map_eq_rationalSection_conj i h t₁] at h1
    have h2 := (normOneSubgroup_normal L (AffineWeil.unitBaseChange F L G)).conj_mem _ h1
      (rationalSection F L G m)⁻¹
    have e : map L T.toGrp _ i (map L T.toGrp T.toGrp (CommGroupScheme.groupHom τ.symm.inv) t₁) =
        (rationalSection F L G m)⁻¹ * (rationalSection F L G m *
          map L T.toGrp _ i (map L T.toGrp T.toGrp (CommGroupScheme.groupHom τ.symm.inv) t₁) *
            (rationalSection F L G m)⁻¹) * (rationalSection F L G m)⁻¹⁻¹ := by
      group
    rw [e]
    exact h2
  · intro β hβ₀
    obtain ⟨β', hβ', e⟩ := hβ β hβ₀
    exact ⟨β', hβ', (normCharacter_map_groupHom_inv τ.symm β t₁).trans e⟩

end Conjugation

section RootMap

variable (F L : Type u) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
  (τ : (L ≃ₐ[F] L) → ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀ ≅
    (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))

local instance : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom :=
  isAffineHom_of_isAffine _

omit [FiniteDimensional F L] in
/-- Each Galois root map is injective on characters. -/
theorem galoisRootMap_injective (σ : L ≃ₐ[F] L) :
    Function.Injective (galoisRootMap F L T₀ τ σ) := by
  intro x y hxy
  have h := (characterAut (τ σ)).injective hxy
  have h' := congrArg (characterLattice.galoisRepresentation F L T₀ σ⁻¹) h
  rwa [Representation.inv_self_apply, Representation.inv_self_apply] at h'

omit [FiniteDimensional F L] in
/-- The Galois root map `a σ` sends `σ⁻¹ (τ σ · β)` back to `β`. -/
theorem galoisRootMap_galoisRepresentation_inv (σ : L ≃ₐ[F] L)
    (β : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)) :
    galoisRootMap F L T₀ τ σ
        (characterLattice.galoisRepresentation F L T₀ σ⁻¹ ((τ σ).symm.inv ≫ β)) = β := by
  rw [galoisRootMap, Representation.self_inv_apply, characterAut_apply, Iso.symm_inv,
    Iso.inv_hom_id_assoc]

variable {F L G T₀ τ}
variable {i : ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp ⟶
    AffineWeil.unitBaseChange F L G}
  {ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)}
  {m : (L ≃ₐ[F] L) → rationalPoints (AffineWeil.unitBaseChange F L G)}

omit [FiniteDimensional F L] [LocallyOfFiniteType G.X.hom] in
/-- Under a Galois root action, `a σ (a σ⁻¹ β) = β` for every simple root `β`. -/
theorem IsGaloisRootAction.galoisRootMap_galoisRootMap_inv (hR : IsGaloisRootAction F L G T₀ i ν m τ)
    (σ : L ≃ₐ[F] L) {β} (hβ : β ∈ simpleRelativeRoots i ν) :
    galoisRootMap F L T₀ τ σ (galoisRootMap F L T₀ τ σ⁻¹ β) = β := by
  rw [← hR.2.2.2.2 σ σ⁻¹ β hβ, mul_inv_cancel, hR.2.2.2.1 β hβ]

omit [FiniteDimensional F L] [LocallyOfFiniteType G.X.hom] in
/-- Under a Galois root action, the root `σ⁻¹ (τ σ · β)` is simple for every simple root
`β`. -/
theorem IsGaloisRootAction.galoisRepresentation_inv_mem (hR : IsGaloisRootAction F L G T₀ i ν m τ)
    (σ : L ≃ₐ[F] L) {β} (hβ : β ∈ simpleRelativeRoots i ν) :
    characterLattice.galoisRepresentation F L T₀ σ⁻¹ ((τ σ).symm.inv ≫ β) ∈
      simpleRelativeRoots i ν := by
  have e : characterLattice.galoisRepresentation F L T₀ σ⁻¹ ((τ σ).symm.inv ≫ β) =
      galoisRootMap F L T₀ τ σ⁻¹ β :=
    galoisRootMap_injective F L T₀ τ σ ((galoisRootMap_galoisRepresentation_inv F L T₀ τ σ β).trans
      (hR.galoisRootMap_galoisRootMap_inv σ hβ).symm)
  rw [e]
  exact hR.2.1 σ⁻¹ β hβ

omit [FiniteDimensional F L] [LocallyOfFiniteType G.X.hom] in
/-- Under a Galois root action, each `a σ` permutes the simple roots. -/
theorem IsGaloisRootAction.image_simpleRelativeRoots (hR : IsGaloisRootAction F L G T₀ i ν m τ)
    (σ : L ≃ₐ[F] L) :
    galoisRootMap F L T₀ τ σ '' simpleRelativeRoots i ν = simpleRelativeRoots i ν :=
  Set.Subset.antisymm (Set.image_subset_iff.mpr fun β hβ => hR.2.1 σ β hβ)
    fun β hβ => ⟨galoisRootMap F L T₀ τ σ⁻¹ β, hR.2.1 σ⁻¹ β hβ,
      hR.galoisRootMap_galoisRootMap_inv σ hβ⟩

omit [FiniteDimensional F L] [LocallyOfFiniteType G.X.hom] in
/-- Under a Galois root action, `a σ` carries the complement of `β` in the simple roots to the
complement of `a σ β`. -/
theorem IsGaloisRootAction.image_diff_singleton (hR : IsGaloisRootAction F L G T₀ i ν m τ)
    (σ : L ≃ₐ[F] L) (β) :
    galoisRootMap F L T₀ τ σ '' (simpleRelativeRoots i ν \ {β}) =
      simpleRelativeRoots i ν \ {galoisRootMap F L T₀ τ σ β} := by
  rw [Set.image_sdiff (galoisRootMap_injective F L T₀ τ σ), hR.image_simpleRelativeRoots σ,
    Set.image_singleton]

end RootMap

section Core

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffine T₀.toGrp.X.left] [LocallyOfFiniteType T₀.toGrp.X.hom]
  (i₀ : T₀.toGrp ⟶ G)

local instance : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom :=
  isAffineHom_of_isAffine _

omit [IsGalois F L] [LocallyOfFiniteType G.X.hom] in
/-- The simple-root norm comparison of clause 3: for a simple root `β`, the root
`β' = σ⁻¹ (τ σ · β)` is simple, and the norm of `τ σ · β` at the twisted point is the norm of
`β'` at the original point. -/
theorem exists_normCharacter_galoisTwistLie
    {ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)}
    {m : (L ≃ₐ[F] L) → rationalPoints (AffineWeil.unitBaseChange F L G)}
    {τ : (L ≃ₐ[F] L) → ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀ ≅
      (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)}
    (hR : IsGaloisRootAction F L G T₀ (torusInclusion F L G T₀ i₀) ν m τ) (σ : L ≃ₐ[F] L)
    (t : AdelicGroupPoints L ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp)
    (β) (hβ : β ∈ simpleRelativeRoots (torusInclusion F L G T₀ i₀) ν) :
    ∃ β' ∈ simpleRelativeRoots (torusInclusion F L G T₀ i₀) ν,
      PositiveRealTorus.normCharacter L ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)
          ((τ σ).symm.inv ≫ β) (galoisTwistLie F L T₀ σ t) =
        PositiveRealTorus.normCharacter L
          ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀) β' t := by
  refine ⟨_, hR.galoisRepresentation_inv_mem σ hβ, ?_⟩
  have h := normCharacter_galoisTwist F L T₀ σ
    (characterLattice.galoisRepresentation F L T₀ σ⁻¹ ((τ σ).symm.inv ≫ β)) t
  rwa [Representation.self_inv_apply] at h

/-- The core of the twisting proof: a Galois root action for the base change of a ground
torus, together with Lemma S, gives a Galois twisting of the split Borel pair, with the
twists `galoisTwist F L G σ`, the rational points `m σ` and the root maps `galoisRootMap τ σ`. -/
theorem hasGaloisBorelTwisting_of_rootAction
    (hS1 : GaloisTwistNormOneStatement.{u}) (hS2 : GaloisTwistSubgroupStatement.{u})
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (m : (L ≃ₐ[F] L) → rationalPoints (AffineWeil.unitBaseChange F L G))
    (τ : (L ≃ₐ[F] L) → ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀ ≅
      (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (hR : IsGaloisRootAction F L G T₀ (torusInclusion F L G T₀ i₀) ν m τ) :
    HasGaloisBorelTwisting F L G ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)
      (torusInclusion F L G T₀ i₀) ν := by
  refine ⟨fun σ => galoisTwist F L G σ, m, galoisRootMap F L T₀ τ, fun σ => ?_, hR.2.2.2.1,
    hR.2.2.2.2⟩
  have hcl := Standard.isClosedSubgroup_parabolicHom (torusInclusion F L G T₀ i₀) ν ∅
  refine ⟨galoisTwist_rationalSection F L G σ, galoisTwist_scalarExtension F L G σ,
    fun t => ?_, fun p => ?_, fun β hβ => ⟨hR.2.1 σ β hβ, ?_⟩⟩
  · exact exists_galoisTwist_torus_conj σ (torusInclusion F L G T₀ i₀) ν (hR.1 σ)
      (hS1 F L G σ) t (galoisTwistLie F L T₀ σ t)
      (galoisTwist_map_torusInclusion F L G T₀ i₀ σ t)
      (fun β hβ => exists_normCharacter_galoisTwistLie F L G T₀ i₀ hR σ t β hβ)
  · have hr := hR.2.2.1 σ ∅ (Set.empty_subset _)
    rw [Set.image_empty] at hr
    exact hS2 F L G σ _ _ _ _ (m σ) hcl hcl hr p
  · have hr := hR.2.2.1 σ (simpleRelativeRoots (torusInclusion F L G T₀ i₀) ν \ {β})
      Set.sdiff_subset
    rwa [hR.image_diff_singleton σ β] at hr

end Core

open TorusExistence in
/-- Lemma S gives the Galois Borel twisting statement: choose a maximal torus `T₀` of `G`
over `F`, a finite Galois extension `L` splitting it and a generic cocharacter `ν` of the
split maximal torus `T₀_L` of `G_L`; Lemma Q (`splitBorelGaloisRootAction`) supplies the
Galois root action, and `hasGaloisBorelTwisting_of_rootAction` the twisting. -/
theorem galoisBorelTwisting_of (hS1 : GaloisTwistNormOneStatement.{u})
    (hS2 : GaloisTwistSubgroupStatement.{u}) : GaloisBorelTwistingStatement.{u} := by
  intro F _ _ G _ _ hG
  let _ : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨T₀, i₀, hi⟩ := maximalTorusExistence F G
  obtain ⟨L, _, _, hfin, hgal, hT⟩ := torusFiniteGaloisSplitting F T₀.toGrp hi.1
  let _ : NumberField L := NumberField.of_module_finite F L
  have hTR := IsTorus.isConnectedReductive_of_fieldSplitting hi.1
  have : IsAffineHom T₀.toGrp.X.hom := hTR.isAffineHom
  have : Smooth T₀.toGrp.X.hom := hTR.smooth
  have : IsAffine T₀.toGrp.X.left := isAffine_of_isAffineHom T₀.toGrp.X.hom
  let _ : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom := isAffineHom_of_isAffine _
  have : LocallyOfFiniteType (AffineWeil.unitBaseChange F L G).X.hom :=
    locallyOfFiniteType_baseChange L G
  obtain ⟨ν, hν⟩ := hT.exists_genericCocharacter (torusInclusion F L G T₀ i₀)
  obtain ⟨m, τ, hR⟩ := splitBorelGaloisRootAction F L G T₀ i₀ hG hi hT ν hν
  exact ⟨{ carrier := L
           finiteDimensional := hfin
           isGalois := hgal
           torus := (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀
           inclusion := torusInclusion F L G T₀ i₀
           isSplitTorus := hT
           isMaximalTorus := (maximalTorusBaseChange F L G T₀ i₀ hi.1 hi.2.1).mp hi },
    ν, hν, hasGaloisBorelTwisting_of_rootAction F L G T₀ i₀ hS1 hS2 ν m τ hR⟩

end Langlands.Global.AdelicGaloisUnit
