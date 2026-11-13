import Langlands.VirtualRepresentation.UnitaryDegreeGenerators
import Langlands.Global.Factors.HenniartCompositeMapStatement
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransportOperations
import Langlands.VirtualRepresentation.DescentProof
import Langlands.Global.Factors.HenniartCompositeOperationWeil
import Langlands.Global.Factors.HenniartCompositeOperationSupercuspidalTwist

/-!
# Proof of the transport of the operation clauses to Henniart's composite map

`HenniartCompositeOperationStatement`: if a generated positive isometry `T`
between the relative Weil and automorphic images at a finite place `v` has the
contragredient, twist and character clauses at `F_v`, then for every
`ℚ_p`-algebra isomorphism `f : K ≅ F_v` the composite `henniartCompositeMap`
at `K` has the operation properties of Henniart's 3.8. Every clause at `K` is
read off from the corresponding clause at `F_v`, because both pullbacks along
`f` preserve pairings, degrees and generators and commute with the
contragredients, the twists and the rank-one classes.
-/

noncomputable section

open CategoryTheory

universe u uF uE uK uW uP uV

namespace Langlands.VirtualRepresentation

/-- A linear equivalence that sends each generator to the generator of a
bijectively relabelled basis element sends exactly the generators to generators. -/
theorem exists_generator_iff_of_map_generator {ι κ : Type*}
    (L : IntegralLattice ι ≃ₗ[ℤ] IntegralLattice κ) (e : ι ≃ κ)
    (hL : ∀ i, L (generator i) = generator (e i)) (x : IntegralLattice ι) :
    (∃ j, L x = generator j) ↔ ∃ i, x = generator i := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨e.symm j, L.injective ?_⟩
    rw [hj, hL, Equiv.apply_symm_apply]
  · rintro ⟨i, rfl⟩
    exact ⟨e i, hL i⟩

/-- For an integral functional that is positive on every generator, a vector of
self-pairing one and positive value is a generator. -/
theorem exists_generator_of_pairing_self_eq_one {ι : Type*}
    (d : IntegralLattice ι →ₗ[ℤ] ℤ) (hd : ∀ i, 0 < d (generator i))
    (x : IntegralLattice ι) (hx : pairing x x = 1) (hpos : 0 < d x) :
    ∃ i, x = generator i := by
  obtain ⟨i, hi, -⟩ := integralNormOneSignedBasis ι x hx
  rcases hi with hi | hi
  · exact ⟨i, hi⟩
  · have hdi := hd i
    rw [hi, map_neg] at hpos
    omega

namespace LocalWeil

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

theorem unitaryDegree_generator_pos (b : UnitaryBasis.{uF, uV} F) :
    0 < unitaryDegree F (generator b) := by
  rw [unitaryDegree_generator]
  exact_mod_cast (b.val.1 : ℕ+).pos

end LocalWeil

namespace PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

theorem unitaryDegree_generator_pos (b : UnitaryBasis.{uF, uV} F) :
    0 < unitaryDegree F (generator b) := by
  rw [unitaryDegree_generator]
  exact_mod_cast (b.val.1 : ℕ+).pos

end PadicSupercuspidal

end Langlands.VirtualRepresentation

namespace Langlands.Global

open Langlands.VirtualRepresentation Langlands.Global.CompletionPadic

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- The supercuspidal pullback to `K` relabels generators bijectively. -/
theorem exists_completionSupercuspidalLatticeEquiv_generator :
    ∃ e : PadicSupercuspidal.UnitaryBasis.{u, uV} (padicField v) ≃
        PadicSupercuspidal.UnitaryBasis.{uK, uV} K,
      ∀ b, completionSupercuspidalLatticeEquiv v h K f (generator b) = generator (e b) := by
  subst h
  exact ⟨PadicSupercuspidal.unitaryBasisEquiv K (padicFieldAt v rfl) f,
    PadicSupercuspidal.unitaryLatticeEquiv_generator K (padicFieldAt v rfl) f⟩

/-- The supercuspidal pullback to `K` preserves the multiplicity pairing. -/
theorem unitaryPairing_completionSupercuspidalLatticeEquiv
    (x y : PadicSupercuspidal.UnitaryLattice.{u, uV} (padicField v)) :
    PadicSupercuspidal.unitaryPairing K (completionSupercuspidalLatticeEquiv v h K f x)
        (completionSupercuspidalLatticeEquiv v h K f y) =
      PadicSupercuspidal.unitaryPairing (padicField v) x y := by
  subst h
  exact PadicSupercuspidal.unitaryPairing_unitaryLatticeEquiv K (padicFieldAt v rfl) f x y

/-- The supercuspidal pullback to `K` preserves the degree. -/
theorem unitaryDegree_completionSupercuspidalLatticeEquiv
    (x : PadicSupercuspidal.UnitaryLattice.{u, uV} (padicField v)) :
    PadicSupercuspidal.unitaryDegree K (completionSupercuspidalLatticeEquiv v h K f x) =
      PadicSupercuspidal.unitaryDegree (padicField v) x := by
  subst h
  exact PadicSupercuspidal.unitaryDegree_unitaryLatticeEquiv K (padicFieldAt v rfl) f x

/-- The supercuspidal pullback to `K` commutes with the canonical contragredient. -/
theorem completionSupercuspidalLatticeEquiv_unitaryContragredientLatticeEquiv
    (x : PadicSupercuspidal.UnitaryLattice.{u, uV} (padicField v)) :
    completionSupercuspidalLatticeEquiv v h K f
        (PadicSupercuspidal.unitaryContragredientLatticeEquiv (padicField v) x) =
      PadicSupercuspidal.unitaryContragredientLatticeEquiv K
        (completionSupercuspidalLatticeEquiv v h K f x) := by
  subst h
  exact PadicSupercuspidal.unitaryLatticeEquiv_unitaryContragredientLatticeEquiv
    K (padicFieldAt v rfl) f x

/-- The Weil pullback to `K` relabels generators bijectively. -/
theorem completionWeilLatticeEquiv_generator
    (b : LocalWeil.UnitaryBasis.{u, uW} (padicField v)) :
    completionWeilLatticeEquiv v h K f (generator b) =
      generator (Weil.restrictUnitaryBasisEquiv (completionWeilEquiv v h K f) b) :=
  Weil.restrictUnitaryLatticeEquiv_generator _ b

end Langlands.Global

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality Langlands.Weil.Local

variable {F E : Type uF} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  {c : FundamentalClass.ClassFamily.{uF}} {v : FinitePlace F}
  {T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v}

/-- A generated positive isometry sends exactly the unitary Weil generators of
the image to unitary supercuspidal generators. -/
theorem RelativeGeneratedPositiveIsometry.exists_generator_iff
    (hT : RelativeGeneratedPositiveIsometry F E c v T)
    (x : weilImage.{uF, uW, uP} F E c v) :
    (∃ b : LocalWeil.UnitaryBasis.{uF, uW} (padicField v),
        (x : LocalWeil.UnitaryLattice (padicField v)) = generator b) ↔
      ∃ b : PadicSupercuspidal.UnitaryBasis.{uF, uF} (padicField v),
        (T x : PadicSupercuspidal.UnitaryLattice (padicField v)) = generator b := by
  obtain ⟨-, hpair, hdeg, hgen⟩ := hT
  constructor
  · rintro ⟨b, hb⟩
    refine (hgen x ?_ ?_).exists
    · change pairing (x : LocalWeil.UnitaryLattice (padicField v)) x = 1
      rw [hb, pairing_generator_self]
    · rw [hb]
      exact LocalWeil.unitaryDegree_generator_pos _ b
  · rintro ⟨b, hb⟩
    refine exists_generator_of_pairing_self_eq_one
      (LocalWeil.unitaryDegree (padicField v))
      (LocalWeil.unitaryDegree_generator_pos _) _ ?_ ?_
    · change LocalWeil.unitaryPairing (padicField v) x x = 1
      rw [← hpair x x]
      change pairing (T x : PadicSupercuspidal.UnitaryLattice (padicField v)) (T x) = 1
      rw [hb, pairing_generator_self]
    · rw [← hdeg x, hb]
      exact PadicSupercuspidal.unitaryDegree_generator_pos _ b

variable (F E c v) {p : ℕ} [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- Every element of the transported Weil image is the transport of an element
of the Weil image at `F_v`. -/
theorem exists_eq_completionWeilLatticeEquiv
    (x : (weilImage.{uF, uW, uP} F E c v).map
      (completionWeilLatticeEquiv v h K f : LocalWeil.UnitaryLattice (padicField v) →ₗ[ℤ]
        LocalWeil.UnitaryLattice K)) :
    ∃ y : weilImage.{uF, uW, uP} F E c v,
      x = ⟨completionWeilLatticeEquiv v h K f y, Submodule.mem_map_of_mem y.2⟩ := by
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp x.2
  exact ⟨⟨y, hy⟩, Subtype.ext hyx.symm⟩

/-- The composite preserves the multiplicity pairings and the degrees. -/
theorem henniartCompositeMap_isometry
    (hT : RelativeGeneratedPositiveIsometry F E c v T) :
    Correspondence.LatticeMap.Isometry K (henniartCompositeMap F E c v h K f T) := by
  obtain ⟨-, hpair, hdeg, -⟩ := hT
  refine ⟨fun x x' => ?_, fun x => ?_⟩
  · obtain ⟨y, rfl⟩ := exists_eq_completionWeilLatticeEquiv F E c v h K f x
    obtain ⟨y', rfl⟩ := exists_eq_completionWeilLatticeEquiv F E c v h K f x'
    rw [henniartCompositeMap_apply, henniartCompositeMap_apply,
      unitaryPairing_completionSupercuspidalLatticeEquiv, hpair]
    exact (Weil.unitaryPairing_restrictUnitaryLatticeEquiv (completionWeilEquiv v h K f)
      (y : LocalWeil.UnitaryLattice.{uF, uW} (padicField v)) y').symm
  · obtain ⟨y, rfl⟩ := exists_eq_completionWeilLatticeEquiv F E c v h K f x
    rw [henniartCompositeMap_apply, unitaryDegree_completionSupercuspidalLatticeEquiv, hdeg]
    exact (Weil.unitaryDegree_restrictUnitaryLatticeEquiv (completionWeilEquiv v h K f)
      (y : LocalWeil.UnitaryLattice.{uF, uW} (padicField v))).symm

/-- The composite sends exactly the unitary Weil generators to unitary
supercuspidal generators. -/
theorem henniartCompositeMap_generatorCompatibility
    (hT : RelativeGeneratedPositiveIsometry F E c v T) :
    Correspondence.LatticeMap.GeneratorCompatibility K
      (henniartCompositeMap F E c v h K f T) := by
  intro x
  obtain ⟨y, rfl⟩ := exists_eq_completionWeilLatticeEquiv F E c v h K f x
  obtain ⟨eA, heA⟩ := exists_completionSupercuspidalLatticeEquiv_generator v h K f
  rw [henniartCompositeMap_apply]
  change (∃ b, completionWeilLatticeEquiv v h K f y = generator b) ↔ _
  rw [exists_generator_iff_of_map_generator (completionWeilLatticeEquiv v h K f)
      (Weil.restrictUnitaryBasisEquiv (completionWeilEquiv v h K f))
      (completionWeilLatticeEquiv_generator v h K f),
    exists_generator_iff_of_map_generator (completionSupercuspidalLatticeEquiv v h K f) eA heA]
  exact hT.exists_generator_iff y

/-- The composite on a class given by any representative of its transport. -/
theorem henniartCompositeMap_eq_of_eq
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v)
    (y : weilImage.{uF, uW, uP} F E c v) (z : LocalWeil.UnitaryLattice.{uK, uW} K)
    (hz : z ∈ (weilImage.{uF, uW, uP} F E c v).map
      (completionWeilLatticeEquiv v h K f : LocalWeil.UnitaryLattice (padicField v) →ₗ[ℤ]
        LocalWeil.UnitaryLattice K))
    (hzy : z = completionWeilLatticeEquiv v h K f y) :
    (henniartCompositeMap F E c v h K f T ⟨z, hz⟩ : PadicSupercuspidal.UnitaryLattice K) =
      completionSupercuspidalLatticeEquiv v h K f (T y) := by
  subst hzy
  exact henniartCompositeMap_apply F E c v h K f T y

/-- The contragredient clause at `F_v` transports to the composite at `K`. -/
theorem henniartCompositeMap_dualCompatibility
    (hD : RelativeIsometryDualCompatibility F E c v T) :
    Correspondence.LatticeMap.DualCompatibility K (henniartCompositeMap F E c v h K f T) := by
  intro x
  obtain ⟨y, rfl⟩ := exists_eq_completionWeilLatticeEquiv F E c v h K f x
  obtain ⟨hy', hTy⟩ := hD y
  have hz := completionWeilLatticeEquiv_unitaryDualLatticeEquiv v h K f
    (y : LocalWeil.UnitaryLattice.{uF, uW} (padicField v))
  have hmem : LocalWeil.unitaryDualLatticeEquiv K (completionWeilLatticeEquiv v h K f y) ∈
      (weilImage.{uF, uW, uP} F E c v).map
        (completionWeilLatticeEquiv v h K f : LocalWeil.UnitaryLattice (padicField v) →ₗ[ℤ]
          LocalWeil.UnitaryLattice K) := by
    rw [← hz]
    exact Submodule.mem_map_of_mem hy'
  refine ⟨hmem, (henniartCompositeMap_eq_of_eq F E c v h K f T ⟨_, hy'⟩ _ hmem hz.symm).trans ?_⟩
  rw [hTy, henniartCompositeMap_apply,
    completionSupercuspidalLatticeEquiv_unitaryContragredientLatticeEquiv]

/-- The twist clause at `F_v` for `(e', χ')` transports to the twist clause at `K`
for `(e, χ)`, when the Weil character of `χ'` restricts to that of `χ` and the
supercuspidal pullback carries the twist by `χ'` to the twist by `χ`. -/
theorem henniartCompositeMap_twistCompatibility
    (e : Correspondence.ReciprocityCandidate K)
    (e' : Correspondence.ReciprocityCandidate (padicField v))
    (χ : Correspondence.QuasiCharacter K) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)
    (χ' : Correspondence.QuasiCharacter (padicField v)) (hχ' : ∀ b, ‖(χ' b : ℂ)‖ = 1)
    (hcomp : (LocalFactor.RankOne.weilCharacter (padicField v) e' χ').comp
        (completionWeilEquiv v h K f : localWeilGroup K →ₜ* localWeilGroup (padicField v)) =
      LocalFactor.RankOne.weilCharacter K e χ)
    (hsc : ∀ z : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v),
      completionSupercuspidalLatticeEquiv v h K f
          (PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv (padicField v) χ' hχ' z) =
        PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv K χ hχ
          (completionSupercuspidalLatticeEquiv v h K f z))
    (hTw : RelativeIsometryTwistCompatibility F E c v T e' χ' hχ') :
    Correspondence.LatticeMap.TwistCompatibility K (henniartCompositeMap F E c v h K f T)
      e χ hχ := by
  intro x
  obtain ⟨y, rfl⟩ := exists_eq_completionWeilLatticeEquiv F E c v h K f x
  obtain ⟨hy', hTy⟩ := hTw y
  have hz := completionWeilLatticeEquiv_unitaryFieldCharacterTwistLatticeEquiv v h K f
    e e' χ hχ χ' hχ' hcomp (y : LocalWeil.UnitaryLattice.{uF, uW} (padicField v))
  have hmem : LocalWeil.unitaryFieldCharacterTwistLatticeEquiv K e χ hχ
      (completionWeilLatticeEquiv v h K f y) ∈
      (weilImage.{uF, uW, uP} F E c v).map
        (completionWeilLatticeEquiv v h K f : LocalWeil.UnitaryLattice (padicField v) →ₗ[ℤ]
          LocalWeil.UnitaryLattice K) := by
    rw [← hz]
    exact Submodule.mem_map_of_mem hy'
  refine ⟨hmem, (henniartCompositeMap_eq_of_eq F E c v h K f T ⟨_, hy'⟩ _ hmem hz.symm).trans ?_⟩
  rw [hTy, hsc, henniartCompositeMap_apply]

/-- The character clause at `F_v` for `(e', χ')` transports to the character
clause at `K` for `(e, χ)`, under the same compatibilities for the rank-one
classes. -/
theorem henniartCompositeMap_characterCompatibility
    (e : Correspondence.ReciprocityCandidate K)
    (e' : Correspondence.ReciprocityCandidate (padicField v))
    (χ : Correspondence.QuasiCharacter K)
    (χ' : Correspondence.QuasiCharacter (padicField v))
    (hcomp : (LocalFactor.RankOne.weilCharacter (padicField v) e' χ').comp
        (completionWeilEquiv v h K f : localWeilGroup K →ₜ* localWeilGroup (padicField v)) =
      LocalFactor.RankOne.weilCharacter K e χ)
    (hsc : ∀ z : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v),
      PadicSupercuspidal.includeUnitary (padicField v) z =
          generator (⟨1, Correspondence.rankOneSupercuspidalClass.{uF, uF} (padicField v) χ'⟩ :
            PadicSupercuspidal.Basis.{uF, uF} (padicField v)) →
        PadicSupercuspidal.includeUnitary K (completionSupercuspidalLatticeEquiv v h K f z) =
          generator (⟨1, Correspondence.rankOneSupercuspidalClass.{uK, uF} K χ⟩ :
            PadicSupercuspidal.Basis.{uK, uF} K))
    (hC : RelativeIsometryCharacterCompatibility F E c v T e' χ') :
    Correspondence.LatticeMap.CharacterCompatibility K (henniartCompositeMap F E c v h K f T)
      e χ := by
  obtain ⟨y, hyW, hyA⟩ := hC
  refine ⟨⟨completionWeilLatticeEquiv v h K f y, Submodule.mem_map_of_mem y.2⟩, ?_, ?_⟩
  · exact includeUnitary_completionWeilLatticeEquiv_rankOne v h K f e e' χ χ' hcomp _ hyW
  · rw [henniartCompositeMap_apply]
    exact hsc _ hyA

/-- The operation properties of the composite at `K`, given the supercuspidal
twist and rank-one compatibilities of the pullback along `f`. -/
theorem henniartCompositeMap_operationProperties_of
    (hscTwist : ∀ (χ : Correspondence.QuasiCharacter K) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)
      (χ' : Correspondence.QuasiCharacter (padicField v)) (hχ' : ∀ b, ‖(χ' b : ℂ)‖ = 1),
      (letI := (padicFieldAt v h).algebra
        ∀ (a : K.Carrierˣ) (b : (padicField v).Carrierˣ),
          (b : (padicField v).Carrier) = f (a : K.Carrier) → χ' b = χ a) →
      ∀ z : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v),
        completionSupercuspidalLatticeEquiv v h K f
            (PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv (padicField v) χ' hχ' z) =
          PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv K χ hχ
            (completionSupercuspidalLatticeEquiv v h K f z))
    (hscRank : ∀ (χ : Correspondence.QuasiCharacter K)
      (χ' : Correspondence.QuasiCharacter (padicField v)),
      (letI := (padicFieldAt v h).algebra
        ∀ (a : K.Carrierˣ) (b : (padicField v).Carrierˣ),
          (b : (padicField v).Carrier) = f (a : K.Carrier) → χ' b = χ a) →
      ∀ z : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v),
        PadicSupercuspidal.includeUnitary (padicField v) z =
            generator (⟨1, Correspondence.rankOneSupercuspidalClass.{uF, uF}
              (padicField v) χ'⟩ : PadicSupercuspidal.Basis.{uF, uF} (padicField v)) →
          PadicSupercuspidal.includeUnitary K (completionSupercuspidalLatticeEquiv v h K f z) =
            generator (⟨1, Correspondence.rankOneSupercuspidalClass.{uK, uF} K χ⟩ :
              PadicSupercuspidal.Basis.{uK, uF} K))
    (hT : RelativeGeneratedPositiveIsometry F E c v T)
    (hO : RelativeIsometryOperations F E c v T) :
    Correspondence.LatticeMap.OperationProperties K (henniartCompositeMap F E c v h K f T) := by
  refine ⟨henniartCompositeMap_isometry F E c v h K f hT,
    henniartCompositeMap_generatorCompatibility F E c v h K f hT,
    henniartCompositeMap_dualCompatibility F E c v h K f hO.1, fun e he χ hχ => ?_⟩
  obtain ⟨e', he', hrec⟩ := exists_geometric_completionReciprocity v h K f e he
  obtain ⟨χ', hχ', hrel⟩ := exists_completionQuasiCharacter v h K f χ hχ
  have hcomp := weilCharacter_comp_completionWeilEquiv v h K f e e' hrec χ χ' hrel
  obtain ⟨hTw, hC⟩ := hO.2 e' he' χ' hχ'
  exact ⟨henniartCompositeMap_twistCompatibility F E c v h K f e e' χ hχ χ' hχ' hcomp
      (hscTwist χ hχ χ' hχ' hrel) hTw,
    henniartCompositeMap_characterCompatibility F E c v h K f e e' χ χ' hcomp
      (hscRank χ χ' hrel) hC⟩

/-- **Transport of the operation clauses.** If a generated positive isometry `T`
between the relative Weil and automorphic images at `v` has the contragredient,
twist and character clauses at `F_v`, then for every `ℚ_p`-algebra isomorphism
`f : K ≅ F_v` the composite `henniartCompositeMap` at `K` has the operation
properties of Henniart's 3.8. -/
theorem henniartCompositeOperation :
    HenniartCompositeOperationStatement.{uF, uK, uW, uP} := by
  intro F E _ _ _ _ _ _ _ c v T hT hO p _ h K f
  exact henniartCompositeMap_operationProperties_of F E c v h K f
    (fun χ hχ χ' hχ' hrel =>
      completionSupercuspidalLatticeEquiv_unitaryCharacterTwistLatticeEquiv v h K f
        χ hχ χ' hχ' hrel)
    (fun χ χ' hrel =>
      includeUnitary_completionSupercuspidalLatticeEquiv_rankOne v h K f χ χ' hrel)
    hT hO

end Langlands.Global.PoleComparison
