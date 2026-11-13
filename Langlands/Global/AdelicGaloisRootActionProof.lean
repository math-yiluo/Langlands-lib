import Langlands.Global.AdelicGaloisRootAction
import Langlands.GroupScheme.Rational.StandardParabolicClassificationProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.PositiveRootStabilizerAveraging
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.Absolute.FixedTorusDynamicGalois
import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Langlands.GroupScheme.Absolute.BorelDynamicConjugacy
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Rational.DominantChamberMove
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport

/-! # Proof of Lemma Q: the Galois action on the simple roots

For each `σ`, a normalizing point `n σ` moves `σ ν` into the closed chamber of `ν`; the map
`A σ = weylAction (n σ) ∘ σ` then preserves the roots and the signs of their pairings with
`ν`, hence the simple roots. The Galois translate of a dynamic parabolic `P(ζ)` is `P(σ ζ)`,
and conjugation by `n σ` turns a standard cocharacter for `J` into one for `A σ '' J`. The
action laws follow because a Weyl element preserving the positive roots acts trivially.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section RootPreserving

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- A linear automorphism of the character lattice preserves the positive roots of `ν` when
it preserves the relative roots and the sign of their pairing with `ν`. -/
def PreservesPositiveRoots (f : characterLattice T ≃ₗ[ℤ] characterLattice T) : Prop :=
  (∀ χ, f χ ∈ relativeRoots i ↔ χ ∈ relativeRoots i) ∧
    ∀ α ∈ relativeRoots i, (0 < latticePairing T (f α) ν ↔ 0 < latticePairing T α ν)

variable {i ν}

theorem PreservesPositiveRoots.symm {f : characterLattice T ≃ₗ[ℤ] characterLattice T}
    (hf : PreservesPositiveRoots i ν f) : PreservesPositiveRoots i ν f.symm := by
  refine ⟨fun χ => ?_, fun α hα => ?_⟩
  · have h := hf.1 (f.symm χ)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · have hα' : f.symm α ∈ relativeRoots i := by
      have h := hf.1 (f.symm α)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.mp hα
    have h := hf.2 (f.symm α) hα'
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

theorem PreservesPositiveRoots.trans {f g : characterLattice T ≃ₗ[ℤ] characterLattice T}
    (hf : PreservesPositiveRoots i ν f) (hg : PreservesPositiveRoots i ν g) :
    PreservesPositiveRoots i ν (f.trans g) := by
  refine ⟨fun χ => ?_, fun α hα => ?_⟩
  · rw [LinearEquiv.trans_apply]
    exact (hg.1 (f χ)).trans (hf.1 χ)
  · rw [LinearEquiv.trans_apply]
    exact (hg.2 (f α) ((hf.1 α).mpr hα)).trans (hf.2 α hα)

theorem PreservesPositiveRoots.mem_positiveRelativeRoots_iff
    {f : characterLattice T ≃ₗ[ℤ] characterLattice T} (hf : PreservesPositiveRoots i ν f)
    (α : characterLattice T) :
    f α ∈ positiveRelativeRoots i ν ↔ α ∈ positiveRelativeRoots i ν := by
  constructor
  · rintro ⟨h1, h2⟩
    have hα := (hf.1 α).mp h1
    exact ⟨hα, (hf.2 α hα).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(hf.1 α).mpr h1, (hf.2 α h1).mpr h2⟩

/-- A lattice automorphism preserving the positive roots preserves the simple roots. -/
theorem PreservesPositiveRoots.mem_simpleRelativeRoots_iff
    {f : characterLattice T ≃ₗ[ℤ] characterLattice T} (hf : PreservesPositiveRoots i ν f)
    (α : characterLattice T) :
    f α ∈ simpleRelativeRoots i ν ↔ α ∈ simpleRelativeRoots i ν := by
  have hs := hf.symm
  constructor
  · rintro ⟨hpos, hns⟩
    refine ⟨(hf.mem_positiveRelativeRoots_iff α).mp hpos, ?_⟩
    rintro ⟨β, hβ, β', hβ', rfl⟩
    exact hns ⟨f β, (hf.mem_positiveRelativeRoots_iff β).mpr hβ, f β',
      (hf.mem_positiveRelativeRoots_iff β').mpr hβ', map_add f β β'⟩
  · rintro ⟨hpos, hns⟩
    refine ⟨(hf.mem_positiveRelativeRoots_iff α).mpr hpos, ?_⟩
    rintro ⟨β, hβ, β', hβ', hsum⟩
    apply hns
    refine ⟨f.symm β, (hs.mem_positiveRelativeRoots_iff β).mpr hβ, f.symm β',
      (hs.mem_positiveRelativeRoots_iff β').mpr hβ', ?_⟩
    rw [← map_add, ← hsum, LinearEquiv.symm_apply_apply]

variable (i ν)

/-- For roots, positivity on a generic `ν` is positivity on any generic cocharacter `ν'`
in the closed chamber of `ν`. -/
theorem pos_iff_of_dominant (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (hν : IsGenericCocharacter i ν) {ν' : cocharacterLattice T}
    (hdom : ∀ α ∈ positiveRelativeRoots i ν, 0 ≤ latticePairing T α ν')
    (hgen : IsGenericCocharacter i ν') :
    ∀ β ∈ relativeRoots i, (0 < latticePairing T β ν ↔ 0 < latticePairing T β ν') := by
  intro β hβ
  constructor
  · intro h
    exact lt_of_le_of_ne (hdom β ⟨hβ, h⟩) (Ne.symm (hgen β hβ))
  · intro h
    by_contra hle
    have hlt : latticePairing T β ν < 0 := lt_of_le_of_ne (not_lt.mp hle) (hν β hβ)
    have hmem : -β ∈ positiveRelativeRoots i ν :=
      ⟨hneg β hβ, by rw [map_neg, LinearMap.neg_apply]; omega⟩
    have h' := hdom _ hmem
    rw [map_neg, LinearMap.neg_apply] at h'
    omega

variable [Mono i.hom.hom.left]

/-- A normalizing point preserving the positive roots of a generic cocharacter acts
trivially on all characters, by the trivial positive-root stabilizer. -/
theorem weylAction_apply_eq_self_of_preserves (hstab : HasTrivialPositiveRootStabilizer i ν)
    (n : normalizerPoints i) (hn : PreservesPositiveRoots i ν (weylAction i n))
    (χ : characterLattice T) : weylAction i n χ = χ := by
  have h1 : (QuotientGroup.mk n : relativeWeylGroup i) = 1 := by
    apply hstab
    intro α hα
    rw [relativeWeylCharacterAction_mk]
    exact hn.2 α hα
  have h2 : weylAction i n = 1 := by
    rw [← relativeWeylCharacterAction_mk, h1, map_one]
  rw [h2]
  rfl

end RootPreserving

section Galois

variable (F L : Type u) [Field F] [Field L] [Algebra F L]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (i₀ : T₀.toGrp ⟶ G)

local instance galoisRootBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F L)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap F L))
  infer_instance

/-- The Galois action and the action of a torus automorphism together preserve the
pairing. -/
theorem latticePairing_characterAut_galois_cocharacterAut_galois (σ : L ≃ₐ[F] L)
    (e : (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀ ≅
      (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (ζ : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)) :
    latticePairing _ (characterAut e (characterLattice.galoisRepresentation F L T₀ σ χ))
        (cocharacterAut e (cocharacterLattice.galoisRepresentation F L T₀ σ ζ)) =
      latticePairing _ χ ζ := by
  rw [latticePairing_characterAut_cocharacterAut, latticePairing_galoisRepresentation]

omit [IsAffineHom G.X.hom] in
/-- The Galois translate of a normalizing point's Weyl action is again a Weyl action. -/
theorem exists_galois_weylAction
    [Mono ((GroupScheme.baseChange (algebraBaseMap F L)).map i₀).hom.hom.left]
    (σ : L ≃ₐ[F] L)
    (n : normalizerPoints (T := (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)
      ((GroupScheme.baseChange (algebraBaseMap F L)).map i₀)) :
    ∃ n' : normalizerPoints (T := (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)
        ((GroupScheme.baseChange (algebraBaseMap F L)).map i₀),
      ∀ ψ, characterLattice.galoisRepresentation F L T₀ σ
          (weylAction (T := (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)
            ((GroupScheme.baseChange (algebraBaseMap F L)).map i₀) n ψ) =
        weylAction (T := (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)
          ((GroupScheme.baseChange (algebraBaseMap F L)).map i₀) n'
          (characterLattice.galoisRepresentation F L T₀ σ ψ) := by
  obtain ⟨n', hn'⟩ := IsNormalizingPoint.exists_descentTransport (algebraBaseMap F L)
    (galoisBaseMap F L σ) (galoisBaseMap_over F L σ) i₀
    (isNormalizingPoint_normalizingAut _ n)
  refine ⟨⟨n', _, hn'⟩, fun ψ => ?_⟩
  exact (characterAut_descentTransport (algebraBaseMap F L) (galoisBaseMap F L σ)
    (galoisBaseMap_over F L σ) (normalizingAut _ n) ψ).symm.trans
    (weylAction_eq (T := (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)
      ((GroupScheme.baseChange (algebraBaseMap F L)).map i₀) (n := ⟨n', _, hn'⟩) hn'
      (characterLattice.galoisRepresentation F L T₀ σ ψ)).symm

omit [IsAffineHom G.X.hom] in
/-- The canonical Galois translate of a represented dynamic parabolic of a torus cocharacter
is the dynamic parabolic of the Galois-transported cocharacter. -/
theorem range_radicalGaloisHom_eq_parabolic (σ : L ≃ₐ[F] L)
    {H : GroupScheme (Spec (CommRingCat.of L))}
    (p : H ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (ζ : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (hp : SubgroupFunctor.range p = Dynamic.parabolic
      (CommGroupScheme.groupHom ζ ≫ (GroupScheme.baseChange (algebraBaseMap F L)).map i₀)) :
    SubgroupFunctor.range (radicalGaloisHom p σ) = Dynamic.parabolic
      (CommGroupScheme.groupHom (cocharacterLattice.galoisRepresentation F L T₀ σ ζ) ≫
        (GroupScheme.baseChange (algebraBaseMap F L)).map i₀) := by
  unfold radicalGaloisHom
  rw [← SubgroupFunctor.descentTransport_range, hp,
    ← Dynamic.parabolic_transportCocharacter_eq_descentTransport,
    ← cocharacterLattice.groupHom_transport_comp]
  rfl

end Galois

end Langlands.GroupScheme


namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Core

variable (F L : Type u) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance galoisRootCoreAffine : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom :=
  isAffineHom_of_isAffine _

omit [FiniteDimensional F L] [LocallyOfFiniteType G.X.hom] in
/-- Lemma Q for an embedding `i` of the split torus `T₀_L` as a maximal split torus of `G_L`,
given three Galois inputs: the Galois action preserves the roots of `i`, conjugates Weyl
actions of normalizing points into Weyl actions, and carries the dynamic parabolic of
`ζ` to the dynamic parabolic of `σ ζ`. -/
theorem exists_isGaloisRootAction_of_galois (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp ⟶
      AffineWeil.unitBaseChange F L G) [Mono i.hom.hom.left]
    (hGL : IsConnectedReductive (AffineWeil.unitBaseChange F L G))
    (hTs : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp)
    (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (hν : IsGenericCocharacter i ν)
    (hgroot : ∀ (σ : L ≃ₐ[F] L) χ,
      characterLattice.galoisRepresentation F L T₀ σ χ ∈ relativeRoots i ↔ χ ∈ relativeRoots i)
    (hgweyl : ∀ (σ : L ≃ₐ[F] L) (n : normalizerPoints i), ∃ n' : normalizerPoints i, ∀ ψ,
      characterLattice.galoisRepresentation F L T₀ σ (weylAction i n ψ) =
        weylAction i n' (characterLattice.galoisRepresentation F L T₀ σ ψ))
    (hgpar : ∀ (σ : L ≃ₐ[F] L) {H : GroupScheme (Spec (CommRingCat.of L))}
      (p : H ⟶ AffineWeil.unitBaseChange F L G) ζ,
      SubgroupFunctor.range p = Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) →
        SubgroupFunctor.range (radicalGaloisHom p σ) = Dynamic.parabolic
          (CommGroupScheme.groupHom (cocharacterLattice.galoisRepresentation F L T₀ σ ζ) ≫ i)) :
    ∃ (m : (L ≃ₐ[F] L) → rationalPoints (AffineWeil.unitBaseChange F L G))
      (τ : (L ≃ₐ[F] L) → ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀ ≅
        (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)),
      IsGaloisRootAction F L G T₀ i ν m τ := by
  have hroot : HasRelativeRootSystem i := relativeRootSystem L _ hGL _ i hi
  have hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i := relativeRootNegation L _ hGL _ i hi
  have hstab : HasTrivialPositiveRootStabilizer i ν :=
    hasTrivialPositiveRootStabilizer i hGL hi hν
  have hstd := standardCocharacter L _ hGL _ i hi ν hν
  -- choose the chamber moves
  have hex : ∀ σ : L ≃ₐ[F] L, ∃ n : normalizerPoints i, ∀ α ∈ positiveRelativeRoots i ν,
      0 ≤ latticePairing _ α (cocharacterAut (normalizingAut i n)
        (cocharacterLattice.galoisRepresentation F L T₀ σ ν)) :=
    fun σ => hroot.exists_normalizerPoint_dominant i hTs ν _
  choose n hn using hex
  -- the root maps as linear equivalences
  let A := fun σ : L ≃ₐ[F] L =>
    (characterLattice.galoisEquiv F L T₀ σ).trans (weylAction i (n σ))
  have hA : ∀ σ χ, A σ χ = characterAut (normalizingAut i (n σ))
      (characterLattice.galoisRepresentation F L T₀ σ χ) := fun _ _ => rfl
  -- the pairing identity
  have hpair : ∀ σ χ ζ, latticePairing _ (A σ χ) (cocharacterAut (normalizingAut i (n σ))
      (cocharacterLattice.galoisRepresentation F L T₀ σ ζ)) = latticePairing _ χ ζ := by
    intro σ χ ζ
    rw [hA]
    exact latticePairing_characterAut_galois_cocharacterAut_galois F L σ _ χ ζ
  -- each root map preserves the positive roots
  have hpres : ∀ σ, PreservesPositiveRoots i ν (A σ) := by
    intro σ
    have hroots : ∀ χ, A σ χ ∈ relativeRoots i ↔ χ ∈ relativeRoots i := by
      intro χ
      change weylAction i (n σ) (characterLattice.galoisRepresentation F L T₀ σ χ) ∈ roots i ↔ _
      rw [weylAction_mem_roots_iff]
      exact hgroot σ χ
    have hgen' : IsGenericCocharacter i (cocharacterAut (normalizingAut i (n σ))
        (cocharacterLattice.galoisRepresentation F L T₀ σ ν)) := by
      intro β hβ
      have hβ' : (A σ).symm β ∈ relativeRoots i := by
        have h := hroots ((A σ).symm β)
        rw [LinearEquiv.apply_symm_apply] at h
        exact h.mp hβ
      have h := hpair σ ((A σ).symm β) ν
      rw [LinearEquiv.apply_symm_apply] at h
      rw [h]
      exact hν _ hβ'
    refine ⟨hroots, fun α hα => ?_⟩
    rw [pos_iff_of_dominant i ν hneg hν (hn σ) hgen' (A σ α) ((hroots α).mpr hα), hpair σ α ν]
  -- the identity acts trivially
  have hone : ∀ χ, A 1 χ = χ := by
    have hw : weylAction i (n 1) = A 1 := by
      apply LinearEquiv.ext
      intro χ
      change _ = weylAction i (n 1) (characterLattice.galoisRepresentation F L T₀ 1 χ)
      rw [map_one]
      rfl
    have hpw : PreservesPositiveRoots i ν (weylAction i (n 1)) := by
      rw [hw]
      exact hpres 1
    intro χ
    rw [← hw]
    exact weylAction_apply_eq_self_of_preserves i ν hstab (n 1) hpw χ
  -- the composition law
  have hmul : ∀ σ σ' χ, A (σ * σ') χ = A σ (A σ' χ) := by
    intro σ σ'
    obtain ⟨n', hn'⟩ := hgweyl σ (n σ')
    have hcomp : ∀ χ, A σ (A σ' χ) =
        weylAction i (n σ * n') (characterLattice.galoisRepresentation F L T₀ (σ * σ') χ) := by
      intro χ
      change weylAction i (n σ) (characterLattice.galoisRepresentation F L T₀ σ
          (weylAction i (n σ') (characterLattice.galoisRepresentation F L T₀ σ' χ))) = _
      rw [hn', map_mul (weylAction i), map_mul (characterLattice.galoisRepresentation F L T₀)]
      rfl
    have hWA : ∀ χ, weylAction i (n σ * n' * (n (σ * σ'))⁻¹) (A (σ * σ') χ) =
        A σ (A σ' χ) := by
      intro χ
      rw [hcomp]
      change weylAction i (n σ * n' * (n (σ * σ'))⁻¹)
          (weylAction i (n (σ * σ')) (characterLattice.galoisRepresentation F L T₀ (σ * σ') χ)) = _
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel_right]
    have hWeq : weylAction i (n σ * n' * (n (σ * σ'))⁻¹) =
        (A (σ * σ')).symm.trans ((A σ').trans (A σ)) := by
      apply LinearEquiv.ext
      intro χ
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← hWA,
        LinearEquiv.apply_symm_apply]
    have hpW : PreservesPositiveRoots i ν (weylAction i (n σ * n' * (n (σ * σ'))⁻¹)) := by
      rw [hWeq]
      exact (hpres (σ * σ')).symm.trans ((hpres σ').trans (hpres σ))
    intro χ
    rw [← hWA, weylAction_apply_eq_self_of_preserves i ν hstab _ hpW]
  -- the Galois translates of the standard parabolics
  have hpar : ∀ σ, ∀ J ⊆ simpleRelativeRoots i ν,
      SubgroupFunctor.range (radicalGaloisHom (Standard.parabolicHom i ν J) σ) =
        SubgroupFunctor.range (Standard.parabolicHom i ν (A σ '' J) ≫
          ((AffineWeil.unitBaseChange F L G).innerIso
            ((n σ : rationalPoints (AffineWeil.unitBaseChange F L G)))⁻¹).hom) := by
    intro σ J hJ
    obtain ⟨ζ, hζ⟩ := (hstd J hJ).1
    have hPJ := ((hstd J hJ).2 ζ hζ).1
    have hsub : A σ '' J ⊆ simpleRelativeRoots i ν := by
      rintro _ ⟨β, hβ, rfl⟩
      exact ((hpres σ).mem_simpleRelativeRoots_iff β).mpr (hJ hβ)
    have hζ' : IsStandardCocharacter i ν (A σ '' J) (cocharacterAut (normalizingAut i (n σ))
        (cocharacterLattice.galoisRepresentation F L T₀ σ ζ)) := by
      refine ⟨hsub, ?_, ?_⟩
      · rintro _ ⟨β, hβ, rfl⟩
        rw [hpair]
        exact hζ.2.1 β hβ
      · intro α hα hnot
        have hβ : (A σ).symm α ∈ simpleRelativeRoots i ν := by
          have h := (hpres σ).mem_simpleRelativeRoots_iff ((A σ).symm α)
          rw [LinearEquiv.apply_symm_apply] at h
          exact h.mp hα
        have hβJ : (A σ).symm α ∉ J :=
          fun h => hnot ⟨_, h, LinearEquiv.apply_symm_apply _ _⟩
        have h := hζ.2.2 _ hβ hβJ
        rw [← hpair σ ((A σ).symm α) ζ, LinearEquiv.apply_symm_apply] at h
        exact h
    have hPJ' := ((hstd (A σ '' J) hsub).2 _ hζ').1
    rw [hgpar σ _ ζ ((Standard.isRepresentedBy_parabolicHom i ν J).2.trans hPJ)]
    have : Mono (Standard.parabolicHom i ν (A σ '' J)).hom.hom :=
      (Standard.isRepresentedBy_parabolicHom i ν (A σ '' J)).1
    rw [range_comp_iso_eq_parabolic
      ((Standard.isRepresentedBy_parabolicHom i ν (A σ '' J)).2.trans hPJ')
      ((AffineWeil.unitBaseChange F L G).innerIso
        ((n σ : rationalPoints (AffineWeil.unitBaseChange F L G)))⁻¹),
      groupHom_cocharacterAut_comp]
    simp only [Category.assoc]
    rw [← innerIso_mul_hom, inv_mul_cancel, innerIso_one_hom, Category.comp_id]
  -- assembly
  refine ⟨fun σ => ((n σ : rationalPoints (AffineWeil.unitBaseChange F L G)))⁻¹,
    fun σ => normalizingAut i (n σ), ?_, ?_, ?_, ?_, ?_⟩
  · intro σ
    show IsNormalizingPoint i ((n σ : rationalPoints (AffineWeil.unitBaseChange F L G))⁻¹)⁻¹
      (normalizingAut i (n σ))
    rw [inv_inv]
    exact isNormalizingPoint_normalizingAut i (n σ)
  · intro σ β hβ
    exact ((hpres σ).mem_simpleRelativeRoots_iff β).mpr hβ
  · intro σ J hJ
    exact hpar σ J hJ
  · intro β _
    exact hone β
  · intro σ σ' β _
    exact hmul σ σ' β

end Core

/-- **Lemma Q.** A maximal torus over `F` that splits over a finite Galois extension `L`,
with a generic cocharacter `ν` of its base change, admits a Galois root action. -/
theorem splitBorelGaloisRootAction : SplitBorelGaloisRootActionStatement.{u} := by
  intro F L _ _ _ _ _ G _ _ T₀ i₀ hG hi₀ hTs ν hν
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hsm : Smooth G.X.hom := hG.smooth
  have hGL : IsConnectedReductive (AffineWeil.unitBaseChange F L G) :=
    hG.baseChange_of_algebraicExtension
  have hiMax : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)
      ((GroupScheme.baseChange (algebraBaseMap F L)).map i₀) :=
    (maximalTorusBaseChange F L G T₀ i₀ hi₀.1 hi₀.2.1).mp hi₀
  have hi := hiMax.isMaximalSplitTorus hTs
  have := hi.isSplitSubtorus.mono
  exact exists_isGaloisRootAction_of_galois F L G T₀
    ((GroupScheme.baseChange (algebraBaseMap F L)).map i₀) hGL hTs hi ν hν
    (fun σ χ => mem_roots_galois_iff F L i₀ σ χ)
    (fun σ n => exists_galois_weylAction F L i₀ σ n)
    (fun σ _ p ζ hp => range_radicalGaloisHom_eq_parabolic F L i₀ σ p ζ hp)

end Langlands.Global.AdelicGaloisUnit
