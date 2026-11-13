import Langlands.Representation.CuspidalSupport.BernsteinCuspidalDataVarietyStatements
import Langlands.Representation.CuspidalSupport.BernsteinComponentWeylGroup
import Langlands.Representation.CuspidalSupport.FiniteGroupInvariantFunctions
import Langlands.Representation.Plancherel.UnramifiedRegularFunctionPoints
import Langlands.Representation.Plancherel.RationalUnramifiedFunctionField
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.CuspidalSupport.RationalTwistStabilizerFiniteProof
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Exponents.FiniteNormalizerRepresentatives
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.Global.AdelicRestrictionSplitCentreCanonical

/-! # Each component of `Ω(G)` is `X(M)/W` (Renard VI.7.1, Theorem)

The generic part works with an actual group-scheme embedding `j : H ⟶ G` and a smooth
representation `ρ` of `H(F)`; the final theorem specializes it to a standard cuspidal datum.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.CuspidalSupport.ComponentWeyl

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance instComponentVarietyTop (M : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine M.X.left] : TopologicalSpace (GroupScheme.rationalPoints M) :=
  rationalPointTopology F M.X

section Generic

variable {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (j : H ⟶ G) (ρ : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H))

/-- The finite group `W` and the variety `X(H)/W`, for an embedding `j` and a representation
`ρ`, from: a monomorphism `j`, finitely many normalizer representatives modulo `H(F)`, a finite
twist stabilizer, a finitely generated domain `ℂ[X(H)]`, and an open common norm kernel. -/
theorem weyl_and_variety [IsTopologicalGroup (GroupScheme.rationalPoints H)]
    (hj : Mono j.hom.hom)
    (hN : ∃ (n : ℕ) (g : Fin n → GroupScheme.rationalPoints G),
      ∀ (w : GroupScheme.rationalPoints G) (φ : H ≅ H),
        φ.hom ≫ j = j ≫ (G.innerIso w).hom →
          ∃ (t : Fin n) (m : GroupScheme.rationalPoints H),
            w = g t * GroupScheme.rationalPoints.map j m)
    (hS : {χ : UChar H | Nonempty (rationalUnramifiedTwist H χ ρ ≅ ρ)}.Finite)
    (hFT : Algebra.FiniteType ℂ
      (unramifiedRegularFunctions (fun χ => (rationalNormCharacters H χ).toMul)))
    (hD : IsDomain
      (unramifiedRegularFunctions (fun χ => (rationalNormCharacters H χ).toMul)))
    (hK : IsOpen (commonNormKernel (fun χ => (rationalNormCharacters H χ).toMul) :
      Set (GroupScheme.rationalPoints H))) :
    let Assoc : UChar H → UChar H → Prop := fun ω ω' =>
      ∃ c : RationalLeviConjugacy j j,
        Nonempty (rationalUnramifiedTwist H ω ρ ≅
          rationalIsoPullback c.iso (rationalUnramifiedTwist H ω' ρ))
    let regular := unramifiedRegularFunctions
      (fun χ => (rationalNormCharacters H χ).toMul)
    let invariant : Set (UChar H → ℂ) :=
      {f | f ∈ regular ∧ ∀ ω ω', Assoc ω ω' → f ω = f ω'}
    (∃ W : Subgroup (Equiv.Perm (UChar H)), Finite W ∧
      (∀ w ∈ W, ∀ f ∈ regular, (fun ω => f (w ω)) ∈ regular) ∧
      ∀ ω ω', Assoc ω ω' ↔ ∃ w ∈ W, w ω' = ω) ∧
    (∃ O : Subalgebra ℂ (UChar H → ℂ), (O : Set (UChar H → ℂ)) = invariant ∧
      Algebra.FiniteType ℂ O ∧ IsDomain O ∧
      (∀ φ : O →ₐ[ℂ] ℂ, ∃ ω : UChar H, ∀ f : O, φ f = (f : UChar H → ℂ) ω) ∧
      ∀ ω ω', Assoc ω ω' ↔ ∀ f ∈ O, f ω = f ω') := by
  intro Assoc regular invariant
  have hW : Finite (weylGroup j ρ) := weylGroup_finite j ρ hj hN hS
  have hpres : ∀ w ∈ weylGroup j ρ, ∀ f ∈ regular, (fun ω => f (w ω)) ∈ regular :=
    fun w hw f hf => weylGroup_comp_mem_regular j ρ hw hf
  have horb : ∀ ω ω', Assoc ω ω' ↔ ∃ w ∈ weylGroup j ρ, w ω' = ω :=
    assoc_iff_exists_weylGroup j ρ
  obtain ⟨O, hO, hft, hdom, hev, hsep⟩ :=
    InvariantFunctions.exists_invariantSubalgebra (R := regular) (W := weylGroup j ρ)
      (fun ψ => unramifiedRegularFunctions_algHom_eq_eval _ hK ψ)
      (fun x y h => unramifiedRegularFunctions_separates _ x y h) hpres
  refine ⟨⟨weylGroup j ρ, hW, hpres, horb⟩, O, ?_, hft, hdom, hev,
    fun ω ω' => (horb ω ω').trans (hsep ω ω')⟩
  rw [hO]
  ext f
  refine ⟨fun ⟨hf, hfw⟩ => ⟨hf, fun ω ω' h => ?_⟩, fun ⟨hf, hfa⟩ => ⟨hf, fun w hw x => ?_⟩⟩
  · obtain ⟨w, hw, rfl⟩ := (horb ω ω').1 h
    exact hfw w hw ω'
  · exact hfa _ _ ((horb _ _).2 ⟨w, hw, rfl⟩)

variable {H' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H'.X.left] [LocallyOfFiniteType H'.X.hom]
  (j' : H' ⟶ G) (ρ' : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H'))

/-- The components clause: twists of `(H, ρ)` and `(H', ρ')` are associated exactly when the
two data are inertially equivalent, every twist of `(H', ρ')` is then reached, and invariant
functions transfer to `ℂ[X(H')]`. -/
theorem component_transfer :
    let Assoc : UChar H → UChar H → Prop := fun ω ω' =>
      ∃ c : RationalLeviConjugacy j j,
        Nonempty (rationalUnramifiedTwist H ω ρ ≅
          rationalIsoPullback c.iso (rationalUnramifiedTwist H ω' ρ))
    let regular := unramifiedRegularFunctions
      (fun χ => (rationalNormCharacters H χ).toMul)
    let invariant : Set (UChar H → ℂ) :=
      {f | f ∈ regular ∧ ∀ ω ω', Assoc ω ω' → f ω = f ω'}
    let Assoc' : UChar H → UChar H' → Prop := fun ω ω' =>
      ∃ c : RationalLeviConjugacy j j',
        Nonempty (rationalUnramifiedTwist H ω ρ ≅
          rationalIsoPullback c.iso (rationalUnramifiedTwist H' ω' ρ'))
    ((∃ ω ω', Assoc' ω ω') ↔
      ∃ c : RationalLeviConjugacy j j', IsRationalInertiaRelated H ρ (rationalIsoPullback c.iso ρ')) ∧
    ((∃ c : RationalLeviConjugacy j j',
        IsRationalInertiaRelated H ρ (rationalIsoPullback c.iso ρ')) →
      (∀ ω' : UChar H', ∃ ω : UChar H, Assoc' ω ω') ∧
      ∀ f ∈ invariant, ∃ f' ∈ unramifiedRegularFunctions
          (fun χ => (rationalNormCharacters H' χ).toMul),
        ∀ ω ω', Assoc' ω ω' → f' ω' = f ω) := by
  intro Assoc regular invariant Assoc'
  -- `(ρ' ⊗ ω')^c ≅ ρ ⊗ ((ω' ∘ c) χ₀)` when `ρ'^c ≅ ρ ⊗ χ₀`.
  have hreach : ∀ (c : RationalLeviConjugacy j j') (χ₀ : UChar H),
      Nonempty (rationalIsoPullback c.iso ρ' ≅ rationalUnramifiedTwist H χ₀ ρ) →
      ∀ ω' : UChar H', Nonempty (rationalUnramifiedTwist H
        (χ₀ * rationalUnramifiedCharacterRestrict c.iso.hom ω') ρ ≅
          rationalIsoPullback c.iso (rationalUnramifiedTwist H' ω' ρ')) := by
    rintro c χ₀ ⟨e⟩ ω'
    obtain ⟨e₁⟩ := pullback_twist c.iso ω' ρ'
    obtain ⟨e₂⟩ := twist_congr (rationalUnramifiedCharacterRestrict c.iso.hom ω') ⟨e⟩
    obtain ⟨e₃⟩ := twist_twist (rationalUnramifiedCharacterRestrict c.iso.hom ω') χ₀ ρ
    obtain ⟨e₄⟩ := twist_eq (mul_comm χ₀ (rationalUnramifiedCharacterRestrict c.iso.hom ω')) ρ
    exact ⟨e₄ ≪≫ e₃.symm ≪≫ e₂.symm ≪≫ e₁.symm⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨ω, ω', c, ⟨e⟩⟩
    refine ⟨c, (rationalUnramifiedCharacterRestrict c.iso.hom ω')⁻¹ * ω, ?_⟩
    obtain ⟨e₁⟩ := pullback_twist c.iso ω' ρ'
    obtain ⟨e₂⟩ := (twist_iso_iff _ _ _).1 ⟨e₁.symm ≪≫ e.symm⟩
    obtain ⟨e₃⟩ := twist_twist (rationalUnramifiedCharacterRestrict c.iso.hom ω')⁻¹ ω ρ
    exact ⟨e₂ ≪≫ e₃⟩
  · rintro ⟨c, χ₀, ⟨e⟩⟩
    refine ⟨χ₀, 1, c, ?_⟩
    obtain ⟨e₁⟩ := twist_one ρ'
    obtain ⟨e₂⟩ := pullback_congr c.iso ⟨e₁⟩
    exact ⟨e.symm ≪≫ e₂.symm⟩
  · rintro ⟨c, χ₀, hχ₀⟩
    refine ⟨fun ω' => ⟨_, c, hreach c χ₀ hχ₀ ω'⟩, fun f ⟨hf, hfa⟩ => ?_⟩
    refine ⟨fun ω' => f (χ₀ * rationalUnramifiedCharacterRestrict c.iso.hom ω'),
      comp_affine_mem_regular c.iso.hom χ₀ hf, ?_⟩
    rintro ω ω' ⟨c', ⟨e'⟩⟩
    refine (hfa ω _ ⟨c'.trans c.symm, ?_⟩).symm
    obtain ⟨e₁⟩ := hreach c χ₀ hχ₀ ω'
    obtain ⟨e₂⟩ := pullback_congr c.iso.symm ⟨e₁⟩
    have e₃ := rationalIsoPullbackCancelIso c.iso.symm (rationalUnramifiedTwist H' ω' ρ')
    rw [Iso.symm_symm_eq] at e₃
    exact ⟨e' ≪≫ (pullback_congr c'.iso ⟨e₃.symm ≪≫ e₂.symm⟩).some ≪≫
      rationalIsoPullbackTransIso c'.iso c.iso.symm _⟩

end Generic

end Langlands.CuspidalSupport.ComponentWeyl

namespace Langlands.CuspidalSupport

open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme

universe uF uV

/-- Renard VI.7.1, Theorem: each inertial component of `Ω(G)` through a standard cuspidal
datum is the quotient `X(M)/W` of the unramified characters of its Levi by a finite group of
algebraic automorphisms, with a finitely generated domain as coordinate algebra, independently
of the chosen representative. -/
theorem bernsteinComponentVariety : BernsteinComponentVarietyStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family a X twist Assoc regular invariant
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let j : bernsteinLeviScheme i ν a.roots ⟶ G := Standard.leviHom i ν (rootSet i ν a.roots)
  have hjc : IsClosedSubgroup j := Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
  have : IsClosedImmersion j.hom.hom.left := hjc
  have hj : Mono j.hom.hom := Over.mono_of_mono_left _
  have hM : IsConnectedReductive (bernsteinLeviScheme i ν a.roots) :=
    standardLeviScheme_isConnectedReductive i ν standardCocharacter dynamicCentralizerReductive
      family.connectedReductive family.maximalSplitTorus family.genericCocharacter a.roots
  have : IsAffineHom (bernsteinLeviScheme i ν a.roots).X.hom := hM.isAffineHom
  have : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
    isAffine_of_isAffineHom (bernsteinLeviScheme i ν a.roots).X.hom
  have : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
    rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
    infer_instance
  let : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
    rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
    rationalPoint_isTopologicalGroup F (bernsteinLeviScheme i ν a.roots)
  have hS := rationalTwistStabilizerFinite.{uF, uV} F _ hM a.representation a.irreducible
  have hFT := rationalUnramifiedRegularFunctions_finiteType _
    (continuous_rationalValuationImageProjection _) hM
  have hD := rationalUnramifiedRegularFunctions_isDomain _
    (continuous_rationalValuationImageProjection _) hM
  have hK := isOpen_rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)
  obtain ⟨A, a₀, ha⟩ := exists_isSplitComponent (bernsteinLeviScheme i ν a.roots)
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G family.connectedReductive T i
    family.maximalSplitTorus ν family.genericCocharacter (rootSet i ν a.roots)
    (rootSet_subset i ν a.roots)
  have hjrep := Standard.isRepresentedBy_leviHom i ν (rootSet i ν a.roots)
  rw [(hcompare ζ hζ).2.1] at hjrep
  have hZ := ha.torusCentralizer_comp_eq_of_dynamicCentralizer
    (CommGroupScheme.groupHom ζ ≫ i) hjrep
  obtain ⟨n, g, -, hN⟩ := ha.exists_finite_normalizer_representatives hjc hZ
  have hgen := ComponentWeyl.weyl_and_variety (H := bernsteinLeviScheme i ν a.roots) j a.representation hj ⟨n, g, hN⟩ hS hFT hD hK
  refine ⟨hgen.1, hgen.2, fun a' => ?_⟩
  have : IsClosedImmersion (Standard.leviHom i ν (rootSet i ν a'.roots)).hom.hom.left :=
    Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a'.roots)
  have : IsAffine (bernsteinLeviScheme i ν a'.roots).X.left :=
    isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a'.roots)).hom.hom.left
  have : LocallyOfFiniteType (bernsteinLeviScheme i ν a'.roots).X.hom := by
    rw [← (Standard.leviHom i ν (rootSet i ν a'.roots)).hom.hom.w]
    infer_instance
  exact ComponentWeyl.component_transfer (H := bernsteinLeviScheme i ν a.roots)
    (H' := bernsteinLeviScheme i ν a'.roots) j a.representation
    (Standard.leviHom i ν (rootSet i ν a'.roots)) a'.representation

end Langlands.CuspidalSupport
