import Langlands.AlgebraicGeometry.Modules.IdealAdicGradedFamily
import Langlands.AlgebraicGeometry.Modules.IdealAdicClosedFibre
import Langlands.AlgebraicGeometry.Modules.CoherentEulerPushforward
import Langlands.AlgebraicGeometry.Modules.CoherentLineBundle
import Langlands.AlgebraicGeometry.Modules.PushforwardVanishing
import Langlands.AlgebraicGeometry.Modules.RationalFibreVanishing
import Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms
import Langlands.AlgebraicGeometry.Modules.PullbackQuasicoherent

/-! # Serre vanishing for modules annihilated by a maximal ideal of the base -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

open DerivedSections

variable {R : CommRingCat.{u}} {X Z : Scheme.{u}} (f : X ⟶ Spec R) {I : Ideal R}

/-- If every element of `I` acts by zero on `G`, the sheaf of `I`-multiples of `G` maps
to `G` by zero. -/
lemma inclusion_eq_zero_of_smulEnd (G : X.Modules) (h : ∀ a ∈ I, smulEnd f a G = 0) :
    inclusion f I G = 0 := by
  rw [← Category.comp_id (inclusion f I G)]
  refine (inclusion_comp_eq_zero_iff f I (𝟙 G)).2 fun U a ha m => ?_
  change (smulEnd f a G).app U m = 0
  rw [h a ha, Scheme.Modules.Hom.zero_app]
  rfl

variable {f} {i : Z ⟶ X} {g : Z ⟶ Spec (CommRingCat.of (R ⧸ I))}

/-- A quasi-coherent module annihilated by `I` is the pushforward of its pullback to the
base change of `Spec (R/I) → Spec R`. -/
def closedFibreIsoOfAnnihilated (hpb : IsPullback i g f (Spec.map (quotientRingHom I)))
    (G : X.Modules) [G.IsQuasicoherent] (h : ∀ a ∈ I, smulEnd f a G = 0) :
    G ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj G) :=
  haveI : IsIso (projection f I G) :=
    cokernel.π_of_zero (inclusion_eq_zero_of_smulEnd f G h)
  asIso (projection f I G) ≪≫ closedFibreIso hpb G

@[simp]
lemma closedFibreIsoOfAnnihilated_hom (hpb : IsPullback i g f (Spec.map (quotientRingHom I)))
    (G : X.Modules) [G.IsQuasicoherent] (h : ∀ a ∈ I, smulEnd f a G = 0) :
    (closedFibreIsoOfAnnihilated hpb G h).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G := by
  simp [closedFibreIsoOfAnnihilated]

/-- The pullback of a quasi-coherent module with finite affine sections to the base change
of `Spec (R/I) → Spec R` has finite affine sections. -/
lemma hasFiniteAffineSections_pullback_of_isPullback
    (hpb : IsPullback i g f (Spec.map (quotientRingHom I))) (G : X.Modules)
    [G.IsQuasicoherent] (hG : HasFiniteAffineSections G) :
    HasFiniteAffineSections ((Scheme.Modules.pullback i).obj G) := by
  have := isClosedImmersion_of_isPullback hpb
  refine HasLocallyFiniteSections.finiteAffineSections (fun z => ?_)
  obtain ⟨U, hU, hzU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := i.base z) (U := ⊤) trivial
  refine ⟨i ⁻¹ᵁ U, hU.preimage i, hzU, ?_⟩
  have : RingHomSurjective (i.app U).hom := ⟨i.app_surjective U hU⟩
  have hfin : (⊤ : Submodule Γ(X, U) Γ(G, U)).FG := (hG ⟨U, hU⟩).fg_top
  rw [Module.finite_def, ← LinearMap.range_eq_top.2
    (sectionPullback_surjective_of_isPullback hpb G hU), LinearMap.range_eq_map]
  exact hfin.map _

/-- Serre vanishing for coherent modules annihilated by a maximal ideal `I` of the base:
if the closed fibre `Z = X ×_{Spec R} Spec (R/I)` is proper over the field `R/I` and the
pullback of `L` to `Z` is ample, then for every quasi-coherent `G` with finite affine
sections on which `I` acts by zero, `H^{p+1}(X, G ⊗ L^d)` vanishes for all `p` and all
large `d`. -/
theorem exists_vanishing_tensorPow_of_annihilated [I.IsMaximal] [IsProper f]
    (hpb : IsPullback i g f (Spec.map (quotientRingHom I))) (L : Picard.LineBundle X)
    (hL : ((Picard.LineBundle.pullback i).obj L).IsAmple) (G : X.Modules)
    (hG : AnnihilatedCoherent f I G) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ p : ℕ,
      IsZero ((relativeCohomology f (p + 1)).obj ((tensorBy (tensorPow L.obj d)).obj G)) := by
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  obtain ⟨hq, hfin, hann⟩ := hG
  have hcl := isClosedImmersion_of_isPullback hpb
  have hg : IsProper g := MorphismProperty.of_isPullback (P := @IsProper) hpb ‹IsProper f›
  let K := (Scheme.Modules.pullback i).obj G
  let L' := (Picard.LineBundle.pullback i).obj L
  obtain ⟨n₀, hn₀⟩ := properAmplePairSerreVanishing (R ⧸ I) Z g hg K inferInstance
    (hasFiniteAffineSections_pullback_of_isPullback hpb G hfin) L' L' hL hL
  refine ⟨n₀ + n₀, fun d hd p => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b, d = n₀ + b := ⟨d - n₀, by omega⟩
  have h₁ := hn₀ n₀ b le_rfl (by omega) (p + 1) (Nat.succ_pos p)
  let e₁ : tensorObj (tensorObj K (tensorPow L'.obj n₀)) (tensorPow L'.obj b) ≅
      tensorObj K (tensorPow L'.obj (n₀ + b)) :=
    tensorAssociator _ _ _ ≪≫
      (tensorFunctor Z).mapIso ((Iso.refl K).prod (tensorPowAddIso L'.obj n₀ b))
  have h₂ : IsZero ((relativeCohomology (i ≫ f) (p + 1)).obj
      (tensorObj K (tensorPow L'.obj (n₀ + b)))) :=
    (isZero_relativeCohomology_iff g (i ≫ f) _ _).1
      (h₁.of_iso ((relativeCohomology g (p + 1)).mapIso e₁).symm)
  have h₃ := h₂.of_iso (pushforwardCohomologyIso i f _
    (fun q => closedImmersionHigherDirectImageVanishing Z X i hcl _ q) (p + 1)).symm
  exact h₃.of_iso ((relativeCohomology f (p + 1)).mapIso
    ((tensorBy (tensorPow L.obj (n₀ + b))).mapIso (closedFibreIsoOfAnnihilated hpb G hann) ≪≫
      coherentTwistPushforwardIso i K L (n₀ + b)))

/-- Uniform vanishing for the maximal-ideal layers of the powers of a line bundle on a
proper scheme over a noetherian local ring whose closed fibre carries an ample pullback:
one `d₀` makes `H^{p+1}(X, 𝔪ⁿL^d / 𝔪ⁿ⁺¹L^d)` vanish for all `d ≥ d₀` and all `n`, `p`. -/
theorem exists_uniform_vanishing_adicLayer_maximalIdeal [IsNoetherianRing R] [IsLocalRing R]
    [IsProper f] {g : Z ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R))}
    (hpb : IsPullback i g f (Spec.map (quotientRingHom (IsLocalRing.maximalIdeal R))))
    (L : Picard.LineBundle X) (hL : ((Picard.LineBundle.pullback i).obj L).IsAmple) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ n p : ℕ,
      IsZero ((relativeCohomology f (p + 1)).obj
        (adicLayer f (IsLocalRing.maximalIdeal R) (tensorPow L.obj d) n)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  exact exists_uniform_vanishing_adicLayer_tensorPow f _ (IsNoetherian.noetherian _) L.obj
    L.property (fun G hG => exists_vanishing_tensorPow_of_annihilated hpb L hL G hG)

end Langlands.AlgebraicGeometry.Modules.IdealAdic
