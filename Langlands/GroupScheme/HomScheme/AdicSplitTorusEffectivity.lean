import Langlands.GroupScheme.HomScheme.AdicReducedSplitTorus
import Langlands.GroupScheme.HomScheme.AdicReducedBase
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompletePunctured
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Adic Hom effectivity from split tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal
  (isAdicComplete_map_of_finite)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.Adic

open Diagonalizable

/-- For a split torus and a smooth separated quasi-compact group with affine
residue fibres, adic restriction over a complete Noetherian local ring is bijective. -/
def SplitTorusAdicEffectivityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (H G : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
    IsSplitTorus H → HasAffineResidueFibers G →
    Function.Bijective (System.restrict (maximalIdeal A) H G)

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A]
  {G : GroupScheme (Spec (CommRingCat.of A))}
  [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]

set_option maxHeartbeats 1100000 in
private theorem splitTorusAdicEffectivity_coordinates (L : Type u) [Fintype L]
    (hG : HasAffineResidueFibers G) :
    Function.Bijective (System.restrict (maximalIdeal A)
      (groupScheme (CommRingCat.of A) (L → ℤ)).toGrp G) := by
  let H := (groupScheme (CommRingCat.of A) (L → ℤ)).toGrp
  let : AddGroup.FG (L → ℤ) := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hH : RelativeMultiplicativeType.IsMultiplicativeType H :=
    .of_isDiagonalizable (isDiagonalizable_groupScheme (CommRingCat.of A) (L → ℤ))
  refine ⟨System.restrict_injective_of_torsion hH G, fun s => ?_⟩
  let N := nilradical A
  let B := A ⧸ N
  let φ : A →+* B := Ideal.Quotient.mk N
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hnil : IsNilpotent (RingHom.ker φ) := by
    rw [show RingHom.ker φ = N from Ideal.mk_ker]
    exact IsNoetherianRing.isNilpotent_nilradical A
  let : Nontrivial B := (Ideal.Quotient.nontrivial_iff (I := N)).mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
      (nilradical_le_prime (maximalIdeal A)))
  let : IsLocalRing B := IsLocalRing.of_surjective' φ hφ
  let : IsNoetherianRing B := inferInstanceAs (IsNoetherianRing (A ⧸ N))
  let : _root_.IsReduced B := (Ideal.isRadical_iff_quotient_reduced N).mp
    (Ideal.radical_isRadical (0 : Ideal A))
  have hm : (maximalIdeal A).map φ = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective φ hφ
  let : IsAdicComplete ((maximalIdeal A).map φ) B :=
    isAdicComplete_map_of_finite (S := A ⧸ N) (maximalIdeal A)
  let : IsAdicComplete (maximalIdeal B) B := hm ▸ inferInstanceAs
    (IsAdicComplete ((maximalIdeal A).map φ) B)
  let b := Spec.map (CommRingCat.ofHom φ)
  let G' := (baseChange b).obj G
  let : Smooth G'.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsSeparated G'.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom b))
  let : QuasiCompact G'.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.X.hom b))
  have hb := System.restrict_bijective_of_iso (maximalIdeal B)
    (baseChangeIso b (L → ℤ)) (Iso.refl G')
    (reducedSplitTorusAdicEffectivity B L G' (hG.baseChange b))
  have hb' : Function.Bijective (System.restrict ((maximalIdeal A).map φ)
      ((baseChange b).obj H) G') := by rw [hm]; exact hb
  obtain ⟨f₀, hf₀⟩ := hb'.2 (s.pull φ)
  have hlift := hasFirstQuotientLift_of_nilpotent_pull hH s φ hφ hnil f₀
    (congrArg (fun k => k.hom 0) hf₀)
  exact exists_algebraization_of_firstQuotientLift hH s hlift

/-- Reduce along the nilradical, then lift the first quotient and correct
all higher quotients by an actual conjugation. -/
theorem splitTorusAdicEffectivity : SplitTorusAdicEffectivityStatement.{u} := by
  classical
  intro A _ _ _ _ H G _ _ _ hH hG
  obtain ⟨L, _, ⟨e⟩⟩ := hH
  let : Fintype L := Fintype.ofFinite L
  let d := splitIso (CommRingCat.of A) (AddEquiv.refl (L → ℤ))
  exact System.restrict_bijective_of_iso (maximalIdeal A) (e ≪≫ d.symm) (Iso.refl G)
    (splitTorusAdicEffectivity_coordinates L hG)

end Langlands.GroupScheme.HomScheme.Adic
