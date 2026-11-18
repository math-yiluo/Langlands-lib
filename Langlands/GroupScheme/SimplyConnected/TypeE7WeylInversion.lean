import Langlands.GroupScheme.Reductive.BasedRootDatumProjection
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneReduction
import Langlands.LinearAlgebra.RootDatumNegation
import Langlands.LinearAlgebra.CartanE7Root
import Langlands.GroupScheme.Reductive.SpecialLinearTorusAutomorphismProof
import Langlands.GroupScheme.Torus.CharacterIsomorphism

/-! # Inversion in the Weyl group of an actual E7 pinning -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.RootDatumNegation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)

/-- For a simply connected E7 root datum, the full lattice negation is Weyl. -/
theorem negAut_mem_weylGroup_of_E7
    (hspan : p.rootDatum.corootSpan ℤ = ⊤) (e : p.base.support ≃ Fin 7)
    (he : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 7 (e a) (e b)) :
    negAut p.rootDatum ∈ p.rootDatum.weylGroup := by
  apply (p.basedRootDatumProjection_eq_one_iff _).mp
  apply Subtype.ext
  apply InnerTypeANormOneReduction.aut_eq_one_of_simple p.base hspan
  intro a
  let θ := p.basedRootDatumProjection (negAut p.rootDatum)
  let f : p.base.support ≃ p.base.support := θ.val.indexEquiv.subtypeEquiv θ.property
  have hcart (i j : Fin 7) :
      CartanMatrix.E 7 (e (f (e.symm i))) (e (f (e.symm j))) = CartanMatrix.E 7 i j := by
    rw [← he]
    change p.rootDatum.pairing (θ.val.indexEquiv (e.symm i).val)
      (θ.val.indexEquiv (e.symm j).val) = _
    rw [RootPairing.Hom.pairing θ.val.toHom, he]
    simp only [Equiv.apply_symm_apply]
  have hfix := Langlands.CartanE7Root.rigid (fun i => e (f (e.symm i))) hcart (e a)
  have hf : f a = a := e.injective (by simpa only [Equiv.symm_apply_apply] using hfix)
  exact congrArg Subtype.val hf

local instance : Mono p.inclusion.hom.hom.left := by
  let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  infer_instance

/-- Full integral negation is realized by an actual geometric normalizer point. -/
theorem exists_normalizer_negates_characters_of_E7
    (hspan : p.rootDatum.corootSpan ℤ = ⊤) (e : p.base.support ≃ Fin 7)
    (he : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 7 (e a) (e b)) :
    ∃ n : normalizerPoints p.inclusion, ∀ χ : characterLattice p.torus,
      weylAction p.inclusion n χ = -χ := by
  let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  obtain ⟨n, hn⟩ := p.isRootDatum.abstractWeylImage_le
    ⟨negAut p.rootDatum, p.negAut_mem_weylGroup_of_E7 hspan e he, rfl⟩
  refine ⟨n, fun χ => ?_⟩
  exact congrArg (fun f : characterLattice p.torus ≃ₗ[ℤ] characterLattice p.torus => f χ) hn

/-- The precise proposition implemented by `exists_normalizer_inverts_torus_of_E7`. -/
def E7TorusInversionStatement : Prop :=
  ∀ (_hspan : p.rootDatum.corootSpan ℤ = ⊤) (e : p.base.support ≃ Fin 7)
    (_he : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 7 (e a) (e b)),
    ∃ n : normalizerPoints p.inclusion,
      IsNormalizingPoint p.inclusion n (SpecialLinearTorusAutomorphism.negIso p.torus)

/-- An actual normalizer realizes inversion on the whole split maximal torus. -/
theorem exists_normalizer_inverts_torus_of_E7
    (hspan : p.rootDatum.corootSpan ℤ = ⊤) (e : p.base.support ≃ Fin 7)
    (he : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 7 (e a) (e b)) :
    ∃ n : normalizerPoints p.inclusion,
      IsNormalizingPoint p.inclusion n (SpecialLinearTorusAutomorphism.negIso p.torus) := by
  obtain ⟨n, hn⟩ := p.exists_normalizer_negates_characters_of_E7 hspan e he
  have hσ : (normalizingAut p.inclusion n).symm =
      SpecialLinearTorusAutomorphism.negIso p.torus := by
    apply Iso.ext
    apply p.isSplitTorus.hom_ext_of_characters
    intro χ
    have hχ := hn χ
    change (normalizingAut p.inclusion n).inv ≫ χ = -χ at hχ
    simpa only [SpecialLinearTorusAutomorphism.negIso, Iso.symm_hom,
      Preadditive.neg_comp, Category.id_comp] using hχ
  refine ⟨n⁻¹, ?_⟩
  have h := (isNormalizingPoint_normalizingAut p.inclusion n).inv
  rwa [hσ] at h

end Langlands.GroupScheme.SplitPinning
