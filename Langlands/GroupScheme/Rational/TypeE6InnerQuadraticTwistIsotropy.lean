import Langlands.GroupScheme.Adjoint.ExistenceProof
import Langlands.GroupScheme.Rational.QuadraticSplitMaximalTorus
import Langlands.GroupScheme.Rational.TypeE6QuadraticTorusIsotropy
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.Reductive.InnerFormStarForward
import Langlands.GroupScheme.Reductive.InnerStarWeights
import Langlands.GroupScheme.Reductive.QuasiSplitStarCriterionProof

/-! # Quadratic pure twists of split type E6 are isotropic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

section InnerComparison

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [Algebra.IsSeparable F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- A conjugation discrepancy preserves the numbered Cartan matrix and
triviality of the star action. -/
theorem LocalGroupIso.exists_inner_numbering_of_conjugation
    (d : TitsIndexData G) (dH : TitsIndexData H) {n : ℕ} (e : d.Vertex ≃ Fin n)
    (C : Matrix (Fin n) (Fin n) ℤ) (hC : ∀ a b, d.cartan a b = C (e a) (e b))
    (hinner : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex), d.star σ a = a)
    (t : LocalGroupIso G H (GaloisCocycle.cover F L))
    (ξ : Cocycle G (GaloisCocycle.cover F L))
    (ht : t.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ) :
    ∃ eH : dH.Vertex ≃ Fin n,
      (∀ a b, dH.cartan a b = C (eH a) (eH b)) ∧
      ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : dH.Vertex), dH.star σ a = a := by
  obtain ⟨A, q, hq⟩ := adjointQuotientExistence F G d.isSemisimple.isConnectedReductive
  have hdt : t.HasInnerDiscrepancy hq.innerAction := by
    intro U a b
    refine ⟨ξ.toFun a b ≫ q.hom.hom, ?_⟩
    intro W r g
    rw [← Category.assoc, hq.innerAction_act_lift, ← ξ.naturality r a b]
    simpa only [AutomorphicAction.conjugation_act, Category.comp_id, Grp.id_hom_hom] using
      ht (r ≫ a) (r ≫ b) g
  obtain ⟨p, hbase, hstar⟩ := InnerFormStarForward.of_localIso hq d.pinning dH.pinning t hdt
  let v : d.Vertex ≃ dH.Vertex := p.indexEquiv.subtypeEquiv hbase
  let eH := v.symm.trans e
  refine ⟨eH, ?_, ?_⟩
  · intro a b
    have h := p.toHom.pairing (i := (v.symm a).val) (j := (v.symm b).val)
    change dH.cartan (v (v.symm a)) (v (v.symm b)) = d.cartan (v.symm a) (v.symm b) at h
    rw [v.apply_symm_apply, v.apply_symm_apply] at h
    exact h.trans (hC _ _)
  · intro σ a
    obtain ⟨b, rfl⟩ := v.surjective a
    apply Subtype.ext
    exact ((congrArg (fun w => w.indexEquiv b.val) (hstar σ)).symm).trans
      (congrArg (fun z : d.Vertex => (v z).val) (hinner σ b))

end InnerComparison

/-- If a simply connected quasi-split inner E6 group is twisted by a cocycle
on a quadratic Galois cover, the pure twist is isotropic and has inner E6 type. -/
def TypeE6InnerQuadraticTwistIsotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] [Infinite F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (e : d.Vertex ≃ Fin 6), IsSimplyConnected G → IsQuasiSplit G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    (∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex), d.star σ a = a) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
      Module.finrank F L = 2 →
      ∀ (ξ : Cocycle G (GaloisCocycle.cover F L)) (H : GroupScheme (Spec (CommRingCat.of F)))
        [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
        (t : LocalGroupIso G H (GaloisCocycle.cover F L)),
        t.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ →
        ∀ dH : TitsIndexData H, ∃ eH : dH.Vertex ≃ Fin 6,
          (∀ a b, dH.cartan a b = CartanMatrix.E 6 (eH a) (eH b)) ∧
          (∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : dH.Vertex), dH.star σ a = a) ∧
          ¬ IsAnisotropic H

theorem typeE6InnerQuadraticTwistIsotropy : TypeE6InnerQuadraticTwistIsotropyStatement.{u} := by
  classical
  intro F _ _ G _ _ d e hsc hqs hE hinner L _ _ _ _ hL ξ H _ _ t ht dH
  obtain ⟨eH, hEH, hinnerH⟩ := t.exists_inner_numbering_of_conjugation d dH e
    (CartanMatrix.E 6) hE hinner ξ ht
  have hstar (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) : d.pinning.starAction σ = 1 := by
    apply Subtype.ext
    apply StarActionIndependence.equiv_ext_of_weightMap
    exact d.pinning.starAction_weight_of_inner hsc (fun τ a => congrArg Subtype.val (hinner τ a)) σ
  obtain ⟨S, s, hS, hs⟩ := (quasiSplitStarCriterion F G hqs d.pinning).mpr hstar
  let b := algebraBaseMap F L
  let j : (GroupScheme.baseChange b).obj G ≅ (GroupScheme.baseChange b).obj H := t.toBaseChangeIso
  have hscH : IsSimplyConnected H := (isSimplyConnected_fieldExtension_iff (K := L) H).mp
    (IsSimplyConnected.of_iso j.symm (isSimplyConnectedFieldExtension F L G hsc))
  let : Smooth G.X.hom := hsc.isSemisimple.isConnectedReductive.smooth
  let SL := (CommGroupScheme.baseChange b).obj S
  let r : SL.toGrp ⟶ (GroupScheme.baseChange b).obj G := (GroupScheme.baseChange b).map s
  have hsplitH : HasSplitMaximalTorus ((GroupScheme.baseChange b).obj H) := by
    have hmax : IsMaximalTorus r :=
      (maximalTorusBaseChange F L G S s hs.1 hs.2.1).mp hs
    have hmax' : IsMaximalTorus (T := SL) (r ≫ j.hom) := hmax.comp_iso j
    have hSL : IsSplitTorus SL.toGrp := hS.baseChange b
    exact ⟨SL, r ≫ j.hom, hSL, hmax'⟩
  obtain ⟨T, i, hi, hT⟩ := quadraticSplitMaximalTorus F L hL H
    hscH.isSemisimple.isConnectedReductive hsplitH
  exact ⟨eH, hEH, hinnerH, typeE6QuadraticTorusIsotropy F H dH eH hscH hEH hinnerH L hL T i hi hT⟩

end Langlands.GroupScheme
