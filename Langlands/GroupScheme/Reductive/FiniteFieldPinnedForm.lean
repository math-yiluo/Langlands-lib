import Langlands.GroupScheme.Reductive.PinnedGaloisStarAction
import Langlands.GroupScheme.Reductive.PinningBaseChange
import Langlands.FieldTheory.FiniteFrobeniusAction

/-! # A finite-stage form with prescribed Frobenius star action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitPinning

open StarActionIndependence

local instance formBaseChangeAffine (k F : Type u) [Field k] [Field F] [Algebra k F]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k F)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k F))
  infer_instance

section ScalarExtension

variable {k F : Type u} [Field k] [Field F] [Algebra k F] [Algebra.IsAlgebraic k F]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- The actual lattice base-change equivalence preserves the chosen base. -/
theorem baseChangeRootDatumEquiv_preserves_base (a : p.rootIndex) :
    a ∈ p.base.support ↔ (p.baseChangeRootDatumEquiv (F := F)).indexEquiv a ∈
      (p.baseChange (F := F)).base.support := by
  change a ∈ p.base.support ↔ a ∈ p.baseChangeBase.support
  rw [p.baseChangeBase_support]

/-- Scalar extension of based automorphisms through the actual lattice equivalence. -/
def baseChangeBasedAut : p.basedRootDatumAut →* (p.baseChange (F := F)).basedRootDatumAut where
  toFun θ :=
    ⟨conjAut (p.baseChangeRootDatumEquiv (F := F)) θ.val,
      by
        intro a
        change a ∈ p.baseChangeBase.support ↔ θ.val.indexEquiv a ∈ p.baseChangeBase.support
        simpa only [p.baseChangeBase_support] using θ.property a⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' θ η := Subtype.ext (map_mul _ _ _)

/-- The actual scalar-extension root equivalence intertwines based automorphisms. -/
theorem baseChangeBasedAut_intertwine (θ : p.basedRootDatumAut) :
    RootPairing.Equiv.comp (p.baseChangeRootDatumEquiv (F := F)) θ.val =
      RootPairing.Equiv.comp (p.baseChangeBasedAut (F := F) θ).val
        (p.baseChangeRootDatumEquiv (F := F)) :=
  comp_eq_conjAut_comp (p.baseChangeRootDatumEquiv (F := F)) θ.val

end ScalarExtension

section FiniteField

variable {k : Type u} [Field k] [Fintype k]
    {G₀ : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G₀.X.hom]
    (p : SplitPinning G₀) (θ : p.basedRootDatumAut)

/-- Every finite-order based automorphism occurs as the Frobenius star action
of an actual form with pinning data over a finite Galois extension. -/
theorem exists_finiteFrobeniusClass (hθ : IsOfFinOrder θ) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
      (_ : IsGalois k K)
      (G : GroupScheme (Spec (CommRingCat.of k))) (_ : IsAffineHom G.X.hom)
      (_ : LocallyOfFiniteType G.X.hom) (d : GaloisPinningData k K G)
      (f : RootPairing.Equiv p.rootDatum d.toSplitPinning.rootDatum),
      (∀ a, a ∈ p.base.support ↔ f.indexEquiv a ∈ d.toSplitPinning.base.support) ∧
      RootPairing.Equiv.comp f θ.val =
        RootPairing.Equiv.comp
          (d.starAction (FiniteField.frobeniusAlgEquivOfAlgebraic k K)).val f := by
  let A := Langlands.FieldTheory.finiteFrobeniusAction k θ hθ
  let K := A.extension
  let q : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G₀) :=
    p.baseChange (F := K)
  let ψ := p.baseChangeBasedAut (F := K)
  let ρ : (K ≃ₐ[k] K) →* q.basedRootDatumAut := ψ.comp A.action
  let s : GaloisTorusSolution q ρ := q.galoisTorusSolution ρ
  let e := p.baseChangeRootDatumEquiv (F := K)
  let f := RootPairing.Equiv.comp s.rootEquiv e
  have hρ : ρ (FiniteField.frobeniusAlgEquivOfAlgebraic k K) = ψ θ := by
    change ψ (A.action _) = ψ θ
    rw [A.frobenius]
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, s.group.obj,
    inferInstance, inferInstance, s.pinningData, f, ?_, ?_⟩
  · intro a
    exact (p.baseChangeRootDatumEquiv_preserves_base (F := K) a).trans
      (s.rootEquiv_preserves_base _)
  · change RootPairing.Equiv.comp (RootPairing.Equiv.comp s.rootEquiv e) θ.val =
      RootPairing.Equiv.comp (s.pinningData.starAction _).val
        (RootPairing.Equiv.comp s.rootEquiv e)
    have he : RootPairing.Equiv.comp e θ.val =
        RootPairing.Equiv.comp (ψ θ).val e :=
      p.baseChangeBasedAut_intertwine (F := K) θ
    have hs : RootPairing.Equiv.comp s.rootEquiv (ψ θ).val =
        RootPairing.Equiv.comp (s.pinningData.starAction
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K)).val s.rootEquiv := by
      simpa only [hρ] using
        s.starAction_intertwine (FiniteField.frobeniusAlgEquivOfAlgebraic k K)
    calc
      _ = RootPairing.Equiv.comp s.rootEquiv (RootPairing.Equiv.comp e θ.val) :=
        RootPairing.Equiv.comp_assoc _ _ _
      _ = RootPairing.Equiv.comp s.rootEquiv (RootPairing.Equiv.comp (ψ θ).val e) :=
        congrArg (RootPairing.Equiv.comp s.rootEquiv) he
      _ = RootPairing.Equiv.comp (RootPairing.Equiv.comp s.rootEquiv (ψ θ).val) e :=
        (RootPairing.Equiv.comp_assoc _ _ _).symm
      _ = RootPairing.Equiv.comp (RootPairing.Equiv.comp
          (s.pinningData.starAction (FiniteField.frobeniusAlgEquivOfAlgebraic k K)).val
          s.rootEquiv) e := congrArg (fun h => RootPairing.Equiv.comp h e) hs
      _ = _ := RootPairing.Equiv.comp_assoc _ _ _

end FiniteField
end Langlands.GroupScheme.SplitPinning
