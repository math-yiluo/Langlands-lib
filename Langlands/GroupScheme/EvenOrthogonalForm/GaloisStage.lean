import Langlands.GroupScheme.Descent.FiniteStageIso
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormFiniteSeparable
import Langlands.GroupScheme.Rational.FiniteGaloisOverlapDiscrepancy
import Langlands.GroupScheme.IdentityComponent.Transport
import Langlands.GroupScheme.OrthogonalMatrix.Subgroups

/-! # A finite Galois splitting field of a form of the split even special orthogonal group

A group scheme `H` over a field `K` that becomes isomorphic over the separable closure to the
split `SO_{2n}` (the identity component of the split orthogonal group) has natural local
isomorphisms to the split `SO_{2n}` over `K` along `Spec N ⟶ Spec K` for a finite Galois
extension `N / K`. Local isomorphisms along a finite Galois cover that are invariant under the
Galois automorphisms are independent of the cover point.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  {G H : GroupScheme (Spec (CommRingCat.of K))}

/-- Local isomorphisms along a finite Galois cover whose values at `s` and at `s ≫ σ*` agree
for every Galois automorphism `σ` are independent of the cover point. -/
theorem isIndependent_of_galois (e : LocalGroupIso G H (ringTest K L))
    (h : ∀ (σ : L ≃ₐ[K] L) {V : Over (Spec (CommRingCat.of K))}
      (s : V ⟶ ringTest K L) (g : V ⟶ G.X),
      e.toFun s g = e.toFun (s ≫ ringTestMap K σ.toAlgHom) g) :
    e.IsIndependent := by
  have huniv :
      e.toFun (fst (ringTest K L ⊗ ringTest K L) G.X ≫ fst (ringTest K L) (ringTest K L))
          (snd (ringTest K L ⊗ ringTest K L) G.X) =
        e.toFun (fst (ringTest K L ⊗ ringTest K L) G.X ≫ snd (ringTest K L) (ringTest K L))
          (snd (ringTest K L ⊗ ringTest K L) G.X) := by
    apply Cocycle.galoisPair_ext_tensor
    intro σ V s y
    rw [← e.naturality, ← e.naturality]
    simp only [lift_fst_assoc, lift_snd, Category.assoc, Cocycle.galoisPair_fst,
      Cocycle.galoisPair_snd, Category.comp_id]
    exact h σ s y
  intro Z a b g
  change e.toFun a g = e.toFun b g
  have h1 := e.naturality (lift (lift a b) g)
    (fst (ringTest K L ⊗ ringTest K L) G.X ≫ fst (ringTest K L) (ringTest K L))
    (snd (ringTest K L ⊗ ringTest K L) G.X)
  have h2 := e.naturality (lift (lift a b) g)
    (fst (ringTest K L ⊗ ringTest K L) G.X ≫ snd (ringTest K L) (ringTest K L))
    (snd (ringTest K L ⊗ ringTest K L) G.X)
  simp only [lift_fst_assoc, lift_fst, lift_snd] at h1 h2
  rw [h1, h2, huniv]

end LocalGroupIso

namespace EvenOrthogonalForm

open OrthogonalMatrix

variable (K : Type u) [Field K]

/-- The split special orthogonal group `SO_{2n}` over `K`: the identity component of the split
orthogonal group `O_{2n}` of the hyperbolic form. -/
abbrev splitGroup (n : ℕ) : GroupScheme (Spec (CommRingCat.of K)) :=
  identityComponent (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of K))

/-- The base change of the split `SO_{2n}` from `K` to an extension field `L` is the split
`SO_{2n}` over `L`. -/
def splitBaseChangeIso (L : Type u) [Field L] [Algebra K L] (n : ℕ) :
    (GroupScheme.baseChange (algebraBaseMap K L)).obj (splitGroup K n) ≅ splitGroup L n :=
  IdentityComponent.baseChangeIso (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of K))
      (algebraMap K L) ≪≫
    IdentityComponent.mapIso (baseChangeModelIso (Fin n) (algebraBaseMap K L))

/-- A form of the split `SO_{2n}` that splits over the separable closure has local
isomorphisms to the split `SO_{2n}` along a finite Galois extension. -/
theorem exists_galois_localIso (H : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffineHom H.X.hom] (n : ℕ)
    (e : (GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj H ≅
      splitGroup (SeparableClosure K) n) :
    ∃ (N : Type u) (_ : Field N) (_ : Algebra K N) (_ : FiniteDimensional K N)
      (_ : IsGalois K N), Nonempty (LocalGroupIso H (splitGroup K n) (ringTest K N)) := by
  obtain ⟨L, _, _, _, _, ⟨φ⟩⟩ :=
    Descent.FiniteStage.exists_finiteSeparable_localIso_of_separableClosure K
      (e ≪≫ (splitBaseChangeIso K (SeparableClosure K) n).symm)
  let N := IntermediateField.normalClosure K L (SeparableClosure K)
  let f : L →ₐ[K] N :=
    (normalClosure.algHomEquiv K L (SeparableClosure K)).symm IsSepClosed.lift
  exact ⟨N, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨φ.refine (QuasiSplitInnerForm.coverRefinement f)⟩⟩

end EvenOrthogonalForm

end Langlands.GroupScheme
