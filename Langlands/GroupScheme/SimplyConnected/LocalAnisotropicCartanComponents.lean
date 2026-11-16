import Langlands.GroupScheme.Reductive.TitsComponentFactorStatement
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicTypeAInnerProof
import Langlands.LocalField.FiniteExtension

/-! # Local anisotropic Cartan components from actual factor realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- A connected Cartan component has a positive type-A Cartan matrix, and every
full absolute Galois element preserving that component fixes all its vertices. -/
def HasInnerTypeAComponent (a : d.Vertex) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ q : d.CartanComponent a ≃ Fin n,
    (∀ b c, d.cartan b.val c.val = CartanMatrix.A n (q b) (q c)) ∧
      ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k),
        d.CartanConnected a (d.star σ a) →
          ∀ b : d.CartanComponent a, d.star σ b.val = b.val

end TitsIndexData

/-- Every connected absolute Cartan component of an anisotropic semisimple
group over a nonarchimedean local field has type A and no internal full-star
action. Distinct components may still be permuted. This statement is unproved. -/
def LocalAnisotropicCartanComponentsStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    IsAnisotropic G → ∀ a : d.Vertex, d.HasInnerTypeAComponent a

/-- The actual-factor realization and the local absolute type-A theorem imply
the full component statement. The inner-type-A input is already published. -/
theorem localAnisotropicCartanComponents_of_componentFactor
    (hfactor : SemisimpleTitsComponentFactorStatement.{u})
    (hA : LocalAnisotropicTypeAStatement.{u}) :
    LocalAnisotropicCartanComponentsStatement.{u} := by
  intro k _ _ _ _ G _ _ d hanis a
  obtain ⟨F⟩ := hfactor k G d a
  let := Langlands.LocalField.FiniteExtension.normedField k F.extension
  let := Langlands.LocalField.FiniteExtension.valuativeRel k F.extension
  let := Langlands.LocalField.FiniteExtension.isLocalField k F.extension
  have hFanis := F.anisotropic hanis
  obtain ⟨n, hn, q, hq⟩ := hA F.extension F.factor F.index F.absolutelyAlmostSimple hFanis
  refine ⟨n, hn, F.vertexEquiv.symm.trans q, ?_, ?_⟩
  · intro b c
    change d.cartan b.val c.val =
      CartanMatrix.A n (q (F.vertexEquiv.symm b)) (q (F.vertexEquiv.symm c))
    calc
      d.cartan b.val c.val =
          F.index.cartan (F.vertexEquiv.symm b) (F.vertexEquiv.symm c) := by
        simpa only [Equiv.apply_symm_apply] using
          F.cartan_eq (F.vertexEquiv.symm b) (F.vertexEquiv.symm c)
      _ = _ := hq _ _
  · intro σ hσ b
    obtain ⟨τ, hτ⟩ := F.stabilizer_lift σ hσ
    have hinner := localAnisotropicTypeAInner F.extension F.factor F.index n
      F.simplyConnected F.absolutelyAlmostSimple hFanis ⟨q, hq⟩
    have hb := hτ (F.vertexEquiv.symm b)
    simpa only [hinner τ, Equiv.apply_symm_apply] using hb.symm

end Langlands.GroupScheme
