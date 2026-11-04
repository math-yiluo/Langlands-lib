import Langlands.GroupScheme.CentralIsogeny.CenterTangentQuotient
import Langlands.GroupScheme.Lie.CenterTangent
import Langlands.GroupScheme.Lie.SemisimpleCentrality

/-! # Killing central semisimple tangent vectors by a central isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}} {G Q : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]

/-- An exact full-centre tangent kernel kills precisely those tangent vectors
whose full scheme centralizer is the whole group. -/
theorem targetMap_eq_one_iff_elementCentralizer_eq_top
    (q : G ⟶ Q)
    (hker : LinearMap.ker (targetMapLinear q R) = (center G).lie R)
    (X : lieKernel G R) :
    targetMap q R X = 1 ↔ elementCentralizer G X = ⊤ := by
  rw [elementCentralizer_eq_top_iff_mem_center_lie, ← hker, LinearMap.mem_ker]
  change targetMap q R X = 1 ↔ Additive.ofMul (targetMap q R X) = 0
  exact ⟨congrArg Additive.ofMul, congrArg Additive.toMul⟩

end Lie

section Field

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- On semisimple tangent vectors an exact centre-tangent kernel is equivalent
to full Lie centralizer, without assuming a smooth centre. -/
theorem Lie.targetMap_eq_one_iff_elementCentralizerLie_eq_top
    (q : G ⟶ Q)
    (hker : LinearMap.ker (Lie.targetMapLinear q k) = (center G).lie k)
    {X : lieKernel G k} (hX : Lie.IsSemisimpleElement G X) :
    Lie.targetMap q k X = 1 ↔ Lie.elementCentralizerLie G X = ⊤ := by
  exact (Lie.targetMap_eq_one_iff_elementCentralizer_eq_top q hker X).trans
    (Lie.elementCentralizerLie_eq_top_iff_elementCentralizer_eq_top G hX).symm

end Field

/-- One central isogeny kills precisely the semisimple source tangent vectors
with full Lie centralizer. The same isogeny retains its exact all-algebra
centre-tangent kernel. -/
theorem exists_centralIsogeny_killing_central_semisimple
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (hp : 1 < p)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
      (_ : Smooth Q.X.hom) (ha : IsAffineHom Q.X.hom)
      (_ : ConnectedSpace Q.X.left),
      letI : IsAffineHom Q.X.hom := ha
      IsCentralIsogeny q ∧
        (∀ (A : Type u) [CommRing A] [Algebra k A],
          LinearMap.ker (Lie.targetMapLinear q A) = (center G).lie A) ∧
        ∀ (X : lieKernel G k), Lie.IsSemisimpleElement G X →
          (Lie.targetMap q k X = 1 ↔ Lie.elementCentralizerLie G X = ⊤) := by
  obtain ⟨Q, q, hs, ha, hc, hq, hker⟩ :=
    exists_connected_centralIsogeny_ker_targetMapLinear_eq_center_lie k p hp G
  refine ⟨Q, q, hs, ha, hc, hq, hker, ?_⟩
  intro X hX
  exact Lie.targetMap_eq_one_iff_elementCentralizerLie_eq_top q (hker k) hX

/-- Universal positive-characteristic semisimple-kernel construction. -/
def CentralSemisimpleKernelStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [ExpChar k p],
    1 < p →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
        (_ : Smooth Q.X.hom) (ha : IsAffineHom Q.X.hom)
        (_ : ConnectedSpace Q.X.left),
        letI : IsAffineHom Q.X.hom := ha
        IsCentralIsogeny q ∧
          (∀ (A : Type u) [CommRing A] [Algebra k A],
            LinearMap.ker (Lie.targetMapLinear q A) = (center G).lie A) ∧
          ∀ (X : lieKernel G k), Lie.IsSemisimpleElement G X →
            (Lie.targetMap q k X = 1 ↔ Lie.elementCentralizerLie G X = ⊤)

theorem centralSemisimpleKernel : CentralSemisimpleKernelStatement.{u} := by
  intro k _ p _ hp G _ _ _
  exact exists_centralIsogeny_killing_central_semisimple k p hp G

end Langlands.GroupScheme
