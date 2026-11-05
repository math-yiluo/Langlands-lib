import Langlands.GroupScheme.Reductive.CharacteristicZeroLeviStatement
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.PerfectFieldProof
import Langlands.GroupScheme.Rational.FppfQuotientSmooth

/-! # Reductive quotients and the remaining section input for Levi decomposition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An actual connected reductive quotient with a smooth connected unipotent
scheme-theoretic kernel, over the original ground field. -/
structure ReductiveUnipotentQuotient
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  quotient : GroupScheme (Spec (CommRingCat.of k))
  projection : G ⟶ quotient
  isConnectedReductive : IsConnectedReductive quotient
  isFppfQuotient :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι projection)) projection
  smooth_projection : Smooth projection.hom.hom.left
  smooth_kernel : Smooth (kernel projection).X.hom
  connectedSpace_kernel : ConnectedSpace (kernel projection).X.left
  isUnipotent_kernel : IsUnipotent (kernel projection)

namespace ReductiveUnipotentQuotient

/-- The represented radical and its quotient construct a reductive quotient
over every perfect field. The output records properties of the actual kernel. -/
theorem nonempty_of_perfectField [PerfectField k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    Nonempty (ReductiveUnipotentQuotient G) := by
  obtain ⟨U, i, hi⟩ := unipotentRadicalExistence k G
  obtain ⟨Q, q, hq, hQ⟩ := unipotentRadicalQuotient k G U i hi
  let : IsAffineHom Q.X.hom := hQ.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Smooth U.X.hom := hi.smooth
  let : ConnectedSpace U.X.left := hi.connectedSpace
  let : QuasiCompact q.hom.hom.left := by
    have hc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hc
    exact QuasiCompact.of_comp _ Q.X.hom
  refine ⟨{
    quotient := Q
    projection := q
    isConnectedReductive := (perfectFieldPseudoReductive k Q).mp hQ
    isFppfQuotient := ?_
    smooth_projection := hq.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hi.smooth
    smooth_kernel := KernelRepresentative.smooth q i hq.2.2.2
    connectedSpace_kernel := KernelRepresentative.connectedSpace q i hq.2.2.2
    isUnipotent_kernel := KernelRepresentative.isUnipotent q i hq.2.2.2 hi.isUnipotent
  }⟩
  rw [hq.2.2.2]
  exact hq

/-- A chosen reductive quotient of a smooth connected affine group over a
perfect field. No radical or quotient is supplied as an input. -/
def ofPerfectField [PerfectField k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    ReductiveUnipotentQuotient G :=
  Classical.choice (nonempty_of_perfectField G)

end ReductiveUnipotentQuotient

/-- The exact Levi target follows from homomorphic sections of smooth
surjections onto connected reductive groups with connected unipotent kernel.
The section-existence input is retained explicitly. -/
theorem characteristicZeroLeviDecomposition_of_reductiveExtensionSections
    (hsection : ∀ (k : Type u) [Field k] [CharZero k]
      (E H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth E.X.hom] [IsAffineHom E.X.hom] [ConnectedSpace E.X.left]
      (q : E ⟶ H) [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
      [ConnectedSpace (kernel q).X.left],
      IsConnectedReductive H → IsUnipotent (kernel q) →
        ∃ s : H ⟶ E, s ≫ q = 𝟙 H) :
    CharacteristicZeroLeviDecompositionStatement.{u} := by
  intro k _ _ G _ _ hsm hconn
  let : Smooth G.X.hom := hsm
  let : ConnectedSpace G.X.left := hconn
  let : IsAffineHom G.X.hom := inferInstance
  let D := ReductiveUnipotentQuotient.ofPerfectField G
  let : Smooth D.projection.hom.hom.left := D.smooth_projection
  let : Surjective D.projection.hom.hom.left := D.isFppfQuotient.2.1
  let : ConnectedSpace (kernel D.projection).X.left := D.connectedSpace_kernel
  obtain ⟨s, hs⟩ := hsection k G D.quotient D.projection
    D.isConnectedReductive D.isUnipotent_kernel
  exact ⟨D.quotient, D.projection, s, hs, D.isConnectedReductive,
    D.smooth_kernel, D.connectedSpace_kernel, D.isUnipotent_kernel⟩

end Langlands.GroupScheme
