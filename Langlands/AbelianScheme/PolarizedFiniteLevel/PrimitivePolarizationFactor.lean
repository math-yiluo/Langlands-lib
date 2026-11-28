import Langlands.AbelianScheme.PolarizedFiniteLevel.PrimitivePolarizationBaseChange
import Langlands.AbelianScheme.PolarizedFiniteLevel.PrimitivePolarizationTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationDoublingDivisionProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationRayPositivityProof
import Langlands.AbelianScheme.Tate.GeometricTorsionRankProof

/-! # Primitive factors of positive-dimensional polarizations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.GroupScheme.Tate (Index)

variable (P : Prerequisites.{u}) {S : Scheme.{u}} {A : AbelianScheme S}

/-- The polarization of an abelian scheme of positive relative dimension is a
positive integer multiple of an actual primitive homomorphism. -/
theorem DualWitness.exists_primitivePolarizationFactor
    (W : DualWitness A) (lam : A ⟶ W.dual P) (hlam : W.IsPolarization P lam)
    (g : ℕ) (hg : 0 < g) (hdim : A.HasRelativeDimension g)
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) :
    ∃ mu : A ⟶ W.dual P, Tate.IsPrimitiveHom mu ∧ ∃ k : ℕ, 0 < k ∧ k • mu = lam := by
  let T := Over.mk s
  let K := (GroupScheme.pointsHom (groupHom lam) T).ker
  let : Finite K := GroupScheme.IsIsogeny.finite_ker_pointsHom s hlam.1
  have divisorBound (k : ℕ) (mu : A ⟶ W.dual P) (hk : 0 < k) (he : k • mu = lam) :
      k ≤ Nat.card K := by
    let f : GroupScheme.Tate.Level A.toGrp T k → K := fun x => ⟨(Additive.toMul x).val, by
      have hz := Tate.levelMap_nsmul_self T mu k x
      rw [he] at hz
      exact congrArg (fun z => Additive.toMul
        (GroupScheme.Tate.toSection (W.dual P).toGrp T k z)) hz⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply GroupScheme.Tate.toSection_injective A.toGrp T k
      exact congrArg (fun z => Additive.ofMul z.val) hxy
    have hcard := Nat.card_le_card_of_injective f hf
    rw [(Tate.geometricTorsionRank S A g hdim k hk (hu ⟨k, hk, trivial⟩) Ω s).2] at hcard
    exact (Nat.le_self_pow (by omega : 2 * g ≠ 0) k).trans hcard
  obtain ⟨k, mu, hk, he, hmu⟩ := Tate.exists_isPrimitiveHom_nsmul_eq lam (Nat.card K) divisorBound
  exact ⟨mu, hmu, k, hk, he⟩

/-- Choose the primitive factor with its positive multiple equation, in the
form used by primitive dual-map base change. -/
def DualWitness.primitivePolarizationFactor
    (W : DualWitness A) (lam : A ⟶ W.dual P) (hlam : W.IsPolarization P lam)
    (g : ℕ) (hg : 0 < g) (hdim : A.HasRelativeDimension g)
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) :
    {mu : A ⟶ W.dual P // Tate.IsPrimitiveHom mu ∧ ∃ k : ℕ, 0 < k ∧ k • mu = lam} :=
  let h := W.exists_primitivePolarizationFactor P lam hlam g hg hdim hu s
  ⟨Classical.choose h, Classical.choose_spec h⟩

/-- Twice a primitive factor of a polarization is an actual polarization. -/
theorem DualWitness.isPolarization_double_of_primitiveFactor
    (W : DualWitness A) (lam : A ⟶ W.dual P) (hlam : W.IsPolarization P lam)
    (mu : {f : A ⟶ W.dual P // Tate.IsPrimitiveHom f ∧ ∃ k : ℕ, 0 < k ∧ k • f = lam}) :
    W.IsPolarization P (2 • mu.val) := by
  obtain ⟨k, hk, he⟩ := mu.property.2
  exact polarizationDoublingDivision P S A W mu.val k hk (he.symm ▸ hlam)

/-- An isomorphism carrying two polarizations into the same rational ray
carries their doubled primitive factors into one another exactly. -/
theorem DualWitness.double_primitiveFactor_transport
    [IsLocallyNoetherian S] [ConnectedSpace S]
    (htor : TorsionFiniteEtaleStatement.{u})
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)
    {B : AbelianScheme S} (e : A ≅ B) (W : DualWitness A) (V : DualWitness B)
    (g : ℕ) (hg : 0 < g) (hdim : A.HasRelativeDimension g)
    {lamA : A ⟶ W.dual P} {lamB : B ⟶ V.dual P}
    (hA : W.IsPolarization P lamA) (hB : V.IsPolarization P lamB)
    {a b : ℤ} (ha : a ≠ 0) (hEq : a • DualWitness.transportMap P e W V lamB = b • lamA)
    (muA : {f : A ⟶ W.dual P // Tate.IsPrimitiveHom f ∧ ∃ k : ℕ, 0 < k ∧ k • f = lamA})
    (muB : {f : B ⟶ V.dual P // Tate.IsPrimitiveHom f ∧ ∃ k : ℕ, 0 < k ∧ k • f = lamB}) :
    DualWitness.transportMap P e W V (2 • muB.val) = 2 • muA.val := by
  obtain ⟨kA, hkA, hmulA⟩ := muA.property.2
  obtain ⟨kB, hkB, hmulB⟩ := muB.property.2
  rw [DualWitness.transportMap_nsmul, DualWitness.transportMap_eq_of_primitive P
    polarizationRayPositivity htor hu s e W V g hg hdim hA hB ha hEq
    muA.property.1 muB.property.1 hkA hkB hmulA hmulB]

end Langlands.AbelianScheme.PolarizedFiniteLevel
