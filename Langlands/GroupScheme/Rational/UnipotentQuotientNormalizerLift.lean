import Langlands.GroupScheme.Rational.TorusUnipotentQuotientConjugacy
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof
import Langlands.GroupScheme.Rational.TorusVectorLinearizationProof
import Langlands.GroupScheme.Torus.Maximal

/-! # Exact normalizer lifts through smooth connected unipotent kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace UnipotentQuotientNormalizerLift

variable {k : Type u} [Field k]
  {N G Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth N.X.hom] [ConnectedSpace N.X.left]
  (r : N ⟶ G) (hr : IsClosedSubgroup r) (hN : IsUnipotent N)
  (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q)
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (hT : IsTorus T.toGrp)
  (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X) (σ : T ≅ T)
  (hn : IsNormalizingPoint (i ≫ q) n σ)

/-- Lift a specified quotient normalizer point with exactly its specified torus
automorphism, when the represented smooth connected unipotent kernel is split. -/
def splitNormalizerLift (hNsplit : RelativeRoot.IsSplitUnipotent N) :
    {m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      m ≫ q.hom.hom = n ∧ IsNormalizingPoint i m σ} := by
  let f : T.toGrp ≅ T.toGrp :=
    { hom := CommGroupScheme.groupHom σ.hom
      inv := CommGroupScheme.groupHom σ.inv
      hom_inv_id := congrArg Additive.toMul σ.hom_inv_id
      inv_hom_id := congrArg Additive.toMul σ.inv_hom_id }
  exact ⟨QuotientConjugacyLift.fppfSplitUnipotentConjugator
      RelativeRoot.splitUnipotentStableVectorSubgroup
      RelativeRoot.torusVectorActionLinearization
      r hr hN hNsplit q hq i i f hT n hn,
    QuotientConjugacyLift.fppfSplitUnipotentConjugator_comp
      RelativeRoot.splitUnipotentStableVectorSubgroup
      RelativeRoot.torusVectorActionLinearization
      r hr hN hNsplit q hq i i f hT n hn,
    QuotientConjugacyLift.fppfSplitUnipotentConjugator_conjugates
      RelativeRoot.splitUnipotentStableVectorSubgroup
      RelativeRoot.torusVectorActionLinearization
      r hr hN hNsplit q hq i i f hT n hn⟩

include hr hN hq hT hn in
/-- The exact normalizer-lifting existence form over a split unipotent kernel. -/
theorem exists_normalizer_lift_of_split_unipotent_kernel
    (hNsplit : RelativeRoot.IsSplitUnipotent N) :
    ∃ m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      m ≫ q.hom.hom = n ∧ IsNormalizingPoint i m σ :=
  ⟨(splitNormalizerLift r hr hN q hq i hT n σ hn hNsplit).val,
    (splitNormalizerLift r hr hN q hq i hT n σ hn hNsplit).property⟩

/-- Over a perfect field, smooth connected unipotence of the represented
kernel supplies the splitness needed for an exact normalizer lift. -/
def perfectFieldNormalizerLift [PerfectField k] :
    {m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      m ≫ q.hom.hom = n ∧ IsNormalizingPoint i m σ} := by
  let : IsClosedImmersion r.hom.hom.left := hr
  let : IsAffineHom N.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed G N r hr
  exact splitNormalizerLift r hr hN q hq i hT n σ hn
    (perfectFieldUnipotentSplit k N inferInstance hN)

include hr hN hq hT hn in
/-- A perfect-field quotient normalizer point lifts, preserving both its
quotient image and its prescribed torus automorphism. -/
theorem exists_normalizer_lift_of_perfect_field_unipotent_kernel [PerfectField k] :
    ∃ m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      m ≫ q.hom.hom = n ∧ IsNormalizingPoint i m σ :=
  ⟨(perfectFieldNormalizerLift r hr hN q hq i hT n σ hn).val,
    (perfectFieldNormalizerLift r hr hN q hq i hT n σ hn).property⟩

include hr hN hq hT in
/-- The same exact lifting conclusion for a separately supplied target torus
map, identified by its actual commuting square with the quotient. -/
theorem exists_normalizer_lift [PerfectField k]
    (i' : T.toGrp ⟶ Q) (h : i ≫ q = i')
    (hn' : IsNormalizingPoint i' n σ) :
    ∃ m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      m ≫ q.hom.hom = n ∧ IsNormalizingPoint i m σ := by
  apply exists_normalizer_lift_of_perfect_field_unipotent_kernel
    r hr hN q hq i hT n σ
  rwa [h]

end UnipotentQuotientNormalizerLift

end Langlands.GroupScheme
