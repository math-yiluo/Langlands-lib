import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.GeometricAdjointWeightRanks
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Root weight modules over local rings -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Every root weight module in a fibrewise split reductive group over a
local ring admits a linear trivialization over the original ring. -/
theorem localRootWeightSpace_nonempty_linearEquiv
    {R : Type u} [CommRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    (hG : IsReductive G)
    (I : Type u) [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J) :
    Nonempty (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R]
      CommRingCat.of R) := by
  classical
  let := hG.smooth
  let W := splitTorus.exponentWeightSpace I G i (P.root α)
  let : Module.Free R W := Module.free_of_flat_of_isLocalRing
  let k := IsLocalRing.ResidueField R
  let GK := (baseChange (algebraBaseMap R k)).obj G
  let iK := splitTorus.baseChangeHom (K := k) G I i
  have hGK : IsConnectedReductive GK :=
    hG.isConnectedReductive_baseChange (algebraBaseMap R k)
  let := hGK.isAffineHom
  have hiK : IsMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) iK :=
    splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hi k
  have hroot : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root α) ∈
      roots iK :=
    (hP.mem_roots_iff k (P.root α)).mpr ⟨α, rfl⟩
  obtain ⟨e⟩ := splitRootLieLine k GK hGK
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    (isSplitTorus_splitTorus I) iK hiK _ hroot
  have hdim : Module.finrank k (splitTorus.exponentWeightSpace I GK iK (P.root α)) = 1 := by
    rw [splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter]
    rw [← e.finrank_eq]
    exact Module.finrank_self k
  have hdimR : Module.finrank R W = 1 := by
    calc
      Module.finrank R W = Module.finrank k (k ⊗[R] W) :=
        Module.finrank_baseChange.symm
      _ = Module.finrank k (splitTorus.exponentWeightSpace I GK iK (P.root α)) :=
        (splitTorus.exponentWeightBaseChangeEquiv (K := k) G I i (P.root α)).finrank_eq
      _ = 1 := hdim
  obtain ⟨eR⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hdimR
  exact ⟨eR.symm⟩

/-- A chosen linear trivialization of each actual root weight module over
the original local ring. -/
def localRootWeightSpaceEquiv
    {R : Type u} [CommRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    (hG : IsReductive G)
    (I : Type u) [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J) :
    splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R]
      CommRingCat.of R :=
  Classical.choice (localRootWeightSpace_nonempty_linearEquiv G hG I i hi P hP α)

end Langlands.GroupScheme
