import Langlands.GroupScheme.Reductive.LocalSplitRootDatumExistence
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.RelativeAdjointWeightRanks
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Actual root lines and full split data over a local ring -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
  (hG : IsReductive G) (I : Type u) [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

include hG

/-- Each actual root exponent space of a fibrewise maximal coordinate split
 torus over a local ring is free of rank one over that ring. -/
theorem localSplitRootSpace
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J) :
    Nonempty (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[R] R) := by
  classical
  let : Smooth G.X.hom := hG.smooth
  let W := splitTorus.exponentWeightSpace I G i (P.root α)
  let : Module.Free R W := Module.free_of_flat_of_isLocalRing
  let k := IsLocalRing.ResidueField R
  let Gk := (baseChange (Spec.algebraMap R k)).obj G
  let : IsAffineHom Gk.X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (Spec.algebraMap R k)))
  have hGk : IsConnectedReductive Gk := hG.isConnectedReductive_algebraMap k
  have hik := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hi k
  have hroot := (hP.mem_roots_iff k (P.root α)).mpr ⟨α, rfl⟩
  obtain ⟨e⟩ := splitRootLieLine k Gk hGk
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    (isSplitTorus_splitTorus I) (splitTorus.baseChangeHom (K := k) G I i) hik
    (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root α)) hroot
  have hexp := splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter I Gk
    (splitTorus.baseChangeHom (K := k) G I i) (P.root α)
  have hek : Nonempty (k ≃ₗ[k] splitTorus.exponentWeightSpace I Gk
      (splitTorus.baseChangeHom (K := k) G I i) (P.root α)) := by
    rw [hexp]
    exact ⟨e⟩
  let eb := splitTorus.exponentWeightBaseChangeEquiv (K := k) G I i (P.root α)
  have hline : Nonempty (k ≃ₗ[k] (k ⊗[R] W)) := ⟨hek.some.trans eb.symm⟩
  have hfin : Module.finrank R W = 1 := by
    rw [← Module.finrank_baseChange (R := k)]
    exact Module.nonempty_linearEquiv_iff_finrank_eq_one.mp hline
  exact ⟨(Module.nonempty_linearEquiv_of_finrank_eq_one hfin).some.symm⟩

/-- A chosen trivialization of an actual root exponent space over a local ring. -/
def localSplitRootSpaceEquiv
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J) :
    splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[R] R :=
  (localSplitRootSpace R G hG I i hi P hP α).some

/-- A closed coordinate split torus maximal on residue fibres in a reductive
 group over a local ring supplies a common full root datum and actual root lines. -/
theorem localSplitDataOfFibrewiseMaximalTorus
    (hic : IsClosedSubgroup i)
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsFibrewiseRootDatumOf I G i P ∧
      ∀ α : J, Nonempty (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[R] R) := by
  obtain ⟨J, P, hP⟩ := localSplitFibrewiseRootDatumExistence R G hG I i hic hi
  exact ⟨J, P, hP, localSplitRootSpace R G hG I i hi P hP⟩

end Langlands.GroupScheme
