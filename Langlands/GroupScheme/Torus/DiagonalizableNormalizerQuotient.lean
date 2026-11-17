import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableNormalizerOrbit
import Langlands.GroupScheme.Torus.FiniteTorsionNormalizerScheme
import Langlands.GroupScheme.QuasiAffineHomogeneousOrbit

/-! # Smooth quasi-affine quotients by diagonalizable normalizers over rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- Every supplied normalizer of a closed diagonalizable subgroup of a smooth
affine group over an arbitrary ring has an actual smooth quasi-affine quotient. -/
theorem diagonalizableNormalizer_exists_smooth_quasiAffine_quotient_overRing
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {G N : GroupScheme (Spec R)} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G) (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hnrep : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    ∃ Q : HomogeneousQuotient n, Smooth Q.scheme.hom ∧ Q.scheme.left.IsQuasiAffine := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hN : Smooth N.X.hom := diagonalizableNormalizer_smooth_overRing i hi n hnrep
  obtain ⟨N', n', hn'closed, hn'rep⟩ :=
    diagonalizableNormalizer_hasClosedRepresentative_overRing i hi
  have hnclosed : IsClosedSubgroup n := by
    rw [← hnrep.isoOfIsRepresentedBy_hom_comp hn'rep]
    exact (IsClosedSubgroup.of_iso (hnrep.isoOfIsRepresentedBy hn'rep)).comp hn'closed
  let E := finiteTorsionNormalizerOverRing i hi
  let P := M ⧸ FiniteCharacterSeparation.multiples E.1
  let : Finite P := FiniteCharacterSeparation.finite_quotient E.2.val.ne'
  let : Fintype P := Fintype.ofFinite P
  let j : (Diagonalizable.groupScheme R P).toGrp ⟶ G :=
    Diagonalizable.restrictMap R
      (QuotientAddGroup.mk' (FiniteCharacterSeparation.multiples (M := M) E.1)) ≫ i
  have hj : IsClosedSubgroup j := E.2.property.1
  have hnormal : (SubgroupFunctor.range j).normalizer =
      (SubgroupFunctor.range i).normalizer := E.2.property.2.2
  let O := HomScheme.FiniteDiagonalizableEmbeddings.normalizerOrbitModel R P G j hj
  let : O.1.left.IsQuasiAffine := O.2.property.1
  apply RelativeHomogeneousQuotient.exists_quasiAffine_quotient_of_quasiAffine_map_kernel
    n hnclosed hN O.1 O.2.val
  intro T g h
  have hf := O.2.property.2 T g h
  change g ≫ O.2.val = h ≫ O.2.val ↔
    g⁻¹ * h ∈ (SubgroupFunctor.range j).normalizer.carrier T at hf
  have hF : (SubgroupFunctor.range j).normalizer = SubgroupFunctor.range n :=
    hnormal.trans hnrep.2.symm
  exact hf.trans (Iff.of_eq (congrArg
    (fun F : SubgroupFunctor G => g⁻¹ * h ∈ F.carrier T) hF))

/-- The ring-local normalizer quotient input used in general-base descent. -/
theorem diagonalizableNormalizer_exists_quasiAffine_quotient_overRing
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {G N : GroupScheme (Spec R)} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G) (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hnrep : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    ∃ Q : HomogeneousQuotient n, Q.scheme.left.IsQuasiAffine := by
  obtain ⟨Q, _, hQ⟩ :=
    diagonalizableNormalizer_exists_smooth_quasiAffine_quotient_overRing i hi n hnrep
  exact ⟨Q, hQ⟩

/-- Choose the actual smooth quasi-affine normalizer quotient over a ring. -/
def diagonalizableNormalizerQuotientOverRing
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {G N : GroupScheme (Spec R)} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G) (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hnrep : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    {Q : HomogeneousQuotient n // Smooth Q.scheme.hom ∧ Q.scheme.left.IsQuasiAffine} :=
  ⟨_, (diagonalizableNormalizer_exists_smooth_quasiAffine_quotient_overRing i hi n hnrep).choose_spec⟩

end Langlands.GroupScheme
