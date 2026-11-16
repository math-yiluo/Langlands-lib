import Langlands.GroupScheme.Reductive.RankOneRingCalculus
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Torus.ExponentHomomorphisms
import Langlands.GroupScheme.Torus.MaximalSelfCentralizingDescent

/-! # Actual local rank-one Weyl data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

/-- An involutive normalizer of a fibrewise maximal split torus in a
reductive group has its square in that torus, over an arbitrary base. -/
theorem IsNormalizingPoint.exists_sq_eq_of_fibrewiseMaximal
    {S : Scheme.{u}} {G : GroupScheme S} {T : CommGroupScheme S}
    {i : T.toGrp ⟶ G} {n : Over.mk (𝟙 S) ⟶ G.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint i n σ) (hσ : σ ≪≫ σ = Iso.refl T)
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i) :
    ∃ z : Over.mk (𝟙 S) ⟶ T.X, n * n = z ≫ i.hom.hom := by
  have hc : n * n ∈ centralizerPoints i := by
    change IsNormalizingPoint i (n * n) (Iso.refl T)
    simpa only [hσ] using hn.mul hn
  have hr := centralizerPoints_le_torusCentralizer i hc
  rw [splitTorusCentralizer_eq_range_of_fibrewiseMaximal hG hT i hi hmax] at hr
  obtain ⟨z, hz⟩ := hr
  exact ⟨z, hz.symm⟩

namespace RingRootCell

/-- The reflection used by the ring calculus is involutive over every
commutative base ring. -/
theorem reflectionIso_trans_self {R : Type u} [CommRing R]
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    (α : characterLattice T) (h : cocharacterLattice T)
    (hh : h ≫ α = (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of R)))) :
    reflectionIso α h hh ≪≫ reflectionIso α h hh = Iso.refl T := by
  apply Iso.ext
  exact (reflectionIso α h hh).hom_inv_id

end RingRootCell

namespace LocalRankOneWeylData

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

omit [DecidableEq I] in
/-- The fixed-exponent coroot and root have the required actual composite
over a local ring, including its nilpotent structure. -/
theorem coroot_comp_root (hP : IsFibrewiseRootDatumOf I G i P) (a : J) :
    splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (P.coroot a) ≫
        splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (P.root a) =
      (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of R))) := by
  rw [splitTorus.exponentCocharacter_comp_exponentCharacter,
    ← hP.pairing (IsLocalRing.ResidueField R), P.root_coroot_two]
  rfl

/-- The ring-calculus reflection is the actual exponent reflection of the
given coordinate root datum. -/
theorem reflectionIso_eq_exponentCommIso (hP : IsFibrewiseRootDatumOf I G i P)
    (a : J) :
    RingRootCell.reflectionIso
        (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (P.root a))
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (P.coroot a))
        (coroot_comp_root hP a) =
      splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I (P.reflection a) := by
  have hc (m : I → ℤ) :
      (𝟙 (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) -
        splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (P.root a) ≫
          splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (P.coroot a)) ≫
        splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m =
      splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (P.reflection a m) := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      splitTorus.exponentCocharacter_comp_exponentCharacter, Gm.powerHom_apply,
      Preadditive.comp_zsmul, Category.comp_id, RootPairing.reflection_apply]
    change _ = splitTorus.exponentCharacterLinear _ I
      (m - P.toLinearMap m (P.coroot a) • P.root a)
    rw [map_sub, map_smul, hP.pairing (IsLocalRing.ResidueField R)]
    rfl
  apply Iso.ext
  apply splitTorus.hom_ext_projections _ I
  intro j
  change (𝟙 _ - _ ≫ _) ≫ splitTorus.proj _ I j =
    splitTorus.exponentHom _ I I (P.reflection a).toLinearMap ≫ splitTorus.proj _ I j
  have hs : splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (Pi.single j 1) =
      splitTorus.proj (Spec (CommRingCat.of R)) I j := by
    simp [splitTorus.exponentCharacter, Pi.single_apply]
  rw [splitTorus.exponentHom_comp_proj, ← hs]
  exact hc (Pi.single j 1)

/-- The actual reflection defined by the supplied root and coroot over
the entire local base. -/
def corootReflectionIso (hP : IsFibrewiseRootDatumOf I G i P) (a : J) :
    splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ≅
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I :=
  RingRootCell.reflectionIso
    (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (P.root a))
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (P.coroot a))
    (coroot_comp_root hP a)

end LocalRankOneWeylData

end Langlands.GroupScheme
