import Langlands.GroupScheme.Reductive.LocalSplitCorootTransport
import Langlands.GroupScheme.Torus.PointedEtaleNormalizer

/-! # Etale-local normalizers of coordinate coroots -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- Every coordinate reflection of a fibrewise datum is represented by an
actual normalizing section on a pointed affine etale neighbourhood. -/
theorem exists_etale_coordinateReflection (hG : IsReductive G)
    (hP : IsFibrewiseRootDatumOf I G i P) (s : Spec (CommRingCat.of R)) (a : J) :
    ∃ (U : Scheme.{u}) (f : U ⟶ Spec (CommRingCat.of R)),
      IsAffine U ∧ Etale f ∧ s ∈ Set.range f ∧
      ∃ n : Over.mk (𝟙 U) ⟶ ((GroupScheme.baseChange f).obj G).X,
        IsNormalizingPoint ((GroupScheme.baseChange f).map i) n
          ((CommGroupScheme.baseChange f).mapIso
            (splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I (P.reflection a)).symm) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let k := (Spec (CommRingCat.of R)).residueField s
  let : Algebra R k :=
    (Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)).hom.toAlgebra
  have hb : algebraBaseMap R k = (Spec (CommRingCat.of R)).fromSpecResidueField s :=
    Spec.map_preimage _
  have h := LocalSplitCorootTransport.isRealizedAt_reflection I G i k P (hP.field k) a
  unfold LocalSplitCorootTransport.IsRealizedAt at h
  rw [hb] at h
  obtain ⟨n, hn⟩ := h
  let σ := (splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I (P.reflection a)).symm
  let d := pointedEtaleNormalizerOfTransporter
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I)
    i σ (isSplitTorus_splitTorus I) hG.smooth s n hn
  refine ⟨d.neighbourhood, d.projection, d.affine, d.etale, ?_, d.sectionPoint, d.isNormalizing⟩
  refine ⟨d.residuePoint default, ?_⟩
  have he := congrArg (fun f => f default) d.residue_over
  simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using he

end Langlands.GroupScheme

namespace Langlands.GroupScheme.splitTorus

variable {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
    (S : Scheme.{u}) (P : RootDatum J (I → ℤ) (I → ℤ))

/-- A coordinate root reflection inverts its actual coroot over every base
when the given integral pairing is the standard coordinate pairing. -/
theorem exponentCocharacter_comp_reflection
    (hpair : ∀ m n : I → ℤ, P.toLinearMap m n = ∑ j, m j * n j) (a : J) :
    exponentCocharacter S I (P.coroot a) ≫
        (exponentCommIso S I (P.reflection a)).symm.hom =
      -exponentCocharacter S I (P.coroot a) := by
  apply hom_ext_projections S I
  intro j
  change exponentCocharacter S I (P.coroot a) ≫
      (exponentHom S I I (P.reflection a).toLinearMap ≫ proj S I j) = _
  rw [exponentHom_comp_proj, exponentCocharacter_comp_exponentCharacter,
    ← hpair, Preadditive.neg_comp, exponentCocharacter_comp_proj]
  have he : P.toLinearMap (P.reflection a (Pi.single j 1)) (P.coroot a) =
      -(P.coroot a j) := by
    change P.toLinearMap
      (Pi.single j 1 - P.toLinearMap (Pi.single j 1) (P.coroot a) • P.root a)
      (P.coroot a) = _
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      P.root_coroot_two, hpair]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, smul_eq_mul]
    ring
  change Gm.powerHom S (P.toLinearMap (P.reflection a (Pi.single j 1)) (P.coroot a)) =
    -Gm.powerHom S (P.coroot a j)
  rw [he, Gm.powerHom_apply, Gm.powerHom_apply, neg_smul]

end Langlands.GroupScheme.splitTorus

namespace Langlands.GroupScheme

/-- An etale cover carrying actual normalizing sections for one fixed
coordinate reflection. -/
structure EtaleCoordinateReflectionData
    {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    {J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ)) (a : J) where
  cover : Scheme.Cover.{u} (Scheme.precoverage @Etale) (Spec (CommRingCat.of R))
  affine : ∀ j, IsAffine (cover.X j)
  sectionPoint : ∀ j, Over.mk (𝟙 (cover.X j)) ⟶
    ((GroupScheme.baseChange (cover.f j)).obj G).X
  isNormalizing : ∀ j,
    IsNormalizingPoint ((GroupScheme.baseChange (cover.f j)).map i) (sectionPoint j)
      ((CommGroupScheme.baseChange (cover.f j)).mapIso
        (splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I (P.reflection a)).symm)

/-- The reflection witnesses already supplied on field fibres lift to an
actual etale covering family of normalizing sections. -/
def etaleCoordinateReflectionData
    {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hG : IsReductive G) (hP : IsFibrewiseRootDatumOf I G i P) (a : J) :
    EtaleCoordinateReflectionData i P a := Classical.choice <| by
  classical
  choose U f hU hf hs n hn using fun s => exists_etale_coordinateReflection hG hP s a
  exact ⟨{
    cover := Scheme.Cover.mkOfCovers (Spec (CommRingCat.of R)) U f
      (fun s => by obtain ⟨v, hv⟩ := hs s; exact ⟨s, v, hv⟩) hf
    affine := hU
    sectionPoint := n
    isNormalizing := hn }⟩

end Langlands.GroupScheme
