import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionStatement
import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusReduction
import Langlands.GroupScheme.Rational.NormalRadicalConjugacy
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.Torus.HeightExistence
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.UnipotentClosedSubgroupStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Radical torus intersections from a unipotent-by-torus decomposition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Conjugation

variable {S : Scheme.{u}} {H R P : GroupScheme S} {F : SubgroupFunctor P} {r : R ⟶ P}

namespace SubgroupFunctor.IsRepresentedBy

/-- Conjugation by a base point restricted to a represented normal subgroup, as an
automorphism of the specified representative. -/
def conjugateIso (hr : F.IsRepresentedBy r) (hn : F.IsNormal)
    (g : Over.mk (𝟙 S) ⟶ P.X) : R ≅ R where
  hom := hr.conjugateFactor hn (𝟙 R) g
  inv := hr.conjugateFactor hn (𝟙 R) g⁻¹
  hom_inv_id := hr.hom_ext (by
    rw [Category.assoc, conjugateFactor_comp, Category.id_comp, ← Category.assoc,
      conjugateFactor_comp, Category.id_comp, Category.assoc, innerIso_inv_hom,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp])
  inv_hom_id := hr.hom_ext (by
    rw [Category.assoc, conjugateFactor_comp, Category.id_comp, ← Category.assoc,
      conjugateFactor_comp, Category.id_comp, Category.assoc, innerIso_inv_hom,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp])

/-- The automorphism acts as conjugation after the inclusion. -/
@[simp] theorem conjugateIso_hom_comp (hr : F.IsRepresentedBy r) (hn : F.IsNormal)
    (g : Over.mk (𝟙 S) ⟶ P.X) :
    (hr.conjugateIso hn g).hom ≫ r = r ≫ (P.innerIso g).hom := by
  change hr.conjugateFactor hn (𝟙 R) g ≫ r = _
  rw [conjugateFactor_comp, Category.id_comp]

/-- Every conjugated factor is the original factor followed by the conjugation
automorphism of the representative. -/
theorem conjugateFactor_eq_comp_conjugateIso (hr : F.IsRepresentedBy r) (hn : F.IsNormal)
    (b : H ⟶ R) (g : Over.mk (𝟙 S) ⟶ P.X) :
    hr.conjugateFactor hn b g = b ≫ (hr.conjugateIso hn g).hom :=
  (hr.conjugateFactor_unique hn b g (by
    rw [Category.assoc, conjugateIso_hom_comp])).symm

end SubgroupFunctor.IsRepresentedBy

end Conjugation

section Field

variable {k : Type u} [Field k]

/-- A closed subgroup represents its own range. -/
theorem IsClosedSubgroup.isRepresentedBy_range {H G : GroupScheme (Spec (CommRingCat.of k))}
    {i : H ⟶ G} (hi : IsClosedSubgroup i) :
    (SubgroupFunctor.range i).IsRepresentedBy i := by
  have : Mono i.hom.hom.left := hi.mono
  exact ⟨Over.mono_of_mono_left _, rfl⟩

/-- Inside an affine group locally of finite type with conjugate maximal tori, let
`f : T → H` be a maximal torus with `T` split, and let `r : R → H` be a closed normal
subgroup each of whose maximal tori `s` has a closed unipotent `u : U → R` with
`U × S → R`, `(n, x) ↦ n * x`, an isomorphism. Then some maximal torus of `R` factors
through `f` by a closed map, and its image in `H` is the whole intersection of the ranges
of `f` and `r` on every test scheme. -/
theorem exists_radicalTorusIntersection_of_complement
    (hunip : UnipotentClosedSubgroupStatement.{u})
    {H R : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (hconj : MaximalToriAreConjugate H)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (f : T.toGrp ⟶ H)
    (hf : IsMaximalTorus f) (hT : IsSplitTorus T.toGrp)
    (r : R ⟶ H) (hr : IsClosedSubgroup r) (hn : (SubgroupFunctor.range r).IsNormal)
    (hcomp : ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ R),
      IsMaximalTorus s →
        ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ R),
          IsClosedSubgroup u ∧ IsUnipotent U ∧ IsIso (subgroupMultiplication u s)) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k)))
      (sT : S.toGrp ⟶ T.toGrp) (sR : S.toGrp ⟶ R),
      IsClosedSubgroup sT ∧ IsMaximalTorus sR ∧
      sT ≫ f = sR ≫ r ∧
      SubgroupFunctor.range (sT ≫ f) =
        SubgroupFunctor.range f ⊓ SubgroupFunctor.range r := by
  have : IsAffineHom R.X.hom := hr.isAffineHom
  have : LocallyOfFiniteType R.X.hom := hr.locallyOfFiniteType
  -- A maximal torus of `R`, enlarged to a maximal torus of `H`, conjugated onto `f`.
  obtain ⟨S₀, s₀, hs₀⟩ := exists_isMaximalTorus R
  obtain ⟨T₁, t₁, ht₁, a, ha⟩ :=
    exists_maximalTorus_extension_of_finiteType H (s₀ ≫ r) hs₀.1 (hs₀.2.1.comp hr)
  obtain ⟨g, e, hg⟩ := hconj T₁ T t₁ f ht₁ hf
  have hrep := hr.isRepresentedBy_range
  let c := hrep.conjugateIso hn g
  let sR : S₀.toGrp ⟶ R := s₀ ≫ c.hom
  let sT : S₀.toGrp ⟶ T.toGrp := a ≫ e.hom
  have hsR : IsMaximalTorus sR := hs₀.comp_iso c
  have hsq : sT ≫ f = sR ≫ r := by
    simp only [sT, sR, c, Category.assoc,
      SubgroupFunctor.IsRepresentedBy.conjugateIso_hom_comp]
    rw [← hg, ← Category.assoc a t₁, ha, Category.assoc]
  have hsT : IsClosedSubgroup sT :=
    IsClosedSubgroup.of_comp hf.2.1 (hsq ▸ hsR.2.1.comp hr)
  refine ⟨S₀, sT, sR, hsT, hsR, hsq, ?_⟩
  obtain ⟨U, u, hu, hU, hmul⟩ := hcomp S₀ sR hsR
  have : IsAffineHom U.X.hom := hu.isAffineHom
  have : LocallyOfFiniteType U.X.hom := hu.locallyOfFiniteType
  -- The torus `T` meets the unipotent part `U` trivially.
  have hbot : ∀ (V : Over (Spec (CommRingCat.of k))) (p : V ⟶ H.X),
      p ∈ (SubgroupFunctor.range f).carrier V →
        p ∈ (SubgroupFunctor.range (u ≫ r)).carrier V → p = 1 := by
    intro V p hpf hpu
    have hsnd : IsClosedSubgroup (subgroupIntersectionSnd f (u ≫ r)) := by
      have : IsClosedImmersion f.hom.hom.left := hf.2.1
      have : IsClosedImmersion (subgroupIntersectionSnd f (u ≫ r)).hom.hom.left :=
        MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme f (u ≫ r)) this
      exact this
    have hW : IsUnipotent (subgroupIntersection f (u ≫ r)) :=
      hunip k U (subgroupIntersection f (u ≫ r)) _ hsnd hU
    have hp : p ∈ (SubgroupFunctor.range (subgroupIntersectionHom f (u ≫ r))).carrier V := by
      rw [range_subgroupIntersectionHom]
      exact ⟨hpf, hpu⟩
    obtain ⟨q, rfl⟩ := SubgroupFunctor.mem_range.1 hp
    change q ≫ (subgroupIntersectionFst f (u ≫ r)).hom.hom ≫ f.hom.hom = 1
    rw [← Category.assoc,
      hW.comp_eq_one_of_isSplitTorus hT (subgroupIntersectionFst f (u ≫ r)) V q,
      MonObj.one_comp]
  apply le_antisymm
  · intro V x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    refine ⟨⟨y ≫ sT.hom.hom, ?_⟩, ⟨y ≫ sR.hom.hom, ?_⟩⟩
    · change (y ≫ sT.hom.hom) ≫ f.hom.hom = y ≫ (sT ≫ f).hom.hom
      simp only [Grp.comp_hom_hom, Category.assoc]
    · change (y ≫ sR.hom.hom) ≫ r.hom.hom = y ≫ (sT ≫ f).hom.hom
      rw [hsq]
      simp only [Grp.comp_hom_hom, Category.assoc]
  · rintro V x ⟨hxf, hxr⟩
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hxf
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hxr
    let m := subgroupMultiplication u sR
    let w : V ⟶ U.X ⊗ S₀.toGrp.X := z ≫ inv m
    have hzw : z = (w ≫ fst _ _ ≫ u.hom.hom) * (w ≫ snd _ _ ≫ sR.hom.hom) := by
      rw [← Category.assoc, ← Category.assoc, ← comp_subgroupMultiplication,
        lift_comp_fst_snd]
      simp only [w, m, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hx : x = ((w ≫ fst _ _) ≫ (u ≫ r).hom.hom) *
        ((w ≫ snd _ _) ≫ (sT ≫ f).hom.hom) := by
      rw [← hz, hzw, MonObj.mul_comp, hsq]
      simp only [Grp.comp_hom_hom, Category.assoc]
    have hft : (w ≫ snd _ _) ≫ (sT ≫ f).hom.hom ∈ (SubgroupFunctor.range f).carrier V :=
      SubgroupFunctor.mem_range.2
        ⟨(w ≫ snd _ _) ≫ sT.hom.hom, by simp only [Grp.comp_hom_hom, Category.assoc]⟩
    have hn1 : (w ≫ fst _ _) ≫ (u ≫ r).hom.hom = 1 := by
      apply hbot V
      · have hq : (w ≫ fst _ _) ≫ (u ≫ r).hom.hom =
            x * ((w ≫ snd _ _) ≫ (sT ≫ f).hom.hom)⁻¹ := by
          rw [hx, mul_inv_cancel_right]
        rw [hq]
        exact Subgroup.mul_mem _ hxf (Subgroup.inv_mem _ hft)
      · exact SubgroupFunctor.mem_range.2 ⟨w ≫ fst _ _, rfl⟩
    rw [hx, hn1, one_mul]
    exact SubgroupFunctor.mem_range.2 ⟨w ≫ snd _ _, rfl⟩

/-- Conjugacy of maximal tori, closed subgroups of unipotent groups being unipotent,
splitting of tori, and a unipotent-by-maximal-torus multiplication decomposition of
smooth connected solvable groups together give the maximal-rank radical intersection
statement. -/
theorem maximalRankRadicalTorusIntersectionStatement_of_complement
    (hconj : MaximalTorusConjugacyStatement.{u})
    (hunip : UnipotentClosedSubgroupStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    (hcomp : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (R : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth R.X.hom] [IsAffineHom R.X.hom] [ConnectedSpace R.X.left],
      IsSolvableGroupScheme R →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ R),
        IsMaximalTorus s →
          ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ R),
            IsClosedSubgroup u ∧ IsUnipotent U ∧ IsIso (subgroupMultiplication u s)) :
    MaximalRankRadicalTorusIntersectionStatement.{u} := by
  intro k _ _ G hG H j hj hHs hHc T t ht f hft R r hR
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffineHom H.X.hom := hj.isAffineHom
  have : Smooth H.X.hom := hHs
  have : ConnectedSpace H.X.left := hHc
  have : Smooth R.X.hom := hR.smooth
  have : ConnectedSpace R.X.left := hR.connectedSpace
  have : IsAffineHom R.X.hom := hR.isClosedSubgroup.isAffineHom
  have hf : IsMaximalTorus f := IsMaximalTorus.of_comp hj (hft ▸ ht)
  exact exists_radicalTorusIntersection_of_complement hunip
    (hconj.maximalToriAreConjugate k H) f hf
    (IsTorus.isSplitTorus_of_finiteGaloisSplitting hsplit hf.1) r hR.isClosedSubgroup
    hR.isNormal (hcomp k R hR.isSolvableGroupScheme)

end Field

end Langlands.GroupScheme
