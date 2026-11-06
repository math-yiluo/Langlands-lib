import Langlands.GroupScheme.Rational.MaximalLeviConeComplementStatement
import Langlands.GroupScheme.Rational.ParabolicNormalizerStatement
import Langlands.GroupScheme.Rational.ParabolicRootConeEvaluation
import Langlands.GroupScheme.Rational.ParabolicRootPresentationTransport
import Langlands.GroupScheme.Absolute.ParabolicNormalizerPointsReduction
import Langlands.Representation.Exponents.MaximalLeviExponentTransport

/-! # Conjugations fixing a missed direction lie in the parabolic

In the proof of Renard VII.1.3 (PDF pp.230–232) the exponent `ω` of `ρ` is matched by at most
one piece of the geometric lemma for a parabolic `Q` with Levi factor `M`. This module proves
the group-theoretic part of that uniqueness, under the published statements
`MaximalLeviConeComplementStatement` and `ParabolicSelfNormalizerStatement`, which are
hypotheses here.

Let `w ∈ G(k)` normalize `M`, through an automorphism `σ` of `M` and an automorphism `e` of
the split component `A`, and let `e` fix a nonzero real character `y` of `A` that vanishes on
the central directions of `G`. Then `w ∈ Q(k)`. Indeed `Q` and `wQw⁻¹` have the Levi factor
`M`, the transported presentation of `wQw⁻¹` has the `e`-transported cone, the cones are
pointed so `y` or `-y` misses both cones, and the cone complement statement gives
`wQw⁻¹ = Q`; then `w` normalizes `Q`, and `Q` is its own normalizer.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

variable {k : Type u} [Field k]

namespace ParabolicRootPresentation

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- The positive cone of a presentation is pointed: it never contains both a nonzero real
character and its negative. -/
theorem notMem_positiveCone_or_neg_notMem (r : ParabolicRootPresentation p l a)
    {x : Vstar A} (hx : x ≠ 0) : x ∉ r.positiveCone ∨ -x ∉ r.positiveCone := by
  by_contra h
  push Not at h
  obtain ⟨h₁, h₂⟩ := h
  rcases r.restrictedRoots.eq_empty_or_nonempty with hempty | hne
  · have hcone := r.positiveCone_of_eq_empty
      (Set.sdiff_eq_empty.mpr (r.restrictedRoots_eq_empty_iff.mp hempty))
    rw [hcone] at h₁
    exact hx h₁
  · have e₁ := r.splitComponentEvaluation_pos_of_mem_positiveCone hne h₁
    have e₂ := r.splitComponentEvaluation_pos_of_mem_positiveCone hne h₂
    rw [map_neg] at e₂
    linarith

end ParabolicRootPresentation

open Langlands.Aubert.General.RepresentedParabolic (pointImage)

section FixedDirection

variable {G P M Q U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q}

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- A point whose inner automorphism preserves the image of the closed subgroup `q` normalizes
it, and so lies in its image when `q` is self-normalizing. -/
theorem mem_pointImage_of_range_comp_innerIso_eq (hq : IsClosedSubgroup q)
    (hself : (SubgroupFunctor.range q).normalizer = SubgroupFunctor.range q)
    (w : rationalPoints G)
    (hw : SubgroupFunctor.range q = SubgroupFunctor.range (q ≫ (G.innerIso w).hom)) :
    w ∈ pointImage q := by
  have : Mono q.hom.hom.left := hq.mono
  have : Mono q.hom.hom := Over.mono_of_mono_left _
  have : IsIso (G.innerIso w).hom.hom.hom :=
    (inferInstance : IsIso ((Grp.forget (Over (Spec (CommRingCat.of k)))).mapIso
      (G.innerIso w)).hom)
  have hi : (SubgroupFunctor.range q).IsRepresentedBy q := ⟨inferInstance, rfl⟩
  have hj : (SubgroupFunctor.range q).IsRepresentedBy (q ≫ (G.innerIso w).hom) :=
    ⟨by rw [Grp.comp_hom_hom]; infer_instance, hw.symm⟩
  have hmem := SubgroupFunctor.mem_normalizer_range_of_innerIso
    (SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hj hi) (n := w)
    (SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hj hi).symm
  rw [hself] at hmem
  exact hmem

/-- The core of the fixed-direction argument, for a direction `y` outside the cone of the
given presentation of `Q`. -/
theorem mem_pointImage_of_fixes_of_notMem_positiveCone
    (hcone : MaximalLeviConeComplementStatement.{u})
    (hnorm : ParabolicSelfNormalizerStatement.{u})
    (hG : IsConnectedReductive G)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (hpG : ¬ IsIso p)
    (hmax : ∀ (Q' : GroupScheme (Spec (CommRingCat.of k))) (q' : Q' ⟶ G) (j : P ⟶ Q'),
      IsParabolicSubgroup q' → j ≫ q' = p → IsIso j ∨ IsIso q')
    (ha : IsSplitComponent a)
    (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hlQ : lQ ≫ q = l ≫ p) (pres : ParabolicRootPresentation q lQ a)
    (w : rationalPoints G) (σ : M ≅ M) (e : A ≅ A)
    (hσ : σ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom)
    (he : CommGroupScheme.groupHom e.hom ≫ a = a ≫ σ.hom)
    (y : Vstar A) (hy : y ≠ 0)
    (hcent : ∀ ν : cocharacterLattice A, IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) →
      pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0)
    (hfix : rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) y = y)
    (hyQ : y ∉ pres.positiveCone) :
    w ∈ pointImage q := by
  let pres₂ := pres.conjugate w σ e ha he
  have hcone₂ : y ∉ pres₂.positiveCone := by
    rw [ParabolicRootPresentation.positiveCone_conjugate]
    rintro ⟨c, hc, hcy⟩
    have hcy' : c = y := by
      have h := congrArg (rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom)) hcy
      rw [hfix, rationalCharacterRestrictReal_comp_apply] at h
      change rationalCharacterRestrictReal (CommGroupScheme.groupHom (e.hom ≫ e.inv)) c = y at h
      rw [Iso.hom_inv_id] at h
      exact (rationalCharacterRestrictReal_id_apply c).symm.trans h
    exact hyQ (hcy' ▸ hc)
  have hlQ₂ : (σ.symm.hom ≫ lQ) ≫ q ≫ (G.innerIso w).hom = l ≫ p := by
    change (σ.inv ≫ lQ) ≫ q ≫ (G.innerIso w).hom = l ≫ p
    rw [Category.assoc, ← Category.assoc lQ, hlQ, Category.assoc, ← hσ, Iso.inv_hom_id_assoc]
  have hrange := (hcone k G hG P M A p l a hp hl hpG hmax ha y hy hcent Q U Q U q lQ rQ
    (q ≫ (G.innerIso w).hom) (σ.symm.hom ≫ lQ) rQ hrQ hrQ hlQ hlQ₂ pres pres₂ hyQ hcone₂).1
  exact mem_pointImage_of_range_comp_innerIso_eq hq.isClosedSubgroup (hnorm k G hG Q q hq) w
    hrange

/-- **Fixed directions force membership in the parabolic.** Let `P = MN` be an actual maximal
proper rational parabolic with split component `a : A ⟶ M`, and let `Q` be a rational
parabolic with Levi factor `lQ : M ⟶ Q` and `lQ ≫ q = l ≫ p`, presented for `a`. Let
`w ∈ G(k)` satisfy `σ ≫ l ≫ p = l ≫ p ≫ Int(w)` for an automorphism `σ` of `M`, and let
`e : A ≅ A` lift `σ` to the split component. If `e` fixes a nonzero real character `y` of `A`
that vanishes on the central cocharacters of `G`, then `w ∈ Q(k)`. -/
theorem mem_pointImage_of_fixes
    (hcone : MaximalLeviConeComplementStatement.{u})
    (hnorm : ParabolicSelfNormalizerStatement.{u})
    (hG : IsConnectedReductive G)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (hpG : ¬ IsIso p)
    (hmax : ∀ (Q' : GroupScheme (Spec (CommRingCat.of k))) (q' : Q' ⟶ G) (j : P ⟶ Q'),
      IsParabolicSubgroup q' → j ≫ q' = p → IsIso j ∨ IsIso q')
    (ha : IsSplitComponent a)
    (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hlQ : lQ ≫ q = l ≫ p) (pres : ParabolicRootPresentation q lQ a)
    (w : rationalPoints G) (σ : M ≅ M) (e : A ≅ A)
    (hσ : σ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom)
    (he : CommGroupScheme.groupHom e.hom ≫ a = a ≫ σ.hom)
    (y : Vstar A) (hy : y ≠ 0)
    (hcent : ∀ ν : cocharacterLattice A, IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) →
      pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0)
    (hfix : rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) y = y) :
    w ∈ pointImage q := by
  rcases pres.notMem_positiveCone_or_neg_notMem hy with hyQ | hyQ
  · exact mem_pointImage_of_fixes_of_notMem_positiveCone hcone hnorm hG hp hl hpG hmax ha hq
      hrQ hlQ pres w σ e hσ he y hy hcent hfix hyQ
  · refine mem_pointImage_of_fixes_of_notMem_positiveCone hcone hnorm hG hp hl hpG hmax ha hq
      hrQ hlQ pres w σ e hσ he (-y) (neg_ne_zero.mpr hy) ?_ ?_ hyQ
    · intro ν hν
      rw [map_neg, LinearMap.neg_apply, hcent ν hν, neg_zero]
    · rw [map_neg, hfix]

end FixedDirection

/-- **Fixed directions force membership in the parabolic**, for all fields: let `P = MN` be an
actual maximal proper rational parabolic of a connected reductive group `G`, with split
component `a : A ⟶ M`, and let `Q` be a rational parabolic with Levi factor `lQ : M ⟶ Q`,
`lQ ≫ q = l ≫ p`, geometric unipotent radical `rQ` and a root presentation for `a`. Let
`w ∈ G(k)`, `σ : M ≅ M` and `e : A ≅ A` satisfy `σ ≫ l ≫ p = l ≫ p ≫ Int(w)` and
`e ≫ a = a ≫ σ`. If `e` fixes a nonzero real character `y` of `A` whose pairing with every
cocharacter of `A` central in `G` vanishes, then `w ∈ Q(k)`. -/
def MaximalLeviFixedDirectionNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    ∀ (P M Q U : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l → ¬ IsIso p →
      (∀ (Q' : GroupScheme (Spec (CommRingCat.of k))) (q' : Q' ⟶ G) (j : P ⟶ Q'),
        IsParabolicSubgroup q' → j ≫ q' = p → IsIso j ∨ IsIso q') →
      IsSplitComponent a →
      IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical rQ →
      lQ ≫ q = l ≫ p →
      ∀ (_ : ParabolicRootPresentation q lQ a) (w : rationalPoints G) (σ : M ≅ M) (e : A ≅ A),
        σ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom →
        CommGroupScheme.groupHom e.hom ≫ a = a ≫ σ.hom →
        ∀ y : Vstar A, y ≠ 0 →
          (∀ ν : cocharacterLattice A, IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) →
            pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) →
          rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) y = y →
            w ∈ pointImage q

/-- The fixed-direction statement as a consequence of the cone complement statement and
the self-normalizing property of parabolics. -/
def MaximalLeviFixedDirectionNormalizerReductionStatement : Prop :=
  MaximalLeviConeComplementStatement.{u} →
    ParabolicSelfNormalizerStatement.{u} →
      MaximalLeviFixedDirectionNormalizerStatement.{u}

/-- The cone complement statement and the self-normalizing property of parabolics give the
fixed-direction statement. -/
theorem maximalLeviFixedDirectionNormalizer_of_coneComplement :
    MaximalLeviFixedDirectionNormalizerReductionStatement.{u} := by
  intro hcone hnorm k _ G hG P M Q U A p l a q lQ rQ hp hl hpG hmax ha hq hrQ hlQ pres w σ e
    hσ he y hy hcent hfix
  have := hG.isAffineHom
  have := hG.smooth
  exact mem_pointImage_of_fixes hcone hnorm hG hp hl hpG hmax ha hq hrQ hlQ pres w σ e hσ he y
    hy hcent hfix

end Langlands.GroupScheme
