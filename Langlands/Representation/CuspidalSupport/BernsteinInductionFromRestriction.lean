import Langlands.Representation.CuspidalSupport.BernsteinSupportComparison
import Langlands.Representation.CuspidalSupport.BernsteinDecompositionStatements
import Langlands.Representation.Aubert.General.FirstAdjointness
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.Representation.Category.IrreducibleSubquotientExistence
import Langlands.Representation.Category.FiniteGenerationExhaustion
import Langlands.Representation.Category.CoproductSize
import Langlands.CategoryTheory.Renard.CategoryDecompositionSimpleClassesProof

/-! # Bernstein induction of arbitrary fibred inputs, from restriction

The induction half of Renard VI.7.3, Proposition, for arbitrary smooth inputs of a standard
Levi, reduced to the decomposition of the category (VI.7.2), uniqueness of the inertial
support, the restriction half, and the induction half for irreducible inputs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

/-- If every summand of a coproduct cofan other than `Y j` is zero, then the leg at `j` is an
isomorphism onto the cone point. Its inverse is the map out of the coproduct that is the identity
on `Y j` and zero on the other summands. -/
def cofanInjIsoOfIsZero {C : Type*} [Category C] [HasZeroMorphisms C] {I : Type*}
    [DecidableEq I] {Y : I → C} {X : C} {ιs : ∀ k, Y k ⟶ X} (hc : IsColimit (Cofan.mk X ιs))
    (j : I) (hzero : ∀ k, k ≠ j → IsZero (Y k)) : Y j ≅ X where
  hom := ιs j
  inv := Cofan.IsColimit.desc hc (fun k => if h : k = j then eqToHom (congrArg Y h) else 0)
  hom_inv_id := by
    change (Cofan.mk X ιs).inj j ≫ Cofan.IsColimit.desc hc _ = _
    rw [Cofan.IsColimit.fac]
    simp
  inv_hom_id := by
    apply Cofan.IsColimit.hom_ext hc
    intro k
    by_cases hk : k = j
    · subst hk
      change (Cofan.mk X ιs).inj k ≫ Cofan.IsColimit.desc hc _ ≫ ιs k = ιs k ≫ 𝟙 X
      rw [← Category.assoc, Cofan.IsColimit.fac]
      simp
    · exact (hzero k hk).eq_of_src _ _

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinInductionFromRestrictionAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinInductionFromRestrictionTopology :
    TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- An irreducible representation of a standard Levi whose normalized induction lies in the
saturated blocks of two cuspidal data forces the two inertial classes to agree, given
uniqueness of inertial support: the induction is nonzero, so it has an irreducible
subquotient, which has inertial support in both classes. -/
theorem bernsteinInertialClass_eq_of_induction_mem_blocks
    (huniq : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (J : Finset (SimpleRoot i ν))
    (a c : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)) (hτ : τ.IsIrreducible)
    (ha : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj τ))
    (hc : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family c)
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj τ)) :
    bernsteinInertialClass i ν family a = bernsteinInertialClass i ν family c := by
  have : Nontrivial τ := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hτ.bot_ne_top
    apply SetLike.ext
    intro v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => Submodule.mem_top,
      fun _ => (⊥ : Subrepresentation τ.representation).toSubmodule.zero_mem⟩
  have : Nontrivial
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj τ) :=
    nontrivial_normalizedInduction (family.decomposition J) (family.closedUnipotent J)
      (continuous_standard_projection i ν standardCocharacter family.connectedReductive
        family.maximalSplitTorus family.genericCocharacter J) τ
  obtain ⟨π, hπ, hπτ⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial
    ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj τ)
  exact huniq π _ _ (ha π hπ hπτ) (hc π hπ hπτ)

/-- Renard VI.7.3, Proposition, induction half, for arbitrary smooth inputs, as a reduction.
Fix a standard Levi `M_J`, and a predicate `Q c τ` on cuspidal data `c` and representations `τ`
of `M_J(F)`. Assume the decomposition of the smooth category along the inertial classes, the
uniqueness of inertial support, that `i_{P_J}^G τ` lies in the block of `[c]` for every
irreducible `τ` with `Q c τ`, and that every irreducible subquotient `τ` of `r_{P_J}^G V`
satisfies `Q c τ` for every `V` in the block of `[c]`. Then for every `ρ` all of whose
irreducible subquotients `τ` satisfy `Q a τ`, `i_{P_J}^G ρ` lies in the block of `[a]`. -/
theorem bernsteinInduction_mem_block_of_restriction
    (hdec : Renard.IsCategoryDecomposition
      (fun s : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, max uF uV} i ν family s))
    (huniq : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (J : Finset (SimpleRoot i ν))
    (Q : BernsteinCuspidalDatum.{uF, max uF uV} i ν family →
      SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) → Prop)
    (hirr : ∀ (c : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
      (τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)), τ.IsIrreducible → Q c τ →
        bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family c)
          ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj
            τ))
    (hres : ∀ (c : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
      (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
      bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family c) V →
        ∀ τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J), τ.IsIrreducible →
          SmoothRep.IsSubquotient τ
            ((normalizedJacquetFunctor (unipotent i ν J) (levi i ν J) (family.closedUnipotent J)
              (family.decomposition J).levi_le_normalizer).obj V) → Q c τ)
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J))
    (hρ : ∀ τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J), τ.IsIrreducible →
      SmoothRep.IsSubquotient τ ρ → Q a τ) :
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj ρ) := by
  classical
  obtain ⟨Y, ιs, hY, ⟨hc⟩⟩ := hdec.1
    ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj ρ)
  let s₀ := bernsteinInertialClass i ν family a
  have hδ := standardUnipotent_isUnimodular_of_standardCocharacterStatement i ν
    standardCocharacter family.connectedReductive family.maximalSplitTorus
    family.genericCocharacter J (family.closedUnipotent J)
  -- every component away from the class of `a` is zero
  have hzero : ∀ s, s ≠ s₀ → IsZero (Y s) := by
    intro s hs
    rw [SmoothRep.isZero_iff_subsingleton]
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    obtain ⟨c, hcs⟩ := Quotient.exists_rep s
    change bernsteinInertialClass i ν family c = s at hcs
    subst hcs
    have hYc := (bernsteinBlockProperty_iff_saturated _ _).mp (hY (bernsteinInertialClass i ν family c))
    have hinj : Function.Injective (SmoothRep.hom (ιs (bernsteinInertialClass i ν family c))) :=
      (SmoothRep.mono_iff_injective _).mp
        (Renard.CategoryDecompositionSimpleClassesProof.cofan_leg_mono hc _)
    obtain ⟨y, hy⟩ := exists_ne (0 : Y (bernsteinInertialClass i ν family c))
    let e := FirstAdjointness.equiv (family.decomposition J) (family.closedUnipotent J) hδ
      (Y (bernsteinInertialClass i ν family c)) ρ
    let φ := e (SmoothRep.hom (ιs (bernsteinInertialClass i ν family c)))
    have hφ : φ ≠ 0 := by
      intro h0
      have h1 : SmoothRep.hom (ιs (bernsteinInertialClass i ν family c)) = 0 :=
        (LinearEquiv.map_eq_zero_iff e).mp h0
      apply hy
      apply hinj
      rw [h1, map_zero]
      rfl
    obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hφ (Representation.IntertwiningMap.ext (LinearMap.ext hall))
    let f : (jacquetFunctor (family.decomposition J) (family.closedUnipotent J)).obj
        (Y (bernsteinInertialClass i ν family c)) ⟶ ρ := SmoothRep.ofHom φ
    have : Nontrivial (SmoothRep.image f) :=
      ⟨⟨⟨SmoothRep.hom f w, w, rfl⟩, 0, fun h' => hw (congrArg Subtype.val h')⟩⟩
    obtain ⟨τ, hτ, hτW⟩ :=
      SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial (SmoothRep.image f)
    have hτρ : SmoothRep.IsSubquotient τ ρ :=
      smoothSubquotientTransitivity ℂ _ _ _ _ hτW
        (SmoothRep.subrepresentation_isSubrepresentation (SmoothRep.hom f).range).isSubquotient
    have hτJ : SmoothRep.IsSubquotient τ
        ((jacquetFunctor (family.decomposition J) (family.closedUnipotent J)).obj
          (Y (bernsteinInertialClass i ν family c))) :=
      smoothSubquotientTransitivity ℂ _ _ _ _ hτW (SmoothRep.image_isQuotient f).isSubquotient
    exact hs (bernsteinInertialClass_eq_of_induction_mem_blocks i ν family huniq J a c τ hτ
      (hirr a τ hτ (hρ τ hτ hτρ)) (hirr c τ hτ (hres c _ hYc τ hτ hτJ))).symm
  -- so the component of the class of `a` is the whole induced representation
  exact (bernsteinBlockProperty_iff_saturated _ _).mp
    (bernsteinBlockProperty_of_iso (hY s₀) (cofanInjIsoOfIsZero hc s₀ hzero).symm)

/-- The same reduction, with the decomposition taken from the published statement of
Renard VI.7.2 at the saturated carrier universe `max uF uV`. -/
theorem bernsteinInduction_mem_block_of_decompositionStatement
    (hdec : BernsteinDecompositionStatement.{uF, max uF uV})
    (huniq : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (J : Finset (SimpleRoot i ν))
    (Q : BernsteinCuspidalDatum.{uF, max uF uV} i ν family →
      SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) → Prop)
    (hirr : ∀ (c : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
      (τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)), τ.IsIrreducible → Q c τ →
        bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family c)
          ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj
            τ))
    (hres : ∀ (c : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
      (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
      bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family c) V →
        ∀ τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J), τ.IsIrreducible →
          SmoothRep.IsSubquotient τ
            ((normalizedJacquetFunctor (unipotent i ν J) (levi i ν J) (family.closedUnipotent J)
              (family.decomposition J).levi_le_normalizer).obj V) → Q c τ)
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J))
    (hρ : ∀ τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J), τ.IsIrreducible →
      SmoothRep.IsSubquotient τ ρ → Q a τ) :
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj ρ) :=
  bernsteinInduction_mem_block_of_restriction i ν family (hdec F G T i ν family) huniq J Q
    hirr hres a ρ hρ

end Langlands.CuspidalSupport
