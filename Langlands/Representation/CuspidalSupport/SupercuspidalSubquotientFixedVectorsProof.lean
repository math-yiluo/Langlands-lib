import Langlands.Representation.CuspidalSupport.SupercuspidalSubquotientFixedVectorsStatement
import Langlands.Representation.CuspidalSupport.RationalCompactRestrictionInertiaDecompositionProof
import Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal
import Langlands.Representation.Exponents.RepresentedCuspidalProjection
import Langlands.Representation.Category.FixedVectorConstituent
import Langlands.Representation.Jacquet.IrreducibleFixedVectorGeneration
import Langlands.Representation.Jacquet.RationalInertiaFixedVectors
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Renard VI.6.3, Proposition: proof

If the `K`-fixed vectors of a smooth representation `V` generate it, every nonzero
supercuspidal subquotient of `V` has a nonzero `K`-fixed vector, for every compact open
subgroup `K`. The proof takes an irreducible subquotient `τ` of the supercuspidal
subquotient, splits `V` along the inertia block of `τ` (VI.3.3.1, compact-restriction
form, available because `τ` is compact on `⁰G` by VI.2.1 (a) ⇒ (c)), finds a
constituent of the block summand with a nonzero `K`-fixed vector, and transfers it to
`τ` along the inertia relation, unramified characters being trivial on `K`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.CuspidalSupport

universe u v

open GroupScheme

/-- Renard VI.6.3, Proposition, for every compact open subgroup `K` of `G(F)`: if the
`K`-fixed vectors generate the smooth representation `V`, every nonzero supercuspidal
subquotient of `V` has a nonzero `K`-fixed vector. -/
theorem supercuspidalSubquotientFixedVectors :
    SupercuspidalSubquotientFixedVectorsStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := Aubert.General.RationalPointFamily.pointTopology
  intro _ _ K hK V hgen D hDV hD hDnt
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  -- An irreducible supercuspidal subquotient `τ` of `D`, hence of `V`.
  obtain ⟨τ, hτirr, hτD⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial D
  have hτsc : Aubert.General.RepresentedParabolic.IsSupercuspidal τ :=
    Aubert.General.RepresentedParabolic.IsSupercuspidal.of_isSubquotient hτD hD
  have hτV : SmoothRep.IsSubquotient τ V := smoothSubquotientTransitivity ℂ _ V D τ hτD hDV
  -- VI.2.1 (a) ⇒ (c): `τ` is compact on the common norm kernel.
  have hcomp := Aubert.General.RepresentedParabolic.compactRestriction_of_isSupercuspidal
    parabolicDynamic standardCocharacter relativeRootSystem
    Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence hG τ hτsc
  -- VI.3.3.1: split `V` along the inertia block of `τ`.
  have hdec : IsRationalInertiaCategoryDecomposition G τ :=
    rationalCompactRestrictionInertiaDecomposition k G hG τ hτirr hcomp
  obtain ⟨Y, j, hY, ⟨hc⟩⟩ := hdec.1 V
  -- The block summand has a nonzero `K`-fixed vector.
  have hYK : Nontrivial (fixedVectors (Y true).representation K.toSubgroup) := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    let f : ∀ b, Y b ⟶ Y true := fun b => match b with
      | true => 𝟙 (Y true)
      | false => 0
    let p : V ⟶ Y true := Cofan.IsColimit.desc hc f
    have hjp : j true ≫ p = 𝟙 (Y true) := Cofan.IsColimit.fac hc f true
    have hker : (SmoothRep.hom p).ker = ⊤ := by
      apply hgen
      intro w hw
      have h0 := congrArg Subtype.val
        (Subsingleton.elim (fixedVectorsMap (SmoothRep.hom p) K.toSubgroup ⟨w, hw⟩) 0)
      exact h0
    have hp : p = 0 := by
      ext w
      have hw : w ∈ (SmoothRep.hom p).ker := by
        rw [hker]
        trivial
      exact hw
    have hid : 𝟙 (Y true) = 0 := by rw [← hjp, hp, Limits.comp_zero]
    have hj : j true = 0 := by
      rw [← Category.id_comp (j true), hid, Limits.zero_comp]
    let g : ∀ b, Y b ⟶ Y false := fun b => match b with
      | false => 𝟙 (Y false)
      | true => 0
    let q : V ⟶ Y false := Cofan.IsColimit.desc hc g
    have hjq : j false ≫ q = 𝟙 (Y false) := Cofan.IsColimit.fac hc g false
    have hqj : q ≫ j false = 𝟙 V := by
      apply Cofan.IsColimit.hom_ext hc
      intro b
      change j b ≫ (q ≫ j false) = j b ≫ 𝟙 V
      rw [← Category.assoc]
      change ((Cofan.mk V j).inj b ≫ Cofan.IsColimit.desc hc g) ≫ j false = _
      rw [Cofan.IsColimit.fac]
      cases b <;> simp [g, hj]
    let e : V ≅ Y false := ⟨q, j false, hqj, hjq⟩
    exact hY false τ hτirr (hτV.of_iso_right e) (IsRationalInertiaRelated.refl τ)
  -- An irreducible constituent `σ` of the block summand with a nonzero fixed vector;
  -- `σ` is inertia-related to `τ`, and unramified twists keep compact fixed vectors.
  obtain ⟨σ, hσirr, hσY, hσK⟩ :=
    SmoothRep.hasFixedVectorConstituent_of_nontrivial (Y true) K.toSubgroup hYK
  have hτK : Nontrivial (fixedVectors τ.representation K.toSubgroup) :=
    (nontrivial_fixedVectors_iff_of_rationalInertiaRelated G K.toSubgroup hK
      (hY true σ hσirr hσY)).mpr hσK
  -- Lift the nonzero fixed vector from `τ` to `D`.
  have hDK := SmoothRep.nontrivial_fixedVectors_of_isSubquotient K hK hτD hτK
  exact Submodule.nontrivial_iff_ne_bot.mp hDK

end Langlands.CuspidalSupport
