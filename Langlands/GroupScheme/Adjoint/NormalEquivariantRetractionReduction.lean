import Langlands.GroupScheme.Reductive.SemisimpleNormalComplementStatement
import Langlands.GroupScheme.Adjoint.NormalEquivariantRetractionStatement
import Langlands.GroupScheme.Rational.LeviRetraction
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Equivariant normal adjoint retractions from commuting normal complements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]
  {G H K : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G} {i : K ⟶ G}

/-- If `H` has trivial centre, the multiplication morphism of two commuting
subgroups `H` and `K` with monic inclusions is a monomorphism. -/
theorem mono_subgroupMultiplication_of_center_eq_bot
    (hH : center H = ⊥) [Mono j.hom.hom] [Mono i.hom.hom]
    (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ H.X) (y : T ⟶ K.X),
      Commute (x ≫ j.hom.hom) (y ≫ i.hom.hom)) :
    Mono (subgroupMultiplication j i) := by
  constructor
  intro T p p' hp
  have hprod : ((p ≫ fst H.X K.X) ≫ j.hom.hom) * ((p ≫ snd H.X K.X) ≫ i.hom.hom) =
      ((p' ≫ fst H.X K.X) ≫ j.hom.hom) * ((p' ≫ snd H.X K.X) ≫ i.hom.hom) := by
    rw [← comp_subgroupMultiplication, ← comp_subgroupMultiplication]
    simpa only [← comp_lift, lift_fst_snd, Category.comp_id] using hp
  set a := p ≫ fst H.X K.X
  set n := p ≫ snd H.X K.X
  set a' := p' ≫ fst H.X K.X
  set n' := p' ≫ snd H.X K.X
  -- The common value of the two quotients lies in both subgroups.
  have hcd : (a'⁻¹ * a) ≫ j.hom.hom = (n' * n⁻¹) ≫ i.hom.hom := by
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, GrpObj.inv_comp]
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
    exact hprod
  have hcenter : a'⁻¹ * a ∈ (center H).carrier T := by
    rw [mem_center]
    intro T' t h
    apply (cancel_mono j.hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, hcd, ← Category.assoc]
    exact (hcomm T' h (t ≫ (n' * n⁻¹))).symm.eq
  rw [hH, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hcenter
  have hd : n' * n⁻¹ = 1 := by
    apply (cancel_mono i.hom.hom).mp
    rw [← hcd, hcenter, MonObj.one_comp, MonObj.one_comp]
  have ha : a = a' := (inv_mul_eq_one.mp hcenter).symm
  have hn : n = n' := (mul_inv_eq_one.mp hd).symm
  exact CartesianMonoidalCategory.hom_ext _ _ ha hn

/-- A flat surjective monic multiplication of closed subgroups of an affine
field group is an isomorphism. -/
theorem isIso_subgroupMultiplication_of_flat_of_surjective
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] (hi : IsClosedSubgroup i)
    [Mono (subgroupMultiplication j i)]
    [Flat (subgroupMultiplication j i).left] [Surjective (subgroupMultiplication j i).left] :
    IsIso (subgroupMultiplication j i) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffine K.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have : IsAffine (H.X ⊗ K.X).left :=
    inferInstanceAs (IsAffine (Limits.pullback H.X.hom K.X.hom))
  have : Mono (subgroupMultiplication j i).left := Over.mono_left_of_mono _
  have : IsIso (subgroupMultiplication j i).left := Flat.isIso_of_surjective_of_mono _
  have : IsIso ((Over.forget _).map (subgroupMultiplication j i)) := by
    change IsIso (subgroupMultiplication j i).left
    infer_instance
  exact isIso_of_reflects_iso _ (Over.forget _)

end Field

/-- Commuting closed normal complements with flat surjective multiplication in
semisimple groups imply the equivariant normal adjoint retraction. -/
theorem normalAdjointEquivariantRetraction_of_semisimpleNormalComplement
    (hcomp : SemisimpleNormalComplementStatement.{u}) :
    NormalAdjointEquivariantRetractionStatement.{u} := by
  intro k _ _ G H hG hH j hj hjN S _ b c hbc
  obtain ⟨K, i, hi, hiN, hcomm, hflat, hsurj⟩ :=
    hcomp k G H hG.isSemisimple j hj hH.isSemisimple.isConnectedReductive.smooth
      hH.isSemisimple.isConnectedReductive.connectedSpace hjN
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  have : IsAffineHom H.X.hom := hH.isSemisimple.isConnectedReductive.isAffineHom
  have : Mono (subgroupMultiplication j i) :=
    mono_subgroupMultiplication_of_center_eq_bot hH.center_eq_bot hcomm
  have : Flat (subgroupMultiplication j i).left := hflat
  have : Surjective (subgroupMultiplication j i).left := hsurj
  have : IsIso (subgroupMultiplication j i) :=
    isIso_subgroupMultiplication_of_flat_of_surjective hi
  -- The action moves the complement into the kernel of the Levi coordinate.
  have hrad : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (n : T ⟶ K.X),
      leviComponent j i (b.act s (n ≫ i.hom.hom)) = 1 := by
    intro T s n
    have hmem : leviComponent j i (b.act s (n ≫ i.hom.hom)) ∈ (center H).carrier T := by
      rw [mem_center]
      intro T' t h
      rw [← leviComponent_comp, AutomorphicAction.naturality, ← Category.assoc]
      have hh : c.act (t ≫ s) (c.act (t ≫ s)⁻¹ h) = h := by
        rw [← c.act_mul_left, mul_inv_cancel, c.act_one_left]
      have hc := ((hcomm T' (c.act (t ≫ s)⁻¹ h) (t ≫ n)).symm.map
        (b.pointAut T' (t ≫ s))).map (leviRetractionPoints j i hiN T')
      change Commute (leviComponent j i (b.act (t ≫ s) ((t ≫ n) ≫ i.hom.hom)))
        (leviComponent j i (b.act (t ≫ s) (c.act (t ≫ s)⁻¹ h ≫ j.hom.hom))) at hc
      rwa [← hbc, leviComponent_comp_levi, hh] at hc
    rwa [hH.center_eq_bot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hmem
  refine ⟨leviRetraction j i hiN, levi_comp_leviRetraction j i hiN, ?_⟩
  intro T s g
  rw [comp_leviRetraction, comp_leviRetraction]
  conv_lhs => rw [← leviComponent_mul_radicalComponent j i g]
  rw [b.act_mul_right, ← hbc, leviComponent_mul j i hiN, leviComponent_comp_levi, hrad,
    mul_one]

end Langlands.GroupScheme
