import Langlands.AbelianScheme.PointedAbelianArtinianLiftingStatement
import Langlands.AlgebraicGeometry.Deformation.ElementaryLiftMultiplication
import Langlands.AlgebraicGeometry.DvrSmoothFibers
import Langlands.AlgebraicGeometry.FibralIsomorphism
import Langlands.AlgebraicGeometry.GeometricallyConnectedDescent
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChange
import Langlands.GroupScheme.DominantHomFlat

/-! # The elementary Artinian lift of a pointed abelian-scheme law -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry
open SquareZeroAffinePairs Deformation.ElementaryMorphismLifts Deformation.ElementaryLiftCech
open Deformation.AffineOpenQuotientSections
open Picard.FieldTwoAxisH1Injectivity (surjective_secHom_top)

private lemma smooth_product {S : Scheme.{u}} (X Y : Over S) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := by
  change Smooth (pullback.fst X.hom Y.hom ≫ X.hom)
  infer_instance

private lemma proper_product {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := by
  change IsProper (pullback.fst X.hom Y.hom ≫ X.hom)
  infer_instance

private lemma connected_product {S : Scheme.{u}} (X Y : Over S) [Smooth X.hom] [Smooth Y.hom]
    [GeometricallyConnected X.hom] [GeometricallyConnected Y.hom] : GeometricallyConnected (X ⊗ Y).hom := by
  change GeometricallyConnected (pullback.fst X.hom Y.hom ≫ X.hom)
  exact GeometricallyConnected.comp _ _

section Quotient

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {I : Ideal R}

local notation "S" => Spec (CommRingCat.of R)
local notation "S₀" => Spec (CommRingCat.of (R ⧸ I))
local notation "T" => Over.mk (𝟙 S)

/-- Factor the residue map through an ideal contained in the maximal ideal. -/
private lemma quotient_to_residue (hI : I ≤ maximalIdeal R) :
    specMap (Ideal.Quotient.factor hI) ≫ specMap (Ideal.Quotient.mk I) = specMap (residue R) := by
  rw [← specMap_comp, Ideal.Quotient.factor_comp_mk]
  rfl

private lemma isIso_of_quotient_reduction [IsArtinianRing R] (hI : I ≤ maximalIdeal R)
    {X Y : Over S} [Smooth X.hom] [Smooth Y.hom] (A : Reduction X I) (B : Reduction Y I)
    (f : X ⟶ Y) [IsIso (A.map B f)] : IsIso f := by
  let q := specMap (Ideal.Quotient.mk I)
  have hq : IsIso ((Over.pullback q).map f) := by
    have : IsIso (A.isoPullback.hom ≫ (Over.pullback q).map f) := by
      rw [← A.isoPullback_naturality B f]
      infer_instance
    exact IsIso.of_isIso_comp_left A.isoPullback.hom _
  let c := (closedPointResidueSpecIso R).inv ≫ specMap (Ideal.Quotient.factor hI)
  have hc : (S).fromSpecResidueField (IsLocalRing.closedPoint R) = c ≫ q := by
    dsimp only [c, q]
    rw [Category.assoc, quotient_to_residue]
    change _ = (closedPointResidueSpecIso R).inv ≫ Spec.algebraMap R (ResidueField R)
    rw [← closedPointResidueSpecIso_hom_fromSpecResidueField R, Iso.inv_hom_id_assoc]
  have hf : IsIso f.left := by
    apply fibralIsomorphism S X Y f inferInstance inferInstance inferInstance
    intro x
    have hx := @Subsingleton.elim S spec_subsingleton x (IsLocalRing.closedPoint R)
    subst x
    let n := Over.pullbackComp c q
    have : IsIso ((Over.pullback c).map ((Over.pullback q).map f)) :=
      (Over.pullback c).map_isIso _
    have : IsIso ((Over.pullback (c ≫ q)).map f ≫ n.hom.app Y) := by
      rw [n.hom.naturality]
      change IsIso (n.hom.app X ≫ (Over.pullback c).map ((Over.pullback q).map f))
      infer_instance
    have : IsIso ((Over.pullback (c ≫ q)).map f) :=
      IsIso.of_isIso_comp_right _ (n.hom.app Y)
    have hiso : IsIso (((Over.pullback (c ≫ q)).map f).left) :=
      (Over.forget (Spec ((S).residueField (IsLocalRing.closedPoint R)))).map_isIso
        ((Over.pullback (c ≫ q)).map f)
    exact (congrArg (fun b ↦ IsIso (((Over.pullback b).map f).left)) hc).mpr hiso
  have : IsIso ((Over.forget S).map f) := hf
  exact isIso_of_reflects_iso f (Over.forget S)

omit [IsLocalRing R] in
private lemma quotient_unit {X : Over S} (B : Reduction X I) [MonObj B.obj] (e : T ⟶ X)
    (he : η[B.obj].left ≫ B.toOriginal = (baseReduction I).toOriginal ≫ e.left) :
    (baseReduction I).map B e = η[B.obj] := by
  apply Over.OverMorphism.ext
  apply (cancel_mono B.toOriginal).mp
  rw [Reduction.map_left_toOriginal, he]

private lemma baseChange_unit_fst {S₁ S₂ : Scheme.{u}} (b : S₂ ⟶ S₁) (A : AbelianScheme S₁) :
    η[((baseChange b).obj A).X].left ≫ pullback.fst A.X.hom b = b ≫ η[A.X].left := by
  have h := unitSection_baseChange_fst b A
  change (toUnit (𝟙_ (Over S₂)) ≫ η[((baseChange b).obj A).X]).left ≫ pullback.fst A.X.hom b =
    b ≫ (toUnit (𝟙_ (Over S₁)) ≫ η[A.X]).left at h
  simpa only [SemiCartesianMonoidalCategory.toUnit_unit, Category.id_comp] using h

/-- The residue group used to compute differences is the base change of the given group law. -/
private def targetOfReduction (X : Over S) (A : AbelianScheme S₀) (i₀ : A.X.left ⟶ X.left)
    (hB : IsPullback i₀ A.X.hom X.hom (specMap (Ideal.Quotient.mk I)))
    (hI : I ≤ maximalIdeal R) : Target R := by
  let a := specMap (Ideal.Quotient.factor hI)
  let F := (baseChange a).obj A
  let i := pullback.fst A.X.hom a
  have h : IsPullback (i ≫ i₀) F.X.hom X.hom (specMap (residue R)) := by
    have hp : IsPullback i F.X.hom A.X.hom a := IsPullback.of_hasPullback _ _
    have h := hp.paste_horiz hB
    rwa [quotient_to_residue hI] at h
  exact ⟨X, F.toGrp, i ≫ i₀, h⟩

end Quotient

section Law

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
variable {I : Ideal R} [Fact (maximalIdeal R * I = ⊥)] {Z : Target R}
  [Smooth Z.X.hom] [IsProper Z.X.hom] [GeometricallyConnected Z.G.X.hom]

local notation "S" => Spec (CommRingCat.of R)
local notation "T" => Over.mk (𝟙 S)

omit [Smooth Z.X.hom] [IsProper Z.X.hom] [GeometricallyConnected Z.G.X.hom] in
private lemma eq_of_reduced_eq_and_pointed {Y : Over (Spec (CommRingCat.of R))}
    [Smooth Y.hom] [IsProper Y.hom]
    (B : Reduction Y I) (F : Reduction Y (maximalIdeal R)) [Smooth F.obj.hom]
    [IsProper F.obj.hom] [GeometricallyConnected F.obj.hom] (b : Z.Coordinates I) (A : Reduction Z.X I)
    (f g : Y ⟶ Z.X) (hf : B.map A f = B.map A g) (s : T ⟶ Y) (hs : s ≫ f = s ≫ g) : f = g :=
  eq_of_eq_at_section B F b ((B.map_eq_iff A f g).mp hf) (surjective_secHom_top F.obj.hom) s hs

private theorem exists_abelian_law (hI : I ≤ maximalIdeal R) (B : Reduction Z.X I)
    [GrpObj B.obj] [IsCommMonObj B.obj] (e : T ⟶ Z.X) (he : (baseReduction I).map B e = η[B.obj]) :
    ∃ A : AbelianScheme S, ∃ i : A.X ≅ Z.X, η[A.X] ≫ i.hom = e := by
  let X := Z.X
  let P := X ⊗ X
  let F := targetFibre Z
  let D := B.fibreProduct B
  let H := F.fibreProduct F
  have : Smooth F.obj.hom := MorphismProperty.of_isPullback F.cartesian inferInstance
  have : Smooth Z.G.X.hom := MorphismProperty.of_isPullback Z.fibre inferInstance
  have : IsProper F.obj.hom := MorphismProperty.of_isPullback F.cartesian inferInstance
  have : GeometricallyConnected F.obj.hom := ‹GeometricallyConnected Z.G.X.hom›
  let b := Target.Coordinates.ofTarget Z I hI
  obtain ⟨m, hm, hp⟩ := exists_multiplication_lift hI b B e he
  have hm' : D.map B m = μ[B.obj] := hm
  let s₂ := lift e e
  have hus (V : Over S) (f : T ⟶ V) : f ≫ toUnit V = 𝟙 T :=
    (Over.mkIdTerminal).hom_ext _ _
  have hright : leftAxis e ≫ m = 𝟙 X := by
    refine eq_of_reduced_eq_and_pointed B F b B _ _ ?_ e ?_
    rw [B.map_comp D B, map_leftAxis, hm', he, leftAxis_mul, Reduction.map_id]
    rw [← Category.assoc, leftAxis, comp_lift, Category.comp_id, ← Category.assoc, hus, Category.id_comp]
    exact hp.trans (Category.comp_id _).symm
  have hleft : rightAxis e ≫ m = 𝟙 X := by
    refine eq_of_reduced_eq_and_pointed B F b B _ _ ?_ e ?_
    rw [B.map_comp D B, map_rightAxis, hm', he, rightAxis_mul, Reduction.map_id]
    rw [← Category.assoc, rightAxis, comp_lift, Category.comp_id, ← Category.assoc, hus, Category.id_comp, hp]
  have : Smooth P.hom := smooth_product X X
  have : IsProper P.hom := proper_product X X
  have : Smooth H.obj.hom := smooth_product F.obj F.obj
  have : IsProper H.obj.hom := proper_product F.obj F.obj
  have : GeometricallyConnected H.obj.hom := connected_product F.obj F.obj
  have hcomm : lift (snd X X) (fst X X) ≫ m = m := by
    refine eq_of_reduced_eq_and_pointed D H b B _ _ ?_ s₂ ?_
    · rw [D.map_comp D B, Reduction.map_lift, Reduction.map_snd, Reduction.map_fst, hm',
        lift_snd_fst, IsCommMonObj.mul_comm]
    · rw [comp_lift_assoc]
      have h₁ : s₂ ≫ snd X X = e := lift_snd e e
      have h₂ : s₂ ≫ fst X X = e := lift_fst e e
      rw [h₁, h₂]
  let Q := D.fibreProduct B
  let J := H.fibreProduct F
  let w₁ : P ⊗ X ⟶ X := fst P X ≫ fst X X
  let w₂ : P ⊗ X ⟶ X := fst P X ≫ snd X X
  let w₃ : P ⊗ X ⟶ X := snd P X
  let s₃ := lift s₂ e
  have : Smooth (P ⊗ X).hom := smooth_product P X
  have : IsProper (P ⊗ X).hom := proper_product P X
  have : Smooth J.obj.hom := smooth_product H.obj F.obj
  have : IsProper J.obj.hom := proper_product H.obj F.obj
  have : GeometricallyConnected J.obj.hom := connected_product H.obj F.obj
  have hAssoc : lift (lift w₁ w₂ ≫ m) w₃ ≫ m = lift w₁ (lift w₂ w₃ ≫ m) ≫ m := by
    refine eq_of_reduced_eq_and_pointed Q J b B _ _ ?_ s₃ ?_
    · have hpair (f g : P ⊗ X ⟶ X) : Q.map B (lift f g ≫ m) =
          lift (Q.map B f) (Q.map B g) ≫ μ[B.obj] := by
        rw [Q.map_comp D B, hm']
        exact congrArg (fun k ↦ k ≫ μ[B.obj]) (Reduction.map_lift Q B B f g)
      simp only [hpair]
      exact MonObj.lift_lift_assoc _ _ _
    · have hfst : s₃ ≫ fst P X = s₂ := lift_fst s₂ e
      have s₃₁ : s₃ ≫ w₁ = e := by
        rw [show w₁ = fst P X ≫ fst X X from rfl, ← Category.assoc, hfst]
        exact lift_fst e e
      have s₃₂ : s₃ ≫ w₂ = e := by
        rw [show w₂ = fst P X ≫ snd X X from rfl, ← Category.assoc, hfst]
        exact lift_snd e e
      have s₃₃ : s₃ ≫ w₃ = e := lift_snd s₂ e
      simp only [comp_lift_assoc, s₃₁, s₃₂, s₃₃, hp]
  let mon : MonObj X := {
    one := e
    mul := m
    one_mul := by
      apply (cancel_epi (λ_ X).inv).mp
      have hk : (λ_ X).inv ≫ (e ▷ X) = rightAxis e := by
        have hinvL : (λ_ X).inv = lift (toUnit X) (𝟙 X) := by
          apply CartesianMonoidalCategory.hom_ext
          · exact (leftUnitor_inv_fst X).trans (lift_fst _ _).symm
          · exact (leftUnitor_inv_snd X).trans (lift_snd _ _).symm
        rw [hinvL]
        exact lift_whiskerRight (toUnit X) (𝟙 X) e
      rw [← Category.assoc, hk, hleft, Iso.inv_hom_id]
    mul_one := by
      apply (cancel_epi (ρ_ X).inv).mp
      have hk : (ρ_ X).inv ≫ (X ◁ e) = leftAxis e := by
        have hinvR : (ρ_ X).inv = lift (𝟙 X) (toUnit X) := by
          apply CartesianMonoidalCategory.hom_ext
          · exact (rightUnitor_inv_fst X).trans (lift_fst _ _).symm
          · exact (rightUnitor_inv_snd X).trans (lift_snd _ _).symm
        rw [hinvR]
        exact lift_whiskerLeft (𝟙 X) (toUnit X) e
      rw [← Category.assoc, hk, hright, Iso.inv_hom_id]
    mul_assoc := by
      have hl : m ▷ X = lift (lift w₁ w₂ ≫ m) w₃ := by
        have hpair : lift w₁ w₂ = fst P X := lift_comp_fst_snd _
        rw [hpair]
        apply CartesianMonoidalCategory.hom_ext
        · exact (whiskerRight_fst m X).trans (lift_fst _ _).symm
        · exact (whiskerRight_snd m X).trans (lift_snd _ _).symm
      have hr : (α_ X X X).hom ≫ (X ◁ m) = lift w₁ (lift w₂ w₃ ≫ m) := by
        have hAssocHom : (α_ X X X).hom = lift w₁ (lift w₂ w₃) := by
          apply CartesianMonoidalCategory.hom_ext
          · exact (associator_hom_fst X X X).trans (lift_fst _ _).symm
          · rw [lift_snd]
            apply CartesianMonoidalCategory.hom_ext
            · exact (associator_hom_snd_fst X X X).trans (lift_fst _ _).symm
            · exact (associator_hom_snd_snd X X X).trans (lift_snd _ _).symm
        rw [hAssocHom]
        exact lift_whiskerLeft w₁ (lift w₂ w₃) m
      rw [hl, ← Category.assoc, hr]
      exact hAssoc }
  let k := lift (fst X X) m
  have hk : D.map D k = (Langlands.GroupScheme.DominantHomFlat.shearLeft (𝟙 B.obj)).hom := by
    change D.map D (lift (fst X X) m) = lift (fst B.obj B.obj) ((fst B.obj B.obj ≫ 𝟙 B.obj) * snd B.obj B.obj)
    rw [Reduction.map_lift, Reduction.map_fst, hm', Category.comp_id, Hom.mul_def, lift_fst_snd, Category.id_comp]
  have : IsIso (D.map D k) := by rw [hk]; infer_instance
  have : IsIso k := isIso_of_quotient_reduction hI D D k
  let n := leftAxis e ≫ CategoryTheory.inv k ≫ snd X X
  have hn : lift (𝟙 X) n = leftAxis e ≫ CategoryTheory.inv k := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, Category.assoc]
      have hf : k ≫ fst X X = fst X X := lift_fst _ _
      rw [← hf, IsIso.inv_hom_id_assoc, leftAxis, lift_fst]
    · simp only [lift_snd, Category.assoc, n]
  have hnr : lift (𝟙 X) n ≫ m = toUnit X ≫ e := by
    rw [hn, Category.assoc]
    have h : k ≫ snd X X = m := lift_snd _ _
    rw [← h, IsIso.inv_hom_id_assoc, leftAxis, lift_snd]
  have hnl : lift n (𝟙 X) ≫ m = toUnit X ≫ e := by
    calc
      lift n (𝟙 X) ≫ m = lift (𝟙 X) n ≫ lift (snd X X) (fst X X) ≫ m := by
        rw [comp_lift_assoc, lift_snd, lift_fst]
      _ = _ := by rw [hcomm, hnr]
  let grp : GrpObj X := { mon with inv := n, left_inv := hnl, right_inv := hnr }
  have : IsCommMonObj X := ⟨by
    change (β_ X X).hom ≫ m = m
    simpa only [lift_snd_fst] using hcomm⟩
  have : Surjective (specMap (Ideal.Quotient.mk (maximalIdeal R))) := by
    refine ⟨fun x ↦ ⟨IsLocalRing.closedPoint (ResidueField R), ?_⟩⟩
    exact @Subsingleton.elim S spec_subsingleton _ _
  have : GeometricallyConnected X.hom := geometricallyConnected_of_surjective_isPullback _ _ F.cartesian
  let A : AbelianScheme S := { X := X, grp := grp }
  exact ⟨A, Iso.refl X, Category.comp_id _⟩

end Law

/-- A smooth proper pointed scheme over a local Artinian base admits the pointed abelian law
when the law is given over an elementary quotient. -/
theorem pointedAbelianArtinianLifting : PointedAbelianArtinianLiftingStatement.{u} := by
  intro R R₀ _ _ _ _ _ _ q hq hann X p s hs hp hpr t hex
  obtain ⟨A₀, e₀, he₀, hunit₀⟩ := hex
  let I := RingHom.ker q
  have : Fact (maximalIdeal R * I = ⊥) := ⟨hann⟩
  have hI : I ≤ maximalIdeal R := le_maximalIdeal (RingHom.ker_ne_top q)
  let X' := Over.mk p
  let e : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X' := Over.homMk s hs
  have : Smooth X'.hom := hp
  have : IsProper X'.hom := hpr
  let r := q.quotientKerEquivOfSurjective hq
  let c := specMap r.symm.toRingHom
  have hc : c ≫ t = specMap (Ideal.Quotient.mk I) := by
    change specMap r.symm.toRingHom ≫ specMap q = _
    rw [← specMap_comp, RingHom.quotientKerEquivOfSurjective_symm_comp]
  let A := (baseChange c).obj A₀
  have h₀ : IsPullback (e₀.hom ≫ pullback.fst p t) A₀.X.hom p t := by
    apply (IsPullback.of_hasPullback p t).of_iso' e₀ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simpa only [Iso.refl_hom, Category.comp_id] using he₀
    · simp
    · simp
  have hA : IsPullback (pullback.fst A₀.X.hom c ≫ e₀.hom ≫ pullback.fst p t)
      A.X.hom p (specMap (Ideal.Quotient.mk I)) := by
    rw [← hc]
    exact (IsPullback.of_hasPullback A₀.X.hom c).paste_horiz h₀
  let B : Reduction X' I := ⟨A.X, _, hA⟩
  let _ : GrpObj B.obj := A.toGrp.grp
  have : IsCommMonObj B.obj := A.comm
  have hunit : (baseReduction I).map B e = η[B.obj] := by
    apply quotient_unit
    change η[A.X].left ≫ pullback.fst A₀.X.hom c ≫ e₀.hom ≫ pullback.fst p t = _
    rw [← Category.assoc, baseChange_unit_fst, Category.assoc, hunit₀, ← Category.assoc, hc]
    rfl
  let Z := targetOfReduction X' A B.toOriginal B.cartesian hI
  have : Smooth Z.X.hom := hp
  have : IsProper Z.X.hom := hpr
  have : GeometricallyConnected Z.G.X.hom := by
    change GeometricallyConnected (((baseChange (specMap (Ideal.Quotient.factor hI))).obj A).X.hom)
    infer_instance
  obtain ⟨A', i, hs'⟩ := exists_abelian_law (Z := Z) hI B e hunit
  let e' : A'.X.left ≅ X := (Over.forget _).mapIso i
  refine ⟨A', e', ?_, ?_⟩
  · exact Over.w i.hom
  · exact congrArg (fun f ↦ f.left) hs'

end Langlands.AbelianScheme
