import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
import Langlands.GroupScheme.Descent.FiniteCoefficientGroup
import Langlands.GroupScheme.Descent.FiniteCoefficientHomGeneral
import Langlands.GroupScheme.Descent.Reindex
import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation
import Langlands.GroupScheme.Torus.RelativeTorusSubalgebraDescent

/-! # Finite coefficient models of actual closed torus-subgroup families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open Descent FiniteCoefficient SubgroupFunctor

private theorem specTower {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A] :
    Spec.algebraMap B A ≫ Spec.algebraMap R B = Spec.algebraMap R A := by
  simp only [Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

private abbrev coefficientTest (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    Over (Spec (CommRingCat.of R)) := Over.mk (Spec.algebraMap R B)

/-- The map of affine tests induced by the two upper rings of an algebra tower. -/
def coefficientMap (R B A : Type u) [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A] :
    coefficientTest R A ⟶ coefficientTest R B :=
  Over.homMk (Spec.algebraMap B A) specTower

/-- A torus subgroup model records a finitely generated
coefficient algebra, its actual admissible family, and exact evaluation. -/
structure AdmissibleCoefficientModel (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    (F : AdmissibleSubgroup ((baseChange (Spec.algebraMap R A)).obj G)) where
  coefficients : Subalgebra R A
  finite : coefficients.FG
  group : GroupScheme (Spec (CommRingCat.of coefficients))
  hom : group ⟶ (baseChange (Spec.algebraMap R coefficients)).obj G
  closed : IsClosedSubgroup hom
  torus : RelativeTorus.IsTorus group
  evaluates : evaluate hom (coefficientMap R coefficients A) = F.val

@[reassoc] private theorem map_fst {S T : Scheme.{u}} (b : T ⟶ S)
    {H G : GroupScheme S} (i : H ⟶ G) :
    ((baseChange b).map i).hom.hom.left ≫ pullback.fst G.X.hom b =
      pullback.fst H.X.hom b ≫ i.hom.hom.left := pullback.lift_fst _ _ _

private theorem closed_at_coefficients {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {H G : GroupScheme (Spec (CommRingCat.of R))} (i : H ⟶ G)
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom] [QuasiSeparated H.X.hom]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    (h : IsClosedSubgroup ((baseChange (Spec.algebraMap R A)).map i)) :
    ∃ B : Subalgebra R A, B.FG ∧
      IsClosedSubgroup ((baseChange (Spec.algebraMap R B)).map i) := by
  let f := i.hom.hom.left
  have w : f ≫ G.X.hom = H.X.hom := Over.w i.hom.hom
  have : LocallyOfFiniteType (f ≫ G.X.hom) := w.symm ▸ inferInstanceAs (LocallyOfFiniteType H.X.hom)
  have : QuasiCompact (f ≫ G.X.hom) := w.symm ▸ inferInstanceAs (QuasiCompact H.X.hom)
  have : QuasiSeparated (f ≫ G.X.hom) := w.symm ▸ inferInstanceAs (QuasiSeparated H.X.hom)
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f G.X.hom
  have : QuasiCompact f := QuasiCompact.of_comp f G.X.hom
  have : QuasiSeparated f := QuasiSeparated.of_comp f G.X.hom
  have hA : ∀ m : pullback (f ≫ G.X.hom) (Spec.algebraMap R A) ⟶
        pullback G.X.hom (Spec.algebraMap R A),
      m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f →
      m ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion m := by
    rw [w]
    intro m hm₁ hm₂
    have hm : m = ((baseChange (Spec.algebraMap R A)).map i).hom.hom.left := by
      apply pullback.hom_ext
      · exact hm₁.trans (map_fst (Spec.algebraMap R A) i).symm
      · exact hm₂.trans ((Over.pullback (Spec.algebraMap R A)).map i.hom.hom).w.symm
    exact hm.symm ▸ h
  obtain ⟨B, hB, -, hb⟩ :=
    IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
      f G.X.hom hA (∅ : Finset A)
  rw [w] at hb
  refine ⟨B, hB, hb _ ?_ ((Over.pullback _).map i.hom.hom).w⟩
  exact pullback.lift_fst _ _ _

set_option maxHeartbeats 800000 in
private theorem closed_torus_at_coefficients {R A : Type u}
    [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    {H G : GroupScheme (Spec (CommRingCat.of R))} (i : H ⟶ G)
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom]
    (h : IsClosedSubgroup ((baseChange (Spec.algebraMap R A)).map i))
    (hT : RelativeTorus.IsTorus ((baseChange (Spec.algebraMap R A)).obj H)) :
    ∃ B : Subalgebra R A, B.FG ∧
      IsClosedSubgroup ((baseChange (Spec.algebraMap R B)).map i) ∧
      RelativeTorus.IsTorus ((baseChange (Spec.algebraMap R B)).obj H) := by
  obtain ⟨B, hB, hBi⟩ := closed_at_coefficients i h
  let b := Spec.algebraMap R B
  let H' := (baseChange b).obj H
  let : Smooth H'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  let : IsAffineHom H'.X.hom := MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  let : Algebra.FiniteType R B := (Subalgebra.fg_iff_finiteType B).mp hB
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have hTA : RelativeTorus.IsTorus ((baseChange (Spec.algebraMap B A)).obj H') :=
    .of_iso (pullbackComparison b _ _ specTower H) hT
  obtain ⟨C, hC, hcT⟩ := RelativeTorus.isTorusSubalgebraDescent H' hTA
  let c := Spec.algebraMap B C
  let d := Spec.algebraMap R (C.restrictScalars R)
  have hcd : c ≫ b = d := specTower
  let eH := pullbackComparison b c d hcd H
  let eG := pullbackComparison b c d hcd G
  have hi := (hBi.baseChange c).comp_iso eG
  change IsClosedSubgroup (((baseChange c).map ((baseChange b).map i)) ≫ eG.hom) at hi
  rw [show ((baseChange c).map ((baseChange b).map i)) ≫ eG.hom =
      eH.hom ≫ (baseChange d).map i from pullbackComparison_naturality b c d hcd i] at hi
  have hfin : Algebra.FiniteType R C :=
    Algebra.FiniteType.trans inferInstance ((Subalgebra.fg_iff_finiteType C).mp hC)
  exact ⟨C.restrictScalars R, (Subalgebra.fg_iff_finiteType _).mpr hfin,
    by simpa only [Iso.symm_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      using hi.iso_comp eH.symm,
    .of_iso eH.symm hcT⟩

private theorem comparison_assoc {S T B A : Scheme.{u}}
    (t : T ⟶ S) (b : B ⟶ T) (d : B ⟶ S) (hbd : b ≫ t = d)
    (w : A ⟶ B) (z : A ⟶ T) (hbz : w ≫ b = z)
    (a : A ⟶ S) (hza : z ≫ t = a) (hda : w ≫ d = a) (G : GroupScheme S) :
    (baseChange w).map (Descent.pullbackComparison t b d hbd G).hom ≫
        (Descent.pullbackComparison d w a hda G).hom =
      (Descent.pullbackComparison b w z hbz ((baseChange t).obj G)).hom ≫
        (Descent.pullbackComparison t z a hza G).hom := by
  subst d
  subst a
  exact Descent.pullbackComparison_assoc t w b z hbz G

private structure SubgroupHomModel (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    (F : AdmissibleSubgroup ((baseChange (Spec.algebraMap R A)).obj G)) where
  coefficients : Subalgebra R A
  finite : coefficients.FG
  source : GroupScheme (Spec (CommRingCat.of coefficients))
  affine : IsAffineHom source.X.hom
  smooth : Smooth source.X.hom
  hom : source ⟶ (baseChange (Spec.algebraMap R coefficients)).obj G
  closedAfterChange : IsClosedSubgroup ((baseChange (Spec.algebraMap coefficients A)).map hom)
  torusAfterChange : RelativeTorus.IsTorus ((baseChange (Spec.algebraMap coefficients A)).obj source)
  evaluates : evaluate hom (coefficientMap R coefficients A) = F.val

set_option maxHeartbeats 1600000 in
private theorem exists_subgroupHomModel (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    (G : GroupScheme (Spec (CommRingCat.of R))) [LocallyOfFinitePresentation G.X.hom]
    (F : AdmissibleSubgroup ((baseChange (Spec.algebraMap R A)).obj G)) :
    Nonempty (SubgroupHomModel R A G F) := by
  let r := admissibleRepresentative F
  let : IsAffineHom r.group.X.hom := r.torus.isAffineHom
  let : IsAffine r.group.X.left := isAffine_of_isAffineHom r.group.X.hom
  let : Smooth r.group.X.hom := r.torus.smooth
  let M := groupModel R A r.group
  let T := M.coefficients
  let t := Spec.algebraMap R T
  let G₀ := (baseChange t).obj G
  let a := Spec.algebraMap R A
  let z := Spec.algebraMap T A
  let e := Descent.pullbackComparison t z a specTower G
  let i := M.iso.inv ≫ r.hom ≫ e.inv
  let : IsAffineHom M.group.X.hom := M.affine
  let : LocallyOfFinitePresentation G₀.X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  obtain ⟨B, hB, -, j, hj⟩ := exists_fg_hom_general M.group G₀ i (∅ : Finset A)
  let B₀ := B.restrictScalars R
  let b := Spec.algebraMap T B
  let d := Spec.algebraMap R B₀
  let w := Spec.algebraMap B A
  let H := (baseChange b).obj M.group
  let eB := Descent.pullbackComparison t b d specTower G
  let eH := Descent.pullbackComparison b w z specTower M.group
  let eJ := Descent.pullbackComparison b w z specTower G₀
  let jB := j ≫ eB.hom
  let eBA := Descent.pullbackComparison d w a specTower G
  have hjA : (baseChange w).map j ≫ eJ.hom = eH.hom ≫ i := hj
  let eSource := eH ≪≫ M.iso.symm
  have hEval : familyHom jB (coefficientMap R B₀ A) = eSource.hom ≫ r.hom := by
    change (baseChange w).map (j ≫ eB.hom) ≫ eBA.hom = _
    have heq : (baseChange w).map eB.hom ≫ eBA.hom = eJ.hom ≫ e.hom :=
      comparison_assoc t b d specTower w z specTower a specTower specTower G
    rw [Functor.map_comp, Category.assoc, heq, ← Category.assoc, hjA]
    simp only [i, eSource, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hCl : IsClosedSubgroup (familyHom jB (coefficientMap R B₀ A)) := by
    rw [hEval]
    exact r.closed.iso_comp eSource
  have hBfin : Algebra.FiniteType R B :=
    Algebra.FiniteType.trans ((Subalgebra.fg_iff_finiteType T).mp M.finite)
      ((Subalgebra.fg_iff_finiteType B).mp hB)
  exact ⟨{
    coefficients := B₀
    finite := (Subalgebra.fg_iff_finiteType _).mpr hBfin
    source := H
    affine := MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ M.affine
    smooth := MorphismProperty.pullback_snd (P := @Smooth) _ _ M.smooth
    hom := jB
    closedAfterChange := (IsClosedSubgroup.comp_iso_iff _ eBA).mp hCl
    torusAfterChange := RelativeTorus.IsTorus.of_iso eSource r.torus
    evaluates := by
      rw [evaluate, hEval, range_iso_comp]
      exact r.represents.2 }⟩

set_option maxHeartbeats 1800000 in
/-- Every actual closed torus subgroup of an algebra pullback over a noetherian
ring descends to finitely generated coefficients. -/
theorem exists_admissibleCoefficientModel (R A : Type u)
    [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom]
    (F : AdmissibleSubgroup ((baseChange (Spec.algebraMap R A)).obj G)) :
    Nonempty (AdmissibleCoefficientModel R A G F) := by
  obtain ⟨M⟩ := exists_subgroupHomModel R A G F
  let B := M.coefficients
  let b := Spec.algebraMap R B
  let J := (baseChange b).obj G
  let : Smooth M.source.X.hom := M.smooth
  let : IsAffineHom M.source.X.hom := M.affine
  let : QuasiCompact J.X.hom := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  let : IsSeparated J.X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  let : Algebra.FiniteType R B := (Subalgebra.fg_iff_finiteType B).mp M.finite
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  obtain ⟨C, hC, hj, hT⟩ := closed_torus_at_coefficients M.hom M.closedAfterChange M.torusAfterChange
  let C₀ := C.restrictScalars R
  let d := Spec.algebraMap R C₀
  let c := Spec.algebraMap B C
  have hcd : c ≫ b = d := specTower
  let aBC : coefficientTest R C₀ ⟶ coefficientTest R B := Over.homMk c hcd
  let aCA := coefficientMap R C₀ A
  let aBA := coefficientMap R B A
  have hCfin : Algebra.FiniteType R C :=
    Algebra.FiniteType.trans inferInstance ((Subalgebra.fg_iff_finiteType C).mp hC)
  have hcomp : aCA ≫ aBC = aBA := by
    apply Over.OverMorphism.ext
    change Spec.algebraMap C A ≫ c = Spec.algebraMap B A
    exact specTower
  let K₀ : GroupScheme (Spec (CommRingCat.of C₀)) := (baseChange c).obj M.source
  let i₀ : K₀ ⟶ (baseChange d).obj G :=
    @familyHom (Spec (CommRingCat.of R)) G
      (coefficientTest R B) (coefficientTest R C₀) M.source M.hom aBC
  have hEvalComp := @evaluate_comp (Spec (CommRingCat.of R)) G
    (coefficientTest R B) (coefficientTest R C₀) (coefficientTest R A)
    M.source M.hom aBC aCA
  let E (q : coefficientTest R A ⟶ coefficientTest R B) :=
    @evaluate (Spec (CommRingCat.of R)) G (coefficientTest R B) (coefficientTest R A)
      M.source M.hom q
  have hEqEval := congrArg E hcomp
  have hEval : evaluate (G := G) i₀ aCA = F.val :=
    hEvalComp.trans (hEqEval.trans M.evaluates)
  have hCfin₀ : C₀.FG := (Subalgebra.fg_iff_finiteType C₀).mpr hCfin
  have hCl : IsClosedSubgroup i₀ := by
    change IsClosedSubgroup ((baseChange c).map M.hom ≫
      (Descent.pullbackComparison b c d hcd G).hom)
    exact hj.comp_iso (Descent.pullbackComparison b c d hcd G)
  have hTorus : RelativeTorus.IsTorus K₀ := hT
  have out : AdmissibleCoefficientModel R A G F :=
    ⟨C₀, hCfin₀, K₀, i₀, hCl, hTorus, hEval⟩
  exact ⟨out⟩

end Langlands.GroupScheme.TorusSubgroupModuli
