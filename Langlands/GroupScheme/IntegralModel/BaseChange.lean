import Langlands.GroupScheme.IntegralModel
import Mathlib.Tactic.IrreducibleDef

/-! # Coefficient base change of actual integral models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

section PullbackSquare

variable {S T U V : Scheme.{u}}
  (b : T ⟶ S) (c : V ⟶ T) (d : U ⟶ S) (e : V ⟶ U)
  (h : c ≫ b = e ≫ d) (G : GroupScheme S)

private irreducible_def squareIso :
    (Langlands.GroupScheme.baseChange c).obj
        ((Langlands.GroupScheme.baseChange b).obj G) ≅
      (Langlands.GroupScheme.baseChange e).obj
        ((Langlands.GroupScheme.baseChange d).obj G) :=
  (baseChangeCompIso b c G).symm ≪≫
    eqToIso (congrArg (fun f => (Langlands.GroupScheme.baseChange f).obj G) h) ≪≫
      baseChangeCompIso d e G

private theorem compIso_hom_fst :
    (baseChangeCompIso b c G).hom.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom b) c ≫ pullback.fst G.X.hom b =
      pullback.fst G.X.hom (c ≫ b) := by
  have hi : (baseChangeCompIso b c G).inv.hom.hom.left ≫
      (baseChangeCompIso b c G).hom.hom.hom.left = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.left) (baseChangeCompIso b c G).inv_hom_id
  apply (cancel_epi (baseChangeCompIso b c G).inv.hom.hom.left).mp
  simp only [← Category.assoc, hi, Category.id_comp]
  exact (baseChangeCompIso_inv_fst b c G).symm

private theorem eqIso_fst {f g : V ⟶ S} (hfg : f = g) :
    (eqToIso (congrArg
      (fun k => (Langlands.GroupScheme.baseChange k).obj G) hfg)).hom.hom.hom.left ≫
        pullback.fst G.X.hom g = pullback.fst G.X.hom f := by
  subst g
  simp

private theorem squareIso_fst_fst :
    (squareIso b c d e h G).hom.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom d) e ≫ pullback.fst G.X.hom d =
      pullback.fst (pullback.snd G.X.hom b) c ≫ pullback.fst G.X.hom b := by
  rw [squareIso_def]
  change ((baseChangeCompIso b c G).inv.hom.hom.left ≫
      ((eqToIso (congrArg
        (fun k => (Langlands.GroupScheme.baseChange k).obj G) h)).hom.hom.hom.left ≫
          (baseChangeCompIso d e G).hom.hom.hom.left)) ≫ _ = _
  simp only [Category.assoc]
  rw [compIso_hom_fst, eqIso_fst G h, baseChangeCompIso_inv_fst]

private theorem squareIso_naturality {H : GroupScheme S} (f : G ⟶ H) :
    (Langlands.GroupScheme.baseChange c).map
        ((Langlands.GroupScheme.baseChange b).map f) ≫ (squareIso b c d e h H).hom =
      (squareIso b c d e h G).hom ≫
        (Langlands.GroupScheme.baseChange e).map
          ((Langlands.GroupScheme.baseChange d).map f) := by
  have heq {q q' : V ⟶ S} (hq : q = q') :
      (Langlands.GroupScheme.baseChange q).map f ≫
          (eqToIso (congrArg (fun k => (Langlands.GroupScheme.baseChange k).obj H) hq)).hom =
        (eqToIso (congrArg (fun k => (Langlands.GroupScheme.baseChange k).obj G) hq)).hom ≫
          (Langlands.GroupScheme.baseChange q').map f := by
    subst q'
    simp
  have hinv : (Langlands.GroupScheme.baseChange c).map
        ((Langlands.GroupScheme.baseChange b).map f) ≫ (baseChangeCompIso b c H).inv =
      (baseChangeCompIso b c G).inv ≫
        (Langlands.GroupScheme.baseChange (c ≫ b)).map f :=
    ((Functor.mapGrpNatIso (Over.pullbackComp c b)) ≪≫
      Functor.mapGrpCompIso).inv.naturality f
  have hhom : (Langlands.GroupScheme.baseChange (e ≫ d)).map f ≫
        (baseChangeCompIso d e H).hom =
      (baseChangeCompIso d e G).hom ≫ (Langlands.GroupScheme.baseChange e).map
        ((Langlands.GroupScheme.baseChange d).map f) :=
    ((Functor.mapGrpNatIso (Over.pullbackComp e d)) ≪≫
      Functor.mapGrpCompIso).hom.naturality f
  rw [squareIso_def, squareIso_def]
  change _ ≫ ((baseChangeCompIso b c H).inv ≫ _ ≫ (baseChangeCompIso d e H).hom) =
    ((baseChangeCompIso b c G).inv ≫ _ ≫ (baseChangeCompIso d e G).hom) ≫ _
  simp only [← Category.assoc]
  rw [hinv]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (baseChangeCompIso d e H).hom, heq h, Category.assoc, hhom]

private theorem section_comp (x : Over.mk (𝟙 S) ⟶ G.X) :
    baseChangeSectionHom c _ (baseChangeSectionHom b G x) ≫
        (baseChangeCompIso b c G).inv.hom.hom =
      baseChangeSectionHom (c ≫ b) G x := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change
      ((baseChangeSectionHom c _ (baseChangeSectionHom b G x)).left ≫
          (baseChangeCompIso b c G).inv.hom.hom.left) ≫
          pullback.fst G.X.hom (c ≫ b) =
        (baseChangeSectionHom (c ≫ b) G x).left ≫
          pullback.fst G.X.hom (c ≫ b)
    simp only [Category.assoc, baseChangeCompIso_inv_fst,
      baseChangeSectionHom_fst]
    have hc := baseChangeSectionHom_fst c
      ((Langlands.GroupScheme.baseChange b).obj G) (baseChangeSectionHom b G x)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ pullback.fst G.X.hom b) hc).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k => c ≫ k) (baseChangeSectionHom_fst b G x))))
  · exact (show
      ((baseChangeSectionHom c _ (baseChangeSectionHom b G x)).left ≫
          (baseChangeCompIso b c G).inv.hom.hom.left) ≫
          pullback.snd G.X.hom (c ≫ b) = 𝟙 _ from
        (baseChangeSectionHom c _ (baseChangeSectionHom b G x) ≫
          (baseChangeCompIso b c G).inv.hom.hom).w).trans
      (baseChangeSectionHom (c ≫ b) G x).w.symm

private theorem section_eq {f g : V ⟶ S} (hfg : f = g)
    (x : Over.mk (𝟙 S) ⟶ G.X) :
    baseChangeSectionHom f G x ≫
        (eqToIso (congrArg
          (fun k => (Langlands.GroupScheme.baseChange k).obj G) hfg)).hom.hom.hom =
      baseChangeSectionHom g G x := by
  subst g
  rfl

private theorem squareIso_section (x : Over.mk (𝟙 S) ⟶ G.X) :
    baseChangeSectionHom c _ (baseChangeSectionHom b G x) ≫
        (squareIso b c d e h G).hom.hom.hom =
      baseChangeSectionHom e _ (baseChangeSectionHom d G x) := by
  rw [squareIso_def]
  change
    (baseChangeSectionHom c _ (baseChangeSectionHom b G x) ≫
        (baseChangeCompIso b c G).inv.hom.hom) ≫
        ((eqToIso (congrArg
          (fun k => (Langlands.GroupScheme.baseChange k).obj G) h)).hom.hom.hom ≫
            (baseChangeCompIso d e G).hom.hom.hom) = _
  rw [← Category.assoc]
  rw [section_comp, section_eq G h]
  apply (cancel_mono (baseChangeCompIso d e G).inv.hom.hom).mp
  have hi : (baseChangeCompIso d e G).hom.hom.hom ≫
      (baseChangeCompIso d e G).inv.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) (baseChangeCompIso d e G).hom_inv_id
  rw [Category.assoc, hi, Category.comp_id]
  exact (section_comp d e G x).symm

private theorem squareIso_section_map
    {H : GroupScheme U} (f : (Langlands.GroupScheme.baseChange d).obj G ⟶ H)
    (x : Over.mk (𝟙 S) ⟶ G.X) :
    baseChangeSectionHom c _ (baseChangeSectionHom b G x) ≫
        ((squareIso b c d e h G).hom.hom.hom ≫
          ((Langlands.GroupScheme.baseChange e).map f).hom.hom) =
      baseChangeSectionHom e H (baseChangeSectionHom d G x ≫ f.hom.hom) := by
  rw [← Category.assoc]
  exact (congrArg (fun y => y ≫ ((Langlands.GroupScheme.baseChange e).map f).hom.hom)
    (squareIso_section b c d e h G x)).trans
      (baseChangeSectionHom_naturality e f (baseChangeSectionHom d G x)).symm

end PullbackSquare

section Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

omit [IsDomain R] [IsFractionRing R K] [IsDomain A] [IsFractionRing A L] in
private theorem coefficientSquare :
    Spec.algebraMap A L ≫ Spec.algebraMap R A =
      Spec.algebraMap K L ≫ Spec.algebraMap R K := by
  calc
    _ = Spec.algebraMap R L := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact (IsScalarTower.algebraMap_apply R A L x).symm
    _ = _ := by
      symm
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact (IsScalarTower.algebraMap_apply R K L x).symm

/-- The generic-fibre comparison for extension of integral coefficients. -/
def baseChangeGenericIso :
    (Langlands.GroupScheme.baseChange (Spec.algebraMap A L)).obj
        ((Langlands.GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group) ≅
      (Langlands.GroupScheme.baseChange (Spec.algebraMap K L)).obj G :=
  squareIso (Spec.algebraMap R A) (Spec.algebraMap A L)
      (Spec.algebraMap R K) (Spec.algebraMap K L)
      (coefficientSquare (R := R) (K := K) A L) M.group ≪≫
        (Langlands.GroupScheme.baseChange (Spec.algebraMap K L)).mapIso M.genericIso

/-- Extend the integral coefficients along a commuting square of fraction fields. -/
def baseChange : IntegralModel A L
    ((Langlands.GroupScheme.baseChange (Spec.algebraMap K L)).obj G) where
  group := (Langlands.GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group
  affine := MorphismProperty.pullback_snd _ _ M.affine
  flat := MorphismProperty.pullback_snd _ _ M.flat
  finiteType := MorphismProperty.pullback_snd _ _ M.finiteType
  genericIso := M.baseChangeGenericIso A L

-- The comparison is composed from the two actual pullback towers.
omit [IsDomain A] [IsFractionRing A L] in
private theorem baseChangeGenericIso_hom :
    (M.baseChangeGenericIso A L).hom.hom.hom =
      (squareIso (Spec.algebraMap R A) (Spec.algebraMap A L)
          (Spec.algebraMap R K) (Spec.algebraMap K L)
          (coefficientSquare (R := R) (K := K) A L) M.group).hom.hom.hom ≫
        ((Langlands.GroupScheme.baseChange (Spec.algebraMap K L)).map
          M.genericIso.hom).hom.hom := by
  simp only [baseChangeGenericIso, Iso.trans_hom, Functor.mapIso_hom,
    Grp.comp_hom_hom]

omit [IsDomain A] [IsFractionRing A L] in
/-- The specified generic comparison preserves projection to the original model. -/
theorem baseChangeGenericIso_hom_fst :
    (M.baseChangeGenericIso A L).hom.hom.hom.left ≫
        pullback.fst G.X.hom (Spec.algebraMap K L) ≫
          M.genericIso.inv.hom.hom.left ≫
            pullback.fst M.group.X.hom (Spec.algebraMap R K) =
      pullback.fst (pullback.snd M.group.X.hom (Spec.algebraMap R A))
          (Spec.algebraMap A L) ≫
        pullback.fst M.group.X.hom (Spec.algebraMap R A) := by
  have hi : M.genericIso.hom.hom.hom.left ≫ M.genericIso.inv.hom.hom.left = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.left) M.genericIso.hom_inv_id
  rw [baseChangeGenericIso_hom]
  change ((squareIso (Spec.algebraMap R A) (Spec.algebraMap A L)
      (Spec.algebraMap R K) (Spec.algebraMap K L)
      (coefficientSquare (R := R) (K := K) A L) M.group).hom.hom.hom.left ≫
        ((Over.pullback (Spec.algebraMap K L)).map M.genericIso.hom.hom.hom).left) ≫
      _ = _
  simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst_assoc]
  rw [← Category.assoc M.genericIso.hom.hom.hom.left, hi, Category.id_comp]
  exact squareIso_fst_fst _ _ _ _ _ _

omit [IsDomain A] [IsFractionRing A L] in
/-- The coefficient-square generic comparisons commute with every model homomorphism. -/
theorem baseChangeGenericIso_naturality
    {H : GroupScheme (Spec (CommRingCat.of K))} (N : IntegralModel R K H)
    {f : G ⟶ H} (φ : M.Hom N f) :
    (Langlands.GroupScheme.baseChange (Spec.algebraMap A L)).map
        ((Langlands.GroupScheme.baseChange (Spec.algebraMap R A)).map φ.hom) ≫
        (N.baseChangeGenericIso A L).hom =
      (M.baseChangeGenericIso A L).hom ≫
        (Langlands.GroupScheme.baseChange (Spec.algebraMap K L)).map f := by
  unfold baseChangeGenericIso
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, squareIso_naturality, Category.assoc, ← Functor.map_comp,
    φ.generic_comm, Functor.map_comp, Category.assoc]

/-- Smoothness of the original model is preserved by the actual pullback. -/
theorem isSmooth_baseChange (hM : M.IsSmooth) : (M.baseChange A L).IsSmooth := by
  have : Smooth M.group.X.hom := hM
  change Smooth (pullback.snd M.group.X.hom (Spec.algebraMap R A))
  infer_instance

omit [IsDomain A] [IsFractionRing A L] in
private theorem baseChangeGenericIso_section (x : M.integralSections) :
    baseChangeSectionHom (Spec.algebraMap A L)
        ((Langlands.GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group)
        (baseChangeSectionHom (Spec.algebraMap R A) M.group x) ≫
        (M.baseChangeGenericIso A L).hom.hom.hom =
      baseChangeSectionHom (Spec.algebraMap K L) G
        (baseChangeSectionHom (Spec.algebraMap R K) M.group x ≫
          M.genericIso.hom.hom.hom) := by
  rw [baseChangeGenericIso_hom]
  exact squareIso_section_map
    (Spec.algebraMap R A) (Spec.algebraMap A L)
    (Spec.algebraMap R K) (Spec.algebraMap K L)
    (coefficientSquare (R := R) (K := K) A L) M.group M.genericIso.hom x

/-- Restriction of an integral section commutes with its specified generic evaluation. -/
theorem baseChange_integralPointMap (x : M.integralSections) :
    (M.baseChange A L).integralPointMap
        (baseChangeSectionHom (Spec.algebraMap R A) M.group x) =
      baseChangeSectionHom (Spec.algebraMap K L) G (M.integralPointMap x) := by
  change baseChangeSectionHom (Spec.algebraMap A L)
      ((Langlands.GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group)
      (baseChangeSectionHom (Spec.algebraMap R A) M.group x) ≫
        (M.baseChangeGenericIso A L).hom.hom.hom = _
  exact M.baseChangeGenericIso_section A L x

/-- Extension of a generic point represented by an integral section stays integral. -/
theorem baseChange_map_mem_integralPoints {g : rationalPoints G}
    (hg : g ∈ M.integralPoints) :
    baseChangeSectionHom (Spec.algebraMap K L) G g ∈
      (M.baseChange A L).integralPoints := by
  obtain ⟨x, rfl⟩ := hg
  exact ⟨baseChangeSectionHom (Spec.algebraMap R A) M.group x,
    M.baseChange_integralPointMap A L x⟩

end Coefficients

end Langlands.GroupScheme.IntegralModel
