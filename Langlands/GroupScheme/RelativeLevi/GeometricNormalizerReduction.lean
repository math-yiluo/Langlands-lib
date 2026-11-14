import Langlands.GroupScheme.RelativeLevi.ConjugatorUniquenessBaseChange
import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Absolute.ParabolicFieldExtensionProof
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange
import Langlands.GroupScheme.RelativeSelfNormalizerProof

/-! # Geometric-fibre reduction for relative Levi self-normalization -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

section BaseChange

variable {S S' S'' : Scheme.{u}} {P L U G : GroupScheme S}

private theorem pullbackComp_naturality (b : S' ⟶ S) (c : S'' ⟶ S') (i : P ⟶ G) :
    (GroupScheme.baseChange (c ≫ b)).map i ≫ (baseChangeCompIso b c G).hom =
      (baseChangeCompIso b c P).hom ≫
        (GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map i) :=
  ((Functor.mapGrpNatIso (Over.pullbackComp c b)) ≪≫
    Functor.mapGrpCompIso).hom.naturality i

/-- Self-normalization is compatible with composing two changes of base. -/
theorem normalizer_eq_baseChange_comp_iff (b : S' ⟶ S) (c : S'' ⟶ S') (l : L ⟶ P) :
    (SubgroupFunctor.range ((GroupScheme.baseChange (c ≫ b)).map l)).normalizer =
        SubgroupFunctor.range ((GroupScheme.baseChange (c ≫ b)).map l) ↔
      (SubgroupFunctor.range ((GroupScheme.baseChange c).map
        ((GroupScheme.baseChange b).map l))).normalizer =
        SubgroupFunctor.range ((GroupScheme.baseChange c).map
          ((GroupScheme.baseChange b).map l)) := by
  constructor
  · intro h
    refine le_antisymm (fun T => ?_) (SubgroupFunctor.le_normalizer _)
    apply (SubgroupFunctor.normalizer_carrier_le_iff_baseChange c _ T).2
    apply (SubgroupFunctor.normalizer_carrier_le_iff_baseChange b l _).2
    apply SubgroupFunctor.normalizer_carrier_le_of_iso l ((Over.mapComp c b).app T)
    exact (SubgroupFunctor.normalizer_carrier_le_iff_baseChange (c ≫ b) l T).1
      (le_of_eq (congrArg (fun F => F.carrier T) h))
  · intro h
    refine le_antisymm (fun T => ?_) (SubgroupFunctor.le_normalizer _)
    apply (SubgroupFunctor.normalizer_carrier_le_iff_baseChange (c ≫ b) l T).2
    apply SubgroupFunctor.normalizer_carrier_le_of_iso l ((Over.mapComp c b).app T).symm
    apply (SubgroupFunctor.normalizer_carrier_le_iff_baseChange b l _).1
    exact (SubgroupFunctor.normalizer_carrier_le_iff_baseChange c _ T).1
      (le_of_eq (congrArg (fun F => F.carrier T) h))

end BaseChange

section GeometricComplement

variable {S : Scheme.{u}} {G P L : GroupScheme S} {i : P ⟶ G} {l : L ⟶ P}

/-- The canonical geometric fibre of a relative parabolic is parabolic. -/
theorem isParabolicSubgroup_geometricFiber (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (s : S) :
    IsParabolicSubgroup (geometricFiberHom i s) := by
  let a := S.fromSpecResidueField s
  let b := toAlgebraicClosure (S.residueField s)
  have hp := parabolicFieldExtensionStatement (S.residueField s)
    (AlgebraicClosure (S.residueField s)) ((GroupScheme.baseChange a).obj G)
    (hG.isConnectedReductive_residueFiber s) _ _ (hi.residueFiber s)
  have h := (hp.iso_comp (baseChangeCompIso a b P)).comp_iso
    (baseChangeCompIso a b G).symm
  change IsParabolicSubgroup ((baseChangeCompIso a b P).hom ≫
    (GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map i) ≫
      (baseChangeCompIso a b G).inv) at h
  rw [← Category.assoc, ← pullbackComp_naturality a b i, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] at h
  exact h

/-- An actual complement on the canonical geometric fibre, retaining the radical,
its inclusion and the original multiplication isomorphism. -/
structure GeometricComplement (i : P ⟶ G) (l : L ⟶ P) (s : S) where
  radical : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure (S.residueField s))))
  radicalHom : radical ⟶ geometricFiber P s
  ambientReductive : IsConnectedReductive (geometricFiber G s)
  parabolic : IsParabolicSubgroup (geometricFiberHom i s)
  unipotentRadical : IsUnipotentRadical radicalHom
  multiplication : IsIso (subgroupMultiplication (geometricFiberHom l s) radicalHom)

/-- Pull the supplied relative Levi decomposition to its actual geometric fibre. -/
def geometricComplement (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hl : IsRelativeLeviSubgroup l) (s : S) : GeometricComplement i l s := by
  let U := Classical.choose hl.exists_unipotentRadical
  let r := Classical.choose (Classical.choose_spec hl.exists_unipotentRadical)
  have hr := Classical.choose_spec (Classical.choose_spec hl.exists_unipotentRadical)
  let := hr.2
  exact ⟨geometricFiber U s, geometricFiberHom r s,
    hG.isConnectedReductive_baseChange (geometricPoint S s),
    isParabolicSubgroup_geometricFiber hG hi s, hr.1.geometricFiber s,
    isIso_subgroupMultiplication_baseChange (geometricPoint S s) l r⟩

end GeometricComplement

section Detection

variable {S : Scheme.{u}} {P L : GroupScheme S} (l : L ⟶ P)

/-- Geometric-fibre equality descends to the actual residue-field fibres. -/
theorem normalizer_eq_residueFiber_of_geometricFiber
    (hl : IsClosedSubgroup l)
    (hgeom : ∀ s : S,
      (SubgroupFunctor.range (geometricFiberHom l s)).normalizer =
        SubgroupFunctor.range (geometricFiberHom l s)) (s : S) :
    (SubgroupFunctor.range (residueFiberHom l s)).normalizer =
      SubgroupFunctor.range (residueFiberHom l s) := by
  let b := toAlgebraicClosure (S.residueField s)
  obtain ⟨hs, hf, hqc⟩ := fieldExtension_fpqc (S.residueField s)
    (AlgebraicClosure (S.residueField s))
  let := hs
  let := hf
  let := hqc
  let : IsClosedImmersion (residueFiberHom l s).hom.hom.left :=
    hl.baseChange (S.fromSpecResidueField s)
  let : Mono (residueFiberHom l s).hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.normalizer_eq_of_baseChange_eq b (residueFiberHom l s)
  rw [← SubgroupFunctor.range_baseChangeHom]
  exact (normalizer_eq_baseChange_comp_iff (S.fromSpecResidueField s) b l).1 (hgeom s)

/-- Equality on residue fibres implies equality after every field-valued base change. -/
theorem normalizer_eq_fieldPoint_of_residueFiber
    (hres : ∀ s : S,
      (SubgroupFunctor.range (residueFiberHom l s)).normalizer =
        SubgroupFunctor.range (residueFiberHom l s))
    {k : Type u} [Field k] (f : Spec (CommRingCat.of k) ⟶ S) :
    (SubgroupFunctor.range ((GroupScheme.baseChange f).map l)).normalizer =
      SubgroupFunctor.range ((GroupScheme.baseChange f).map l) := by
  let s := f (IsLocalRing.closedPoint k)
  let φ : S.residueField s ⟶ CommRingCat.of k :=
    S.descResidueField (Scheme.stalkClosedPointTo f)
  have hd : (SubgroupFunctor.range ((GroupScheme.baseChange (Spec.map φ)).map
      (residueFiberHom l s))).normalizer =
      SubgroupFunctor.range ((GroupScheme.baseChange (Spec.map φ)).map
        (residueFiberHom l s)) := by
    rw [SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.normalizer_baseChange, hres s]
  have h := (normalizer_eq_baseChange_comp_iff (S.fromSpecResidueField s) (Spec.map φ) l).2 hd
  have he : Spec.map φ ≫ S.fromSpecResidueField s = f :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S f
  rwa [he] at h

/-- For a smooth closed subgroup of a smooth affine group, canonical geometric
fibres suffice to detect self-normalization on every test scheme. -/
theorem normalizer_eq_of_geometricFiber [IsAffineHom P.X.hom]
    (hl : IsClosedSubgroup l) (hP : Smooth P.X.hom) (hL : Smooth L.X.hom)
    (hgeom : ∀ s : S,
      (SubgroupFunctor.range (geometricFiberHom l s)).normalizer =
        SubgroupFunctor.range (geometricFiberHom l s)) :
    (SubgroupFunctor.range l).normalizer = SubgroupFunctor.range l := by
  let : IsClosedImmersion l.hom.hom.left := hl
  let : Mono l.hom.hom := Over.mono_of_mono_left _
  have hfield : ∀ (k : Type u) [Field k] (f : Spec (CommRingCat.of k) ⟶ S),
      (SubgroupFunctor.range ((GroupScheme.baseChange f).map l)).normalizer =
        SubgroupFunctor.range ((GroupScheme.baseChange f).map l) :=
    fun _ _ f => normalizer_eq_fieldPoint_of_residueFiber l
      (normalizer_eq_residueFiber_of_geometricFiber l hl hgeom) f
  refine le_antisymm (fun T x hx => ?_) (SubgroupFunctor.le_normalizer _)
  apply SubgroupFunctor.mem_range_of_affineCover l x
  intro j
  exact SubgroupFunctor.normalizer_carrier_le_of_isAffine l hl hP hL
    (SubgroupFunctor.normalizer_carrier_le_of_fieldPoint l hfield) _
    (Scheme.isAffine_affineCover _ j) ((SubgroupFunctor.range l).normalizer.comp_mem _ hx)

end Detection

end Langlands.GroupScheme.RelativeLevi
