import Langlands.GroupScheme.Torus.FiniteModel
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport
import Langlands.GroupScheme.Descent.GaloisClosedSubgroups
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Finite-model descent from geometric Frobenius invariance -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

private theorem descentPoint_fst {B S : Scheme.{u}}
    (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (G : GroupScheme B)
    (U : Over S) (x : U ⟶ ((baseChange b).obj G).X) :
    (descentPoint b a ha G U x).left ≫ pullback.fst G.X.hom b =
      x.left ≫ pullback.fst G.X.hom b := by
  have h := congrArg (fun z => z.left) (baseChangePointsEquiv_descentPoint b a ha G U x)
  change (descentPoint b a ha G U x).left ≫ pullback.fst G.X.hom b =
    (𝟙 U.left) ≫ (x.left ≫ pullback.fst G.X.hom b) at h
  simpa only [Category.id_comp] using h

private theorem descentTransport_tower {B S S' : Scheme.{u}}
    (b : S ⟶ B) (c : S' ⟶ S) (d : S' ⟶ B)
    (a : S ⟶ S) (ha : a ≫ b = b)
    (a' : S' ⟶ S') (ha' : a' ≫ d = d) (hc : a' ≫ c = c ≫ a)
    (G : GroupScheme B)
    (e : (baseChange d).obj G ≅ (baseChange c).obj ((baseChange b).obj G))
    (he : e.hom.hom.hom.left ≫ pullback.fst ((baseChange b).obj G).X.hom c ≫
      pullback.fst G.X.hom b = pullback.fst G.X.hom d)
    (F : SubgroupFunctor ((baseChange b).obj G)) :
    SubgroupFunctor.descentTransport d a' ha' G ((F.baseChange c).comap e.hom) =
      ((SubgroupFunctor.descentTransport b a ha G F).baseChange c).comap e.hom := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.mem_descentTransport_iff_descentPoint,
    SubgroupFunctor.mem_comap, SubgroupFunctor.mem_baseChange,
    SubgroupFunctor.mem_comap, SubgroupFunctor.mem_baseChange,
    SubgroupFunctor.mem_descentTransport_iff_descentPoint]
  let v : (Over.map c).obj ((Over.map a').obj U) ≅
      (Over.map a).obj ((Over.map c).obj U) :=
    Over.isoMk (Iso.refl _) (by simp [Category.assoc, hc])
  have hp : v.hom ≫ descentPoint b a ha G ((Over.map c).obj U)
      (baseChangePointsEquiv c ((baseChange b).obj G) U (x ≫ e.hom.hom.hom)) =
      baseChangePointsEquiv c ((baseChange b).obj G) ((Over.map a').obj U)
        (descentPoint d a' ha' G U x ≫ e.hom.hom.hom) := by
    apply (baseChangePointsEquiv b G ((Over.map c).obj ((Over.map a').obj U))).injective
    rw [baseChangePointsEquiv_naturality]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.map_map_left, v, Over.isoMk_hom_left,
      Iso.refl_hom, baseChangePointsEquiv_left,
      descentPoint_fst, Category.assoc, he]
    change (𝟙 U.left) ≫ _ = _
    exact Category.id_comp _
  rw [← hp]
  constructor
  · intro hx
    simpa only [Iso.inv_hom_id_assoc] using F.comp_mem v.inv hx
  · exact F.comp_mem v.hom

private theorem closed_range_eq_of_baseChange_eq {S S' : Scheme.{u}}
    (c : S' ⟶ S) [QuasiCompact c] [Flat c] [Surjective c]
    {G H K : GroupScheme S} (i : H ⟶ G) (j : K ⟶ G)
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (h : (SubgroupFunctor.range i).baseChange c =
      (SubgroupFunctor.range j).baseChange c) :
    SubgroupFunctor.range i = SubgroupFunctor.range j := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  exact SubgroupFunctor.range_eq_of_baseChange_eq c i j h

private theorem finiteStage_comparison_projection
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (E : Langlands.AlgebraicGeometry.Picard.FinIntermediateField k Ω)
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    (Descent.FiniteStage.comparison k Ω E G).hom.hom.hom.left ≫
        pullback.fst ((baseChange (algebraBaseMap k E.1)).obj G).X.hom
          (algebraBaseMap E.1 Ω) ≫ pullback.fst G.X.hom (algebraBaseMap k E.1) =
      pullback.fst G.X.hom (algebraBaseMap k Ω) := by
  change (Descent.FiniteStage.comparison k Ω E G).hom.hom.hom.left ≫
    pullback.fst (pullback.snd G.X.hom (algebraBaseMap k E.1))
      (algebraBaseMap E.1 Ω) ≫ pullback.fst G.X.hom (algebraBaseMap k E.1) = _
  rw [← Category.assoc, Descent.FiniteStage.comparison_hom_fst]
  simp [Langlands.AlgebraicGeometry.Picard.baseChangeCone]

private theorem frobeniusBaseMap_tower
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    [Fintype k] [Algebra.IsAlgebraic k Ω]
    (E : Langlands.AlgebraicGeometry.Picard.FinIntermediateField k Ω) :
    galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ≫
        algebraBaseMap E.1 Ω =
      algebraBaseMap E.1 Ω ≫
        galoisBaseMap k E.1 (FiniteField.frobeniusAlgEquivOfAlgebraic k E.1) := by
  unfold galoisBaseMap algebraBaseMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

namespace TorusFiniteModel

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
variable {T : CommGroupScheme (Spec (CommRingCat.of Ω))}
variable {i : T.toGrp ⟶ (baseChange (algebraBaseMap k Ω)).obj G}

/-- The finite model recovers the specified subgroup on every relative test. -/
theorem Model.range_baseChange_comap_comparison (D : Model k Ω i) :
    ((SubgroupFunctor.range D.inclusion).baseChange
      (algebraBaseMap D.fieldOfDefinition.1 Ω)).comap
        (Descent.FiniteStage.comparison k Ω D.fieldOfDefinition G).hom =
      SubgroupFunctor.range i := by
  rw [← SubgroupFunctor.range_baseChangeHom, D.comparison,
    SubgroupFunctor.range_iso_comp,
    SubgroupFunctor.range_comp_iso, ← SubgroupFunctor.comap_comp,
    Iso.hom_inv_id, SubgroupFunctor.comap_id]

/-- Geometric all-test Frobenius invariance reflects to the finite model. -/
theorem Model.frobeniusInvariant [Fintype k] [Algebra.IsAlgebraic k Ω]
    (D : Model k Ω i)
    (h : SubgroupFunctor.galoisTransport k Ω G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (SubgroupFunctor.range i) =
        SubgroupFunctor.range i) :
    SubgroupFunctor.galoisTransport k D.fieldOfDefinition.1 G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k D.fieldOfDefinition.1)
        (SubgroupFunctor.range D.inclusion) = SubgroupFunctor.range D.inclusion := by
  let E := D.fieldOfDefinition
  let b := algebraBaseMap k E.1
  let c := algebraBaseMap E.1 Ω
  let a := galoisBaseMap k E.1 (FiniteField.frobeniusAlgEquivOfAlgebraic k E.1)
  let ha := galoisBaseMap_over k E.1 (FiniteField.frobeniusAlgEquivOfAlgebraic k E.1)
  let e := Descent.FiniteStage.comparison k Ω E G
  have ht := descentTransport_tower b c (algebraBaseMap k Ω) a ha
    (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
    (galoisBaseMap_over k Ω _) (frobeniusBaseMap_tower k Ω E)
    G e (finiteStage_comparison_projection k Ω E G) (SubgroupFunctor.range D.inclusion)
  change SubgroupFunctor.galoisTransport k Ω G _
      (((SubgroupFunctor.range D.inclusion).baseChange c).comap e.hom) =
    ((SubgroupFunctor.galoisTransport k E.1 G _
      (SubgroupFunctor.range D.inclusion)).baseChange c).comap e.hom at ht
  rw [D.range_baseChange_comap_comparison, h] at ht
  have hcom : ((SubgroupFunctor.galoisTransport k E.1 G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k E.1)
      (SubgroupFunctor.range D.inclusion)).baseChange c).comap e.hom =
        ((SubgroupFunctor.range D.inclusion).baseChange c).comap e.hom :=
    ht.symm.trans D.range_baseChange_comap_comparison.symm
  have hb := congrArg (fun F => F.comap e.inv) hcom
  simp only [← SubgroupFunctor.comap_comp, Iso.inv_hom_id,
    SubgroupFunctor.comap_id] at hb
  let j := (baseChange a).map D.inclusion ≫ (descentBaseChangeIso b a ha G).hom
  have hj : IsClosedSubgroup j :=
    (D.isClosedSubgroup.baseChange a).comp_iso (descentBaseChangeIso b a ha G)
  have hfpqc := fieldExtension_fpqc E.1 Ω
  let : Surjective c := hfpqc.1
  let : Flat c := hfpqc.2.1
  let : QuasiCompact c := hfpqc.2.2
  change (SubgroupFunctor.descentTransport b a ha G
      (SubgroupFunctor.range D.inclusion)).baseChange c = _ at hb
  rw [SubgroupFunctor.descentTransport_range] at hb
  change SubgroupFunctor.descentTransport b a ha G
      (SubgroupFunctor.range D.inclusion) = _
  rw [SubgroupFunctor.descentTransport_range]
  exact closed_range_eq_of_baseChange_eq c j D.inclusion hj D.isClosedSubgroup hb

/-- Descend the actual finite model by finite-field Frobenius generation. -/
def Model.descentOfFrobenius [Fintype k] [Algebra.IsAlgebraic k Ω]
    [IsAffineHom G.X.hom] (D : Model k Ω i)
    (h : SubgroupFunctor.galoisTransport k Ω G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (SubgroupFunctor.range i) =
        SubgroupFunctor.range i) : TorusDescent D.inclusion := by
  let : FiniteDimensional k D.fieldOfDefinition.1 := D.fieldOfDefinition.2
  let : Finite D.fieldOfDefinition.1 := Finite.of_injective _
    (Module.finBasis k D.fieldOfDefinition.1).equivFun.injective
  have hf := D.frobeniusInvariant h
  change SubgroupFunctor.descentTransport _ _ _ _ _ = _ at hf
  rw [SubgroupFunctor.descentTransport_range] at hf
  exact D.isSplitTorus.isTorus.descentOfOverlapRangeEq D.isClosedSubgroup
    (D.isClosedSubgroup.overlap_range_eq_of_galois_range_eq
      (SubgroupFunctor.galois_range_eq_of_frobenius_range_eq
        k D.fieldOfDefinition.1 G D.inclusion hf))

end TorusFiniteModel

end Langlands.GroupScheme
