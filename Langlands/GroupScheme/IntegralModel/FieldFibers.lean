import Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreadingStatement
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Field fibres of simultaneous reductive and parabolic models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading

/-- The three field-valued conditions on one actual subgroup homomorphism.
The base change in every field uses the algebra structure being quantified over. -/
structure GoodFieldFibers {R : Type u} [CommRing R]
    {G P : GroupScheme (Spec (CommRingCat.of R))} (p : P ⟶ G) : Prop where
  reductive : ∀ (k : Type u) [Field k] [Algebra R k],
    IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj G)
  parabolic : ∀ (k : Type u) [Field k] [Algebra R k],
    IsParabolicSubgroup ((baseChange (Spec.algebraMap R k)).map p)
  connected : ∀ (k : Type u) [Field k] [Algebra R k],
    ConnectedSpace (((baseChange (Spec.algebraMap R k)).obj P).X.left)

namespace GoodFieldFibers

variable {R : Type u} [CommRing R]
  {G P : GroupScheme (Spec (CommRingCat.of R))} {p : P ⟶ G}

/-- Testing all algebra structures also tests every actual field-valued scheme map. -/
theorem atFieldPoint (h : GoodFieldFibers p) (k : Type u) [Field k]
    (f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    IsConnectedReductive ((baseChange f).obj G) ∧
      IsParabolicSubgroup ((baseChange f).map p) ∧
      ConnectedSpace (((baseChange f).obj P).X.left) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  let : Algebra R k := φ.hom.toAlgebra
  exact ⟨h.reductive k, h.parabolic k, h.connected k⟩

/-- Smooth affine models with these field fibres satisfy the exact geometric-fibre
predicate used in `IsReductive`. -/
theorem isReductive (h : GoodFieldFibers p) (hSmooth : Smooth G.X.hom)
    (hAffine : IsAffineHom G.X.hom) : IsReductive G where
  smooth := hSmooth
  isAffineHom := hAffine
  geometricFiber s := (h.atFieldPoint _ (geometricPoint _ s)).1.isPseudoReductive

/-- Pullback composition is natural in the supplied homomorphism. -/
private theorem baseChangeCompIso_naturality {S S' S'' : Scheme.{u}}
    (a : S' ⟶ S) (b : S'' ⟶ S') {H K : GroupScheme S} (i : H ⟶ K) :
    (baseChange (b ≫ a)).map i ≫ (baseChangeCompIso a b K).hom =
      (baseChangeCompIso a b H).hom ≫
        (baseChange b).map ((baseChange a).map i) := by
  exact ((Functor.mapGrpNatIso (Over.pullbackComp b a)) ≪≫
    Functor.mapGrpCompIso).hom.naturality i

/-- The field-valued conditions persist after any change of affine coefficient base. -/
theorem baseChange (h : GoodFieldFibers p) {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) :
    GoodFieldFibers ((GroupScheme.baseChange a).map p) := by
  constructor
  · intro k _ _
    let b := Spec.algebraMap A k
    exact (h.atFieldPoint k (b ≫ a)).1.of_iso (baseChangeCompIso a b G).symm
  · intro k _ _
    let b := Spec.algebraMap A k
    have hp := ((h.atFieldPoint k (b ≫ a)).2.1.iso_comp
      (baseChangeCompIso a b P).symm).comp_iso (baseChangeCompIso a b G)
    have he : (baseChangeCompIso a b P).inv ≫
        (GroupScheme.baseChange (b ≫ a)).map p ≫ (baseChangeCompIso a b G).hom =
        (GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map p) := by
      rw [baseChangeCompIso_naturality, Iso.inv_hom_id_assoc]
    simp only [Iso.symm_hom, Category.assoc] at hp
    rwa [he] at hp
  · intro k _ _
    let b := Spec.algebraMap A k
    exact (Scheme.homeoOfIso ((Grp.forget _ ⋙ Over.forget _).mapIso
      (baseChangeCompIso a b P))).connectedSpace_iff.1 (h.atFieldPoint k (b ≫ a)).2.2

end GoodFieldFibers

/-- Extract exactly the three field conditions from the published model record. -/
theorem ModelData.goodFieldFibers {R F : Type u} [CommRing R] [IsDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    {G P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
    (M : ModelData R F p) : GoodFieldFibers M.inclusion.hom :=
  ⟨M.fieldReductive, M.fieldParabolic, M.fieldConnected⟩

end Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading
