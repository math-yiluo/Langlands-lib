import Langlands.GroupScheme.SimplyConnected.DerivedCoverSplitTorusStatement
import Langlands.GroupScheme.Derived.MaximalSplitTorusStatement
import Langlands.GroupScheme.SimplyConnected.SplitTorusStatement
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacter
import Langlands.GroupScheme.Rational.SplitCentralEmbedding

/-! # Assembling maximal split tori through a simply connected derived cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

namespace RealTorusSpace

variable {k : Type u} [Field k]
  {A B T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Postcomposition on actual integral cocharacters preserves composition. -/
@[simp] theorem cocharacterMapInt_comp (f : A ⟶ B) (e : B ⟶ T) :
    cocharacterMapInt (f ≫ e) = (cocharacterMapInt e).comp (cocharacterMapInt f) := by
  ext ν
  exact (Category.assoc ν f e).symm

/-- Real scalar extension of actual postcomposition preserves composition. -/
@[simp] theorem cocharacterMapReal_comp (f : A ⟶ B) (e : B ⟶ T) :
    cocharacterMapReal (f ≫ e) = (cocharacterMapReal e).comp (cocharacterMapReal f) := by
  unfold cocharacterMapReal
  rw [cocharacterMapInt_comp, LinearMap.baseChange_comp]

/-- Rational scalar extension is injective for a scheme monomorphism. -/
theorem cocharacterMapInt_baseChange_rat_injective (e : B ⟶ T)
    [Mono (CommGroupScheme.groupHom e).hom.hom.left] :
    Function.Injective ((cocharacterMapInt e).baseChange ℚ) := by
  simpa only [LinearMap.baseChange_eq_ltensor] using
    Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ)
      (cocharacterMapInt e) (cocharacterMapInt_injective e)

/-- A map bijective on rational and real cocharacters followed by a closed embedding is
injective on those spaces, with the same range as that embedding. -/
theorem cocharacterMap_comp_injective_range (f : A ⟶ B) (e : B ⟶ T)
    (he : IsClosedSubgroup (CommGroupScheme.groupHom e))
    (hq : Function.Bijective ((cocharacterMapInt f).baseChange ℚ))
    (hr : Function.Bijective (cocharacterMapReal f)) :
    Function.Injective ((cocharacterMapInt (f ≫ e)).baseChange ℚ) ∧
      LinearMap.range ((cocharacterMapInt (f ≫ e)).baseChange ℚ) =
        LinearMap.range ((cocharacterMapInt e).baseChange ℚ) ∧
      Function.Injective (cocharacterMapReal (f ≫ e)) ∧
      LinearMap.range (cocharacterMapReal (f ≫ e)) =
        LinearMap.range (cocharacterMapReal e) := by
  have : IsClosedImmersion (CommGroupScheme.groupHom e).hom.hom.left := he
  rw [cocharacterMapInt_comp, LinearMap.baseChange_comp, cocharacterMapReal_comp]
  exact ⟨(cocharacterMapInt_baseChange_rat_injective e).comp hq.1,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hq.2),
    (cocharacterMapReal_injective e).comp hr.1,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hr.2)⟩

end RealTorusSpace

/-- The three structural inputs used by the derived-cover assembly. -/
def SimplyConnectedDerivedCoverSplitTorusPremises : Prop :=
  DerivedMaximalSplitTorusStatement.{u} ∧
    SimplyConnectedCoverSplitTorusStatement.{u} ∧
    SplitTorusIsogenyCocharacterStatement.{u}

/-- The derived-torus, covering-torus and split-isogeny statements together imply the
published derived-cover split-torus statement on the actual cocharacter maps. -/
theorem simplyConnectedDerivedCoverSplitTorusStatement_of_inputs
    (hderived : DerivedMaximalSplitTorusStatement.{u})
    (hcover : SimplyConnectedCoverSplitTorusStatement.{u})
    (hisogeny : SplitTorusIsogenyCocharacterStatement.{u}) :
    SimplyConnectedDerivedCoverSplitTorusStatement.{u} := by
  intro k _ G D C d π h S i hi
  obtain ⟨S_D, j, e, hj, he, hjd⟩ :=
    hderived k G D d h.isConnectedReductive h.isDerivedSubgroup S i hi
  obtain ⟨S_C, i_C, f, hi_C, hf, hfiso⟩ :=
    hcover k D C π h.isSimplyConnectedCover S_D j hj
  obtain ⟨-, -, hq, hr⟩ := hisogeny k S_C S_D f hi_C.1.1 hj.1.1 hfiso.isIsogeny
  refine ⟨S_D, j, e, hj, he, hjd, S_C, i_C, f, hi_C, hf, hfiso, ?_,
    RealTorusSpace.cocharacterMap_comp_injective_range f e he hq hr⟩
  calc
    i_C ≫ π ≫ d = (i_C ≫ π) ≫ d := (Category.assoc _ _ _).symm
    _ = (CommGroupScheme.groupHom f ≫ j) ≫ d := by rw [hf]
    _ = CommGroupScheme.groupHom f ≫ (CommGroupScheme.groupHom e ≫ i) := by
      rw [Category.assoc, hjd]
    _ = CommGroupScheme.groupHom (f ≫ e) ≫ i := (Category.assoc _ _ _).symm

/-- The bundled form of the conditional assembly. -/
theorem SimplyConnectedDerivedCoverSplitTorusPremises.statement
    (h : SimplyConnectedDerivedCoverSplitTorusPremises.{u}) :
    SimplyConnectedDerivedCoverSplitTorusStatement.{u} :=
  simplyConnectedDerivedCoverSplitTorusStatement_of_inputs h.1 h.2.1 h.2.2

end Langlands.GroupScheme
