import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.LeviFactorization
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Actual central split tori inside maximal split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme

namespace RealTorusSpace

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A scheme monomorphism is injective on the actual integral cocharacter lattices. -/
theorem cocharacterMapInt_injective (f : A ⟶ T)
    [Mono (CommGroupScheme.groupHom f).hom.hom.left] :
    Function.Injective (cocharacterMapInt f) := by
  intro ν μ h
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_mono (CommGroupScheme.groupHom f).hom.hom.left).mp
    (congrArg (fun z : cocharacterLattice T =>
      (CommGroupScheme.groupHom z).hom.hom.left) h)

/-- Real scalar extension preserves the injectivity of a scheme monomorphism
on actual cocharacters. -/
theorem cocharacterMapReal_injective (f : A ⟶ T)
    [Mono (CommGroupScheme.groupHom f).hom.hom.left] :
    Function.Injective (cocharacterMapReal f) := by
  simpa only [cocharacterMapReal, LinearMap.baseChange_eq_ltensor] using
    Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
      (cocharacterMapInt f) (cocharacterMapInt_injective f)

end RealTorusSpace

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every actual central split torus has a closed commutative-group-scheme
embedding into every maximal split torus, compatibly with the ambient maps. -/
theorem IsCentralSplitTorus.exists_commFactor_of_isMaximalSplitTorus
    [IsAffineHom G.X.hom] {a : A.toGrp ⟶ G} (ha : IsCentralSplitTorus a)
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) :
    ∃ f : A ⟶ T,
      CommGroupScheme.groupHom f ≫ i = a ∧
      IsClosedSubgroup (CommGroupScheme.groupHom f) ∧
      Function.Injective (cocharacterMapReal f) := by
  have hGid : IsClosedSubgroup (𝟙 G) := by
    change IsClosedImmersion (𝟙 G.X.left)
    infer_instance
  have himax : IsMaximalSplitTorus (i ≫ 𝟙 G) := by simpa using hi
  obtain ⟨g, hg⟩ := ha.exists_factor_of_isMaximalSplitTorus hGid himax
  let f : A ⟶ T := Additive.ofMul g
  have hf : CommGroupScheme.groupHom f ≫ i = a := hg
  have hfc : IsClosedSubgroup (CommGroupScheme.groupHom f) :=
    IsClosedSubgroup.of_comp hi.1.2 (by rw [hf]; exact ha.1.2)
  have : IsClosedImmersion (CommGroupScheme.groupHom f).hom.hom.left := hfc
  exact ⟨f, hf, hfc, cocharacterMapReal_injective f⟩

/-- The closed actual embedding and real-cocharacter injectivity for every
supplied split component, without choosing a new component. -/
theorem IsSplitComponent.exists_commFactor_of_isMaximalSplitTorus
    [IsAffineHom G.X.hom] {a : A.toGrp ⟶ G} (ha : IsSplitComponent a)
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) :
    ∃ f : A ⟶ T,
      CommGroupScheme.groupHom f ≫ i = a ∧
      IsClosedSubgroup (CommGroupScheme.groupHom f) ∧
      Function.Injective (cocharacterMapReal f) :=
  ha.isCentralSplitTorus.exists_commFactor_of_isMaximalSplitTorus hi

/-- A chosen actual closed factor of a central split torus through the supplied
maximal split torus. -/
def IsCentralSplitTorus.commFactor
    [IsAffineHom G.X.hom] {a : A.toGrp ⟶ G} (ha : IsCentralSplitTorus a)
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) : A ⟶ T :=
  Classical.choose (ha.exists_commFactor_of_isMaximalSplitTorus hi)

/-- The chosen factor has the required ambient composite, is closed, and is
injective on real cocharacters. -/
theorem IsCentralSplitTorus.commFactor_spec
    [IsAffineHom G.X.hom] {a : A.toGrp ⟶ G} (ha : IsCentralSplitTorus a)
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) :
    CommGroupScheme.groupHom (ha.commFactor hi) ≫ i = a ∧
      IsClosedSubgroup (CommGroupScheme.groupHom (ha.commFactor hi)) ∧
      Function.Injective (cocharacterMapReal (ha.commFactor hi)) :=
  Classical.choose_spec (ha.exists_commFactor_of_isMaximalSplitTorus hi)

end Langlands.GroupScheme
