import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Rational.CompatibleTorusCocharacter
import Langlands.GroupScheme.Rational.MinimalParabolicSplitComponent
import Langlands.GroupScheme.Rational.OriginalLeviCocharacter

/-! # Geometric compatible refinements and minimal-parabolic split components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A dynamic parabolic of a connected reductive group is a genuine
geometrically parabolic subgroup functor over the original field. -/
theorem isParabolicFunctor_dynamic (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    IsParabolicFunctor (Dynamic.parabolic χ) := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact ⟨Dynamic.Affine.parabolicScheme χ, Dynamic.Affine.parabolicHom χ,
    isParabolicSubgroup_of_range_eq_dynamicParabolic hG _
      (Dynamic.Affine.isClosedSubgroup_parabolicHom χ) χ
      (Dynamic.Affine.isRepresentedBy_parabolicHom χ).2,
    (Dynamic.Affine.isRepresentedBy_parabolicHom χ).2⟩

/-- A compatible whole-torus centralizing cocharacter, together with its
geometric parabolicity and both all-test dynamic inclusions. -/
def IsSplitTorus.parabolicCompatibleCocharacter
    {B : CommGroupScheme (Spec (CommRingCat.of k))}
    (hB : IsSplitTorus B.toGrp) (hG : IsConnectedReductive G)
    (b : B.toGrp ⟶ G) (ν : cocharacterLattice B) :
    {ζ : cocharacterLattice B //
      Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ b) = torusCentralizer b ∧
        IsParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ b)) ∧
        Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ b) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b) ∧
        Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ b) ≤
          Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ b)} := by
  have := hG.isAffineHom
  have := hG.smooth
  let ζ := compatibleCentralizingCocharacter hB b ν
  obtain ⟨hZ, hP, hU⟩ := compatibleCentralizingCocharacter_spec hB b ν
  exact ⟨ζ, hZ, isParabolicFunctor_dynamic hG _, hP, hU⟩

section Maximality

variable {P L : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {i : L ⟶ G} {a : A.toGrp ⟶ L}

/-- A split component whose cocharacter presents a minimal parabolic is
ambient maximal, provided the given reductive subgroup is its centralizer. -/
theorem IsSplitComponent.isMaximalSplitTorus_of_minimalParabolic_presentingCocharacter
    (hA : IsSplitComponent a) (hG : IsConnectedReductive G)
    (hp : IsMinimalParabolicSubgroup p)
    (hL : IsConnectedReductive L) (hi : IsClosedSubgroup i)
    (hLi : SubgroupFunctor.range i ≤ SubgroupFunctor.range p)
    (ha : (torusCentralizer (a ≫ i)).IsRepresentedBy i)
    (ν : cocharacterLattice A)
    (hν : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ a ≫ i) =
      SubgroupFunctor.range p) :
    IsMaximalSplitTorus (a ≫ i) := by
  have := hG.isAffineHom
  have := hG.smooth
  apply hA.isMaximalSplitTorus_of_minimalParabolic_compatible_extensions
    hp hL hi hLi ha
  intro B b hb f hf
  let extensionCocharacter : cocharacterLattice B :=
    Additive.ofMul (CommGroupScheme.groupHom ν ≫ f)
  let ζ := hb.1.1.parabolicCompatibleCocharacter hG b extensionCocharacter
  refine ⟨ζ.val, ζ.property.1, ζ.property.2.1, ζ.property.2.2.1.trans ?_⟩
  have hExtension : CommGroupScheme.groupHom extensionCocharacter ≫ b =
      CommGroupScheme.groupHom ν ≫ a ≫ i := by
    change (CommGroupScheme.groupHom ν ≫ f) ≫ b = _
    rw [Category.assoc, hf]
  rw [hExtension, hν]

end Maximality

section OriginalLevi

variable {P L : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {l : L ⟶ P} {a : A.toGrp ⟶ L}

/-- Any supplied dynamic presentation of a minimal parabolic makes every
specified split component of its original rational Levi ambient maximal. -/
theorem IsRationalLeviSubgroup.isMaximalSplitTorus_splitComponent_of_dynamicMinimalParabolic
    (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G)
    (hp : IsMinimalParabolicSubgroup p)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p) (hA : IsSplitComponent a) :
    IsMaximalSplitTorus (a ≫ l ≫ p) := by
  obtain ⟨ν, hνP, -, hcent⟩ :=
    hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP hA
  have hi : IsClosedSubgroup (l ≫ p) :=
    hl.isClosedSubgroup.comp hp.1.isClosedSubgroup
  have : IsClosedImmersion (l ≫ p).hom.hom.left := hi
  have : Mono (l ≫ p).hom.hom := Over.mono_of_mono_left _
  exact hA.isMaximalSplitTorus_of_minimalParabolic_presentingCocharacter hG hp
    hl.isConnectedReductive hi (SubgroupFunctor.range_comp_le l p)
    ⟨inferInstance, hcent.symm⟩ ν hνP.2.symm

end OriginalLevi

end Langlands.GroupScheme
