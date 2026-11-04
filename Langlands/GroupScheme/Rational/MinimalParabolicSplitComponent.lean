import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Dynamic.TrivialUnipotentCentralizer
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.CentralLeviTorusRadical

/-! # Minimal parabolics and ambient maximality of Levi split components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

namespace Dynamic

/-- A full dynamic parabolic in a smooth affine group with trivial unipotent
radical has full centralizer. The actual contracting subgroup is unipotent
by the published torus-action theorem. -/
theorem parabolic_eq_top_iff_centralizer_eq_top
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : HasTrivialUnipotentRadical G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    parabolic χ = ⊤ ↔ centralizer χ = ⊤ := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact parabolic_eq_top_iff_centralizer_eq_top_of_isUnipotent χ hG
    (Affine.isRepresentedBy_unipotentHom χ)
    (Affine.isClosedSubgroup_unipotentHom χ)
    (isUnipotent_unipotentRepresentative χ (Affine.isRepresentedBy_unipotentHom χ))

/-- If a cocharacter of a smooth affine closed subgroup with trivial
unipotent radical contracts every point of that subgroup in the ambient
group, then it centralizes that subgroup on every test scheme. -/
theorem range_le_centralizer_of_range_le_parabolic
    {G L : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth L.X.hom] [IsAffineHom L.X.hom]
    (hL : HasTrivialUnipotentRadical L)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L)
    (i : L ⟶ G) (hi : IsClosedSubgroup i)
    (hle : SubgroupFunctor.range i ≤ parabolic (χ ≫ i)) :
    SubgroupFunctor.range i ≤ centralizer (χ ≫ i) := by
  have hP : parabolic χ = ⊤ := by
    rw [parabolic_eq_comap_of_isClosedSubgroup χ i hi]
    exact SubgroupFunctor.range_le_iff_comap_eq_top.mp hle
  have hZ := (parabolic_eq_top_iff_centralizer_eq_top hL χ).mp hP
  have hmap : (centralizer χ).map i ≤ centralizer (χ ≫ i) :=
    SubgroupFunctor.map_le_iff_le_comap.mpr (centralizer_le_comap χ i)
  simpa only [hZ, SubgroupFunctor.map_top] using hmap

end Dynamic

section Centralizer

variable {G P L : GroupScheme (Spec (CommRingCat.of k))}
    {A B : CommGroupScheme (Spec (CommRingCat.of k))}
    {j : P ⟶ G} {i : L ⟶ G}
    {a : A.toGrp ⟶ G} {b : B.toGrp ⟶ G}

/-- A genuinely parabolic compatible refinement of a split extension has
the same centralizer as the original torus, when that centralizer is a
connected reductive closed subgroup of a minimal parabolic. No second
rational Levi or centralizer-reductivity theorem is needed. -/
theorem IsMinimalParabolicSubgroup.represents_torusCentralizer_of_compatible_extension
    (hj : IsMinimalParabolicSubgroup j)
    (hL : IsConnectedReductive L) (hi : IsClosedSubgroup i)
    (hLi : SubgroupFunctor.range i ≤ SubgroupFunctor.range j)
    (ha : (torusCentralizer a).IsRepresentedBy i)
    (hb : IsSplitSubtorus b)
    (f : A.toGrp ⟶ B.toGrp) (hf : f ≫ b = a)
    (ν : cocharacterLattice B)
    (hν : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ b) = torusCentralizer b)
    (hpar : IsParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b)))
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b) ≤
      SubgroupFunctor.range j) :
    (torusCentralizer b).IsRepresentedBy i := by
  let : Smooth L.X.hom := hL.smooth
  let : IsAffineHom L.X.hom := hL.isAffineHom
  have hcontained : SubgroupFunctor.range b ≤ SubgroupFunctor.range i :=
    (range_le_torusCentralizer_of_factor a b f hf).trans ha.2.ge
  let bL := (hb.factorInClosedSubgroup hi hcontained).val
  have hbL : bL ≫ i = b := hb.factorInClosedSubgroup_comp hi hcontained
  have hP : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b) =
      SubgroupFunctor.range j :=
    hj.isMinimalParabolicFunctor.2 _ hpar hle
  have hPl : SubgroupFunctor.range i ≤
      Dynamic.parabolic ((CommGroupScheme.groupHom ν ≫ bL) ≫ i) := by
    rw [Category.assoc, hbL, hP]
    exact hLi
  have hZ := Dynamic.range_le_centralizer_of_range_le_parabolic
    hL.hasTrivialUnipotentRadical (CommGroupScheme.groupHom ν ≫ bL) i hi hPl
  rw [Category.assoc, hbL, hν] at hZ
  exact ⟨ha.1, le_antisymm hZ
    ((torusCentralizer_le_of_factor b a f hf).trans ha.2.ge)⟩

end Centralizer

section Maximality

variable {G P L : GroupScheme (Spec (CommRingCat.of k))}
    {A B : CommGroupScheme (Spec (CommRingCat.of k))}
    {j : P ⟶ G} {i : L ⟶ G}
    {a : A.toGrp ⟶ L} {b : B.toGrp ⟶ G}

/-- One ambient maximal split extension with a genuinely parabolic
compatible whole-torus cocharacter makes the original split component
ambient maximal. -/
theorem IsSplitComponent.isMaximalSplitTorus_of_minimalParabolic_extension
    (hA : IsSplitComponent a)
    (hj : IsMinimalParabolicSubgroup j)
    (hL : IsConnectedReductive L) (hi : IsClosedSubgroup i)
    (hLi : SubgroupFunctor.range i ≤ SubgroupFunctor.range j)
    (ha : (torusCentralizer (a ≫ i)).IsRepresentedBy i)
    (hb : IsMaximalSplitTorus b)
    (f : A.toGrp ⟶ B.toGrp) (hf : f ≫ b = a ≫ i)
    (ν : cocharacterLattice B)
    (hν : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ b) = torusCentralizer b)
    (hpar : IsParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b)))
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b) ≤
      SubgroupFunctor.range j) :
    IsMaximalSplitTorus (a ≫ i) := by
  have hZ := hj.represents_torusCentralizer_of_compatible_extension
    hL hi hLi ha hb.1 f hf ν hν hpar hle
  let bL := torusCentralizerFactor b hZ
  have hbL : bL ≫ i = b := torusCentralizerFactor_comp b hZ
  have hfL : f ≫ bL = a := by
    apply ha.hom_ext
    rw [Category.assoc, hbL, hf]
  have : IsIso f := hA.2 B bL
    (hb.1.isCentralSplitTorus_torusCentralizerFactor hZ hi) f hfL
  apply hb.of_factor (hA.1.1.comp hi) (inv f)
  rw [← hf, IsIso.inv_hom_id_assoc]

/-- For affine ambient groups locally of finite type, it suffices to
construct a genuinely parabolic compatible cocharacter for each ambient
maximal split extension. The geometric parabolicity input is explicit. -/
theorem IsSplitComponent.isMaximalSplitTorus_of_minimalParabolic_compatible_extensions
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hA : IsSplitComponent a)
    (hj : IsMinimalParabolicSubgroup j)
    (hL : IsConnectedReductive L) (hi : IsClosedSubgroup i)
    (hLi : SubgroupFunctor.range i ≤ SubgroupFunctor.range j)
    (ha : (torusCentralizer (a ≫ i)).IsRepresentedBy i)
    (hcompat : ∀ (B : CommGroupScheme (Spec (CommRingCat.of k)))
      (b : B.toGrp ⟶ G), IsMaximalSplitTorus b →
        ∀ f : A.toGrp ⟶ B.toGrp, f ≫ b = a ≫ i →
          ∃ ν : cocharacterLattice B,
            Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ b) = torusCentralizer b ∧
              IsParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b)) ∧
                Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b) ≤
                  SubgroupFunctor.range j) :
    IsMaximalSplitTorus (a ≫ i) := by
  obtain ⟨B, b, hb, f, hf⟩ := exists_maximalSplitTorus_extension G (a ≫ i)
    (hA.1.1.comp hi)
  obtain ⟨ν, hν, hpar, hle⟩ := hcompat B b hb f hf
  exact hA.isMaximalSplitTorus_of_minimalParabolic_extension
    hj hL hi hLi ha hb f hf ν hν hpar hle

end Maximality

section Radical

variable {G P L R : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {j : P ⟶ G} {l : L ⟶ P} {r : R ⟶ P} {a : A.toGrp ⟶ L}

/-- The original split component factors through the specified solvable
radical, with ambient maximality and the given Levi centralizer, once
genuinely parabolic compatible refinements have been supplied. -/
def IsRationalLeviSubgroup.splitComponentRadicalWitness_of_minimalParabolic
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hl : IsRationalLeviSubgroup l) (hj : IsMinimalParabolicSubgroup j)
    (hR : IsSolvableRadical r) (hA : IsSplitComponent a)
    (ha : (torusCentralizer (a ≫ l ≫ j)).IsRepresentedBy (l ≫ j))
    (hcompat : ∀ (B : CommGroupScheme (Spec (CommRingCat.of k)))
      (b : B.toGrp ⟶ G), IsMaximalSplitTorus b →
        ∀ f : A.toGrp ⟶ B.toGrp, f ≫ b = a ≫ l ≫ j →
          ∃ ν : cocharacterLattice B,
            Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ b) = torusCentralizer b ∧
              IsParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b)) ∧
                Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b) ≤
                  SubgroupFunctor.range j) :
    {aR : A.toGrp ⟶ R // aR ≫ r = a ≫ l ∧
      IsMaximalSplitTorus (aR ≫ r ≫ j) ∧
        torusCentralizer (aR ≫ r ≫ j) = SubgroupFunctor.range (l ≫ j)} := by
  have hLi : SubgroupFunctor.range (l ≫ j) ≤ SubgroupFunctor.range j := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr
      ⟨y ≫ l.hom.hom, by simp only [Grp.comp_hom_hom, Category.assoc]⟩
  have hmax : IsMaximalSplitTorus (a ≫ l ≫ j) :=
    hA.isMaximalSplitTorus_of_minimalParabolic_compatible_extensions
      hj hl.isConnectedReductive (hl.isClosedSubgroup.comp hj.1.isClosedSubgroup)
      hLi ha hcompat
  let aR := hl.centralTorusRadicalFactor a hR hA.1.1.1.isTorus hA.1.1.2 hA.1.2
  have hfac : aR ≫ r = a ≫ l :=
    hl.centralTorusRadicalFactor_comp a hR hA.1.1.1.isTorus hA.1.1.2 hA.1.2
  have hamb : aR ≫ r ≫ j = a ≫ l ≫ j := by
    rw [← Category.assoc, hfac, Category.assoc]
  exact ⟨aR, hfac, by rwa [hamb], by rw [hamb]; exact ha.2.symm⟩

end Radical

end Langlands.GroupScheme
