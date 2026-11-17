import Langlands.GroupScheme.Rational.SemistandardSpectralIndex
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.GroupScheme.Rational.ReductiveParabolicContraction

/-! # Fixed-torus realization of every intrinsic semistandard triple -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

namespace SubgroupFunctor

/-- An all-test complementary decomposition of actual closed representatives
makes their multiplication a scheme isomorphism. -/
theorem isIso_subgroupMultiplication_of_allTestDecomposition
    {S : Scheme.{u}} {G P L U : GroupScheme S}
    {F M N : SubgroupFunctor G} {j : P ⟶ G} {l : L ⟶ P} {r : U ⟶ P}
    (hP : F.IsRepresentedBy j) (hM : M.IsRepresentedBy (l ≫ j))
    (hN : N.IsRepresentedBy (r ≫ j))
    (hpoint : ∀ X : Over S,
      N.carrier X ≤ F.carrier X ∧ M.carrier X ≤ F.carrier X ∧
        ((N.carrier X).subgroupOf (F.carrier X)).Normal ∧
        ((N.carrier X).subgroupOf (F.carrier X)).IsComplement'
          ((M.carrier X).subgroupOf (F.carrier X)) ∧
        (↑(F.carrier X) : Set (X ⟶ G.X)) =
          (↑(M.carrier X) : Set (X ⟶ G.X)) *
            (↑(N.carrier X) : Set (X ⟶ G.X))) :
    IsIso (subgroupMultiplication l r) := by
  refine isIso_of_yoneda_map_bijective _ fun X => ?_
  let a (x : X ⟶ L.X) : (M.carrier X).subgroupOf (F.carrier X) :=
    ⟨⟨x ≫ (l ≫ j).hom.hom, (hpoint X).2.1 (hM.pointsEquiv X x).property⟩,
      (hM.pointsEquiv X x).property⟩
  let b (x : X ⟶ U.X) : (N.carrier X).subgroupOf (F.carrier X) :=
    ⟨⟨x ≫ (r ≫ j).hom.hom, (hpoint X).1 (hN.pointsEquiv X x).property⟩,
      (hN.pointsEquiv X x).property⟩
  have hc := (hpoint X).2.2.2.1.symm
  constructor
  · intro w w' hw
    have he := congrArg (fun f => f ≫ j.hom.hom) hw
    change (w ≫ subgroupMultiplication l r) ≫ j.hom.hom =
      (w' ≫ subgroupMultiplication l r) ≫ j.hom.hom at he
    simp only [subgroupMultiplication, MonObj.comp_mul, MonObj.mul_comp,
      Category.assoc, ← Grp.comp_hom_hom] at he
    have hab : (a (w ≫ fst L.X U.X), b (w ≫ snd L.X U.X)) =
        (a (w' ≫ fst L.X U.X), b (w' ≫ snd L.X U.X)) :=
      hc.1 (Subtype.ext he)
    have ha := congrArg (fun z => z.1.val.val) hab
    have hb := congrArg (fun z => z.2.val.val) hab
    exact CartesianMonoidalCategory.hom_ext _ _
      (hM.1.right_cancellation _ _ ha) (hN.1.right_cancellation _ _ hb)
  · intro x
    have hx : x ≫ j.hom.hom ∈
        (↑(M.carrier X) : Set (X ⟶ G.X)) *
          (↑(N.carrier X) : Set (X ⟶ G.X)) := by
      rw [← (hpoint X).2.2.2.2]
      exact (hP.pointsEquiv X x).property
    obtain ⟨m, hm, n, hn, hmn⟩ := Set.mem_mul.mp hx
    let m' := (hM.pointsEquiv X).symm ⟨m, hm⟩
    let n' := (hN.pointsEquiv X).symm ⟨n, hn⟩
    refine ⟨lift m' n', hP.1.right_cancellation _ _ ?_⟩
    change (lift m' n' ≫ subgroupMultiplication l r) ≫ j.hom.hom = x ≫ j.hom.hom
    rw [comp_subgroupMultiplication, MonObj.mul_comp, Category.assoc,
      Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom,
      hM.pointsEquiv_symm_comp, hN.pointsEquiv_symm_comp]
    exact hmn

end SubgroupFunctor

/-- Every intrinsic triple is realized by one cocharacter of its specified
maximal split torus. -/
theorem semistandardSpectralDynamicCoverage :
    SemistandardSpectralDynamicCoverageStatement.{u} := by
  intro k _ G hG T i hi p
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨P, L, U, j, l, r, hP, hj, hl, hL, hMl, hr, hUr, hpoint⟩ :=
    p.isParabolicWithLeviAndRadical
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  let : IsClosedImmersion l.hom.hom.left := hl
  let : IsClosedImmersion r.hom.hom.left := hr.1
  let : IsAffineHom P.X.hom := hj.isClosedSubgroup.isAffineHom
  let : Mono j.hom.hom := hP.1
  have hM : p.levi.IsRepresentedBy (l ≫ j) := by
    refine ⟨?_, hMl⟩
    change Mono (l.hom.hom ≫ j.hom.hom)
    let : Mono l.hom.hom := Over.mono_of_mono_left _
    exact mono_comp _ _
  have hU : p.radical.IsRepresentedBy (r ≫ j) := by
    refine ⟨?_, hUr⟩
    change Mono (r.hom.hom ≫ j.hom.hom)
    let : Mono r.hom.hom := Over.mono_of_mono_left _
    exact mono_comp _ _
  have hmul := SubgroupFunctor.isIso_subgroupMultiplication_of_allTestDecomposition
    hP hM hU hpoint
  have hlR := IsRationalLeviSubgroup.of_geometricUnipotentRadical hl hL hr hmul
  obtain ⟨ψ, hψP, hψM⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi
    parabolicDynamic dynamicGeometricUnipotentRadical hG hj hlR
  have hTP : SubgroupFunctor.range i ≤ Dynamic.centralizer ψ := by
    rw [← hψM, hMl]
    exact p.torus_le_levi
  have hcomm : ∀ (X : Over (Spec (CommRingCat.of k)))
      (x : X ⟶ (Gm (Spec (CommRingCat.of k))).X) (y : X ⟶ T.X),
      Commute (x ≫ ψ.hom.hom) (y ≫ i.hom.hom) := by
    intro X x y
    have hy := hTP X (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
    rw [← torusCentralizer_gm_eq_dynamicCentralizer] at hy
    simpa only [Category.id_comp] using (hy X (𝟙 X) x).symm
  obtain ⟨ζ, hζ⟩ := hi.exists_factor_of_commute isSplitTorus_gm ψ hcomm
  have hψU : SubgroupFunctor.range (r ≫ j) = Dynamic.unipotent ψ :=
    Dynamic.range_comp_radical_eq_unipotent_of_reductive hG ψ j
      ⟨hP.1, hψP⟩ r hr.isUnipotentRadical
  refine ⟨Additive.ofMul ζ, SemistandardSpectralIndex.ext ?_ ?_ ?_⟩
  · change Dynamic.parabolic (ζ ≫ i) = p.parabolic
    rw [hζ, ← hψP, hP.2]
  · change Dynamic.centralizer (ζ ≫ i) = p.levi
    rw [hζ, ← hψM, hMl]
  · change Dynamic.unipotent (ζ ≫ i) = p.radical
    rw [hζ, ← hψU, hUr]

end Langlands.GroupScheme
