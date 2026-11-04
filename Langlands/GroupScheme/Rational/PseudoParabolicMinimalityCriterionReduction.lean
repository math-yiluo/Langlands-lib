import Langlands.GroupScheme.Rational.PseudoParabolicMaximalSplitTorusStructureReduction
import Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeStatement
import Langlands.GroupScheme.SplitSolvableIntoPseudoParabolicStatement
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The product criterion implies minimality of a pseudo-parabolic subgroup

Conditional reduction of the reverse implication in the minimality criterion of CGP
Proposition C.2.4: if a pseudo-parabolic subgroup `P` of a smooth connected affine group
`G` is the fppf-local product `Z_G(S) · R_us,k(P)` for a maximal split torus `S` of `P`,
then `P` is minimal. The inputs are the published statements of rational conjugacy of
maximal split tori (C.2.3), of the split solvable envelope `S ⋉ R_us,k(P)`, and of
rational conjugation of split solvable subgroups into pseudo-parabolics (C.2.2).

The module also proves, unconditionally, that a closed subgroup of an affine group of
finite type over a field which contains its image under an automorphism of the ambient
group equals that image on every test. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G P : GroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

namespace IsClosedSubgroup

/-- A closed subgroup of an affine group of finite type over a field that contains its
image under an ambient automorphism equals that image on every test. The kernel ideals
of the iterated images form an ascending chain in the Noetherian coordinate ring. -/
theorem range_comp_iso_eq_of_le [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {i : P ⟶ G} (hi : IsClosedSubgroup i) (e : G ≅ G)
    (hle : SubgroupFunctor.range (i ≫ e.hom) ≤ SubgroupFunctor.range i) :
    SubgroupFunctor.range (i ≫ e.hom) = SubgroupFunctor.range i := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let U : G.X.left.affineOpens := ⟨⊤, isAffineOpen_top G.X.left⟩
  have : IsNoetherianRing Γ(G.X.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian U
  let e' : Aut G := e
  let φ : ℕ → Aut G := fun n => e' ^ n
  have hφ : ∀ n, (φ (n + 1)).hom = e.hom ≫ (φ n).hom := fun n => by
    simp only [φ, pow_succ, Aut.Aut_mul_def]
    rfl
  let a : ℕ → (P ⟶ G) := fun n => i ≫ (φ n).hom
  have ha : ∀ n, a (n + 1) = (i ≫ e.hom) ≫ (φ n).hom := fun n => by
    simp only [a, hφ, Category.assoc]
  have hstep : ∀ n, SubgroupFunctor.range (a (n + 1)) ≤ SubgroupFunctor.range (a n) :=
    fun n => by
      rw [ha n]
      exact SubgroupFunctor.range_comp_mono hle _
  let ideals : Set (Ideal Γ(G.X.left, ⊤)) :=
    Set.range fun n => (a n).hom.hom.left.ker.ideal U
  obtain ⟨I, ⟨n, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr
      (inferInstance : IsNoetherian Γ(G.X.left, ⊤) Γ(G.X.left, ⊤)) ideals ⟨_, 0, rfl⟩
  have : IsClosedImmersion (a n).hom.hom.left := hi.comp_iso (φ n)
  have : IsClosedImmersion (a (n + 1)).hom.hom.left := hi.comp_iso (φ (n + 1))
  have : Mono (a n).hom.hom := Over.mono_of_mono_left _
  have : Mono (a (n + 1)).hom.hom := Over.mono_of_mono_left _
  let f := SubgroupFunctor.factorOfRangeLE (hstep n)
  have hf : f ≫ a n = a (n + 1) := SubgroupFunctor.factorOfRangeLE_comp (hstep n)
  have hfs : f.hom.hom.left ≫ (a n).hom.hom.left = (a (n + 1)).hom.hom.left :=
    congrArg (fun z : P ⟶ G => z.hom.hom.left) hf
  have hk : (a n).hom.hom.left.ker ≤ (a (n + 1)).hom.hom.left.ker := by
    rw [← hfs]
    exact Scheme.Hom.le_ker_comp _ _
  have heq : (a n).hom.hom.left.ker.ideal U = (a (n + 1)).hom.hom.left.ker.ideal U :=
    eq_of_le_of_not_lt (hk U) (hmax _ ⟨n + 1, rfl⟩)
  have hker : (a (n + 1)).hom.hom.left.ker = (a n).hom.hom.left.ker :=
    Scheme.IdealSheafData.ext_of_isAffine heq.symm
  have : IsIso f.hom.hom.left :=
    IsClosedImmersion.isIso_of_ker_eq _ _ _ hfs hker
  have : IsIso f.hom.hom :=
    (isIso_iff_of_reflects_iso _ (Over.forget _)).mp
      (show IsIso f.hom.hom.left from inferInstance)
  have : IsIso f.hom :=
    (isIso_iff_of_reflects_iso _ (Mon.forget _)).mp
      (show IsIso f.hom.hom from inferInstance)
  have : IsIso f :=
    (isIso_iff_of_reflects_iso _ (Grp.forget₂Mon _)).mp
      (show IsIso f.hom from inferInstance)
  have hge : SubgroupFunctor.range (a n) ≤ SubgroupFunctor.range (a (n + 1)) :=
    SubgroupFunctor.range_le_of_factor (inv f) ((IsIso.inv_comp_eq f).mpr hf.symm)
  have hn : SubgroupFunctor.range ((i ≫ e.hom) ≫ (φ n).hom) =
      SubgroupFunctor.range (i ≫ (φ n).hom) := by
    rw [← ha n]
    exact le_antisymm (hstep n) hge
  exact (SubgroupFunctor.range_comp_iso_eq_iff _ _ (φ n)).mp hn

/-- A closed subgroup of an affine group of finite type over a field that is contained in
its image under an ambient automorphism equals that image on every test. -/
theorem range_comp_iso_eq_of_ge [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {i : P ⟶ G} (hi : IsClosedSubgroup i) (e : G ≅ G)
    (hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range (i ≫ e.hom)) :
    SubgroupFunctor.range (i ≫ e.hom) = SubgroupFunctor.range i := by
  have h' : SubgroupFunctor.range (i ≫ e.symm.hom) ≤ SubgroupFunctor.range i := by
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      SubgroupFunctor.range_comp_mono hle e.inv
  have h := hi.range_comp_iso_eq_of_le e.symm h'
  have h2 := (SubgroupFunctor.range_comp_iso_eq_iff (i ≫ e.symm.hom) i e).mpr h
  simpa only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h2.symm

end IsClosedSubgroup

namespace IsPseudoParabolicSubgroup

/-- Conditionally on C.2.3, the split solvable envelope and C.2.2: a pseudo-parabolic
subgroup that is the fppf-local product of the ambient centralizer of a maximal split
torus and its split unipotent radical is a minimal pseudo-parabolic subgroup. -/
theorem isMinimal_of_isFppfProduct
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (henvelope : PseudoParabolicSplitSolvableEnvelopeStatement.{u})
    (hcontainment : SplitSolvableIntoPseudoParabolicStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : P ⟶ G} (hi : IsPseudoParabolicSubgroup i)
    {s : S.toGrp ⟶ P} (hs : IsMaximalSplitTorus s)
    {U : GroupScheme (Spec (CommRingCat.of k))} {z : U ⟶ P}
    (hz : IsSplitUnipotentRadical z)
    (hprod : SubgroupFunctor.IsFppfProduct (torusCentralizer (s ≫ i))
      (SubgroupFunctor.range (z ≫ i)) i) :
    IsMinimalPseudoParabolicSubgroup i := by
  refine ⟨hi, fun Q j hj hle => ?_⟩
  obtain ⟨H, h, hsplit, hHprod⟩ := henvelope k G P i hi S s hs U z hz
  obtain ⟨g, f, hf⟩ :=
    hcontainment k G Q j hj H (h ≫ i)
      (hHprod.isClosedSubgroup.comp hi.isClosedSubgroup) hsplit
  let e := G.innerIso g
  let j' := j ≫ e.inv
  have hj' : IsPseudoParabolicSubgroup j' := hj.comp_iso e.symm
  have hf' : f ≫ j' = h ≫ i := by
    simpa only [j', e, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun a => a ≫ e.inv) hf
  have hH : SubgroupFunctor.range (h ≫ i) ≤ SubgroupFunctor.range j' :=
    SubgroupFunctor.range_le_of_factor f hf'
  have hT : SubgroupFunctor.range (s ≫ i) ≤ SubgroupFunctor.range j' :=
    (SubgroupFunctor.range_comp_mono hHprod.left_le i).trans hH
  have hU : SubgroupFunctor.range (z ≫ i) ≤ SubgroupFunctor.range j' :=
    (SubgroupFunctor.range_comp_mono hHprod.right_le i).trans hH
  have hsG : IsMaximalSplitTorus (s ≫ i) := hi.isMaximalSplitTorus_comp hconj hs
  have : IsClosedImmersion j'.hom.hom.left := hj'.isClosedSubgroup
  have : Mono j'.hom.hom := Over.mono_of_mono_left _
  have hjrep : (SubgroupFunctor.range j').IsRepresentedBy j' := ⟨inferInstance, rfl⟩
  obtain ⟨sQ, hsQ, hsQcomp⟩ := hsG.exists_lift hjrep hj'.isClosedSubgroup hT
  have hcentralizer : torusCentralizer (s ≫ i) ≤ SubgroupFunctor.range j' := by
    have hc := hj'.torusCentralizer_le_range hconj hsQ
    rwa [hsQcomp] at hc
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hPle : SubgroupFunctor.range i ≤ SubgroupFunctor.range j' :=
    hprod.range_le hcentralizer hU
  have hj'le : SubgroupFunctor.range j' ≤ SubgroupFunctor.range (i ≫ e.symm.hom) :=
    SubgroupFunctor.range_comp_mono hle e.inv
  have hconjeq : SubgroupFunctor.range (i ≫ e.symm.hom) = SubgroupFunctor.range i :=
    hi.isClosedSubgroup.range_comp_iso_eq_of_ge e.symm (hPle.trans hj'le)
  have hj'eq : SubgroupFunctor.range (j ≫ e.symm.hom) =
      SubgroupFunctor.range (i ≫ e.symm.hom) :=
    le_antisymm hj'le (hconjeq.le.trans hPle)
  exact (SubgroupFunctor.range_comp_iso_eq_iff j i e.symm).mp hj'eq

end IsPseudoParabolicSubgroup

/-- The reverse implication of the minimality criterion of CGP Proposition C.2.4: a
pseudo-parabolic subgroup `P` of a smooth connected affine group `G` over a field is
minimal as soon as it is the fppf-local product `Z_G(S) · R_us,k(P)` for a maximal split
torus `S` of `P` and a split unipotent radical of `P`. This proposition is the conclusion
of the conditional reduction `pseudoParabolicMinimalityOfCentralizerProduct_of_statements`,
not an assertion that it holds unconditionally. -/
def PseudoParabolicMinimalityOfCentralizerProduct : Prop :=
  ∀ (k : Type u) [Field k] (G P : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : P ⟶ G), IsPseudoParabolicSubgroup i →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ P),
        IsMaximalSplitTorus s →
          ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ P),
            IsSplitUnipotentRadical j →
              SubgroupFunctor.IsFppfProduct (torusCentralizer (s ≫ i))
                  (SubgroupFunctor.range (j ≫ i)) i →
                IsMinimalPseudoParabolicSubgroup i

/-- Conditionally on C.2.3, the split solvable envelope and C.2.2, the product criterion
implies minimality. -/
theorem pseudoParabolicMinimalityOfCentralizerProduct_of_statements
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (henvelope : PseudoParabolicSplitSolvableEnvelopeStatement.{u})
    (hcontainment : SplitSolvableIntoPseudoParabolicStatement.{u}) :
    PseudoParabolicMinimalityOfCentralizerProduct.{u} := by
  intro k _ G P _ _ _ i hi S s hs U j hj hprod
  exact hi.isMinimal_of_isFppfProduct hconj henvelope hcontainment hs hj hprod

end Langlands.GroupScheme
