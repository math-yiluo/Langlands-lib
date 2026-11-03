import Langlands.GroupScheme.Rational.CocharacterMaximalSplitTorusProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.StandardLeviLiftIndependence
import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Dynamic.SmoothConnectedStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Conjugating cocharacters into a maximal split torus

Conditional reductions: from the published theorem `cocharacterMaximalSplitTorus`, the
published statement on conjugacy of maximal split tori, and the published statements on
smoothness and connectedness of dynamic parabolics, every cocharacter of a smooth
connected affine group is rationally conjugate into a given maximal split torus, and
by a point of `P(ζ)` when `P(ζ)` contains a dynamic parabolic of that torus. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Naturality

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Inner automorphisms are natural along homomorphisms of group schemes. -/
theorem comp_innerIso_hom_comp (j : H ⟶ G) (p : Over.mk (𝟙 S) ⟶ H.X) :
    j ≫ (G.innerIso (p ≫ j.hom.hom)).hom = (H.innerIso p).hom ≫ j := by
  refine hom_ext_points fun T x => ?_
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
    comp_innerIso_hom, comp_innerIso_hom, ← constantPoint_comp, MonObj.mul_comp,
    MonObj.mul_comp, GrpObj.inv_comp]

/-- The image of a cocharacter lies in its own dynamic parabolic. -/
theorem Dynamic.range_le_parabolic (zeta : (Gm S).toGrp ⟶ G) :
    SubgroupFunctor.range zeta ≤ Dynamic.parabolic zeta := by
  have h := range_le_torusCentralizer zeta
  rw [torusCentralizer_gm_eq_dynamicCentralizer] at h
  exact h.trans (Dynamic.centralizer_le_parabolic zeta)

end Naturality

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Conditionally on conjugacy of maximal split tori, every cocharacter of a
smooth connected affine group is conjugate, by a rational point, to a cocharacter of a
given maximal split torus. -/
theorem exists_innerIso_comp_eq_cocharacter
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (ξ : cocharacterLattice T),
      zeta ≫ (G.innerIso g).hom = CommGroupScheme.groupHom ξ ≫ i := by
  obtain ⟨T₁, i₁, ν₁, hi₁, hν₁⟩ := cocharacterMaximalSplitTorus k G zeta
  obtain ⟨g, e, hge⟩ := hconj k G T₁ T i₁ i hi₁ hi
  refine ⟨g, ν₁ ≫ Additive.ofMul e.hom, ?_⟩
  rw [← hν₁, Category.assoc, hge]
  rfl

/-- Conditionally on conjugacy of maximal split tori, every dynamic parabolic of
a smooth connected affine group is rationally conjugate to the dynamic parabolic of a
cocharacter of a given maximal split torus. -/
theorem exists_parabolic_isRationallyConjugate_cocharacter
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ ξ : cocharacterLattice T, (Dynamic.parabolic zeta).IsRationallyConjugate
      (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)) := by
  obtain ⟨g, ξ, h⟩ := exists_innerIso_comp_eq_cocharacter hconj hi zeta
  exact ⟨ξ, h ▸ Dynamic.parabolic_isRationallyConjugate zeta g⟩

/-- Conditionally on conjugacy of maximal split tori and on smoothness and
connectedness of dynamic parabolics: if `P(ζ)` contains the dynamic parabolic of a
cocharacter `ν` of a maximal split torus `i`, then a rational point of `P(ζ)`
conjugates `ζ` to a cocharacter of `i`. -/
theorem exists_mem_parabolic_innerIso_comp_eq_cocharacter
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hsmooth : DynamicSmoothStatement.{u}) (hconn : DynamicConnectedStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ Dynamic.parabolic zeta) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (ξ : cocharacterLattice T),
      g ∈ (Dynamic.parabolic zeta).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ∧
      zeta ≫ (G.innerIso g).hom = CommGroupScheme.groupHom ξ ≫ i := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hj := Dynamic.Affine.isRepresentedBy_parabolicHom zeta
  have hjc := Dynamic.Affine.isClosedSubgroup_parabolicHom zeta
  have : Smooth (Dynamic.Affine.parabolicScheme zeta).X.hom := (hsmooth k G zeta _ _).1 hj
  have : ConnectedSpace (Dynamic.Affine.parabolicScheme zeta).X.left :=
    ((hconn k G zeta _ _).2 inferInstance).1 hj
  have : IsClosedImmersion (Dynamic.Affine.parabolicHom zeta).hom.hom.left := hjc
  have : IsAffineHom (Dynamic.Affine.parabolicScheme zeta).X.hom := by
    rw [← Over.w (Dynamic.Affine.parabolicHom zeta).hom.hom]
    infer_instance
  have hzH := hj.factorHom_comp zeta (Dynamic.range_le_parabolic zeta)
  obtain ⟨T₁, i₁, ν₁, hi₁, hν₁⟩ :=
    cocharacterMaximalSplitTorus k _ (hj.factorHom zeta (Dynamic.range_le_parabolic zeta))
  obtain ⟨iH, hiH, hiHj⟩ := hi.exists_lift_of_parabolic_le ν zeta hP hj hjc
  obtain ⟨p, e, hpe⟩ := hconj k _ T₁ T i₁ iH hi₁ hiH
  refine ⟨p ≫ (Dynamic.Affine.parabolicHom zeta).hom.hom, ν₁ ≫ Additive.ofMul e.hom, ?_, ?_⟩
  · rw [← hj.2]
    exact ⟨p, rfl⟩
  · calc zeta ≫ (G.innerIso (p ≫ (Dynamic.Affine.parabolicHom zeta).hom.hom)).hom
        = hj.factorHom zeta (Dynamic.range_le_parabolic zeta) ≫
            (Dynamic.Affine.parabolicHom zeta ≫
              (G.innerIso (p ≫ (Dynamic.Affine.parabolicHom zeta).hom.hom)).hom) := by
          rw [← Category.assoc, hzH]
      _ = CommGroupScheme.groupHom (ν₁ ≫ Additive.ofMul e.hom) ≫ i := by
          rw [comp_innerIso_hom_comp, ← hν₁, Category.assoc, reassoc_of% hpe, hiHj]
          rfl

/-- Conditionally on conjugacy of maximal split tori and on smoothness and
connectedness of dynamic parabolics: every dynamic parabolic containing the dynamic
parabolic of a cocharacter of a maximal split torus `i` is the dynamic parabolic of a
cocharacter of `i`, as subgroup functors on every test scheme. -/
theorem exists_parabolic_eq_cocharacter_of_parabolic_le
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hsmooth : DynamicSmoothStatement.{u}) (hconn : DynamicConnectedStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ Dynamic.parabolic zeta) :
    ∃ ξ : cocharacterLattice T,
      Dynamic.parabolic zeta = Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i) := by
  obtain ⟨g, ξ, hg, h⟩ :=
    exists_mem_parabolic_innerIso_comp_eq_cocharacter hconj hsmooth hconn hi ν zeta hP
  have h1 := Dynamic.parabolic_eq_comap_of_iso zeta (G.innerIso g)
  rw [h] at h1
  have h2 := (SubgroupFunctor.eq_comap_iso_iff (G.innerIso g)).1 h1
  rw [← innerIso_inv_hom,
    SubgroupFunctor.comap_innerIso_hom_eq_of_mem _ ((Subgroup.inv_mem _ hg))] at h2
  exact ⟨ξ, h2⟩

/-- Under the hypotheses of `exists_parabolic_eq_cocharacter_of_parabolic_le`, a chosen
cocharacter of `i` whose dynamic parabolic is `P(ζ)`, bundled with that equality. -/
def parabolicCocharacterOfParabolicLE
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hsmooth : DynamicSmoothStatement.{u}) (hconn : DynamicConnectedStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ Dynamic.parabolic zeta) :
    {ξ : cocharacterLattice T //
      Dynamic.parabolic zeta = Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)} :=
  Classical.indefiniteDescription _
    (exists_parabolic_eq_cocharacter_of_parabolic_le hconj hsmooth hconn hi ν zeta hP)

end Langlands.GroupScheme
