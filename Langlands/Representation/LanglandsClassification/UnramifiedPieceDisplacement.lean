import Langlands.Representation.LanglandsClassification.UnramifiedPieceWeylParameter

/-! # Nonzero displacement of an actual unramified geometric-lemma piece -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

section Nonidentity

variable {k : Type u} [Field k]
  {G P M Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (pres : ParabolicRootPresentation p l a)

local instance : Mono pres.data.i.hom.hom.left :=
  pres.isCompatible.maximalSplit.isSplitSubtorus.mono

/-- A Levi correction of a nonidentity original double coset has inverse
Weyl class outside the actual standard Levi Weyl subgroup. -/
theorem inverse_normalizerClass_not_mem_standardLeviWeyl
    (q : Q ⟶ G) (z : rationalPoints G)
    (hz : DoubleCoset.mk (pointImage p) (pointImage q) z ≠
      DoubleCoset.mk (pointImage p) (pointImage q) 1)
    (mS mT : rationalPoints M) (n : normalizerPoints pres.data.i)
    (hn : n.val = (mS ≫ (l ≫ p).hom.hom) * z *
      (mT ≫ (l ≫ p).hom.hom)⁻¹) :
    (QuotientGroup.mk n : relativeWeylGroup pres.data.i)⁻¹ ∉
      standardRelativeWeylGroup pres.data.i pres.data.ν pres.data.J := by
  intro hw
  have hw' : (QuotientGroup.mk n : relativeWeylGroup pres.data.i) ∈
      standardRelativeWeylGroup pres.data.i pres.data.ν pres.data.J :=
    inv_mem_iff.mp hw
  have hstd := coe_mem_standardLeviPoints_of_mk_mem
    pres.data.i pres.data.ν pres.data.J hw'
  have himg : n.val ∈ pointImage (l ≫ p) := by
    rw [pointImage_eq_range_carrier, pres.isCompatible.levi_eq]
    exact hstd
  have hmS : mS ≫ (l ≫ p).hom.hom ∈ pointImage (l ≫ p) := ⟨mS, rfl⟩
  have hmT : mT ≫ (l ≫ p).hom.hom ∈ pointImage (l ≫ p) := ⟨mT, rfl⟩
  have hzimg : z ∈ pointImage (l ≫ p) := by
    have heq : z = (mS ≫ (l ≫ p).hom.hom)⁻¹ * n.val *
        (mT ≫ (l ≫ p).hom.hom) := by
      rw [hn]
      group
    rw [heq]
    exact (pointImage (l ≫ p)).mul_mem
      ((pointImage (l ≫ p)).mul_mem ((pointImage (l ≫ p)).inv_mem hmS) himg) hmT
  apply hz
  exact DoubleCoset.eq.mpr ⟨z⁻¹,
    (pointImage p).inv_mem (pointImage_comp_le p l hzimg),
    1, (pointImage q).one_mem, by simp⟩

end Nonidentity

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ z)
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (pres : ParabolicRootPresentation p l a)

local instance : Mono pres.data.i.hom.hom.left :=
  pres.isCompatible.maximalSplit.isSplitSubtorus.mono

/-- The original pulled-back unramified character on a nonidentity piece has
its original parameter minus a nonzero vector in the source parabolic cone. -/
theorem normalizedRealPart_piece_eq_sub_nonzeroCone_of_nonidentity
    (hLevi : lQ ≫ q = l ≫ p)
    (hG : IsConnectedReductive G) (R : RelativeRootReflectionData pres.data.i)
    (ψ : leviUnramifiedCharacters l hl)
    (hψ : leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ ∈
      restrictedCorootChamber pres.data.i pres.data.ν pres.data.J pres.data.f R)
    (b : A.toGrp ⟶ D.L') (hb : b ≫ D.lQ' ≫ D.q' = a)
    (hz : DoubleCoset.mk (pointImage p) (pointImage q) z ≠
      DoubleCoset.mk (pointImage p) (pointImage q) 1) :
    letI := leviPointTopology l hl
    ∃ δ : Vstar A, δ ∈ pres.nonnegCone ∧ δ ≠ 0 ∧
      Plancherel.SplitTorus.normalizedRealPart
        pres.isCompatible.splitComponent.isCentralSplitTorus.1.1
        (ψ.val.toMonoidHom.comp
          (rationalPoints.map (b ≫ D.φ.hom ≫ D.l' ≫ D.p'))) =
        leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ - δ := by
  let := leviPointTopology l hl
  obtain ⟨mS, mT, n, hn⟩ := D.exists_normalizerPoint_sameLevi pres hLevi
  have hw := inverse_normalizerClass_not_mem_standardLeviWeyl pres q z hz mS mT n hn
  obtain ⟨δ, hδ, hδ0, hres⟩ :=
    restrict_weyl_leviUnramifiedFullRealPart_eq_sub_nonzeroCone pres hG R ψ hψ
      ((QuotientGroup.mk n)⁻¹) hw
  refine ⟨δ, hδ, hδ0, ?_⟩
  rw [D.normalizedRealPart_piece_eq_of_normalizerCorrection
    pres hLevi b hb mS mT n hn ψ]
  exact hres

/-- The existing full-piece parameter has the same nonzero source-cone
displacement along every supplied target split-component factor. -/
theorem unramifiedPieceRealPart_eq_sub_nonzeroCone_of_nonidentity
    (hLevi : lQ ≫ q = l ≫ p)
    (hG : IsConnectedReductive G) (R : RelativeRootReflectionData pres.data.i)
    (ψ : leviUnramifiedCharacters l hl)
    (hψ : leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ ∈
      restrictedCorootChamber pres.data.i pres.data.ν pres.data.J pres.data.f R)
    {A' : CommGroupScheme (Spec (CommRingCat.of k))}
    (a' : A'.toGrp ⟶ D.L') (f : A ⟶ A')
    (hf : CommGroupScheme.groupHom f ≫ a' ≫ D.lQ' ≫ D.q' = a)
    (hz : DoubleCoset.mk (pointImage p) (pointImage q) z ≠
      DoubleCoset.mk (pointImage p) (pointImage q) 1) :
    ∃ δ : Vstar A, δ ∈ pres.nonnegCone ∧ δ ≠ 0 ∧
      D.unramifiedPieceRealPart pres.isCompatible.splitComponent a' f ψ =
        leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ - δ := by
  have hb : (CommGroupScheme.groupHom f ≫ a') ≫ D.lQ' ≫ D.q' = a := by
    simpa only [Category.assoc] using hf
  simpa only [unramifiedPieceRealPart, Category.assoc] using
    D.normalizedRealPart_piece_eq_sub_nonzeroCone_of_nonidentity
      pres hLevi hG R ψ hψ (CommGroupScheme.groupHom f ≫ a') hb hz

/-- The displacement of the original unramified piece parameter from the
original Levi split-component parameter. -/
def unramifiedPieceDisplacement
    (ψ : leviUnramifiedCharacters l hl)
    {A' : CommGroupScheme (Spec (CommRingCat.of k))}
    (a' : A'.toGrp ⟶ D.L') (f : A ⟶ A') : Vstar A :=
  leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ -
    D.unramifiedPieceRealPart pres.isCompatible.splitComponent a' f ψ

/-- The actual displacement is a nonzero vector in the source parabolic cone. -/
theorem unramifiedPieceDisplacement_mem_nonnegCone_and_ne_zero
    (hLevi : lQ ≫ q = l ≫ p)
    (hG : IsConnectedReductive G) (R : RelativeRootReflectionData pres.data.i)
    (ψ : leviUnramifiedCharacters l hl)
    (hψ : leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ ∈
      restrictedCorootChamber pres.data.i pres.data.ν pres.data.J pres.data.f R)
    {A' : CommGroupScheme (Spec (CommRingCat.of k))}
    (a' : A'.toGrp ⟶ D.L') (f : A ⟶ A')
    (hf : CommGroupScheme.groupHom f ≫ a' ≫ D.lQ' ≫ D.q' = a)
    (hz : DoubleCoset.mk (pointImage p) (pointImage q) z ≠
      DoubleCoset.mk (pointImage p) (pointImage q) 1) :
    D.unramifiedPieceDisplacement pres ψ a' f ∈ pres.nonnegCone ∧
      D.unramifiedPieceDisplacement pres ψ a' f ≠ 0 := by
  obtain ⟨δ, hδ, hδ0, hreal⟩ :=
    D.unramifiedPieceRealPart_eq_sub_nonzeroCone_of_nonidentity
      pres hLevi hG R ψ hψ a' f hf hz
  simpa only [unramifiedPieceDisplacement, hreal, sub_sub_cancel] using And.intro hδ hδ0

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
