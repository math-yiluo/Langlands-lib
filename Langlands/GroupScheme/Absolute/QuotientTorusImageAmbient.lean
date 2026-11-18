import Langlands.GroupScheme.Absolute.QuotientTorusImage
import Langlands.GroupScheme.Absolute.BorelMaximalTorusProof
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.Rational.TorusCentralizerImage

/-! # Maximal-torus images from Borel images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuotientTorusImage

variable {k : Type u} [Field k]
  {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- Every Borel of the source has a Borel image under the supplied homomorphism, with
an actual surjective factor map. -/
def BorelImagesExist (q : G ⟶ Q) : Prop :=
  ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
    IsBorelSubgroup b → ∃ (C : GroupScheme (Spec (CommRingCat.of k)))
      (c : C ⟶ Q) (p : B ⟶ C), IsBorelSubgroup c ∧
        Surjective p.hom.hom.left ∧ b ≫ q = p ≫ c

variable [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]

omit [ConnectedSpace G.X.left] in
/-- If each Borel subgroup has a Borel image under a homomorphism, every supplied smooth
closed image of a maximal torus is maximal. -/
theorem isMaximalTorus_image_of_borel_images (q : G ⟶ Q)
    (himages : BorelImagesExist q)
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ G) (s : S.toGrp ⟶ Q) (f : T.toGrp ⟶ S.toGrp)
    (hs : IsClosedSubgroup s) (hSsm : Smooth S.X.hom)
    (hf : Surjective f.hom.hom.left) (hcomm : t ≫ q = f ≫ s)
    (ht : IsMaximalTorus t) : IsMaximalTorus s := by
  obtain ⟨B, b, hb, _, tB, htB⟩ := maximalToriLieInBorels G T t ht
  let : Smooth B.X.hom := hb.smooth
  let : IsAffineHom B.X.hom := hb.isClosedSubgroup.isAffineHom
  let : ConnectedSpace B.X.left := hb.connectedSpace
  obtain ⟨C, c, p, hc, hp, hbc⟩ := himages B b hb
  let : Smooth C.X.hom := hc.smooth
  let : IsAffineHom C.X.hom := hc.isClosedSubgroup.isAffineHom
  let : ConnectedSpace C.X.left := hc.connectedSpace
  let : Smooth S.X.hom := hSsm
  let : IsReduced S.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k S.X.left S.X.hom
  let : Surjective f.hom.hom.left := hf
  let : IsSchemeTheoreticallyDominant f.hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have hr : SubgroupFunctor.range s ≤ SubgroupFunctor.range c := by
    apply (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant f s c
      hc.isClosedSubgroup).mp
    rw [← hcomm, ← htB, Category.assoc, hbc, ← Category.assoc]
    intro V x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ (tB ≫ p).hom.hom, by
      simp only [Grp.comp_hom_hom, Category.assoc]⟩
  have hcrep : (SubgroupFunctor.range c).IsRepresentedBy c := by
    let : Mono c.hom.hom.left := hc.isClosedSubgroup.mono
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  let sC : S.toGrp ⟶ C := hcrep.factorHom s hr
  have hsC : sC ≫ c = s := hcrep.factorHom_comp s hr
  have hcommC : tB ≫ p = f ≫ sC := by
    let : Mono c.hom.hom.left := hc.isClosedSubgroup.mono
    let : Mono c.hom.hom := Over.mono_of_mono_left _
    let : Mono c := (Grp.forget _).mono_of_mono_map (inferInstance : Mono c.hom.hom)
    apply (cancel_mono c).mp
    rw [Category.assoc, ← hbc, ← Category.assoc, htB, Category.assoc, hsC, hcomm]
  have htBmax : IsMaximalTorus tB :=
    IsMaximalTorus.of_comp hb.isClosedSubgroup (htB ▸ ht)
  have hsCmax : IsMaximalTorus sC := isMaximalTorus_image_solvable
    hb.isSolvableGroupScheme hc.isSolvableGroupScheme p hp tB sC f
    (IsClosedSubgroup.of_comp hc.isClosedSubgroup (hsC ▸ hs)) hSsm hf hcommC htBmax
  have hconj : MaximalToriAreConjugate C :=
    solvableMaximalTorusConjugacy k C hc.isSolvableGroupScheme
  obtain ⟨T', t', ht'⟩ := borelMaximalTorus k Q C c hc
  obtain ⟨a, ha⟩ := ht'.2.2
  have hambient : IsMaximalTorus (sC ≫ c) :=
    hconj.isMaximalTorus_comp c hc.isClosedSubgroup hsCmax ⟨T', a, ha ▸ ht'.2.1⟩
  rwa [hsC] at hambient

end Langlands.GroupScheme.QuotientTorusImage
