import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.SplitOfDomination

/-! # Realizing prescribed subgroup images by rational conjugation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuotientSubgroupRealization

variable {k : Type u} [Field k]

/-- The given homomorphism has a surjective factorization through a supplied target map,
with the ambient homomorphism and the source map fixed. No embedding is assumed here. -/
def HasSurjectiveImageFactorization
    {G Q H C : GroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ Q) (i : H ⟶ G) (j : C ⟶ Q) : Prop :=
  ∃ p : H ⟶ C, Surjective p.hom.hom.left ∧ i ≫ q = p ≫ j

variable [IsAlgClosed k]

/-- A rational conjugate of a supplied image is the image of a rational conjugate upstairs. -/
theorem exists_conjugate_image
    {G Q H C C' : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom]
    (q : G ⟶ Q) (hq : Surjective q.hom.hom.left)
    (i : H ⟶ G) (j : C ⟶ Q) (p : H ⟶ C)
    (hp : Surjective p.hom.hom.left) (hcomm : i ≫ q = p ≫ j)
    (j' : C' ⟶ Q) (hconj : SubgroupConjugate j j') :
    ∃ g : rationalPoints G,
      HasSurjectiveImageFactorization q (i ≫ (G.innerIso g).hom) j' := by
  let : Surjective q.hom.hom.left := hq
  have : LocallyOfFiniteType (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w]
    infer_instance
  let : LocallyOfFiniteType q.hom.hom.left :=
    locallyOfFiniteType_of_comp q.hom.hom.left Q.X.hom
  obtain ⟨x, e, he⟩ := hconj
  obtain ⟨g, hg⟩ := exists_rationalPointLift q x
  refine ⟨g, p ≫ e.hom, ?_, ?_⟩
  · let : Surjective p.hom.hom.left := hp
    have : IsIso e.hom.hom.hom.left :=
      (Over.forget _).map_isIso ((Grp.forget _).map e.hom)
    change Surjective (p.hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  · rw [Category.assoc, innerIso_hom_comp, hg, ← Category.assoc, hcomm,
      Category.assoc, he, ← Category.assoc]

section Connected

variable {G Q : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]

/-- Borel images and rational conjugacy realize every prescribed Borel subgroup downstairs. -/
theorem exists_borel_image_of_borel_images (q : G ⟶ Q)
    (hq : Surjective q.hom.hom.left)
    (himages : ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
      IsBorelSubgroup b → ∃ (C : GroupScheme (Spec (CommRingCat.of k)))
        (c : C ⟶ Q) (p : B ⟶ C), IsBorelSubgroup c ∧
          Surjective p.hom.hom.left ∧ b ≫ q = p ≫ c)
    {C' : GroupScheme (Spec (CommRingCat.of k))} (j : C' ⟶ Q)
    (hj : IsBorelSubgroup j) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G) (f : B ⟶ C'),
      IsBorelSubgroup b ∧ Surjective f.hom.hom.left ∧ b ≫ q = f ≫ j := by
  obtain ⟨B, b, hb⟩ := (borelConjugacy k G).1
  obtain ⟨C, c, p, hc, hp, hcomm⟩ := himages B b hb
  have hconj : SubgroupConjugate c j := (borelConjugacy k Q).2 C C' c j hc hj
  obtain ⟨g, f, hf, hgf⟩ := exists_conjugate_image q hq b c p hp hcomm j hconj
  exact ⟨B, b ≫ (G.innerIso g).hom, f, hb.comp_iso (G.innerIso g), hf, hgf⟩

omit [ConnectedSpace G.X.left] in
/-- Maximal-torus image preservation and rational conjugacy realize every prescribed maximal
 torus downstairs, including a surjective map of commutative source groups. -/
theorem exists_maximalTorus_image_of_maximalTorus_images (q : G ⟶ Q)
    (hq : Surjective q.hom.hom.left)
    (himages : ∀ (T S : CommGroupScheme (Spec (CommRingCat.of k)))
      (t : T.toGrp ⟶ G) (s : S.toGrp ⟶ Q) (p : T.toGrp ⟶ S.toGrp),
      IsClosedSubgroup s → Smooth S.X.hom → Surjective p.hom.hom.left →
        t ≫ q = p ≫ s → IsMaximalTorus t → IsMaximalTorus s)
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (s : S.toGrp ⟶ Q)
    (hs : IsMaximalTorus s) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G) (f : T ⟶ S),
      IsMaximalTorus t ∧ Surjective (CommGroupScheme.groupHom f).hom.hom.left ∧
        t ≫ q = CommGroupScheme.groupHom f ≫ s := by
  obtain ⟨T, t, ht⟩ := exists_isMaximalTorus G
  let : Smooth T.X.hom := ht.1.smooth
  let : ConnectedSpace T.X.left := ht.1.connectedSpace
  let : IsAffineHom T.X.hom := ht.2.1.isAffineHom
  obtain ⟨C, c, p, hc, hpc, hpflat, hp, hpqc, hplfp, hCsm, hCconn, hCa⟩ :=
    HomImage.exists_image (t ≫ q)
  let : Smooth C.X.hom := hCsm
  let : IsAffineHom C.X.hom := hCa
  let : IsReduced C.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k C.X.left C.X.hom
  let : Surjective p.hom.hom.left := hp
  have hT := ht.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have hC : IsSplitTorus C := hT.of_schematicallyDominant_hom p
    (IsSchemeTheoreticallyDominant.of_isDominant _)
  let S₀ : CommGroupScheme (Spec (CommRingCat.of k)) := { C with comm := hC.isCommMonObj }
  have hcmax : IsMaximalTorus (T := S₀) c :=
    himages T S₀ t c p hc hCsm hp hpc.symm ht
  obtain ⟨x, e, he⟩ := maximalTorusConjugacy k Q S₀ S c s hcmax hs
  let eGrp : C ≅ S.toGrp :=
    { hom := CommGroupScheme.groupHom e.hom
      inv := CommGroupScheme.groupHom e.inv
      hom_inv_id := congrArg Additive.toMul e.hom_inv_id
      inv_hom_id := congrArg Additive.toMul e.inv_hom_id }
  have hconj : SubgroupConjugate c s := ⟨x, eGrp, he⟩
  obtain ⟨g, f, hf, hgf⟩ := exists_conjugate_image q hq t c p hp hpc.symm s hconj
  exact ⟨T, t ≫ (G.innerIso g).hom, Additive.ofMul f,
    ht.comp_iso (G.innerIso g), hf, hgf⟩

end Connected

end Langlands.GroupScheme.QuotientSubgroupRealization
