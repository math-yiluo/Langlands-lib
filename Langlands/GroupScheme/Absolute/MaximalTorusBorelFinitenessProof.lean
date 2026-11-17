import Langlands.GroupScheme.Absolute.MaximalTorusBorelFinitenessStatement
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionProof
import Langlands.GroupScheme.Cartan.StructureProof
import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # Finitely many Borel subgroups through a maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MaximalTorusBorelFiniteness

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G B B' : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The whole maximal-torus centralizer lies in each Borel containing the torus. -/
theorem centralizer_le_borel
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    (b : B ⟶ G) (hb : IsBorelSubgroup b)
    (hjb : SubgroupFunctor.range j ≤ SubgroupFunctor.range b) :
    torusCentralizer j ≤ SubgroupFunctor.range b := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨C, c, hc, hrep⟩ := exists_isCartanSubgroup_of_isMaximalTorus hj
  obtain ⟨hsm, hconn, hnil⟩ := cartanStructure k G C c hc
  let : Smooth C.X.hom := hsm
  let : ConnectedSpace C.X.left := hconn
  have hsplit := hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨ν, hν⟩ := hsplit.exists_cocharacter_centralizer j
  let χ := CommGroupScheme.groupHom ν ≫ j
  have hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b := by
    intro V x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply hjb V
    exact SubgroupFunctor.mem_range.mpr
      ⟨t ≫ (CommGroupScheme.groupHom ν).hom.hom, Category.assoc _ _ _⟩
  have hrepχ : (Dynamic.centralizer χ).IsRepresentedBy c := by
    rw [show Dynamic.centralizer χ = torusCentralizer j from hν]
    exact hrep
  obtain ⟨D, d, hd, hdb⟩ :=
    centralizerBorelIntersection k G χ C c hc.1 hrepχ hsm hconn B b hb hχ
  have : IsIso d := hd.maximal C (𝟙 C) d (by
    change IsClosedImmersion (𝟙 C.X.left)
    infer_instance) hsm hconn hnil.isSolvableGroupScheme (Category.comp_id _)
  have hdc : SubgroupFunctor.range (d ≫ c) = SubgroupFunctor.range c :=
    SubgroupFunctor.range_iso_comp (asIso d) c
  rw [← hrep.2, ← hdc]
  exact hdb

/-- Conjugacy of Borels and maximal tori gives normalizer transitivity. -/
theorem exists_normalizer_conjugating_borel
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    (b : B ⟶ G) (hb : IsBorelSubgroup b)
    (hjb : SubgroupFunctor.range j ≤ SubgroupFunctor.range b)
    (b' : B' ⟶ G) (hb' : IsBorelSubgroup b')
    (hjb' : SubgroupFunctor.range j ≤ SubgroupFunctor.range b') :
    ∃ n : normalizerPoints j,
      SubgroupFunctor.range (b ≫ (G.innerIso n.val).hom) =
        SubgroupFunctor.range b' := by
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : IsClosedImmersion b'.hom.hom.left := hb'.isClosedSubgroup
  have hr : (SubgroupFunctor.range b).IsRepresentedBy b :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hr' : (SubgroupFunctor.range b').IsRepresentedBy b' :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let f := hr.factorHom j hjb
  let f' := hr'.factorHom j hjb'
  have hf : f ≫ b = j := hr.factorHom_comp j hjb
  have hf' : f' ≫ b' = j := hr'.factorHom_comp j hjb'
  have hfmax : IsMaximalTorus f := IsMaximalTorus.of_comp hb.isClosedSubgroup (hf ▸ hj)
  have hf'max : IsMaximalTorus f' := IsMaximalTorus.of_comp hb'.isClosedSubgroup (hf' ▸ hj)
  obtain ⟨g, e, he⟩ := (borelConjugacy k G).2 B B' b b' hb hb'
  let : Smooth B'.X.hom := hb'.smooth
  let : ConnectedSpace B'.X.left := hb'.connectedSpace
  let : IsAffineHom B'.X.hom := by
    rw [← Over.w b'.hom.hom]
    infer_instance
  obtain ⟨p, σ, hp⟩ :=
    maximalTorusConjugacy k B' T T (f ≫ e.hom) f' (hfmax.comp_iso e) hf'max
  let n := (p ≫ b'.hom.hom) * g
  have hn : j ≫ (G.innerIso n).hom = CommGroupScheme.groupHom σ.hom ≫ j := by
    calc
      _ = ((f ≫ e.hom) ≫ (B'.innerIso p).hom) ≫ b' := by
        rw [← hf, innerIso_mul_hom]
        simp only [Category.assoc]
        rw [reassoc_of% he, innerIso_hom_comp b' p]
      _ = (CommGroupScheme.groupHom σ.hom ≫ f') ≫ b' := by rw [hp]
      _ = CommGroupScheme.groupHom σ.hom ≫ j := by rw [Category.assoc, hf']
  refine ⟨⟨n, σ, hn⟩, ?_⟩
  change SubgroupFunctor.range (b ≫ (G.innerIso n).hom) = _
  have hbn : b ≫ (G.innerIso n).hom = (e ≪≫ B'.innerIso p).hom ≫ b' := by
    rw [innerIso_mul_hom]
    simp only [Category.assoc, Iso.trans_hom]
    rw [reassoc_of% he, innerIso_hom_comp b' p]
  rw [hbn, SubgroupFunctor.range_iso_comp]

omit [IsAlgClosed k] in
/-- Right multiplication by a point of a subgroup preserves its conjugate range. -/
theorem range_conjugate_mul
    (b : B ⟶ G)
    (n z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hz : z ∈ (SubgroupFunctor.range b).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    SubgroupFunctor.range (b ≫ (G.innerIso (n * z)).hom) =
      SubgroupFunctor.range (b ≫ (G.innerIso n).hom) := by
  obtain ⟨p, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  rw [innerIso_mul_hom, ← Category.assoc,
    ← innerIso_hom_comp b p, Category.assoc, SubgroupFunctor.range_iso_comp]

end MaximalTorusBorelFiniteness

/-- Milne, Corollary 17.26(a): a maximal torus of a smooth connected affine
group over an algebraically closed field lies in finitely many Borel subgroups. -/
theorem maximalTorusBorelFiniteness : MaximalTorusBorelFinitenessStatement.{u} := by
  classical
  intro k _ _ G _ _ _ T j hj
  have : IsClosedImmersion j.hom.hom.left := hj.2.1
  have hsplit := hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  let : Finite (weylAction j).range := splitTorusWeylImageFinite k G T hsplit j hj.2.1
  have hquot : Finite (relativeWeylGroup j) := by
    unfold relativeWeylGroup
    rw [← hsplit.weylAction_ker j]
    exact Finite.of_injective (QuotientGroup.quotientKerEquivRange (weylAction j))
      (QuotientGroup.quotientKerEquivRange (weylAction j)).injective
  let : Finite (relativeWeylGroup j) := hquot
  obtain ⟨B, b, hb, _, f, hf⟩ := maximalToriLieInBorels G T j hj
  have hjb : SubgroupFunctor.range j ≤ SubgroupFunctor.range b := by
    intro V x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr
      ⟨t ≫ f.hom.hom, by rw [← hf, Grp.comp_hom_hom, Category.assoc]⟩
  have hc : centralizerPoints j ≤ (SubgroupFunctor.range b).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    fun _ hn => MaximalTorusBorelFiniteness.centralizer_le_borel j hj b hb hjb _
      (centralizerPoints_le_torusCentralizer j hn)
  let orbit : relativeWeylGroup j → SubgroupFunctor G :=
    Quotient.lift (fun n : normalizerPoints j =>
      SubgroupFunctor.range (b ≫ (G.innerIso n.val).hom)) (by
        intro n n' h
        have heq : (QuotientGroup.mk n : relativeWeylGroup j) = QuotientGroup.mk n' :=
          Quotient.sound h
        have hz : n⁻¹ * n' ∈ (centralizerPoints j).subgroupOf (normalizerPoints j) :=
          QuotientGroup.eq.mp heq
        have hr := MaximalTorusBorelFiniteness.range_conjugate_mul b n.val
          (n.val⁻¹ * n'.val) (hc hz)
        simpa only [mul_inv_cancel_left] using hr.symm)
  apply (Set.finite_range orbit).subset
  rintro F ⟨B', b', hb', rfl, hjb'⟩
  obtain ⟨n, hn⟩ :=
    MaximalTorusBorelFiniteness.exists_normalizer_conjugating_borel j hj b hb hjb b' hb' hjb'
  exact ⟨QuotientGroup.mk n, hn⟩

end Langlands.GroupScheme
