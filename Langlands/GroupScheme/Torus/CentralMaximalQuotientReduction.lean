import Langlands.GroupScheme.Torus.CentralMaximalQuotientStatement
import Langlands.GroupScheme.Torus.CentralExtensionStatement
import Langlands.GroupScheme.Torus.ImageStatement
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.FieldSeparatedProof

/-! # Reduction of Milne 16.43 for central maximal tori to extensions and images of tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Central extensions of tori by tori being tori, and homomorphisms from tori factoring through
closed tori, imply that the quotient by a central maximal torus contains no torus, at every
universe. -/
def CentralMaximalTorusQuotientReductionStatement : Prop :=
  CentralTorusExtensionStatement.{u} → TorusImageClosedTorusStatement.{u} →
    CentralMaximalTorusQuotientStatement.{u}

/-- The inverse image `E = T ×_Q H` of a homomorphism `g : T ⟶ Q` from a torus is a central
extension of `T` by `Z`, hence a torus; its image in `H` lies in a closed torus containing `Z`,
which by maximality equals `Z`, so `g` is trivial. Both structural statements remain explicit
hypotheses. -/
theorem centralMaximalTorusQuotientReduction :
    CentralMaximalTorusQuotientReductionStatement.{u} := by
  intro hext himage k _ H _ _ Z j hjc hjm Q q hq T hT g
  -- `j` followed by `q` is trivial.
  have hjq : j ≫ q = 0 := by
    have hmem : j.hom.hom ∈ (SubgroupFunctor.range (kernelι q)).carrier (Z.toGrp.X) := by
      rw [hq.2.2.2]
      exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
    rw [mem_range_kernelι_iff] at hmem
    exact (Grp.forget _).map_injective hmem
  -- The inverse image `E` of `g` with its projections `p : E ⟶ T` and `e : E ⟶ H`.
  let E : GroupScheme (Spec (CommRingCat.of k)) := pullback g q
  let p : E ⟶ T.toGrp := pullback.fst g q
  let e : E ⟶ H := pullback.snd g q
  have hpb : IsPullback p.hom.hom e.hom.hom g.hom.hom q.hom.hom :=
    IsPullback.map (Grp.forget _) (IsPullback.of_hasPullback g q)
  have hpbS : IsPullback p.hom.hom.left e.hom.hom.left g.hom.hom.left q.hom.hom.left :=
    IsPullback.map (Over.forget _) hpb
  -- The inclusion `zE : Z ⟶ E` lifting `j`.
  let zE : Z.toGrp ⟶ E := pullback.lift 0 j (by rw [zero_comp, hjq])
  have hzEp : zE ≫ p = 0 := pullback.lift_fst _ _ _
  have hzEe : zE ≫ e = j := pullback.lift_snd _ _ _
  have hzEp' : zE.hom.hom ≫ p.hom.hom = 1 := congrArg (fun φ => φ.hom.hom) hzEp
  have hzEe' : zE.hom.hom ≫ e.hom.hom = j.hom.hom := congrArg (fun φ => φ.hom.hom) hzEe
  have hcentral : IsCentral zE := by
    intro U x U' a h
    rw [← Category.assoc]
    refine hpb.hom_ext ?_ ?_
    · rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, hzEp', MonObj.comp_one, one_mul,
        mul_one]
    · rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, hzEe']
      exact (commute_of_mem_center (hjc U' (a ≫ x)) (h ≫ e.hom.hom)).eq
  have hclosed : IsClosedSubgroup zE := by
    have : IsSeparated T.toGrp.X.hom := fieldSeparated k T.toGrp
    have : IsSeparated (g.hom.hom.left ≫ Q.X.hom) := by rw [Over.w]; infer_instance
    have : IsSeparated g.hom.hom.left := IsSeparated.of_comp _ Q.X.hom
    have : IsSeparated e.hom.hom.left := MorphismProperty.of_isPullback hpbS inferInstance
    have : IsClosedImmersion (zE.hom.hom.left ≫ e.hom.hom.left) := by
      rw [← Over.comp_left, hzEe']
      exact hjm.2.1
    exact IsClosedImmersion.of_comp _ e.hom.hom.left
  have hpq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range zE) p := by
    refine ⟨MorphismProperty.of_isPullback hpbS.flip hq.1,
      MorphismProperty.of_isPullback hpbS.flip hq.2.1,
      MorphismProperty.of_isPullback hpbS.flip hq.2.2.1, ?_⟩
    ext U x
    rw [mem_range_kernelι_iff]
    constructor
    · intro hx
      have hxe : x ≫ e.hom.hom ∈ (SubgroupFunctor.range (kernelι q)).carrier U := by
        rw [mem_range_kernelι_iff, Category.assoc, ← hpb.w, ← Category.assoc, hx,
          MonObj.one_comp]
      rw [hq.2.2.2] at hxe
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hxe
      refine SubgroupFunctor.mem_range.mpr ⟨y, hpb.hom_ext ?_ ?_⟩
      · rw [Category.assoc, hzEp', MonObj.comp_one, hx]
      · rw [Category.assoc, hzEe', hy]
    · intro hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      rw [Category.assoc, hzEp', MonObj.comp_one]
  have hpa : IsAffineHom p.hom.hom.left := by
    have : IsSeparated Q.X.hom := fieldSeparated k Q
    have : IsAffineHom (q.hom.hom.left ≫ Q.X.hom) := by rw [Over.w]; infer_instance
    have : IsAffineHom q.hom.hom.left := IsAffineHom.of_comp _ Q.X.hom
    exact MorphismProperty.of_isPullback hpbS.flip inferInstance
  have hE : IsTorus E := hext k E Z zE hjm.1 hclosed hcentral T p hT hpa hpq
  obtain ⟨Z', j', f, hZ', hj', hf⟩ := himage k H E hE e
  have hiso : IsIso (zE ≫ f) :=
    hjm.2.2 Z' j' (zE ≫ f) hZ' hj' (by rw [Category.assoc, hf, hzEe])
  have hj' : j' = inv (zE ≫ f) ≫ j := by
    have h : (zE ≫ f) ≫ j' = j := by rw [Category.assoc, hf, hzEe]
    rw [← h, IsIso.inv_hom_id_assoc]
  -- Hence `p ≫ g` is trivial, and `g` is trivial because `p` is faithfully flat.
  have hpg : p ≫ g = 0 := by
    rw [show p ≫ g = e ≫ q from pullback.condition, ← hf, hj', Category.assoc, Category.assoc, hjq, comp_zero, comp_zero]
  have : Flat p.hom.hom.left := hpq.1
  have : Surjective p.hom.hom.left := hpq.2.1
  have : Epi p.hom.hom.left := Flat.epi_of_flat_of_surjective _
  have hg : g.hom.hom = 1 := by
    ext1
    refine (cancel_epi p.hom.hom.left).mp ?_
    rw [← Over.comp_left, ← Over.comp_left]
    exact congrArg (fun φ => φ.hom.hom.left) (hpg.trans (comp_zero).symm)
  ext U x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [hg, MonObj.comp_one]
  · rintro rfl
    exact Subgroup.one_mem _

end Langlands.GroupScheme
