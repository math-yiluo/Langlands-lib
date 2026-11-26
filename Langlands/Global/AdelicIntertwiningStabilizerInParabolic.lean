import Langlands.Global.AdelicIntertwiningCommonCocharacters
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison
import Langlands.GroupScheme.Dynamic.ParabolicLieDecomposition

/-! # The intertwining stabilizer as a dynamic subgroup of the target parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {iU : U ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  {q : Q ⟶ G} {l' : M' ⟶ Q} {iV : V ⟶ Q} {a' : A'.toGrp ⟶ M'}
  (r' : ParabolicRootPresentation q l' a')
  {c : M' ⟶ M} {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
  (hw : IsWeylConjugation p l q l' w c)

local notation "χP" => CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p
local notation "χQ" => CommGroupScheme.groupHom r'.splitComponentCocharacter ≫ a' ≫ l' ≫ q
local notation "d" => (iU ≫ p ≫ Iso.hom (G.innerIso w))
local notation "j" => iV ≫ q
local notation "C" => IntertwiningStabilizer p iU (iV ≫ q) w

/-- The actual stabilizer's immersion into the target parabolic. -/
def intertwiningStabilizerToParabolic (iU : U ⟶ P) (iV : V ⟶ Q) (q : Q ⟶ G)
    (p : P ⟶ G) (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :
    IntertwiningStabilizer p iU (iV ≫ q) w ⟶ Q :=
  subgroupIntersectionFst (iV ≫ q) (iU ≫ p ≫ (G.innerIso w).hom) ≫ iV

local notation "ιC" => intertwiningStabilizerToParabolic iU iV q p w

@[simp, reassoc] theorem intertwiningStabilizerToParabolic_comp :
    ιC ≫ q = intertwiningStabilizerHom p iU j w := by
  rw [intertwiningStabilizerToParabolic, Category.assoc]
  rfl

private theorem range_of_mono_after_comp {J H X : GroupScheme (Spec (CommRingCat.of F))}
    (f : J ⟶ H) (g : H ⟶ X) [Mono g.hom.hom] :
    (SubgroupFunctor.range (f ≫ g)).comap g = SubgroupFunctor.range f := by
  ext T x
  simp only [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, Grp.comp_hom_hom, ← Category.assoc]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, (cancel_mono g.hom.hom).mp hy⟩,
    fun ⟨y, hy⟩ => ⟨y, congrArg (fun z => z ≫ g.hom.hom) hy⟩⟩

private theorem range_intersection_to_intermediate {N X Y W : GroupScheme (Spec (CommRingCat.of F))}
    (u : N ⟶ W) (v : X ⟶ Y) (q : Y ⟶ W) :
    SubgroupFunctor.range (subgroupIntersectionFst (v ≫ q) u ≫ v) =
      SubgroupFunctor.range v ⊓ (SubgroupFunctor.range u).comap q := by
  let baseMap := v ≫ q
  let i := subgroupIntersectionFst baseMap u
  ext T x
  change x ∈ (SubgroupFunctor.range (i ≫ v)).carrier T ↔
    x ∈ ((SubgroupFunctor.range v) ⊓ (SubgroupFunctor.range u).comap q).carrier T
  rw [SubgroupFunctor.inf_carrier, Subgroup.mem_inf, SubgroupFunctor.mem_comap,
    SubgroupFunctor.mem_range, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    have hz : z ≫ i.hom.hom ∈ (SubgroupFunctor.range i).carrier T := ⟨z, rfl⟩
    have hi : SubgroupFunctor.range i = (SubgroupFunctor.range u).comap baseMap :=
      range_subgroupIntersectionFst_eq_comap baseMap u
    rw [hi, SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range] at hz
    have h₁ : (z ≫ i.hom.hom) ≫ v.hom.hom = z ≫ (i ≫ v).hom.hom := by
      rw [Grp.comp_hom_hom, Category.assoc]
    have h₂ : (z ≫ i.hom.hom) ≫ baseMap.hom.hom = (z ≫ (i ≫ v).hom.hom) ≫ q.hom.hom := by
      simp only [baseMap, Grp.comp_hom_hom, Category.assoc]
    exact ⟨⟨_, h₁⟩, by rwa [← h₂]⟩
  · rintro ⟨⟨z, rfl⟩, y, hy⟩
    have h : y ≫ u.hom.hom = z ≫ baseMap.hom.hom := by
      change y ≫ u.hom.hom = z ≫ (v ≫ q).hom.hom
      rw [Grp.comp_hom_hom, ← Category.assoc]
      exact hy
    have hz : z ∈ ((SubgroupFunctor.range u).comap baseMap).carrier T := ⟨y, h⟩
    have hi : SubgroupFunctor.range i = (SubgroupFunctor.range u).comap baseMap :=
      range_subgroupIntersectionFst_eq_comap baseMap u
    rw [← hi, SubgroupFunctor.mem_range] at hz
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hx]

include r' hw in
set_option maxHeartbeats 700000 in
/-- The transported cocharacter takes values in the target Levi. Inside the target parabolic,
its centralizer is that Levi and its identity-limit subgroup is the intertwining stabilizer. -/
theorem exists_intertwiningStabilizer_dynamic
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) :
    ∃ χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ Q,
      χ ≫ q = χP ≫ (G.innerIso w).hom ∧
      (Dynamic.centralizer χ).IsRepresentedBy l' ∧
      (Dynamic.unipotent χ).IsRepresentedBy ιC := by
  let : IsIso c := hw.isIso
  let χM := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ inv c
  let χ := χM ≫ l'
  have : IsClosedImmersion q.hom.hom.left := r'.isCompatible.parabolic.isClosedSubgroup
  have : Mono q.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion l'.hom.hom.left := r'.isCompatible.levi.isClosedSubgroup
  have : Mono l'.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion (l' ≫ q).hom.hom.left :=
    r'.isCompatible.levi.isClosedSubgroup.comp r'.isCompatible.parabolic.isClosedSubgroup
  have : Mono (l' ≫ q).hom.hom := Over.mono_of_mono_left _
  have hχ : χ ≫ q = χP ≫ (G.innerIso w).hom := by
    simpa only [χ, χM, Category.assoc] using congrArg
      (fun k : M ⟶ G => CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ k)
      hw.comp_inner_hom.symm
  have hZ' : Dynamic.centralizer (χ ≫ q) = SubgroupFunctor.range (l' ≫ q) := by
    rw [hχ, centralizer_conjugate_sourceCocharacter r hw]
  have hZc : Dynamic.centralizer χ = SubgroupFunctor.range l' := by
    rw [Dynamic.centralizer_eq_comap_of_mono χ q, hZ', range_of_mono_after_comp]
  have hχM : Dynamic.centralizer χM = ⊤ := by
    rw [Dynamic.centralizer_eq_comap_of_mono χM (l' ≫ q)]
    have hcomp : χM ≫ l' ≫ q = χ ≫ q := by simp only [χ, Category.assoc]
    rw [hcomp, hZ']
    ext T x
    simp only [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.top_carrier,
      Subgroup.mem_top, iff_true]
    exact ⟨x, rfl⟩
  have : IsAffineHom M'.X.hom := r'.isCompatible.levi.isConnectedReductive.isAffineHom
  have hUbot : Dynamic.unipotent χM = ⊥ := by
    have h := (AutomorphicAction.cocharacterAction χM).centralizer_inf_unipotent_eq_bot
    rw [AutomorphicAction.cocharacterAction_centralizer, AutomorphicAction.cocharacterAction_unipotent] at h
    rw [hχM] at h
    have htop : ⊤ ⊓ Dynamic.unipotent χM = Dynamic.unipotent χM := by
      ext T x
      simp
    rwa [htop] at h
  let τ := χQ
  have : IsClosedImmersion (iV ≫ q).hom.hom.left := hV.1.isClosedSubgroup.comp r'.isCompatible.parabolic.isClosedSubgroup
  have : Mono (iV ≫ q).hom.hom := Over.mono_of_mono_left _
  have hQ : (Dynamic.parabolic τ).IsRepresentedBy q := ⟨inferInstance, r'.parabolic_eq_splitComponentCocharacter⟩
  have hM' : (Dynamic.centralizer τ).IsRepresentedBy (l' ≫ q) :=
    ⟨inferInstance, r'.levi_eq_splitComponentCocharacter⟩
  have hV' : (Dynamic.unipotent τ).IsRepresentedBy (iV ≫ q) := ⟨inferInstance, r'.range_comp_radical_eq hV⟩
  let lim := Dynamic.limitGroupHom hQ hM'
  have hl : Dynamic.centralizerToParabolic hQ hM' = l' :=
    hQ.hom_ext (Dynamic.centralizerToParabolic_comp hQ hM')
  have hlim : l' ≫ lim = 𝟙 _ := hl ▸ Dynamic.centralizerToParabolic_comp_limitGroupHom hQ hM'
  have hχlim : χ ≫ lim = χM := by rw [show χ = χM ≫ l' from rfl, Category.assoc, hlim, Category.comp_id]
  have hsub : Dynamic.unipotent χ ≤ SubgroupFunctor.range iV := by
    intro T x hx
    have h := Dynamic.unipotent_le_comap χ lim T hx
    rw [SubgroupFunctor.mem_comap, hχlim, hUbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at h
    have hx' := (Dynamic.limitGroupHom_eq_one_iff τ hQ hM' x).mp h
    rw [← hV'.2, SubgroupFunctor.mem_range] at hx'
    obtain ⟨v, hv⟩ := hx'
    exact SubgroupFunctor.mem_range.mpr ⟨v, (cancel_mono q.hom.hom).mp (by
      simpa only [Grp.comp_hom_hom, Category.assoc] using hv)⟩
  have hd : IsClosedSubgroup d := by
    rw [← Category.assoc iU p]
    exact (hU.1.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup).comp_iso (G.innerIso w)
  have hC : IsClosedSubgroup ιC := (isClosedSubgroup_subgroupIntersectionFst j hd).comp hV.1.isClosedSubgroup
  have : Mono (ιC).hom.hom.left := hC.mono
  have : Mono (ιC).hom.hom := Over.mono_of_mono_left _
  refine ⟨χ, hχ, ⟨inferInstance, hZc.symm⟩, ⟨inferInstance, ?_⟩⟩
  have hcomap : Dynamic.unipotent χ = (SubgroupFunctor.range d).comap q := by
    rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup χ q r'.isCompatible.parabolic.isClosedSubgroup,
      hχ, range_conjugate_sourceRadical r hU]
  have hinf : SubgroupFunctor.range ιC = (SubgroupFunctor.range iV) ⊓ (SubgroupFunctor.range d).comap q :=
    range_intersection_to_intermediate d iV q
  rw [hinf, ← hcomap]
  apply SubgroupFunctor.ext
  intro T
  exact Subgroup.ext fun x => ⟨And.right, fun hx => ⟨hsub T hx, hx⟩⟩

end Langlands.Global.AdelicGroupPoints
