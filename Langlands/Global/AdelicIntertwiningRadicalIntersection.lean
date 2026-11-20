import Langlands.Global.AdelicIntertwiningOperator
import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.GroupScheme.Dynamic.StableIntersection
import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.Representation.Geometric.RepresentedGeometricLemmaDynamicRealization

/-! # The radical of `Q` meets `w P w⁻¹` inside `w U w⁻¹`

For a parabolic `P = MU` with a root presentation, a parabolic `Q = M'V` and a point `w` with
`w⁻¹ M' w = M`, the subgroup functor `w⁻¹ V w ∩ P` lies in `U`, on every test scheme. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- If `P = MU` is presented by `r`, `V` is the geometric unipotent radical of a parabolic `Q`
with a Levi `M'` complementary to it, and `c : M' ≅ M` satisfies `l(c(m')) = w⁻¹ l'(m') w`,
then every point of `w⁻¹ V w` that lies in `P` lies in `U`. -/
theorem range_conj_radical_inf_parabolic_le
    {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (r : ParabolicRootPresentation p l a) {q : Q ⟶ G} {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) {c : M' ⟶ M}
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hmul : IsIso (subgroupMultiplication l' iV)) (hc : IsIso c)
    (hcomp : c ≫ l ≫ p = l' ≫ q ≫ (G.innerIso w).inv) :
    SubgroupFunctor.range (iV ≫ q ≫ (G.innerIso w).inv) ⊓ SubgroupFunctor.range p ≤
      SubgroupFunctor.range (iU ≫ p) := by
  have : IsSeparated G.X.hom := IsSeparated.of_isAffineHom _
  obtain ⟨ζ, -, hP, hM⟩ := r.isCompatible.realization
  set χ := CommGroupScheme.groupHom ζ ≫ r.data.i with hχ
  have hUχ : SubgroupFunctor.range (iU ≫ p) = Dynamic.unipotent χ :=
    radical_range_eq_dynamic_unipotent hG r.isCompatible.parabolic hU χ hP
  set e := (G.innerIso w).inv with he
  -- The conjugated radical `w⁻¹ V w` is a closed subgroup.
  have hqc : IsClosedImmersion q.hom.hom.left := hq.isClosedSubgroup
  have hqm : Mono q.hom.hom := Over.mono_of_mono_left _
  have hjc : IsClosedSubgroup (iV ≫ q ≫ e) := by
    change IsClosedImmersion (iV ≫ q ≫ e).hom.hom.left
    rw [← Category.assoc]
    change IsClosedImmersion ((iV ≫ q).hom.hom.left ≫ e.hom.hom.left)
    have : IsIso e.hom.hom.left := by
      refine ⟨⟨(G.innerIso w).hom.hom.hom.left, ?_, ?_⟩⟩
      · have h := congrArg (fun f : G ⟶ G => f.hom.hom.left) (G.innerIso w).inv_hom_id
        simpa only [he, Grp.comp_hom_hom, Grp.id_hom_hom, Over.comp_left, Over.id_left] using h
      · have h := congrArg (fun f : G ⟶ G => f.hom.hom.left) (G.innerIso w).hom_inv_id
        simpa only [he, Grp.comp_hom_hom, Grp.id_hom_hom, Over.comp_left, Over.id_left] using h
    infer_instance
  have hjm : Mono (iV ≫ q ≫ e).hom.hom := by
    have : IsClosedImmersion (iV ≫ q ≫ e).hom.hom.left := hjc
    exact Over.mono_of_mono_left _
  have hrep : (SubgroupFunctor.range (iV ≫ q ≫ e)).IsRepresentedBy (iV ≫ q ≫ e) := ⟨hjm, rfl⟩
  -- The Levi `M` is `w⁻¹ M' w`.
  have hMrange : SubgroupFunctor.range (l ≫ p) = SubgroupFunctor.range (l' ≫ q ≫ e) := by
    rw [← hcomp]
    exact (SubgroupFunctor.range_iso_comp (asIso c) (l ≫ p)).symm
  have hem : Mono (q ≫ e).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  -- Conjugation by the cocharacter preserves `w⁻¹ V w`.
  have hstable :
      (AutomorphicAction.conjugation χ).IsStable (SubgroupFunctor.range (iV ≫ q ≫ e)) := by
    intro T t g hg
    rw [AutomorphicAction.conjugation_act]
    have hz : t ≫ χ.hom.hom ∈ (SubgroupFunctor.range (l' ≫ q ≫ e)).carrier T := by
      rw [← hMrange, hM]
      exact Dynamic.range_le_centralizer χ T (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩)
    obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hz
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hg
    obtain ⟨v', hv'⟩ := SubgroupFunctor.mem_range.mp
      (hV.1.isNormal T (m ≫ l'.hom.hom) (v ≫ iV.hom.hom) trivial
        (SubgroupFunctor.mem_range.mpr ⟨v, rfl⟩))
    refine SubgroupFunctor.mem_range.mpr ⟨v', ?_⟩
    have key : v' ≫ (iV ≫ q ≫ e).hom.hom = (v' ≫ iV.hom.hom) ≫ (q ≫ e).hom.hom := by
      simp only [Grp.comp_hom_hom, Category.assoc]
    rw [← hm, ← hv, key, hv', MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    simp only [Grp.comp_hom_hom, Category.assoc]
  -- `w⁻¹ V w` meets the centralizer `M` trivially.
  have hbot : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range (iV ≫ q ≫ e)).carrier T →
        x ∈ (Dynamic.centralizer χ).carrier T → x = 1 := by
    intro T x hx hz
    rw [← hM, hMrange] at hz
    obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hz
    have h1 : m ≫ l'.hom.hom = v ≫ iV.hom.hom := by
      apply (cancel_mono (q ≫ e).hom.hom).1
      simpa only [Grp.comp_hom_hom, Category.assoc] using hm
    have h2 : lift m 1 ≫ subgroupMultiplication l' iV =
        lift 1 v ≫ subgroupMultiplication l' iV := by
      rw [comp_subgroupMultiplication, comp_subgroupMultiplication, MonObj.one_comp,
        MonObj.one_comp, mul_one, one_mul, h1]
    have h3 := (cancel_mono _).1 h2
    have hv1 : v = 1 := by
      have := congrArg (fun z => z ≫ snd M'.X V.X) h3
      simpa only [lift_snd] using this.symm
    rw [hv1, MonObj.one_comp]
  intro T x hx
  obtain ⟨hxj, hxp⟩ := hx
  rw [hP] at hxp
  obtain ⟨z, ⟨hzj, hzZ⟩, n, ⟨-, hnU⟩, hzn⟩ :=
    (Dynamic.inf_parabolic_isPointwiseProduct_of_isStable χ hrep hjc hstable T x).1 ⟨hxj, hxp⟩
  rw [hbot T z hzj hzZ, one_mul] at hzn
  rw [hUχ, ← hzn]
  exact hnU

end Langlands.GroupScheme

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
open NumberField Opposite

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

omit [IsAffineHom G.X.hom] in
/-- On adelic points the inverse inner automorphism `(innerIso w)⁻¹` is conjugation
`v ↦ W⁻¹ v W` by the conjugating adelic point `W = innerAdelicPoint F G w`. -/
theorem comp_innerIso_inv_adelic (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (v : AdelicGroupPoints F G) :
    v ≫ (G.innerIso w).inv.hom.hom =
      (innerAdelicPoint F G w)⁻¹ * v * innerAdelicPoint F G w := by
  have h := G.comp_innerIso_hom w ((algSpec (CommRingCat.of F)).obj
    (op (CommAlgCat.of F (AdeleRing (𝓞 F) F)))) (v ≫ (G.innerIso w).inv.hom.hom)
  have hid : (v ≫ (G.innerIso w).inv.hom.hom) ≫ (G.innerIso w).hom.hom.hom = v := by
    have e := congrArg (fun f : G ⟶ G => f.hom.hom) (G.innerIso w).inv_hom_id
    simp only [Grp.comp_hom_hom, Grp.id_hom_hom] at e
    rw [Category.assoc, e, Category.comp_id]
  rw [hid] at h
  set W := innerAdelicPoint F G w
  change v = W * (v ≫ (G.innerIso w).inv.hom.hom) * W⁻¹ at h
  calc v ≫ (G.innerIso w).inv.hom.hom
      = W⁻¹ * (W * (v ≫ (G.innerIso w).inv.hom.hom) * W⁻¹) * W := by group
    _ = W⁻¹ * v * W := by rw [← h]

/-- Adelic form of `range_conj_radical_inf_parabolic_le`: if `v ∈ V(𝔸)` and `W⁻¹ v W ∈ P(𝔸)`
for the conjugating point `W` of a Weyl conjugation `(w, c)`, then `W⁻¹ v W ∈ U(𝔸)`. -/
theorem conj_mem_parabolicUnipotentImage
    {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (r : ParabolicRootPresentation p l a) {q : Q ⟶ G} {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) {c : M' ⟶ M}
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hmul : IsIso (subgroupMultiplication l' iV)) (hw : IsWeylConjugation p l q l' w c)
    {v : AdelicGroupPoints F G}
    (hv : v ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)))
    (hvP : (innerAdelicPoint F G w)⁻¹ * v * innerAdelicPoint F G w ∈
      (map F P G p).toMonoidHom.range) :
    (innerAdelicPoint F G w)⁻¹ * v * innerAdelicPoint F G w ∈
      parabolicUnipotentImage F p iU := by
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hv
  obtain ⟨z, hz⟩ := hvP
  have hmem := range_conj_radical_inf_parabolic_le r w hG hU hq hV hmul hw.isIso hw.comp_eq
    ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (AdeleRing (𝓞 F) F))))
    (x := (innerAdelicPoint F G w)⁻¹ * v * innerAdelicPoint F G w)
    ⟨SubgroupFunctor.mem_range.mpr ⟨y, by
      rw [← comp_innerIso_inv_adelic, ← hy]
      simp only [Grp.comp_hom_hom, Category.assoc]⟩,
     SubgroupFunctor.mem_range.mpr ⟨z, hz⟩⟩
  obtain ⟨u, hu⟩ := SubgroupFunctor.mem_range.mp hmem
  exact ⟨u, hu⟩

end Langlands.Global
