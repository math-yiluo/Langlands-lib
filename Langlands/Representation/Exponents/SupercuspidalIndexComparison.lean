import Mathlib.GroupTheory.DoubleCoset
import Langlands.GroupScheme.Dynamic.StableIntersection
import Langlands.Representation.Geometric.RepresentedGeometricLemmaDynamicRealization
import Langlands.Representation.Exponents.LeviCuspidalEmbeddingSteps
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.Representation.Exponents.ActualGeometricFullPiece
import Langlands.Representation.Geometric.FullIntersectionIrreducible

/-! # Full source intersections at double cosets carrying a Levi conjugacy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G H Q : GroupScheme S}

/-- Conjugation by a cocharacter factoring through a subgroup preserves its range. -/
theorem isStable_range_of_comp (χ : (Gm S).toGrp ⟶ Q) (q : Q ⟶ G) :
    (AutomorphicAction.conjugation (χ ≫ q)).IsStable (SubgroupFunctor.range q) := by
  intro T h g hg
  rw [AutomorphicAction.conjugation_act]
  have hh : h ≫ (χ ≫ q).hom.hom ∈ (SubgroupFunctor.range q).carrier T :=
    SubgroupFunctor.mem_range.mpr ⟨h ≫ χ.hom.hom, by
      rw [Grp.comp_hom_hom, Category.assoc]⟩
  exact mul_mem (mul_mem hh hg) (inv_mem hh)

variable [IsSeparated G.X.hom] (χ : (Gm S).toGrp ⟶ G)
  {F : SubgroupFunctor G} {j : H ⟶ G}

/-- If conjugation by a point `a` of `P(χ)` moves `Z(χ)` into a closed subgroup
stable under `χ`, then `Z(χ)` already lies in that subgroup. The limit of
`a⁻¹ (c m c⁻¹) a`, for `c` the limit of `a`, is `m`. -/
theorem centralizer_carrier_le_of_conj_mem (hj : F.IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hF : (AutomorphicAction.conjugation χ).IsStable F)
    {T : Over S} (a : T ⟶ G.X) (ha : a ∈ (parabolic χ).carrier T)
    (h : ∀ m ∈ (centralizer χ).carrier T, a⁻¹ * m * a ∈ F.carrier T) :
    (centralizer χ).carrier T ≤ F.carrier T := by
  intro m hm
  let c := limitHom χ T ⟨a, ha⟩
  have hcm : (c : T ⟶ G.X) * m * (c : T ⟶ G.X)⁻¹ ∈ (centralizer χ).carrier T :=
    mul_mem (mul_mem c.2 hm) (inv_mem c.2)
  have hxP : a⁻¹ * ((c : T ⟶ G.X) * m * (c : T ⟶ G.X)⁻¹) * a ∈
      (parabolic χ).carrier T :=
    mul_mem (mul_mem (inv_mem ha) (centralizer_le_parabolic χ T hcm)) ha
  have hlim : HasLimit χ (a⁻¹ * ((c : T ⟶ G.X) * m * (c : T ⟶ G.X)⁻¹) * a) m := by
    rw [hasLimit_iff_limitHom]
    refine ⟨hxP, ?_⟩
    have hx : (⟨_, hxP⟩ : (parabolic χ).carrier T) =
        (⟨a, ha⟩ : (parabolic χ).carrier T)⁻¹ *
          Subgroup.inclusion (centralizer_le_parabolic χ T) ⟨_, hcm⟩ * ⟨a, ha⟩ :=
      rfl
    rw [hx, map_mul, map_mul, map_inv, limitHom_inclusion]
    change (c : T ⟶ G.X)⁻¹ * ((c : T ⟶ G.X) * m * (c : T ⟶ G.X)⁻¹) *
      (c : T ⟶ G.X) = m
    group
  exact HasLimit.mem_of_isClosedSubgroup_of_isStable χ hj hjc hF (h _ hcm) hlim

end Langlands.GroupScheme.Dynamic

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

/-- The source intersection `M ∩ zQz⁻¹` is all of `M` once `M ⊆ zQz⁻¹` on every test
scheme. -/
theorem isIso_p'_of_range_le
    (h : SubgroupFunctor.range (l ≫ p) ≤ SubgroupFunctor.range (q ≫ (G.innerIso z).hom)) :
    IsIso D.p' := by
  apply IsClosedSubgroup.isIso_of_range_le_range_comp D.hp'.isClosedSubgroup
    (hl.isClosedSubgroup.comp hp.isClosedSubgroup)
  rw [D.parabolic_eq]
  exact fun T _ hx => ⟨hx, h T hx⟩

/-- If some `w = a z b` with `a ∈ P(F)` and `b ∈ Q(F)` conjugates `L` onto `M`, then, given
a simultaneous dynamic realization, the source intersection at `z` is full. -/
theorem isIso_p'_of_dynamicRealization (R : D.DynamicRealization) [IsSeparated G.X.hom]
    {a b : rationalPoints G} (ha : a ∈ pointImage p) (hb : b ∈ pointImage q)
    (ψ : L ≅ M) (hψ : ψ.hom ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso (a * z * b)).hom) :
    IsIso D.p' := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  let χ := CommGroupScheme.groupHom R.sourceCocharacter ≫
    D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q
  have hχq : χ = (CommGroupScheme.groupHom R.sourceCocharacter ≫
      D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ) ≫ q := by
    simp only [χ, Category.assoc]
  have hqc := hq.isClosedSubgroup
  have : IsClosedImmersion q.hom.hom.left := hqc
  have : Mono q.hom.hom := Over.mono_of_mono_left _
  have hrep : (SubgroupFunctor.range q).IsRepresentedBy q := ⟨inferInstance, rfl⟩
  have hstab : (AutomorphicAction.conjugation χ).IsStable (SubgroupFunctor.range q) := by
    rw [hχq]
    exact Dynamic.isStable_range_of_comp _ q
  have hlp : l ≫ p = ψ.inv ≫ lQ ≫ q ≫ (G.innerIso
      (rationalPoints.map p a' * z * rationalPoints.map q b')).hom := by
    rw [← hψ, Iso.inv_hom_id_assoc]
  have hZ : ∀ T : Over (Spec (CommRingCat.of k)),
      (Dynamic.centralizer χ).carrier T ≤ (SubgroupFunctor.range q).carrier T := by
    intro T
    have ha₀ : G.constantPoint (z⁻¹ * rationalPoints.map p a' * z) T ∈
        (Dynamic.parabolic χ).carrier T := by
      rw [← R.sourceParabolic]
      refine SubgroupFunctor.mem_range.mpr ⟨P.constantPoint a' T, ?_⟩
      rw [constantPoint_comp]
      congr 1
      rw [rationalPoints.map_apply, Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom,
        constantPoint_rationalPoint, inv_inv]
    refine Dynamic.centralizer_carrier_le_of_conj_mem χ hrep hqc hstab _ ha₀ ?_
    intro m hm
    rw [← R.sourceLevi] at hm
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hm
    let x := y ≫ (ψ.inv ≫ lQ).hom.hom
    have hy : y ≫ (l ≫ p ≫ (G.innerIso z⁻¹).hom).hom.hom =
        ((x ≫ q.hom.hom) ≫ (G.innerIso
          (rationalPoints.map p a' * z * rationalPoints.map q b')).hom.hom.hom) ≫
          (G.innerIso z⁻¹).hom.hom.hom := by
      rw [← Category.assoc l p, hlp]
      simp only [x, Grp.comp_hom_hom, Category.assoc]
    have hB : G.constantPoint (rationalPoints.map q b') T ∈
        (SubgroupFunctor.range q).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨Q.constantPoint b' T, constantPoint_comp q b' T⟩
    have hX : x ≫ q.hom.hom ∈ (SubgroupFunctor.range q).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
    have key : (G.constantPoint (z⁻¹ * rationalPoints.map p a' * z) T)⁻¹ *
          (y ≫ (l ≫ p ≫ (G.innerIso z⁻¹).hom).hom.hom) *
          G.constantPoint (z⁻¹ * rationalPoints.map p a' * z) T =
        G.constantPoint (rationalPoints.map q b') T * (x ≫ q.hom.hom) *
          (G.constantPoint (rationalPoints.map q b') T)⁻¹ := by
      rw [hy, comp_innerIso_hom, comp_innerIso_hom]
      simp only [constantPoint_mul, constantPoint_inv]
      group
    rw [key]
    exact mul_mem (mul_mem hB hX) (inv_mem hB)
  apply D.isIso_p'_of_range_le
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hm : y ≫ (l ≫ p ≫ (G.innerIso z⁻¹).hom).hom.hom ∈
      (Dynamic.centralizer χ).carrier T := by
    rw [← R.sourceLevi]
    exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
  obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.mp (hZ T hm)
  refine SubgroupFunctor.mem_range.mpr ⟨y', ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hy', ← Category.assoc l p, Grp.comp_hom_hom,
    ← Category.assoc, comp_innerIso_hom, comp_innerIso_hom, constantPoint_inv]
  group

/-- Under the parabolic-dynamic statement, the source intersection at `z` is full as soon as
the double coset `P(F) z Q(F)` contains an element conjugating `L` onto `M`. -/
theorem isIso_p'_of_doubleCoset (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G) {w : rationalPoints G}
    (hw : DoubleCoset.mk (pointImage p) (pointImage q) w =
      DoubleCoset.mk (pointImage p) (pointImage q) z)
    (ψ : L ≅ M) (hψ : ψ.hom ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso w).hom) :
    IsIso D.p' := by
  have := hG.isAffineHom
  obtain ⟨a, ha, b, hb, hz⟩ := DoubleCoset.eq.mp hw
  have hw' : w = a⁻¹ * z * b⁻¹ := by
    rw [hz]
    group
  rw [hw'] at hψ
  exact D.isIso_p'_of_dynamicRealization (D.dynamicRealizationOfParabolicDynamic hPD hG)
    (inv_mem ha) (inv_mem hb) ψ hψ

/-- Under the parabolic-dynamic statement and for isomorphic outer Levis, the source
intersection at `z` is full exactly when `P(F) z Q(F)` contains an element conjugating `L`
onto `M`. -/
theorem isIso_p'_iff (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (E : M ≅ L) :
    IsIso D.p' ↔ ∃ (w : rationalPoints G) (ψ : L ≅ M),
      DoubleCoset.mk (pointImage p) (pointImage q) w =
          DoubleCoset.mk (pointImage p) (pointImage q) z ∧
        ψ.hom ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso w).hom := by
  constructor
  · intro _
    have := D.isIso_q'_of_isIso_p'_of_iso E
    refine ⟨z, D.fullLeviConjugacy.val.symm, rfl, ?_⟩
    have h := congrArg
      (fun f : M ⟶ G => D.fullLeviConjugacy.val.inv ≫ f ≫ (G.innerIso z).hom)
      D.fullLeviConjugacy.property
    simpa only [Iso.symm_hom, innerIso_inv_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id] using h.symm
  · rintro ⟨w, ψ, hw, hψ⟩
    exact D.isIso_p'_of_doubleCoset hPD hG hw ψ hψ

end GeometricLemmaIntersectionDatum

/-- Under the parabolic-dynamic statement and for isomorphic outer Levis, an enumeration `c`
of `P(F) \ G(F) / Q(F)` with representatives `z i` and intersection data `D i` restricts to a
bijection from the indices with full source intersection onto the double cosets containing an
element that conjugates `L` onto `M`. -/
def fullIndexEquiv (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (E : M ≅ L) {I : Type*}
    (c : I ≃ DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
      (pointImage q : Set (rationalPoints G)))
    (z : I → rationalPoints G)
    (hz : ∀ i, DoubleCoset.mk (pointImage p) (pointImage q) (z i) = c i)
    (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ (z i)) :
    {i : I // IsIso (D i).p'} ≃
      {x : DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
          (pointImage q : Set (rationalPoints G)) //
        ∃ (w : rationalPoints G) (ψ : L ≅ M),
          DoubleCoset.mk (pointImage p) (pointImage q) w = x ∧
            ψ.hom ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso w).hom} :=
  c.subtypeEquiv fun i => by
    rw [← hz i]
    exact (D i).isIso_p'_iff hPD hG E

/-- The bijection sends a full index to its own double coset. -/
@[simp] theorem fullIndexEquiv_apply_coe (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G) (E : M ≅ L) {I : Type*}
    (c : I ≃ DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
      (pointImage q : Set (rationalPoints G)))
    (z : I → rationalPoints G)
    (hz : ∀ i, DoubleCoset.mk (pointImage p) (pointImage q) (z i) = c i)
    (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ (z i))
    (i : {i : I // IsIso (D i).p'}) :
    (fullIndexEquiv hPD hG E c z hz D i).1 = c i.1 :=
  rfl

end Langlands.Aubert.General.RepresentedParabolic
