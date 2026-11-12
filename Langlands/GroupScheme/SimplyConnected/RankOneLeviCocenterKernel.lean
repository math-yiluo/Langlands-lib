import Langlands.GroupScheme.SimplyConnected.RankOneLeviFactors
import Langlands.GroupScheme.SubgroupFunctor.QuotientNormality
import Langlands.GroupScheme.CommutingFactorRetraction

/-!
# Kernels of cocenter maps and cocenters of subgroup intersections

Abstract part of the comparison between the kernel of the map from the cocenter of the
minimal Levi subgroup to the cocenter of a standard Levi subgroup and the image of the
cocenter of the intersection with a rank-one Levi factor.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Relative

variable {S : Scheme.{u}} {G M A L E D Q Dα Qα R : GroupScheme S}

/-- For a retraction `pA` of `aE`, every point is its `A`-part times a point killed
by `pA`. -/
theorem retraction_inv_mul_comp_eq_one (aE : A ⟶ E) (pA : E ⟶ A) (hpA : aE ≫ pA = 𝟙 A)
    {T : Over S} (y : T ⟶ E.X) :
    ((y ≫ pA.hom.hom ≫ aE.hom.hom)⁻¹ * y) ≫ pA.hom.hom = 1 := by
  have h : aE.hom.hom ≫ pA.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, hpA, Grp.id_hom_hom]
  rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, h,
    Category.comp_id, inv_mul_cancel]

variable (j : M ⟶ G) (a : A ⟶ G) (l : L ⟶ G) (e : E ⟶ L) (aE : A ⟶ E) (pA : E ⟶ A)
  (d : D ⟶ M) (δ : D ⟶ E)

/-- If the kernel of the retraction `pA` maps into the image of `D` in `M`, then the
`A`-part of a point of `E` lying in `M` also lies in `M`, up to a point of `D`. -/
theorem retraction_comp_eq_mul_inv (haE : aE ≫ e ≫ l = a) (hpA : aE ≫ pA = 𝟙 A)
    (hK : ∀ (T : Over S) (y : T ⟶ E.X), y ≫ pA.hom.hom = 1 →
      y ≫ (e ≫ l).hom.hom ∈ (SubgroupFunctor.range (d ≫ j)).carrier T)
    {T : Over S} (y : T ⟶ E.X) (g : T ⟶ M.X)
    (hy : y ≫ (e ≫ l).hom.hom = g ≫ j.hom.hom) :
    ∃ t : T ⟶ D.X, (y ≫ pA.hom.hom) ≫ a.hom.hom = (g * (t ≫ d.hom.hom)⁻¹) ≫ j.hom.hom := by
  let w := (y ≫ pA.hom.hom ≫ aE.hom.hom)⁻¹ * y
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.1
    (hK T w (retraction_inv_mul_comp_eq_one aE pA hpA y))
  refine ⟨t, ?_⟩
  have hw : y ≫ pA.hom.hom ≫ aE.hom.hom = y * w⁻¹ := by
    simp only [w, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have ha : a.hom.hom = aE.hom.hom ≫ (e ≫ l).hom.hom := by
    rw [← Grp.comp_hom_hom, haE]
  rw [ha, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, ← Category.assoc pA.hom.hom,
    ← Category.assoc y, hw, MonObj.mul_comp, GrpObj.inv_comp, hy, ← ht]
  simp only [Grp.comp_hom_hom, Category.assoc]

variable {j a l e aE pA d δ}

/-- The inverse image in the intersection `M ∩ A` of the kernel of `M → Q` lies in the
derived subgroup of the intersection, when `D` is perfect and maps to `E` compatibly
with `M`, and `E` retracts onto `A` with kernel mapping into the image of `D`. -/
theorem comap_range_kernelι_le_range_kernelι_intersection
    [Mono j.hom.hom] [Mono a.hom.hom] [Mono (e ≫ l).hom.hom]
    (haE : aE ≫ e ≫ l = a) (hpA : aE ≫ pA = 𝟙 A)
    (hK : ∀ (T : Over S) (y : T ⟶ E.X), y ≫ pA.hom.hom = 1 →
      y ≫ (e ≫ l).hom.hom ∈ (SubgroupFunctor.range (d ≫ j)).carrier T)
    (hδ : δ ≫ e ≫ l = d ≫ j) (hDperf : derivedSubgroup D = ⊤)
    {q : M ⟶ Q} (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    {dα : Dα ⟶ subgroupIntersection j a} (hdα : IsDerivedSubgroup dα)
    {qα : subgroupIntersection j a ⟶ Qα}
    (hqα : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range dα) qα) :
    (SubgroupFunctor.range (kernelι q)).comap (subgroupIntersectionFst j a) ≤
      SubgroupFunctor.range (kernelι qα) := by
  intro T z hz
  rw [SubgroupFunctor.mem_comap, hq.2.2.2] at hz
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.1 hz
  have hpb := subgroupIntersection_isPullback j a
  have hpb' : (subgroupIntersectionFst j a).hom.hom ≫ j.hom.hom =
      (subgroupIntersectionSnd j a).hom.hom ≫ a.hom.hom := hpb.w
  -- the point `x` of `D` maps to the `A`-coordinate of `z`
  have hxδ : x ≫ δ.hom.hom ≫ pA.hom.hom = z ≫ (subgroupIntersectionSnd j a).hom.hom := by
    have h1 : x ≫ δ.hom.hom = z ≫ (subgroupIntersectionSnd j a).hom.hom ≫ aE.hom.hom := by
      apply (cancel_mono (e ≫ l).hom.hom).1
      have h2 : δ.hom.hom ≫ (e ≫ l).hom.hom = d.hom.hom ≫ j.hom.hom := by
        rw [← Grp.comp_hom_hom, hδ, Grp.comp_hom_hom]
      have h3 : aE.hom.hom ≫ (e ≫ l).hom.hom = a.hom.hom := by
        rw [← Grp.comp_hom_hom, haE]
      rw [Category.assoc, h2, ← Category.assoc, hx, Category.assoc, Category.assoc,
        Category.assoc, h3, hpb']
    have h : aE.hom.hom ≫ pA.hom.hom = 𝟙 _ := by
      rw [← Grp.comp_hom_hom, hpA, Grp.id_hom_hom]
    rw [← Category.assoc, h1, Category.assoc, Category.assoc, h, Category.comp_id]
  -- the homomorphism `D → M ∩ A`
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  have hrange : SubgroupFunctor.range (δ ≫ pA ≫ a) ≤ SubgroupFunctor.range j := by
    intro T' g hg
    obtain ⟨x', rfl⟩ := SubgroupFunctor.mem_range.1 hg
    have hy : (x' ≫ δ.hom.hom) ≫ (e ≫ l).hom.hom = (x' ≫ d.hom.hom) ≫ j.hom.hom := by
      rw [Category.assoc, ← Grp.comp_hom_hom, hδ, Grp.comp_hom_hom, Category.assoc]
    obtain ⟨t, ht⟩ := retraction_comp_eq_mul_inv j a l e aE pA d haE hpA hK _ _ hy
    exact SubgroupFunctor.mem_range.2 ⟨_, by
      rw [← ht]; simp only [Grp.comp_hom_hom, Category.assoc]⟩
  let f1 : D ⟶ M := SubgroupFunctor.IsRepresentedBy.factorHom hjrep (δ ≫ pA ≫ a) hrange
  have hf1 : f1 ≫ j = δ ≫ pA ≫ a :=
    SubgroupFunctor.IsRepresentedBy.factorHom_comp hjrep (δ ≫ pA ≫ a) hrange
  let ψ : D ⟶ subgroupIntersection j a := pullback.lift f1 (δ ≫ pA) (by rw [hf1, Category.assoc])
  have hψ1 : ψ ≫ subgroupIntersectionFst j a = f1 := pullback.lift_fst _ _ _
  have hψ2 : ψ ≫ subgroupIntersectionSnd j a = δ ≫ pA := pullback.lift_snd _ _ _
  have hxz : x ≫ ψ.hom.hom = z := by
    apply hpb.hom_ext
    · apply (cancel_mono j.hom.hom).1
      have hψ1' : ψ.hom.hom ≫ (subgroupIntersectionFst j a).hom.hom ≫ j.hom.hom =
          δ.hom.hom ≫ pA.hom.hom ≫ a.hom.hom := by
        rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, ← Category.assoc, hψ1, hf1]
        simp only [Grp.comp_hom_hom]
      simp only [Category.assoc]
      rw [hψ1', hpb', ← Category.assoc z, ← hxδ]
      simp only [Category.assoc]
    · rw [Category.assoc, ← Grp.comp_hom_hom, hψ2, Grp.comp_hom_hom, hxδ]
  rw [hqα.2.2.2, hdα.2, ← hxz]
  apply mem_derivedSubgroup_comp ψ
  rw [hDperf]
  trivial

/-- Under the hypotheses of `comap_range_kernelι_le_range_kernelι_intersection`, any
homomorphism completing the cocenter square of the intersection is a monomorphism. -/
theorem mono_of_cocenter_square
    [Mono j.hom.hom] [Mono a.hom.hom] [Mono (e ≫ l).hom.hom]
    (haE : aE ≫ e ≫ l = a) (hpA : aE ≫ pA = 𝟙 A)
    (hK : ∀ (T : Over S) (y : T ⟶ E.X), y ≫ pA.hom.hom = 1 →
      y ≫ (e ≫ l).hom.hom ∈ (SubgroupFunctor.range (d ≫ j)).carrier T)
    (hδ : δ ≫ e ≫ l = d ≫ j) (hDperf : derivedSubgroup D = ⊤) (hd : IsDerivedSubgroup d)
    {q : M ⟶ Q} (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    {dα : Dα ⟶ subgroupIntersection j a} (hdα : IsDerivedSubgroup dα)
    {qα : subgroupIntersection j a ⟶ Qα}
    (hqα : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range dα) qα)
    [QuasiCompact qα.hom.hom.left]
    (φ : Qα ⟶ Q) (hsq : subgroupIntersectionFst j a ≫ q = qα ≫ φ) :
    Mono φ.hom.hom := by
  have : Flat qα.hom.hom.left := hqα.1
  have : Surjective qα.hom.hom.left := hqα.2.1
  have hkernel : SubgroupFunctor.range (kernelι qα) ≤
      (SubgroupFunctor.range (kernelι q)).comap (subgroupIntersectionFst j a) := by
    intro T x hx
    rw [hqα.2.2.2, hdα.2] at hx
    rw [SubgroupFunctor.mem_comap, hq.2.2.2, hd.2]
    exact mem_derivedSubgroup_comp _ hx
  have hkernel' := comap_range_kernelι_le_range_kernelι_intersection haE hpA hK hδ hDperf hq
    hdα hqα
  rw [SubgroupFunctor.quotientSubgroupHom_unique _ q qα hkernel φ hsq]
  exact SubgroupFunctor.quotientSubgroupHom_mono _ q qα hkernel hkernel'

/-- A point of the cocenter `Q` of `M` killed by the map to the cocenter `R` of `L` lies in
the image of the cocenter of `M ∩ A`. -/
theorem mem_range_of_comp_eq_one
    [Mono j.hom.hom] [Mono a.hom.hom] [Mono (e ≫ l).hom.hom]
    (haE : aE ≫ e ≫ l = a) (hpA : aE ≫ pA = 𝟙 A)
    (hK : ∀ (T : Over S) (y : T ⟶ E.X), y ≫ pA.hom.hom = 1 →
      y ≫ (e ≫ l).hom.hom ∈ (SubgroupFunctor.range (d ≫ j)).carrier T)
    {q : M ⟶ Q} (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    [QuasiCompact q.hom.hom.left]
    (qα : subgroupIntersection j a ⟶ Qα) (φ : Qα ⟶ Q) [Mono φ.hom.hom]
    (hsq : subgroupIntersectionFst j a ≫ q = qα ≫ φ)
    (jL : M ⟶ L) (hjL : jL ≫ l = j) {r : L ⟶ R}
    (hr : SubgroupFunctor.range (kernelι r) = SubgroupFunctor.range e)
    (π : Q ⟶ R) (hπ : q ≫ π = jL ≫ r)
    {T : Over S} (x : T ⟶ Q.X) (hx : x ≫ π.hom.hom = 1) :
    x ∈ (SubgroupFunctor.range φ).carrier T := by
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  apply SubgroupFunctor.mem_range_of_local_quotient_lift q φ x x
  intro V b g hbg
  have h1 : (g ≫ jL.hom.hom) ≫ r.hom.hom = 1 := by
    have hπ' : q.hom.hom ≫ π.hom.hom = jL.hom.hom ≫ r.hom.hom := by
      rw [← Grp.comp_hom_hom, hπ, Grp.comp_hom_hom]
    rw [Category.assoc, ← hπ', ← Category.assoc, ← hbg, Category.assoc, hx, MonObj.comp_one]
  have h2 := (mem_range_kernelι_iff r _).2 h1
  rw [hr] at h2
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 h2
  have hy' : y ≫ (e ≫ l).hom.hom = g ≫ j.hom.hom := by
    rw [Grp.comp_hom_hom, ← Category.assoc, hy, Category.assoc, ← Grp.comp_hom_hom, hjL]
  obtain ⟨t, ht⟩ := retraction_comp_eq_mul_inv j a l e aE pA d haE hpA hK y g hy'
  have hpb := subgroupIntersection_isPullback j a
  let z := hpb.lift (g * (t ≫ d.hom.hom)⁻¹) (y ≫ pA.hom.hom) ht.symm
  have hz : z ≫ (subgroupIntersectionFst j a).hom.hom = g * (t ≫ d.hom.hom)⁻¹ := hpb.lift_fst _ _ _
  have htd : (t ≫ d.hom.hom) ≫ q.hom.hom = 1 := by
    apply (mem_range_kernelι_iff q _).1
    rw [hq.2.2.2]
    exact SubgroupFunctor.mem_range.2 ⟨t, rfl⟩
  refine SubgroupFunctor.mem_range.2 ⟨z ≫ qα.hom.hom, ?_⟩
  have hsq' : qα.hom.hom ≫ φ.hom.hom = (subgroupIntersectionFst j a).hom.hom ≫ q.hom.hom := by
    rw [← Grp.comp_hom_hom, ← hsq, Grp.comp_hom_hom]
  rw [Category.assoc, hsq', ← Category.assoc, hz, MonObj.mul_comp, GrpObj.inv_comp, htd,
    inv_one, mul_one, hbg]

end Relative

end Langlands.GroupScheme
