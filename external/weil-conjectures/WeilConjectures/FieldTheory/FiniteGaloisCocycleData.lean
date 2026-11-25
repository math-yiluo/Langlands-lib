/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.Topology.ContinuousOpenNormalStabilizer
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Abel

/-!
# Finite quotient data for a continuous Galois two-cocycle

Source: Stacks Project, Theorem 03R7, surjectivity, and Section 0DVG.
(blueprint: lem-sc-finite-galois-cocycle-data).
-/

@[expose] public section

universe u

namespace Field

private theorem finite_pair_factorization (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {S : Type u} [TopologicalSpace S] [DiscreteTopology S]
    (c : G × G → S) (hc : Continuous c) :
    ∃ (n : ℕ) (_ : n ≠ 0) (grp : Group (Fin n)),
      let := grp
      ∃ (q : G →* Fin n) (d : Fin n → Fin n → S),
        Function.Surjective q ∧ IsLocallyConstant q ∧
          ∀ g h, c (g, h) = d (q g) (q h) := by
  classical
  obtain ⟨U, hU⟩ := ProfiniteGrp.exists_openNormalSubgroup_right_invariant
    (ProfiniteGrp.of (G × G)) S c hc
  let i₁ : G →* G × G := MonoidHom.inl G G
  let i₂ : G →* G × G := MonoidHom.inr G G
  let V₁ := U.toOpenSubgroup.comap i₁ (continuous_id.prodMk continuous_const)
  let V₂ := U.toOpenSubgroup.comap i₂ (continuous_const.prodMk continuous_id)
  let N : OpenNormalSubgroup G :=
    ⟨V₁ ⊓ V₂, by
      change ((U.toSubgroup.comap i₁) ⊓ (U.toSubgroup.comap i₂)).Normal
      infer_instance⟩
  have hN (g h a b : G) (ha : a ∈ N) (hb : b ∈ N) :
      c (g * a, h * b) = c (g, h) := by
    have ha' : (a, 1) ∈ U := ha.1
    have hb' : (1, b) ∈ U := hb.2
    have hab : (a, b) ∈ U := by
      change (a, b) ∈ U.toSubgroup
      simpa using U.toSubgroup.mul_mem ha' hb'
    exact hU (g, h) (a, b) hab
  let : N.toSubgroup.Normal := N.isNormal'
  let Q := G ⧸ N.toSubgroup
  let : Fintype Q := Fintype.ofFinite Q
  let e := Fintype.equivFin Q
  let grp : Group (Fin (Fintype.card Q)) := e.symm.group
  let := grp
  let : Mul (Fin (Fintype.card Q)) := grp.toMul
  let E : Q ≃* Fin (Fintype.card Q) := e.symm.mulEquiv.symm
  let q : G →* Fin (Fintype.card Q) := E.toMonoidHom.comp (QuotientGroup.mk' N.toSubgroup)
  have hq : Function.Surjective q := E.surjective.comp (QuotientGroup.mk'_surjective _)
  let r : Fin (Fintype.card Q) → G := fun j ↦ (hq j).choose
  have hr (j) : q (r j) = j := (hq j).choose_spec
  have same (g g' h h' : G) (hg : q g = q g') (hh : q h = q h') :
      c (g, h) = c (g', h') := by
    have hg' : QuotientGroup.mk' N.toSubgroup g = QuotientGroup.mk' N.toSubgroup g' :=
      E.injective hg
    have hh' : QuotientGroup.mk' N.toSubgroup h = QuotientGroup.mk' N.toSubgroup h' :=
      E.injective hh
    obtain ⟨a, ha, rfl⟩ := (QuotientGroup.mk'_eq_mk' N.toSubgroup).mp hg'
    obtain ⟨b, hb, rfl⟩ := (QuotientGroup.mk'_eq_mk' N.toSubgroup).mp hh'
    exact (hN g h a b ha hb).symm
  refine ⟨Fintype.card Q, Fintype.card_ne_zero, grp, q,
    fun i j ↦ c (r i, r j), hq, ?_, ?_⟩
  · have hlc : IsLocallyConstant (QuotientGroup.mk' N.toSubgroup) :=
      (IsLocallyConstant.iff_continuous _).mpr QuotientGroup.continuous_mk
    exact hlc.comp E
  · intro g h
    exact same g (r (q g)) h (r (q h)) (hr _).symm (hr _).symm

private theorem scalar_cocycle_identity (K : Type u) [Field K]
    (z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2)
    (g h r : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    galoisUnitsCocycleValue K z g h * galoisUnitsCocycleValue K z (g * h) r =
      Units.map g.toRingHom (galoisUnitsCocycleValue K z h r) *
        galoisUnitsCocycleValue K z g (h * r) := by
  let A := galoisUnitsTopRep K
  let C := TopRep.homogeneousCochains A
  let f := (C.iCycles 2).hom z
  have hf : (C.d 2 3).hom f = 0 := by
    have he := congrArg (fun t ↦ t.hom z) (C.iCycles_d 2 3)
    exact he
  have hz := DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun
    (DFunLike.congr_fun (congrArg Subtype.val hf) 1) g) (g * h)) ((g * h) * r)
  rw [TopRep.homogeneousCochains.d_apply] at hz
  change f.val g (g * h) ((g * h) * r) -
    (f.val 1 (g * h) ((g * h) * r) -
      (f.val 1 g ((g * h) * r) - f.val 1 g (g * h))) = 0 at hz
  have he : A.ρ g (f.val 1 h (h * r)) = f.val g (g * h) (g * (h * r)) := by
    have hi := DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun
      ((ContRepresentation.mem_invariants _).mp f.property g) (g * 1)) (g * h))
        (g * (h * r))
    simpa using hi
  rw [mul_assoc, ← he] at hz
  have hadd : f.val 1 g (g * h) + f.val 1 (g * h) ((g * h) * r) =
      A.ρ g (f.val 1 h (h * r)) + f.val 1 g (g * (h * r)) := by
    rw [mul_assoc]
    have hz' := sub_eq_zero.mp hz
    rw [hz']
    abel
  exact congrArg Additive.toMul hadd

/-- A prescribed continuous two-cocycle factors through a finite group quotient.

Proof: put G = Gal(Ksep/K) and c(g,h) = z(1,g,g*h). Uncurry the iterated
continuous homogeneous cochain by the exponential law for compact Hausdorff G.
Evaluation at (1,g,g*h) is continuous. The coefficient representation is discrete,
so compactness gives finite image and local constancy. Cover G^2 by finitely many
clopen rectangles on which c is constant. In each coordinate refine the resulting
finite clopen partition by cosets of an open subgroup, and intersect the normal
cores of those subgroups. The resulting open normal N has c constant on pairs
of N-cosets. Its finite quotient is nonempty. Transport its group law and quotient
map to Fin n using a finite enumeration; n is nonzero. Define d on quotient pairs
by c on representatives; coset constancy makes this independent of representatives,
and the quotient map q is locally constant because its fibres are open cosets.

The homogeneous cycle equation evaluated on (1,g,g*h,g*h*j), together with
homogeneous equivariance, yields c(g,h)c(g*h,j) = g(c(h,j))c(g,h*j).
For any quotient index j choose a representative r. Substitute r for j in that
identity and use the factorization of c and q(g*h)=q(g)q(h). Commutativity of
units reorders the two factors on the right. This gives the last displayed
identity for d. The construction concerns the prescribed cocycle itself, not
only its class. It needs no normalization, no division by the group order, and
no matrix algebra. For a trivial quotient one may have d(1,1) different from 1.

Source: Stacks Project, Theorem 03R7 surjectivity sketch and Section 0DVG;
finite coset refinement and the homogeneous-coordinate calculation are expanded
here.
(blueprint: lem-sc-finite-galois-cocycle-data). -/
theorem exists_finite_galois_cocycle_data (K : Type u) [Field K]
    (z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2) :
    ∃ (n : ℕ) (_ : n ≠ 0) (grp : Group (Fin n)),
      letI := grp
      ∃ (q : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →* Fin n)
        (d : Fin n → Fin n → (SeparableClosure K)ˣ),
        IsLocallyConstant q ∧
        (∀ g h, galoisUnitsCocycleValue K z g h = d (q g) (q h)) ∧
        (∀ g h j, d (q g) (@Mul.mul (Fin n) grp.toMul (q h) j) * Units.map g.toRingHom (d (q h) j) =
          d (q g) (q h) * d (q (g * h)) j) := by
  classical
  let G := SeparableClosure K ≃ₐ[K] SeparableClosure K
  let A := galoisUnitsTopRep K
  have : DiscreteTopology A := ⟨rfl⟩
  let f : ((TopRep.resolution' A).X 2).invariants :=
    ((TopRep.homogeneousCochains A).iCycles 2).hom z
  let F : C(G, C(G, C(G, A))) := f.val
  let c : C(G × G, A) := ⟨fun p ↦ F 1 p.1 (p.1 * p.2),
    continuous_eval.comp
      (((F 1).continuous.comp continuous_fst).prodMk (continuous_fst.mul continuous_snd))⟩
  obtain ⟨n, hn, grp, hdata⟩ := finite_pair_factorization G c c.continuous
  let := grp
  obtain ⟨q, da, hq, hlc, hda⟩ := hdata
  let d : Fin n → Fin n → (SeparableClosure K)ˣ := fun i j ↦ (da i j).toMul
  have hd (g h : G) : galoisUnitsCocycleValue K z g h = d (q g) (q h) :=
    congrArg Additive.toMul (hda g h)
  refine ⟨n, hn, grp, q, d, hlc, hd, ?_⟩
  intro g h j
  obtain ⟨r, rfl⟩ := hq j
  have he := scalar_cocycle_identity K z g h r
  rw [hd, hd, hd, hd, q.map_mul h r] at he
  exact (mul_comm _ _).trans he.symm

end Field
