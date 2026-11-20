import Langlands.GroupScheme.HomScheme.AdicClosedSubgroupContainment
import Langlands.GroupScheme.HomScheme.AdicFiniteClosedEmbedding
import Langlands.GroupScheme.HomScheme.AdicTorusFamily
import Langlands.GroupScheme.HomScheme.AdmissibleBaseChange
import Langlands.GroupScheme.HomScheme.AffineFiberTorusConnectedReduction
import Langlands.GroupScheme.HomScheme.TorusMonomorphismFromTorsion

/-! # Adic limits for closed tori from algebraization of their homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing
open Langlands.AlgebraicGeometry.AdicAffinePoints
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor Langlands.AlgebraicGeometry.UnramifiedFunctor HomScheme.Adic

variable {S : Scheme.{u}} {G : GroupScheme S}
variable {A : Type u} [CommRing A] (f : Spec (CommRingCat.of A) ⟶ S)

private def algebraAdmissibleEquiv (B : Type u) [CommRing B] [Algebra A B] :
    AdmissibleSubgroup ((GroupScheme.baseChange (Spec.algebraMap A B)).obj
        ((GroupScheme.baseChange f).obj G)) ≃
      (smallAdmissiblePresheaf G).obj (op (algebraOver f B)) :=
  (smallAdmissibleEquiv _ (Over.mk (Spec.algebraMap A B))).symm.trans
    (smallAdmissibleBaseChangeEquiv f (Over.mk (Spec.algebraMap A B)))

private def algebraArrow {B C : Type u} [CommRing B] [Algebra A B]
    [CommRing C] [Algebra A C] (φ : B →ₐ[A] C) :
    Over.mk (Spec.algebraMap A C) ⟶ Over.mk (Spec.algebraMap A B) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : B →+* C))) (by
    change Spec.map (CommRingCat.ofHom (φ : B →+* C)) ≫ Spec.algebraMap A B =
      Spec.algebraMap A C
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

set_option maxHeartbeats 900000 in
private theorem algebraAdmissibleEquiv_map {B C : Type u} [CommRing B] [Algebra A B]
    [CommRing C] [Algebra A C] (φ : B →ₐ[A] C)
    (F : AdmissibleSubgroup ((GroupScheme.baseChange (Spec.algebraMap A B)).obj
        ((GroupScheme.baseChange f).obj G))) :
    algebraAdmissibleEquiv (G := G) f C (restrict (algebraArrow φ) F) =
      (smallAdmissiblePresheaf G).map (algHomOver f φ).op
        (algebraAdmissibleEquiv f B F) := by
  let a := algebraArrow φ
  let M := (GroupScheme.baseChange f).obj G
  let U := Over.mk (Spec.algebraMap A B)
  let V := Over.mk (Spec.algebraMap A C)
  let z := (smallAdmissibleEquiv M U).symm F
  let e := smallAdmissiblePresheafBaseChangeIso (G := G) f
  have hz : (smallAdmissiblePresheaf M).map a.op z =
      (smallAdmissibleEquiv M V).symm (restrict a F) := by
    apply (smallAdmissibleEquiv M V).injective
    have hV := (smallAdmissibleEquiv M V).apply_symm_apply (restrict a F)
    have hU := (smallAdmissibleEquiv M U).apply_symm_apply F
    rw [smallAdmissibleEquiv_map a z, hV]
    exact congrArg (restrict a) hU
  have h := congrArg (fun g => g z) (e.hom.naturality a.op)
  change (smallAdmissibleBaseChangeEquiv f V) ((smallAdmissiblePresheaf M).map a.op z) =
    (smallAdmissiblePresheaf G).map ((Over.map f).map a).op
      ((smallAdmissibleBaseChangeEquiv f U) z) at h
  have ha : (Over.map f).map a = algHomOver f φ := Over.OverMorphism.ext rfl
  rw [hz, ha] at h
  exact h

set_option maxHeartbeats 850000 in
private theorem evaluate_algebraAdmissibleEquiv (B : Type u) [CommRing B] [Algebra A B]
    {H : GroupScheme (Spec (CommRingCat.of A))} (j : H ⟶ (GroupScheme.baseChange f).obj G)
    (x : (smallAdmissiblePresheaf G).obj (op (Over.mk f)))
    (hx : range j = (smallAdmissibleEquiv G (Over.mk f) x).val)
    (F : AdmissibleSubgroup ((GroupScheme.baseChange (Spec.algebraMap A B)).obj
        ((GroupScheme.baseChange f).obj G))) :
    (smallAdmissiblePresheaf G).map (algebraOverBase f B).op x =
        algebraAdmissibleEquiv f B F ↔
      range ((GroupScheme.baseChange (Spec.algebraMap A B)).map j) = F.val := by
  let a := algebraOverBase f B
  let b := Spec.algebraMap A B
  let c := Descent.pullbackComparison f b (b ≫ f) rfl G
  let E := smallAdmissibleEquiv G (algebraOver f B)
  rw [← E.injective.eq_iff, ← Subtype.val_inj, smallAdmissibleEquiv_map]
  rw [restrict_eq_evaluate _ j hx a]
  have h : (E (algebraAdmissibleEquiv f B F)).val = F.val.comap c.inv := by
    let U := Over.mk b
    let K := (GroupScheme.baseChange f).obj G
    let e := smallAdmissibleEquiv K U
    change (E (smallAdmissibleBaseChangeEquiv f U (e.symm F))).val = _
    unfold smallAdmissibleBaseChangeEquiv
    simp only [Equiv.trans_apply]
    change ((smallAdmissibleEquiv G ((Over.map f).obj U))
      ((smallAdmissibleEquiv G ((Over.map f).obj U)).symm _)).val = _
    rw [Equiv.apply_symm_apply, show smallAdmissibleEquiv ((GroupScheme.baseChange f).obj G) U
      (e.symm F) = F from e.apply_symm_apply F]
    rfl
  rw [h]
  change range ((GroupScheme.baseChange b).map j ≫ c.hom) = _ ↔ _
  rw [range_comp_iso]
  constructor
  · intro h
    have hc := congrArg (comap c.hom) h
    simpa only [← comap_comp, Iso.hom_inv_id, comap_id] using hc
  · exact congrArg (comap c.inv)

private theorem adicRestriction_injective [IsLocalRing A] [IsNoetherianRing A]
    (x y : (smallAdmissiblePresheaf G).obj (op (Over.mk f)))
    (h : ∀ n : ℕ, (smallAdmissiblePresheaf G).map
        (algebraOverBase f (A ⧸ maximalIdeal A ^ n)).op x =
      (smallAdmissiblePresheaf G).map (algebraOverBase f (A ⧸ maximalIdeal A ^ n)).op y) :
    x = y := by
  let r := admissibleRepresentative (smallAdmissibleEquiv G (Over.mk f) x)
  let t := admissibleRepresentative (smallAdmissibleEquiv G (Over.mk f) y)
  have he (n : ℕ) : let B := GroupScheme.baseChange (Spec.algebraMap A (A ⧸ maximalIdeal A ^ n))
      range (B.map r.hom) = range (B.map t.hom) := by
    let C := A ⧸ maximalIdeal A ^ n
    let B := GroupScheme.baseChange (Spec.algebraMap A C)
    let F : AdmissibleSubgroup (B.obj ((GroupScheme.baseChange f).obj G)) :=
      ⟨range (B.map t.hom), isAdmissible_range _ (t.closed.baseChange _) (t.torus.baseChange _)⟩
    apply (evaluate_algebraAdmissibleEquiv f C r.hom x r.represents.2 F).mp
    exact (h n).trans ((evaluate_algebraAdmissibleEquiv f C t.hom y t.represents.2 F).mpr rfl)
  apply (smallAdmissibleEquiv G (Over.mk f)).injective
  apply Subtype.ext
  rw [← r.represents.2, ← t.represents.2]
  exact le_antisymm (range_le_of_adic_restrictions (R := CommRingCat.of A) _ _ r.torus t.closed
    (fun n => (he n).le)) (range_le_of_adic_restrictions (R := CommRingCat.of A) _ _ t.torus r.closed
    (fun n => (he n).ge))

private theorem isClosedSubgroup_of_adic_torus_algebraization
    [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
    {H K : GroupScheme (Spec (CommRingCat.of A))} [Smooth K.X.hom] [IsSeparated K.X.hom]
    [QuasiCompact K.X.hom] (hK : HasAffineResidueFibers K) (hH : RelativeTorus.IsTorus H)
    (s : System (maximalIdeal A) H K) (hs : ∀ n, IsClosedSubgroup (s.hom n))
    (j : H ⟶ K) (hj : System.restrict (maximalIdeal A) H K j = s) : IsClosedSubgroup j := by
  have : IsCommMonObj H.X := hH.isCommMonObj
  have : Mono j.hom.hom := by
    apply mono_of_torus_torsion_mono hH
    intro n hn
    rw [(s.restrict_eq_iff_torsionRestriction hH.isMultiplicativeType j).mp hj n hn]
    have : IsClosedImmersion (s.torsionRestriction hH.isMultiplicativeType n hn).hom.hom.left :=
      s.torsionRestriction_isClosedSubgroup hH hs n hn
    infer_instance
  exact isClosedSubgroup_of_mono_of_affineResidueFibers hK hH j

/-- For smooth separated quasi-compact groups with affine residue fibres,
algebraization of the levelwise closed torus Hom systems implies the adic
limit condition for the actual torus subgroup presheaf. -/
def AffineFiberTorusAdicLimitsStatement : Prop :=
  ∀ {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
    HasAffineResidueFibers G →
    (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [IsAdicComplete (maximalIdeal A) A] (f : Spec (CommRingCat.of A) ⟶ S)
      (H : GroupScheme (Spec (CommRingCat.of A))), RelativeTorus.IsTorus H →
      ∀ s : System (maximalIdeal A) H ((GroupScheme.baseChange f).obj G),
        (∀ n, IsClosedSubgroup (s.hom n)) →
        ∃ j, System.restrict (maximalIdeal A) H ((GroupScheme.baseChange f).obj G) j = s) →
    AdicLimits (smallAdmissiblePresheaf G)

set_option maxHeartbeats 1500000 in
/-- Produce the actual torus lift and recover the original subgroup on every
adic quotient, with uniqueness from closed-subgroup containment. -/
theorem affineFiberTorusAdicLimits_of_homEffectivity : AffineFiberTorusAdicLimitsStatement.{u} := by
  intro S G _ _ _ hG heff A _ _ _ _ f
  refine ⟨adicRestriction_injective f, ?_⟩
  intro x hx
  let M := (GroupScheme.baseChange f).obj G
  let I := maximalIdeal A
  let R (n : ℕ) := A ⧸ I ^ n
  let P := smallAdmissiblePresheaf G
  let a (n : ℕ) := algebraOverBase f (R n)
  let φ (n : ℕ) : R (n + 1) →ₐ[A] R n := Ideal.Quotient.factorₐ A
    (Ideal.pow_le_pow_right (I := I) n.le_succ)
  let b (n : ℕ) := algHomOver f (φ n)
  let E (n : ℕ) := algebraAdmissibleEquiv (G := G) f (R (n + 1))
  let F (n : ℕ) := (E n).symm (x (n + 1))
  have hh (n : ℕ) : E n (F n) = x (n + 1) := (E n).apply_symm_apply _
  have hF (n : ℕ) : restrict (transitionOver I n) (F (n + 1)) = F n := by
    apply (E n).injective
    have h : E n (restrict (transitionOver I n) (F (n + 1))) =
        P.map (b (n + 1)).op (E (n + 1) (F (n + 1))) :=
      algebraAdmissibleEquiv_map (G := G) f (B := R (n + 2)) (C := R (n + 1))
        (φ (n + 1)) (F (n + 1))
    exact h.trans ((congrArg (P.map (b (n + 1)).op) (hh (n + 1))).trans
      ((hx (n + 1)).trans (hh n).symm))
  obtain ⟨H, s, hH, hs⟩ := adicTorusFamily A M F hF
  obtain ⟨j, hj⟩ := heff A f H hH s (fun n => (hs n).1)
  have : Smooth M.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : IsSeparated M.X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  have : QuasiCompact M.X.hom := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  have hjc := isClosedSubgroup_of_adic_torus_algebraization (hG.baseChange f) hH s
    (fun n => (hs n).1) j hj
  let J : AdmissibleSubgroup M := ⟨range j, isAdmissible_range j hjc hH⟩
  let E₀ := smallAdmissibleEquiv G (Over.mk f)
  let y := E₀.symm J
  have hy : range j = (E₀ y).val := congrArg Subtype.val (E₀.apply_symm_apply J).symm
  have hpos (n : ℕ) : P.map (a (n + 1)).op y = x (n + 1) := by
    have h := congrArg (fun d : System I H M => d.hom n) hj
    change (GroupScheme.baseChange (Spec.algebraMap A (R (n + 1)))).map j = s.hom n at h
    exact ((evaluate_algebraAdmissibleEquiv f (R (n + 1)) j y hy (F n)).mpr
      ((congrArg range h).trans (hs n).2)).trans (hh n)
  refine ⟨y, fun n => ?_⟩
  cases n with
  | succ n => exact hpos n
  | zero =>
    have hb : b 0 ≫ a 1 = a 0 := by
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom _) ≫ Spec.algebraMap A (R 1) = Spec.algebraMap A (R 0)
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
    change P.map (a 0).op y = x 0
    rw [← hb, op_comp, P.map_comp_apply, hpos 0]
    exact hx 0

end Langlands.GroupScheme.TorusSubgroupModuli
