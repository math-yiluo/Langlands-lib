import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelTrivialization

/-! # Full level as an actual torsion-enumeration isomorphism -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S : Scheme.{u}} {A : AbelianScheme S} {g n : ℕ}

/-- The enumeration-to-kernel comparison before imposing fullness. -/
theorem torsionSection_restrict (v : SectionTuple A g n)
    (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (a : Fin (2 * g) → ZMod n) :
    kernelLevelEquiv A.toGrp (Over.mk s) n
        (Additive.ofMul ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫
          torsionSection v a)) =
      levelRestrict A.toGrp (Over.homMk s (by simp)) n (enumerateTuple v a) := by
  simpa only [torsionSection, AddEquiv.apply_symm_apply] using
    (levelRestrict_kernelLevelEquiv A.toGrp
      (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) n
      ((kernelLevelEquiv A.toGrp (Over.mk (𝟙 S)) n).symm
        (enumerateTuple v a))).symm

/-- An actual enumeration isomorphism gives a bijection on all field-valued fibres. -/
theorem torsionSection_fibre_bijective_of_isIso (v : SectionTuple A g n)
    [IsIso (torsionCoproductMap v)]
    (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) :
    Function.Bijective (fun a : Fin (2 * g) → ZMod n =>
      (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ torsionSection v a) := by
  let X := (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X
  let C := fun _ : Fin (2 * g) → ZMod n => S
  let w : Spec (CommRingCat.of K) := default
  constructor
  · intro a b hab
    have hmaps : s ≫ (torsionSection v a).left =
        s ≫ (torsionSection v b).left :=
      congrArg Over.Hom.left hab
    have h' : torsionCoproductMap v (Sigma.ι C a (s w)) =
        torsionCoproductMap v (Sigma.ι C b (s w)) := by
      have hι (c : Fin (2 * g) → ZMod n) :
          torsionCoproductMap v (Sigma.ι C c (s w)) =
            (torsionSection v c).left (s w) :=
        (Scheme.Hom.comp_apply (Sigma.ι C c) (torsionCoproductMap v) (s w)).symm.trans
          (congrArg (fun f => f (s w)) (torsionCoproductMap_ι v c))
      rw [hι a, hι b]
      exact congrArg (fun f : Spec (CommRingCat.of K) ⟶ X.left => f w) hmaps
    have h'' := (torsionCoproductMap v).isOpenEmbedding.injective h'
    exact congrArg Sigma.fst ((sigmaι_eq_iff C a b (s w) (s w)).mp h'')
  · intro x
    let q : Spec (CommRingCat.of K) ⟶ ∐ C := x.left ≫ inv (torsionCoproductMap v)
    obtain ⟨a, z, hz⟩ :
        ∃ (a : Fin (2 * g) → ZMod n) (z : S), Sigma.ι C a z = q w :=
      (sigmaOpenCover C).exists_eq (q w)
    have hq : Set.range q ⊆ Set.range (Sigma.ι C a) := by
      rintro _ ⟨w', rfl⟩
      refine ⟨z, ?_⟩
      have hw : w' = w := Subsingleton.elim _ _
      rw [hw]
      exact hz
    let l := IsOpenImmersion.lift (Sigma.ι C a) q hq
    have hl : l ≫ Sigma.ι C a = q := IsOpenImmersion.lift_fac _ _ _
    have hx : l ≫ (torsionSection v a).left = x.left := by
      rw [← torsionCoproductMap_ι, ← Category.assoc, hl]
      simp only [q, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hls : l = s := by
      calc
        l = (l ≫ (torsionSection v a).left) ≫ X.hom := by
          rw [Category.assoc, (torsionSection v a).w]
          exact (Category.comp_id l).symm
        _ = x.left ≫ X.hom := by rw [hx]
        _ = s := x.w
    refine ⟨a, ?_⟩
    apply Over.OverMorphism.ext
    change s ≫ (torsionSection v a).left = x.left
    simpa only [hls] using hx

/-- The fibrewise basis condition follows from the actual enumeration isomorphism. -/
theorem isFull_of_torsionCoproductMap_isIso (v : SectionTuple A g n)
    [IsIso (torsionCoproductMap v)] : IsFull v := by
  intro K _ _ s
  let l := Fintype.linearCombination (ZMod n) (fibreTuple v s)
  have heq (a : Fin (2 * g) → ZMod n) :
      l a = kernelLevelEquiv A.toGrp (Over.mk s) n
        (Additive.ofMul ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫
          torsionSection v a)) := by
    rw [torsionSection_restrict]
    simp only [l, Fintype.linearCombination_apply, enumerateTuple, map_sum,
      ZMod.map_smul, fibreTuple]
  have hbij : Function.Bijective l := by
    simpa only [Function.comp_def, ← heq] using
      (kernelLevelEquiv A.toGrp (Over.mk s) n).bijective.comp
        (Additive.ofMul.bijective.comp (torsionSection_fibre_bijective_of_isIso v K s))
  let e := LinearEquiv.ofBijective l hbij
  refine ⟨Module.Basis.ofEquivFun e.symm, ?_⟩
  intro i
  rw [Module.Basis.coe_ofEquivFun]
  change l (Pi.single i 1) = fibreTuple v s i
  simp [l]

/-- Recover the exact existing full-level structure from the actual isomorphism. -/
def fullLevelOfTorsionCoproductIsIso (v : SectionTuple A g n)
    [IsIso (torsionCoproductMap v)] : FullLevel A g n :=
  ⟨v, isFull_of_torsionCoproductMap_isIso v⟩

/-- At positive invertible level, the exact fullness condition is equivalent
to invertibility of the actual scheme enumeration map. -/
theorem isFull_iff_torsionCoproductMap_isIso (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    IsFull v ↔ IsIso (torsionCoproductMap v) := by
  constructor
  · intro h
    exact (FullLevel.mk v h).torsionCoproductMap_isIso hn hunit
  · intro h
    exact isFull_of_torsionCoproductMap_isIso v

end Langlands.AbelianScheme.PolarizedFiniteLevel
