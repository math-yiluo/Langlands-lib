import Langlands.GroupScheme.Lie.SemisimpleCentralizerMaximalTori
import Langlands.GroupScheme.Cartan.StructureProof
import Langlands.GroupScheme.Nilpotent.CentralTorusProof
import Langlands.GroupScheme.Lie.UnipotentSemisimpleProof
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Commuting semisimple Lie elements in the Lie algebra of one maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Lie

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Differentiation of actual homomorphisms respects composition. -/
theorem targetMap_comp_apply {J : GroupScheme (Spec (CommRingCat.of k))}
    (f : H ⟶ G) (g : G ⟶ J) (X : lieKernel H k) :
    targetMap (f ≫ g) k X = targetMap g k (targetMap f k X) := by
  apply Subtype.ext
  change X.val ≫ (f ≫ g).hom.hom = (X.val ≫ f.hom.hom) ≫ g.hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

/-- A monomorphic homomorphism reflects all-test centralization of a lifted
tangent vector, point by point on every test scheme. -/
theorem mem_elementCentralizer_of_comp_mono (j : H ⟶ G) (hj : Mono j.hom.hom)
    (Y : lieKernel H k) {U : Over (Spec (CommRingCat.of k))} (g : U ⟶ H.X)
    (h : g ≫ j.hom.hom ∈ (elementCentralizer G (targetMap j k Y)).carrier U) :
    g ∈ (elementCentralizer H Y).carrier U := by
  intro A _ _ a
  have hc := h A a
  rw [lieKernelMap_target] at hc
  apply (commute_iff_eq _ _).mpr
  apply hj.right_cancellation
  rw [MonObj.mul_comp, MonObj.mul_comp]
  simpa only [constant, affineMap_apply, lieKernelTarget_val, Category.assoc] using hc.eq

/-- A monomorphic homomorphism reflects membership in Lie-element centralizers
of lifted tangent vectors. -/
theorem mem_elementCentralizerLie_of_mono [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (j : H ⟶ G) (hj : Mono j.hom.hom) {X Z : lieKernel H k}
    (h : Additive.ofMul (targetMap j k Z) ∈ elementCentralizerLie G (targetMap j k X)) :
    Additive.ofMul Z ∈ elementCentralizerLie H X :=
  mem_elementCentralizer_of_comp_mono j hj X Z.val h

/-- **Commuting semisimple Lie elements lie in one maximal torus.** Over any
field, let `G` be a smooth affine group scheme and let `l` be a finite list of
semisimple actual Lie elements of `G` such that each later entry lies in the
Lie centralizer of each earlier entry. Then one maximal torus of `G` has every
entry of `l` in its tangent image. -/
theorem exists_isMaximalTorus_forall_tangent_of_pairwise :
    ∀ (n : ℕ) (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom]
      [IsAffineHom G.X.hom] (l : List (lieKernel G k)), l.length = n →
      (∀ X ∈ l, IsSemisimpleElement G X) →
      l.Pairwise (fun X Z => Additive.ofMul Z ∈ elementCentralizerLie G X) →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
        IsMaximalTorus i ∧ ∀ X ∈ l, ∃ Y : lieKernel T.toGrp k, targetMap i k Y = X := by
  classical
  intro n
  induction n with
  | zero =>
    intro G _ _ l hl _ _
    obtain ⟨T, i, hi⟩ := maximalTorusExistence k G
    refine ⟨T, i, hi, ?_⟩
    intro X hX
    rw [List.length_eq_zero_iff.mp hl] at hX
    simp at hX
  | succ n ih =>
    intro G _ _ l hl hsem hpair
    match l, hl, hsem, hpair with
    | X :: rest, hl, hsem, hpair =>
      have hX : IsSemisimpleElement G X := hsem X List.mem_cons_self
      rw [List.pairwise_cons] at hpair
      let C := elementCentralizerGroup G X
      let c : C ⟶ G := elementCentralizerGroupι G X
      have hrep : (elementCentralizer G X).IsRepresentedBy c :=
        elementCentralizerGroup_isRepresentedBy G X
      have hc : IsClosedSubgroup c := isClosedSubgroup_elementCentralizerGroupι G X
      have : IsAffineHom C.X.hom := isAffineHom_elementCentralizerGroup G X
      have : Smooth C.X.hom := smooth_elementCentralizerGroup G hX
      have : IsAffineHom (identityComponent C).X.hom := inferInstance
      let : CommGroup (lieKernel (identityComponent C) k) :=
        lieKernelCommGroup (identityComponent C)
      let : Module k (Additive (lieKernel (identityComponent C) k)) :=
        lieKernelModule (identityComponent C)
      let incl : identityComponent C ⟶ G := identityComponentι C ≫ c
      have hincl : IsClosedSubgroup incl :=
        (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hc
      have : IsClosedImmersion incl.hom.hom.left := hincl
      have hinclmono : Mono incl.hom.hom := Over.mono_of_mono_left _
      have hrange : ∀ Z ∈ rest, ∃ Z' : lieKernel (identityComponent C) k,
          targetMap incl k Z' = Z := by
        intro Z hZ
        have hmem : Additive.ofMul Z ∈ LinearMap.range (targetMapLinear incl k) := by
          rw [← hrep.lie_eq_range_identityComponent k]
          exact hpair.1 Z hZ
        obtain ⟨Z', hZ'⟩ := hmem
        exact ⟨Z'.toMul, congrArg Additive.toMul hZ'⟩
      let lift : lieKernel G k → lieKernel (identityComponent C) k := fun Z =>
        if h : ∃ Z' : lieKernel (identityComponent C) k, targetMap incl k Z' = Z then
          h.choose else 1
      have hlift : ∀ Z ∈ rest, targetMap incl k (lift Z) = Z := by
        intro Z hZ
        have h := hrange Z hZ
        simp only [lift, h, ↓reduceDIte]
        exact h.choose_spec
      obtain ⟨S, s, hs, hS⟩ := ih (identityComponent C) (rest.map lift)
        (by simpa using hl)
        (by
          intro Z' hZ'
          obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hZ'
          apply isSemisimpleElement_of_closed_subgroup incl hincl
          rw [hlift Z hZ]
          exact hsem Z (List.mem_cons_of_mem X hZ))
        (by
          rw [List.pairwise_map]
          refine hpair.2.imp_of_mem ?_
          intro Z W hZ hW hZW
          apply mem_elementCentralizerLie_of_mono incl hinclmono
          rw [hlift Z hZ, hlift W hW]
          exact hZW)
      refine ⟨S, s ≫ identityComponentι C ≫ c,
        preservesMaximalTori_identityComponent_elementCentralizer_of_semisimple
          nilpotentCentralTorusStatement unipotentSemisimpleStatement cartanStructure
          hX c hrep hc S s hs, ?_⟩
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact ⟨semisimpleCentralizerTorusFactor nilpotentCentralTorusStatement
          unipotentSemisimpleStatement cartanStructure hX c hrep hc s hs,
          targetMap_semisimpleCentralizerTorusFactor _ _ _ _ _ _ _ _ _⟩
      · obtain ⟨Y, hY⟩ := hS (lift Z) (List.mem_map.mpr ⟨Z, hZ, rfl⟩)
        refine ⟨Y, ?_⟩
        change targetMap (s ≫ incl) k Y = Z
        rw [targetMap_comp_apply, hY, hlift Z hZ]

end Lie

end Langlands.GroupScheme
