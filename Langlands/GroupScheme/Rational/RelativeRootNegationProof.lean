import Langlands.GroupScheme.Rational.RelativeRootNegationStatement
import Langlands.GroupScheme.Rational.AbsoluteRootRestriction
import Langlands.GroupScheme.Reductive.RootReducednessProof
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Negation stability of the actual relative roots: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RootReducedness in
/-- The actual roots of a split maximal torus of a connected reductive group have
opposites. Pass to the reductive centralizer of a generic cocharacter in the kernel
of the given root, apply rank-one negation there, and include its roots in those
of the original group. -/
theorem neg_mem_roots_of_split_maximalTorus
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) {α : characterLattice T} :
    haveI := hG.isAffineHom
    α ∈ roots i → -α ∈ roots i := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  intro hα
  have hαζ := latticePairing_kernelCocharacter hT hα.1 (hT.finite_relativeRoots i)
  have hζ := fun chi (hchi : chi ∈ roots i) =>
    not_linearIndependent_of_latticePairing_kernelCocharacter hT hα.1
      (hT.finite_relativeRoots i) hchi
  generalize kernelCocharacter hT hα.1 (hT.finite_relativeRoots i) = ζ at hαζ hζ
  have hj := Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hjc := Dynamic.Affine.isClosedSubgroup_centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hL := dynamicCentralizerReductive k G hG _ _ _ hjc hj
  have := hL.isAffineHom
  have hiL : IsMaximalTorus (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) :=
    IsMaximalTorus.of_comp hjc (by rwa [Dynamic.torusFactor_comp])
  have hdep : ∀ chi ∈ roots (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj),
      ∀ psi ∈ roots (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj),
        ¬ LinearIndependent ℤ ![chi, psi] := by
    intro chi hchi psi hpsi
    obtain ⟨hchi', hchiζ⟩ := mem_roots_of_mem_roots_torusFactor i ζ hj hchi
    obtain ⟨hpsi', hpsiζ⟩ := mem_roots_of_mem_roots_torusFactor i ζ hj hpsi
    exact not_linearIndependent_of_not_linearIndependent hT hα.1 hpsi'.1
      (hζ chi hchi' hchiζ) (hζ psi hpsi' hpsiζ)
  have hneg := neg_mem_roots_of_rankOne hL hT _ hiL hdep
    (mem_roots_torusFactor i ζ hj hα hαζ)
  exact (mem_roots_of_mem_roots_torusFactor i ζ hj hneg).1

/-- Over every field, the actual relative roots of a maximal split torus in a
connected reductive group scheme are stable under additive negation. -/
theorem relativeRootNegation : RelativeRootNegationStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hG.smooth
  obtain ⟨M, j, hj, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G i hi.1.1.isTorus hi.1.2
  obtain ⟨K, _, _, hMK⟩ := hj.1
  let b := algebraBaseMap k K
  let G_K := (GroupScheme.baseChange b).obj G
  let M_K := (CommGroupScheme.baseChange b).obj M
  have hGK : IsConnectedReductive G_K := connectedReductiveFieldExtensionStatement k K G hG
  have := hGK.isAffineHom
  have hjK : IsMaximalTorus (T := M_K) ((GroupScheme.baseChange b).map j) :=
    (maximalTorusBaseChange k K G M j hj.1 hj.2.1).mp hj
  have hneg : ∀ α ∈ roots (f ≫ j), -α ∈ roots (f ≫ j) :=
    roots_negation_of_splittingField_restriction hi.1.1 hMK (Additive.ofMul f) j
      (fun _ hβ => neg_mem_roots_of_split_maximalTorus hGK hMK _ hjK hβ)
  change ∀ α ∈ roots i, -α ∈ roots i
  rwa [hf] at hneg

end Langlands.GroupScheme
