import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeCentralizerReductive
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeCentralizerGeometry
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralizerReductiveProof
import Langlands.GroupScheme.Reductive.IdentityComponentClopenProof

/-! # Proof: centralizers of subgroups of multiplicative type over a general base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- `RelativeMultiplicativeTypeCentralizerStatement` follows from Conrad's Proposition 3.1.3
(`IdentityComponentClopenStatement`): parts (1) and (2) hold without this premise, and part
(3) uses it through `relativeMultiplicativeTypeCentralizer_reductive`. -/
theorem relativeMultiplicativeTypeCentralizer_of_identityComponentClopen
    (hClopen : IdentityComponentClopenStatement.{u}) :
    RelativeMultiplicativeTypeCentralizerStatement.{u} := by
  intro S G _ hlfp H i hH _
  have hcl := relativeMultiplicativeTypeCentralizer_isClosedRepresentable_of_affine i hH
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨Z, z, hrep, hz⟩ := hcl
    exact ⟨Z, z, hz,
      relativeMultiplicativeTypeCentralizer_locallyOfFinitePresentation i hH hrep hlfp, hrep⟩
  · intro hG Z z hz
    exact relativeMultiplicativeTypeCentralizer_smooth_of_smooth i hH hz hG
  · intro hG Z z hz Z₀ z₀ h₀
    exact relativeMultiplicativeTypeCentralizer_reductive hClopen
      multiplicativeTypeCentralizerReductive i hH hG hcl hz
      (relativeMultiplicativeTypeCentralizer_smooth_of_smooth i hH hz hG.smooth) h₀

/-- **Centralizers of subgroups of multiplicative type** (Conrad, *Reductive group schemes*
(2014), Lemma 2.2.4 for subgroups of multiplicative type, and Remark 3.1.5), in every
universe: for a finitely presented affine group scheme `G` over an arbitrary scheme `S` and a
closed subgroup `i : H ⟶ G` of multiplicative type, `Z_G(H)` is represented by a finitely
presented closed subgroup, every representative is smooth when `G` is smooth, and when `G` is
reductive the relative identity component of every representative is reductive, closed, and
has connected reductive fibres. -/
theorem relativeMultiplicativeTypeCentralizer :
    RelativeMultiplicativeTypeCentralizerStatement.{u} :=
  relativeMultiplicativeTypeCentralizer_of_identityComponentClopen identityComponentClopen

end Langlands.GroupScheme
